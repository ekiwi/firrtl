// SPDX-License-Identifier: Apache-2.0
// Author: Kevin Laeufer <laeufer@cs.berkeley.edu>

package firrtl.backends.experimental.smt

import FirrtlExpressionSemantics.getWidth
import firrtl.{
  ir,
  MemoryArrayInit,
  MemoryInitValue,
  MemoryScalarInit,
  Namespace,
  Utils
}
import logger.LazyLogging

import scala.collection.mutable

private class MemoryEncoding(makeRandom: (String, Int) => BVExpr, namespace: Namespace) extends LazyLogging {
  type Connects = Iterable[(String, BVExpr)]
  def onMemory(
    defMem:    ir.DefMemory,
    connects:  Connects,
    initValue: Option[MemoryInitValue]
  ): (Iterable[State], Connects) = {
    // we can only work on appropriately lowered memories
    assert(
      defMem.dataType.isInstanceOf[ir.GroundType],
      s"Memory $defMem is of type ${defMem.dataType} which is not a ground type!"
    )
    assert(defMem.readwriters.isEmpty, "Combined read/write ports are not supported! Please split them up.")

    // collect all memory meta-data in a custom class
    val m = new MemInfo(defMem)

    // find all connections related to this memory
    val inputs = connects.filter(_._1.startsWith(m.prefix)).toMap

    // there could be a constant init
    val init = initValue.map(getInit(m, _))

    // parse and check read and write ports
    val writers = defMem.writers.map(w => new WritePort(m, w, inputs))
    val readers = defMem.readers.map(r => new ReadPort(m, r, inputs))

    // derive next state from all write ports
    assert(defMem.writeLatency == 1, "Only memories with write-latency of one are supported.")
    val next: ArrayExpr = if (writers.isEmpty) { m.sym }
    else {
      if (writers.length > 2) {
        throw new UnsupportedFeatureException(s"memories with 3+ write ports (${m.name})")
      }
      val validData = writers.foldLeft[ArrayExpr](m.sym) { case (sym, w) => w.writeTo(sym) }
      if (writers.length == 1) { validData }
      else {
        assert(writers.length == 2)
        val conflict = writers.head.doesConflict(writers.last)
        val conflictData = writers.head.makeRandomData("_write_write_collision")
        val conflictStore = ArrayStore(m.sym, writers.head.addr, conflictData)
        ArrayIte(conflict, conflictStore, validData)
      }
    }
    val state = State(m.sym, init, Some(next))

    // derive data signals from all read ports
    assert(defMem.readLatency >= 0)
    if (defMem.readLatency > 1) {
      throw new UnsupportedFeatureException(s"memories with read latency 2+ (${m.name})")
    }
    val readPortSignals = if (defMem.readLatency == 0) {
      readers.map { r =>
        // combinatorial read
        if (defMem.readUnderWrite != ir.ReadUnderWrite.New) {
          logger.warn(
            s"WARN: Memory ${m.name} with combinatorial read port will always return the most recently written entry." +
              s" The read-under-write => ${defMem.readUnderWrite} setting will be ignored."
          )
        }
        // since we do a combinatorial read, the "old" data is the current data
        val data = r.read()
        r.data.name -> data
      }
    } else { Seq() }
    val readPortSignalsAndStates = if (defMem.readLatency == 1) {
      readers.map { r =>
        defMem.readUnderWrite match {
          case ir.ReadUnderWrite.New =>
            // create a state to save the address and the enable signal
            val enPrev = BVSymbol(namespace.newName(r.en.name + "_prev"), r.en.width)
            val addrPrev = BVSymbol(namespace.newName(r.addr.name + "_prev"), r.addr.width)
            val signal = r.data.name -> r.read(addr = addrPrev, en = enPrev)
            val states = Seq(State(enPrev, None, next = Some(r.en)), State(addrPrev, None, next = Some(r.addr)))
            (Seq(signal), states)
          case ir.ReadUnderWrite.Undefined =>
            // check for potential read/write conflicts in which case we need to return an arbitrary value
            val anyWriteToTheSameAddress = any(writers.map(_.doesConflict(r)))
            val next = if (anyWriteToTheSameAddress == False) { r.read() }
            else {
              val readUnderWriteData = r.makeRandomData("_read_under_write_undefined")
              BVIte(anyWriteToTheSameAddress, readUnderWriteData, r.read())
            }
            (Seq(), Seq(State(r.data, init = None, next = Some(next))))
          case ir.ReadUnderWrite.Old =>
            // we create a register for the read port data
            (Seq(), Seq(State(r.data, init = None, next = Some(r.read()))))
        }
      }
    } else { Seq() }

    val allReadPortSignals = readPortSignals ++ readPortSignalsAndStates.flatMap(_._1)
    val readPortStates = readPortSignalsAndStates.flatMap(_._2)

    (state +: readPortStates, allReadPortSignals)
  }

  private def getInit(m: MemInfo, initValue: MemoryInitValue): ArrayExpr = initValue match {
    case MemoryScalarInit(value) => ArrayConstant(BVLiteral(value, m.dataWidth), m.indexWidth)
    case MemoryArrayInit(values) =>
      assert(
        values.length == m.depth,
        s"Memory ${m.name} of depth ${m.depth} cannot be initialized with an array of length ${values.length}!"
      )
      // in order to get a more compact encoding try to find the most common values
      val histogram = mutable.LinkedHashMap[BigInt, Int]()
      values.foreach(v => histogram(v) = 1 + histogram.getOrElse(v, 0))
      val baseValue = histogram.maxBy(_._2)._1
      val base = ArrayConstant(BVLiteral(baseValue, m.dataWidth), m.indexWidth)
      values.zipWithIndex
        .filterNot(_._1 == baseValue)
        .foldLeft[ArrayExpr](base) {
          case (array, (value, index)) =>
            ArrayStore(array, BVLiteral(index, m.indexWidth), BVLiteral(value, m.dataWidth))
        }
    case other => throw new RuntimeException(s"Unsupported memory init option: $other")
  }

  private class MemInfo(m: ir.DefMemory) {
    val name = m.name
    val depth = m.depth
    // derrive the type of the memory from the dataType and depth
    val dataWidth = getWidth(m.dataType)
    val indexWidth = Utils.getUIntWidth(m.depth - 1).max(1)
    val sym = ArraySymbol(m.name, indexWidth, dataWidth)
    val prefix = m.name + "."
    val fullAddressRange = (BigInt(1) << indexWidth) == m.depth
    lazy val depthBV = BVLiteral(m.depth, indexWidth)
    def isValidAddress(addr: BVExpr): BVExpr = {
      if (fullAddressRange) { True }
      else {
        BVComparison(Compare.Greater, depthBV, addr, signed = false)
      }
    }
  }
  private abstract class MemPort(memory: MemInfo, val name: String, inputs: String => BVExpr) {
    val en:   BVSymbol = makeField("en", 1)
    val data: BVSymbol = makeField("data", memory.dataWidth)
    val addr: BVSymbol = makeField("addr", memory.indexWidth)
    protected def makeField(field: String, width: Int): BVSymbol = BVSymbol(memory.prefix + name + "." + field, width)
    // make sure that all widths are correct
    assert(inputs(en.name).width == en.width)
    assert(inputs(addr.name).width == addr.width)
    val enIsTrue: Boolean = inputs(en.name) == True
    def makeRandomData(suffix: String): BVExpr =
      makeRandom(memory.name + "_" + name + suffix, memory.dataWidth)
    def read(addr: BVSymbol = addr, en: BVSymbol = en): BVExpr = {
      val canBeOutOfRange = !memory.fullAddressRange
      val canBeDisabled = !enIsTrue
      val data = ArrayRead(memory.sym, addr)
      val dataWithRangeCheck = if (canBeOutOfRange) {
        val outOfRangeData = makeRandomData("_addr_out_of_range")
        BVIte(memory.isValidAddress(addr), data, outOfRangeData)
      } else { data }
      val dataWithEnabledCheck = if (canBeDisabled) {
        val disabledData = makeRandomData("_not_enabled")
        BVIte(en, dataWithRangeCheck, disabledData)
      } else { dataWithRangeCheck }
      dataWithEnabledCheck
    }
  }
  private class WritePort(memory: MemInfo, name: String, inputs: String => BVExpr)
    extends MemPort(memory, name, inputs) {
    assert(inputs(data.name).width == data.width)
    val mask: BVSymbol = makeField("mask", 1)
    assert(inputs(mask.name).width == mask.width)
    val maskIsTrue: Boolean = inputs(mask.name) == True
    val doWrite: BVExpr = (enIsTrue, maskIsTrue) match {
      case (true, true)   => True
      case (true, false)  => mask
      case (false, true)  => en
      case (false, false) => and(en, mask)
    }
    def doesConflict(r: ReadPort): BVExpr = {
      val sameAddress = BVEqual(r.addr, addr)
      if (doWrite == True) { sameAddress }
      else { and(doWrite, sameAddress) }
    }
    def doesConflict(w: WritePort): BVExpr = {
      val bothWrite = and(doWrite, w.doWrite)
      val sameAddress = BVEqual(addr, w.addr)
      if (bothWrite == True) { sameAddress }
      else { and(bothWrite, sameAddress) }
    }
    def writeTo(array: ArrayExpr): ArrayExpr = {
      val doUpdate = if (memory.fullAddressRange) doWrite else and(doWrite, memory.isValidAddress(addr))
      val update = ArrayStore(array, index = addr, data = data)
      if (doUpdate == True) update else ArrayIte(doUpdate, update, array)
    }

  }
  private class ReadPort(memory: MemInfo, name: String, inputs: String => BVExpr)
    extends MemPort(memory, name, inputs) {}

  private def and(a: BVExpr, b: BVExpr): BVExpr = (a, b) match {
    case (True, True) => True
    case (True, x)    => x
    case (x, True)    => x
    case _            => BVOp(Op.And, a, b)
  }
  private def or(a: BVExpr, b: BVExpr): BVExpr = BVOp(Op.Or, a, b)
  private val True = BVLiteral(1, 1)
  private val False = BVLiteral(0, 1)
  private def all(b: Iterable[BVExpr]): BVExpr = if (b.isEmpty) False else b.reduce((a, b) => and(a, b))
  private def any(b: Iterable[BVExpr]): BVExpr = if (b.isEmpty) True else b.reduce((a, b) => or(a, b))
}