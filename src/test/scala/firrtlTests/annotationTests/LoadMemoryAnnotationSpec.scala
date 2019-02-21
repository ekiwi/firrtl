// See LICENSE for license details.

package firrtlTests.annotationTests

import firrtl.annotations.{CircuitName, ComponentName, LoadMemoryAnnotation, ModuleName}
import org.scalatest.{FreeSpec, Matchers}

class LoadMemoryAnnotationSpec extends FreeSpec with Matchers {
  "LoadMemoryAnnotation getFileName" - {
    "add name of subcomponent to file name when a memory was split" in {
      val lma = new LoadMemoryAnnotation(
        ComponentName("init_mem_subdata", ModuleName("b", CircuitName("c"))),
        "somepath/init_mem",
        originalMemoryNameOpt = Some("init_mem")
      )

      lma.getFileName should be("somepath/init_mem_subdata")
    }
    "and do that properly when there are dots in earlier sections of the path" in {
      val lma = new LoadMemoryAnnotation(
        ComponentName("init_mem_subdata", ModuleName("b", CircuitName("c"))),
        "./target/scala-2.12/test-classes/init_mem",
        originalMemoryNameOpt = Some("init_mem")
      )

      lma.getFileName should be("./target/scala-2.12/test-classes/init_mem_subdata")
    }
  }
}