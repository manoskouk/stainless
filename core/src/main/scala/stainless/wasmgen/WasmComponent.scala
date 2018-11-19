/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package wasmgen

import inox.Context
import inox.transformers.SymbolTransformer
import extraction.StainlessPipeline
import scala.concurrent.Future

object DebugSectionWasm extends inox.DebugSection("wasm")

class WasmAnalysis extends AbstractAnalysis {
  val name = "no analysis"
  type Report = NoReport

  def toReport = new NoReport
}

object WasmComponent extends Component {
  val name = "wasm-codegen"
  val description = "Generate WebAssembly code that runs parameterless functions in the program"
  type Report = NoReport
  type Analysis = WasmAnalysis

  override val lowering: SymbolTransformer {
    val s: extraction.trees.type
    val t: extraction.trees.type
  } = inox.transformers.SymbolTransformer(new transformers.TreeTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees
  })

  def run(pipeline: StainlessPipeline)(implicit context: Context) =
    new WasmComponentRun(pipeline)(context)
}

class WasmComponentRun(override val pipeline: StainlessPipeline)
                      (override implicit val context: inox.Context) extends {
  override val component = WasmComponent
  override val trees: stainless.trees.type = stainless.trees
} with ComponentRun {

  def parse(json: io.circe.Json): component.Report = new NoReport

  private[stainless] def apply(functions: Seq[Identifier], symbols: trees.Symbols): Future[WasmAnalysis] = {
    Future.successful {
      val fw = new wasm.FileWriter(codegen.LinearMemoryCodeGen.transform(intermediate.RecordAbstractor.transform(symbols)))
      fw.writeWasmText()
      fw.writeNodejsWrapper()
      new WasmAnalysis
    }
  }
}
