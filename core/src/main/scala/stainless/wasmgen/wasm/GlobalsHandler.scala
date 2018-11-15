package stainless.wasmgen.wasm
import Types.Type

class GlobalsHandler {
  private var globals_ = Seq[(Label, Type)]()

  def getFreshGlobal(l: Label, tpe: Type): Label = {
    globals_ :+= (l, tpe)
    l
  }
  def getType(l: Label): Type = globals_.find(_._1 == l).get._2
  private[wasmgen] def globals: Seq[(Label, Type)] = {
    globals_
  }
}

