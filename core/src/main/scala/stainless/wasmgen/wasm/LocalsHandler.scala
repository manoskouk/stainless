package stainless.wasmgen.wasm
import Types.Type

class LocalsHandler(args: Seq[(Label, Type)]) {
  private var locals_ = args

  def getFreshLocal(l: Label, tpe: Type): Label = {
    locals_ :+= (l, tpe)
    l
  }
  def getType(l: Label): Type = locals.find(_._1 == l).get._2
  private[wasmgen] def locals: Seq[(Label, Type)] = {
    locals_.drop(args.size)
  }
}

