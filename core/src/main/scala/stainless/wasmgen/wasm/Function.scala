package stainless.wasmgen.wasm

import Expressions.Expr
import Types.Type

case class Function private
  (name: String, args: Seq[(Label, Type)], returnType: Type, locals: Seq[(Label, Type)], body: Expr)
{
  override def toString: String = ModulePrinter(this)
}


object Function {
  def apply(name: String, args: Seq[(Label, Type)], returnType: Type)(codeGen: LocalsHandler => Expr): Function = {
    val lh = new LocalsHandler(args)
    // Make code first, as it may increment the locals in lh
    val body = codeGen(lh)
    new Function(name, args, returnType, lh.locals, body)
  }
}
