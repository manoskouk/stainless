package stainless.wasmgen.wasm

import Expressions.Expr
import Types.Type

object Definitions {

  case class ValDef(name: Label, tpe: Type)

  case class FunDef private
    (name: String, args: Seq[ValDef], returnType: Type, locals: Seq[ValDef], body: Expr)
  {
    override def toString: String = ModulePrinter(this)
  }

  object FunDef {
    def apply(name: String, args: Seq[ValDef], returnType: Type)(codeGen: LocalsHandler => Expr): FunDef = {
      val lh = new LocalsHandler(args)
      // Make code first, as it may increment the locals in lh
      val body = codeGen(lh)
      FunDef(name, args, returnType, lh.locals, body)
    }
  }

  case class Import()

  case class Table(funs: Seq[Label]) {
    def indexOf(fun: Label) = funs.indexOf(fun)
  }
}
