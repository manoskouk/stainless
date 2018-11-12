package stainless.wasmgen.wasm

import Expressions.Expr
import Types.Type

case class Function private (name: String, args: Seq[Type], returnType: Type, locals: Seq[Type], body: Expr) {
  override def toString: String = ModulePrinter(this)
}

class LocalsHandler[Id](args: Seq[(Id, Type)]) {
  import scala.collection.mutable.{Map => MMap}
  private var index = args.size - 1
  private var locals_ = MMap[Id, (Int, Type)]()
  locals_ ++= {
    args.zipWithIndex.map{ case ((a, tpe), ind) =>
      a -> (ind, tpe)
    }
  }
  def getFreshLocal(a: Id, tpe: Type): Int = {
    index += 1
    locals_ += a -> (index, tpe)
    index
  }
  def getLocal(a: Id): Int = locals_(a)._1
  private[wasmgen] def locals: Seq[Type] = {
    locals_.toSeq.sortBy(_._2._1).map(_._2._2).drop(args.size)
  }
}

object Function {
  def apply[Id](name: String, args: Seq[(Id, Type)], returnType: Type)(codeGen: LocalsHandler[Id] => Expr): Function = {
    val lh = new LocalsHandler(args)
    // Make code first, as it may increment the locals in lh
    val body = codeGen(lh)
    new Function(name, args map (_._2), returnType, lh.locals, body)
  }
}
