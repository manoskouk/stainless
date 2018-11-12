package stainless
package wasmgen
package wasm

import scala.language.implicitConversions

// A subset of instructions defined by the WASM standard
object Expressions {
  import Types._
  type Label = String

  abstract class Sign
  case object Signed   extends Sign { override def toString = "s" }
  case object Unsigned extends Sign { override def toString = "u" }

  abstract class UnOp
  // Int only
  case object eqz extends UnOp // Return 1 if operand is 0, 0 otherwise
  // TODO: Add the rest
  // Float only
  case object neg extends UnOp
  // TODO: ADD the rest
  // Int and float
  case class load(loadType: Option[(Type,Sign)]) extends UnOp {
    override def toString = loadType match {
      case None => "load"
      case Some((tpe, sign)) => s"load${tpe.size}_$sign"
    }
  }
  case class SetLocal(index: Int) extends UnOp {
    override def toString = s"set_local $index"
  }
  case class SetGlobal(index: Int) extends UnOp {
    override def toString = s"set_global $index"
  }

  abstract class BinOp
  trait Signed {
    val sign: Sign
    val name = getClass.getName.init

    override def toString = s"${name}_$sign"
  }

  // mk: This is a little hacky since we use the same names for multiple operations but oh well
  // Int and float instructions
  case object add extends BinOp
  case object sub extends BinOp
  case object mul extends BinOp
  case object eq  extends BinOp
  case object ne  extends BinOp
  // Int only
  case class div(sign: Sign) extends BinOp with Signed
  case class rem(sign: Sign) extends BinOp with Signed
  case object and extends BinOp
  case object or  extends BinOp
  case object xor extends BinOp
  case object shl extends BinOp
  case class shr(sign: Sign) extends BinOp with Signed
  case object rotl extends BinOp
  case object rotr extends BinOp
  case class lt(sign: Sign) extends BinOp with Signed
  case class le(sign: Sign) extends BinOp with Signed
  case class gt(sign: Sign) extends BinOp with Signed
  case class ge(sign: Sign) extends BinOp with Signed
  // float only
  case object div extends BinOp
  case object min extends BinOp
  case object max extends BinOp
  case object copysign extends BinOp
  case object lt extends BinOp
  case object le extends BinOp
  case object gt extends BinOp
  case object ge extends BinOp


  case class store(storageSize: Option[Type]) extends BinOp {
    override def toString = storageSize match {
      case None => "store"
      case Some(tpe) => s"store${tpe.size}"
    }
  }

  abstract class Expr

  // Operators
  case class Binary(op: BinOp, tpe: Type, lhs: Expr, rhs: Expr) extends Expr
  case class Unary(op: UnOp, tpe: Type, expr: Expr) extends Expr

  // Int-Int Conversions
  case class Extend(from: Type, to: Type, sign: Sign, e: Expr) extends Expr
  case class Wrap(from: Type, to: Type, e: Expr) extends Expr

  // Constants
  case class I32Const(value: Int) extends Expr
  case class I64Const(value: Long) extends Expr
  case class F32Const(value: Float) extends Expr
  case class F64Const(value: Double) extends Expr

  // Control instructions
  case class If(label: Label, tpe: Type, cond: Expr, thenn: Expr, elze: Expr) extends Expr
  case class Loop(label: Label, tpe: Type, body: Expr) extends Expr // A block of instructions with a label at the beginning
  case class Branch(label: Label, tpe: Type, body: Expr) extends Expr // A block of instructions with a label at the end
  case class Br(label: Label)  extends Expr // Jump to "label", which MUST be the label of an enclosing structure
  case class Call(name: Label, args: Seq[Expr]) extends Expr
  case object Return           extends Expr
  case object Unreachable      extends Expr

  // Variable instructions
  case class GetLocal(index: Int) extends Expr
  case class GetGlobal(index: Int) extends Expr

  case class Sequence(es: Seq[Expr]) extends Expr
}
