package stainless
package wasmgen
package wasm

import scala.language.implicitConversions
import Types._

// A subset of instructions defined by the WASM standard
object Expressions { self =>

  abstract class Sign
  case object Signed   extends Sign { override def toString = "s" }
  case object Unsigned extends Sign { override def toString = "u" }

  abstract class UnOp {
    def apply(e1: Expr) = Unary(this, e1.getType, e1)
  }
  // Int only
  case object eqz extends UnOp // Return 1 if operand is 0, 0 otherwise
  // TODO: Add the rest
  // Float only
  case object neg extends UnOp
  // TODO: ADD the rest

  abstract class BinOp {
    def apply(e1: Expr, e2: Expr) = Binary(this, e1.getType, e1, e2)
  }
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

  abstract class Expr { def getType: Type }

  // Operators
  case class Binary(op: BinOp, tpe: Type, lhs: Expr, rhs: Expr) extends Expr {
    val getType = op match {
      case self.eq | self.ne => i32
      case _ => tpe
    }
  }
  case class Unary(op: UnOp, tpe: Type, expr: Expr) extends Expr {
    val getType = op match {
      case `eqz` => i32
      case _ => tpe
    }
  }

  // Int-Int Conversions
  case class Extend(from: Type, to: Type, sign: Sign, e: Expr) extends Expr {
    val getType = to
  }
  case class Wrap(from: Type, to: Type, e: Expr) extends Expr {
    val getType = to
  }

  // Constants
  case class I32Const(value: Int)     extends Expr { val getType = i32 }
  case class I64Const(value: Long)    extends Expr { val getType = i64 }
  case class F32Const(value: Float)   extends Expr { val getType = f32 }
  case class F64Const(value: Double)  extends Expr { val getType = f64 }

  // Control instructions
  case class If(label: Label, tpe: Type, cond: Expr, thenn: Expr, elze: Expr) extends Expr {
    val getType = tpe 
  }
  // A block of instructions with a label at the beginning
  case class Loop(label: Label, tpe: Type, body: Expr) extends Expr {
    val getType = tpe
  }
  // A block of instructions with a label at the end
  case class Branch(label: Label, tpe: Type, body: Expr) extends Expr {
    val getType = tpe
  }
  // Jump to "label", which MUST be the label of an enclosing structure
  case class Br(label: Label) extends Expr {
    val getType = void
  }

  case class Br_If(label: Label, cond: Expr) extends Expr {
    val getType = void
  }

  case class Call(name: Label, tpe: Type, args: Seq[Expr]) extends Expr {
    val getType = tpe
  }
  case object Drop extends Expr {
    val getType = void
  }
  case object Return extends Expr {
    val getType = void 
  }
  case object Unreachable extends Expr {
    val getType = void
  }

  case class Load(tpe: Type, truncate: Option[(Type,Sign)], address: Expr) extends Expr {
    val getType = truncate.map(_._1).getOrElse(tpe)
  }
  
  case class Store(tpe: Type, truncate: Option[Type], address: Expr, value: Expr) extends Expr {
    val getType = void
  }

  // Variable instructions
  case class GetLocal(label: Label)(implicit lh: LocalsHandler) extends Expr {
    val getType = lh.getType(label)
  }
  case class SetLocal(l: Label, value: Expr) extends Expr {
    val getType = void
  }

  case class GetGlobal(label: Label)(implicit gh: GlobalsHandler) extends Expr {
    val getType = gh.getType(label)
  }
  case class SetGlobal(l: Label, value: Expr) extends Expr {
    val getType = void
  }

  case class Sequence(es: Seq[Expr]) extends Expr {
    val getType = es.map(_.getType).filter(_ != void) match {
      case Seq(tpe) => tpe
      case other => sys.error("Sequence containing multiple values with non-void types")
    }
  }

}
