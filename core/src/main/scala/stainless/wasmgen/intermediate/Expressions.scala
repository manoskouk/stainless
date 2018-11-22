/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.intermediate

import inox.ast.Identifier

trait Expressions extends stainless.ast.Expressions { self: Trees =>

  sealed case class Record(tpe: RecordType, fields: Seq[Expr]) extends Expr {
    def getType(implicit s: Symbols): Type = {
      checkParamTypes(fields, tpe.getRecord.flattenFields, tpe)
    }
  }

  sealed case class RecordSelector(record: Expr, selector: Identifier) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols) = {
      record.getType match {
        case RecordType(id, tps) =>
          s.getRecord(id, tps).flattenFields
           .find(_.id == selector).get
           .tpe
        case _ =>
          Untyped
      }
    }
  }

  sealed case class FunctionPointer(id: Identifier) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = {
      s.lookupFunction(id)
        .map(tfd => FunctionType(tfd.params.map(_.getType), tfd.getType))
        .getOrElse(Untyped)
    }
  }

  sealed case class CastDown(e: Expr, subtype: RecordType) extends Expr {
    def getType(implicit s: Symbols): Type = {
      e.getType match {
        case supertype: RecordType if subtype conformsWith supertype => subtype
        case _ => Untyped
      }
    }
  }

  sealed case class CastUp(e: Expr, supertype: RecordType) extends Expr {
    def getType(implicit s: Symbols): Type = e.getType match {
      case subtype: RecordType if subtype conformsWith supertype => supertype
      case _ => Untyped
    }
  }

  sealed case class Output(msg: Expr) extends Expr {
    def getType(implicit s: Symbols) = UnitType()
  }

  sealed case class Sequence(e1: Expr, e2: Expr) extends Expr {
    def getType(implicit s: Symbols) = e2.getType
  }

  /** $encodingof `... == ...` */
  sealed case class EqualsI32(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = {
      if (lhs.getType == rhs.getType) Int32Type()
      else Untyped
    }
  }

  sealed case class IfExprI32(cond: Expr, thenn: Expr, elze: Expr) extends Expr {
    def getType(implicit s: Symbols) = (cond.getType, thenn.getType, elze.getType) match {
      case (Int32Type(), tt, et) if tt == et => tt
      case _ => Untyped
    }
  }

  sealed case class NewArray(length: Expr, base: Type, init: Option[Expr]) extends Expr {
    def getType(implicit s: Symbols) =
      if (length.getType == Int32Type() && init.forall(_.getType == base)) ArrayType(base)
      else Untyped
  }

  sealed case class ArraySet(array: Expr, index: Expr, value: Expr) extends Expr {
    def getType(implicit s: Symbols) = (array.getType, index.getType, value.getType) match {
      case (ArrayType(base1), Int32Type(), base2) if base1 == base2 => UnitType()
      case _ => Untyped
    }
  }

  /** Copies elements from array 'from' to array 'to',
    * starting with the element at index 'start' and ending with the element at index 'end'-1
    */
  sealed case class ArrayCopy(from: Expr, to: Expr, start: Expr, end: Expr) extends Expr {
    def getType(implicit s: Symbols) = (from.getType, to.getType, start.getType, end.getType) match {
      case (ArrayType(base1), ArrayType(base2), Int32Type(), Int32Type()) if base1 == base2 => UnitType()
      case _ => Untyped
    }
  }

  // Helpers for unsigned literals
  object IndexLiteral {
    def apply(x: Int): BVLiteral = BVLiteral(false, BigInt(x), 32)
    def unapply(e: Expr): Option[Int] = e match {
      case b @ BVLiteral(false, _, 32) => Some(b.toBigInt.toByte)
      case _ => None
    }
  }

  object ByteLiteral {
    def apply(x: Byte): BVLiteral = BVLiteral(false, BigInt(x), 8)
    def unapply(e: Expr): Option[Byte] = e match {
      case b @ BVLiteral(false, _, 8) => Some(b.toBigInt.toByte)
      case _ => None
    }
  }
}
