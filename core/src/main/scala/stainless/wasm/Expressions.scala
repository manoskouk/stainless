/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasm

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
          val typedRec = s.getRecord(id, tps)
          typedRec.flattenFields.find(_.id == id).get.tpe
        case _ => Untyped
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

  sealed case class NewArray(length: Expr, init: Expr) extends Expr {
    def getType(implicit s: Symbols) =
      if (length.getType == Int32Type())
        unveilUntyped(ArrayType(init.getType))
      else Untyped
  }

  sealed case class ArrayGet(array: Expr, index: Expr) extends Expr {
    def getType(implicit s: Symbols) = (array.getType, index.getType) match {
      case (ArrayType(base), Int32Type()) => base
      case _ => Untyped
    }
  }
  
  sealed case class ArraySet(array: Expr, index: Expr, value: Expr) extends Expr {
    def getType(implicit s: Symbols) = (array.getType, index.getType, value.getType) match {
      case (ArrayType(base1), Int32Type(), base2) if base1 == base2 => UnitType()
      case _ => Untyped
    }
  }

  sealed case class ArrayLength32(array: Expr) extends Expr {
    def getType(implicit s: Symbols) = array.getType match {
      case ArrayType(_) => Int32Type()
      case _ => Untyped
    }
  }

  sealed case class ArrayCopy(from: Expr, to: Expr, startIndex: Expr) extends Expr {
    def getType(implicit s: Symbols) = (from.getType, to.getType, startIndex.getType) match {
      case (ArrayType(base1), ArrayType(base2), Int32Type()) if base1 == base2 => UnitType()
      case _ => Untyped
    }
  }
 
}
