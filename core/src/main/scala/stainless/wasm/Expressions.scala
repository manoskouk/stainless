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

  sealed case class NewArray(length: Expr, elem: Expr) extends Expr {
    def getType(implicit s: Symbols) =
      if (length.getType == Int32Type)
        unveilUntyped(ArrayType(elem.getType))
      else Untyped
  }

  sealed case class ArrayGet(array: Expr, index: Expr)
}
