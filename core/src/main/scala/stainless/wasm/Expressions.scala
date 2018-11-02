/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasm

import inox.ast.Identifier

trait Expressions extends stainless.ast.Expressions { self: Trees =>
  sealed case class Record(tpe: RecordType, fields: Seq[Expr]) extends Expr {
    def getType(implicit s: Symbols): Type = {
      checkParamTypes(fields, tpe.flattenFields, tpe)
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
    def getType(implicit s: Symbols): Type = {
      e.getType match {
        case subtype: RecordType if subtype conformsWith supertype => supertype
        case _ => Untyped
      }
    }
  }
}
