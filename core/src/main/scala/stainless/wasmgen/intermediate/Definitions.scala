/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.intermediate

import stainless.{FreshIdentifier, Identifier}

trait Definitions extends stainless.ast.Definitions { self: Trees =>
  override type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols extends super.AbstractSymbols { self0: Symbols =>
    val records: Map[Identifier, RecordSort]
    val sorts: Map[Identifier, ADTSort] = Map()

    def lookupRecord(id: Identifier): Option[RecordSort] = records.get(id)
    def getRecord(id: Identifier): RecordSort = records.getOrElse(id, throw ADTLookupException(id))
  }

  /** Tags dynamically called functions */
  case object Dynamic extends Flag("dynamic", Seq.empty)

  /** A record type represents a sequence of named fields in memory.
    * The parent's fields come first, then the fields of the current record.
    * A record complies to its parent's type.
    * Implementation is left abstract:
    *   it can be implemented either in linear memory, or the heap when this is available
    */
  class RecordSort(
    val id: Identifier,
    val parent: Option[Identifier],
    val fields: Seq[ValDef],
    val flags: Seq[Flag] = Seq()
  ) extends Definition {

    def lookupParent(implicit s: Symbols): Option[RecordSort] = {
      parent.map(s.getRecord)
    }
    def allFields(implicit s: Symbols): Seq[ValDef] = {
      lookupParent.toSeq.flatMap(_.allFields) ++ fields
    }
    def ancestors(implicit s: Symbols): Seq[Identifier] = {
      id +: lookupParent.toSeq.flatMap(_.ancestors)
    }
    def conformsWith(ancestor: Identifier)(implicit s: Symbols): Boolean = ancestors.contains(ancestor)
  }

  private[wasmgen] val typeTagID = FreshIdentifier("typeTag")
  private[wasmgen] val typeTag = ValDef(typeTagID, Int32Type())
  private[wasmgen] val funPointerId = FreshIdentifier("fPointer")
  private[wasmgen] val boxedValueId = FreshIdentifier("value")

  object AnyRefSort extends RecordSort(FreshIdentifier("anyref"), None, Seq(typeTag), Seq())

  private def prependParamType(tpe: Type, ft: FunctionType) =
    FunctionType(tpe +: ft.from, ft.to)

  sealed class FunPointerSort(id: Identifier, ft: FunctionType)
    extends RecordSort(
      id,
      Some(AnyRefSort.id),
      Seq(ValDef(funPointerId, prependParamType(RecordType(id), ft))))

  sealed class ClosureSort(parent: Identifier, env: Seq[ValDef])
    extends RecordSort(FreshIdentifier("closure"), Some(parent), env)

  sealed class RecordADTSort(id: Identifier)
    extends RecordSort(id, Some(AnyRefSort.id), Seq())

  sealed class ConstructorSort(
    id: Identifier,
    parent: Identifier,
    val typeTag: Int,
    fields: Seq[ValDef]
  ) extends RecordSort(id, Some(parent), fields)

  sealed class BoxedSort(tpe: Type)
    extends RecordSort(
      FreshIdentifier("Boxed" + tpe.asString(PrinterOptions())),
      Some(AnyRefSort.id),
      Seq(ValDef(boxedValueId, tpe)))

  def typeToTag(tpe: Type): Int = tpe match {
    case BVType(_, 32) => 0
    case BooleanType() => 0
    case BVType(_, 64) => 1
    case RealType() => 3
    case ArrayType(_) => 4
    case FunctionType(_, _) => 5
  }

}
