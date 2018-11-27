/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.intermediate

import inox.ast.{FreshIdentifier, Identifier}

trait Definitions extends stainless.ast.Definitions { self: Trees =>
  override type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols extends super.AbstractSymbols { self0: Symbols =>
    val records: Map[Identifier, RecordSort]
    val sorts = Map[Identifier, ADTSort]()

    def lookupRecord(id: Identifier): Option[RecordSort] = records.get(id)
    def getRecord(id: Identifier): RecordSort = records.getOrElse(id, throw ADTLookupException(id))

    //def childrenOf(id: Identifier): Seq[ConstructorSort] = records.collect{ case (_, cs:ConstructorSort) if cs.parent.contains(id) => cs }
  }

  // Used to tag dynamically called functions
  case object Dynamic extends Flag("dynamic", Seq.empty)

  /** A record type represents a sequence of named fields in memory.
    * The parent's fields come first, then the fields of the current record.
    * A record complies to its parent's type.
    * Implementation is left abstract:
    *   it can be implemented either in linear memory, or the heap when this is available
    */
  class RecordSort(
    val id: Identifier,
    //val tparams: Seq[TypeParameterDef],
    val parent: Option[Identifier],
    val fields: Seq[ValDef],
    val flags: Seq[Flag] = Seq()
  ) extends Definition {

    //def typeArgs: Seq[TypeParameter] = tparams.map(_.tp)

    def lookupParent(implicit s: Symbols): Option[RecordSort] = {
      parent.map(s.getRecord)
    }
    def flattenFields(implicit s: Symbols): Seq[ValDef] = {
      lookupParent.toSeq.flatMap(_.flattenFields) ++ fields
    }
    def ancestors(implicit s: Symbols): Seq[Identifier] = {
      id +: lookupParent.toSeq.flatMap(_.ancestors)
    }
    def conformsWith(ancestor: Identifier)(implicit s: Symbols): Boolean = ancestors.contains(ancestor)

    ///** Wraps this [[RecordSort]] in a in [[TypedRecordSort]] with its own type parameters */
    //def typed(implicit s: Symbols): TypedRecordSort = typed(tparams.map(_.tp))
//
    ///** Wraps this [[RecordSort]] in a in [[TypedRecordSort]] with the specified type parameters */
    //def typed(tps: Seq[Type])(implicit s: Symbols): TypedRecordSort = TypedRecordSort(s.getRecord(id), tps)
  }

  //case class TypedRecordSort private (definition: RecordSort, tps: Seq[Type])(implicit s: Symbols) extends Tree {
  //  require(tps.length == definition.tparams.length)
  //  copiedFrom(definition)
//
  //  @inline def id: Identifier = definition.id
//
  //  @inline def tpSubst: Map[TypeParameter, Type] = _tpSubst.get
  //  private[this] val _tpSubst = Lazy((definition.typeArgs zip tps).toMap.filter(tt => tt._1 != tt._2))
//
  //  def flattenFields(implicit s: Symbols): Seq[ValDef] =
  //    definition.flattenFields.map(vd => ValDef(vd.id, typeOps.instantiateType(vd.getType, tpSubst)))
//
  //  def ancestors(implicit s: Symbols): Seq[Identifier] =
  //    definition.ancestors
  //}

  private[wasmgen] val typeTagID = FreshIdentifier("typeTag")
  private[wasmgen] val typeTag = ValDef(typeTagID, Int32Type())
  private[wasmgen] val funPointerId = FreshIdentifier("fPointer")
  private[wasmgen] val boxedValueId = FreshIdentifier("value")

  object AnyRefSort extends RecordSort(FreshIdentifier("anyref"), None, Seq(typeTag), Seq())

  private def prependParamType(tpe: Type, ft: FunctionType) =
    FunctionType(tpe +: ft.from, ft.to)
  // Sorts that represent function pointers to a function of `original` type ft
  // modify this ft to include as parameter a pointer of this type
  sealed class FunPointerSort(id: Identifier, ft: FunctionType)
    extends RecordSort(
      id, Some(AnyRefSort.id),
      Seq(ValDef(funPointerId, prependParamType(RecordType(id), ft)))
    )

  sealed class ClosureSort(parent: Identifier, env: Seq[ValDef])
    extends RecordSort(FreshIdentifier("closure"), Some(parent), env)

  sealed class RecordADTSort(id: Identifier)
    extends RecordSort(id, Some(AnyRefSort.id), Seq()) // TODO: Fix type

  sealed class ConstructorSort(
    id: Identifier,
    parent: Identifier,
    val typeTag: Int,
    fields: Seq[ValDef]
  ) extends RecordSort(id, Some(parent), fields)

  sealed class BoxedSort(tpe: Type)
    extends RecordSort(FreshIdentifier("Boxed" + tpe.asString(PrinterOptions())), Some(AnyRefSort.id), Seq(ValDef(boxedValueId, tpe)))

  def typeToTag(tpe: Type): Int = tpe match {
    case BVType(_, 32) => 0
    case BooleanType() => 0
    case BVType(_, 64) => 1
    case RealType() => 3
    case ArrayType(_) => 4
    case FunctionType(_, _) => 5
  }

}
