/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.intermediate

import inox.ast.{FreshIdentifier, Identifier}
import inox.utils.Lazy

trait Definitions extends stainless.ast.Definitions { self: Trees =>
  override type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols extends super.AbstractSymbols { self0: Symbols =>
    val records: Map[Identifier, RecordSort]
    val sorts = Map[Identifier, ADTSort]()

    def lookupRecord(id: Identifier): Option[RecordSort] = records.get(id)
    def getRecord(id: Identifier): RecordSort = records.getOrElse(id, throw ADTLookupException(id))

    def lookupRecord(id: Identifier, tps: Seq[Type]): Option[TypedRecordSort] = lookupRecord(id).map(_.typed(tps))
    def getRecord(id: Identifier, tps: Seq[Type]): TypedRecordSort = getRecord(id).typed(tps)

    def childrenOf(id: Identifier) = records.collect{ case (_, cs:ConstructorSort) if cs.parent.contains(id) => cs }
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
    val tparams: Seq[TypeParameterDef],
    val parent: Option[Identifier],
    val fields: Seq[ValDef],
    val flags: Seq[Flag] = Seq()
  ) extends Definition {

    def typeArgs: Seq[TypeParameter] = tparams.map(_.tp)

    def lookupParent(implicit s: Symbols): Option[RecordSort] = {
      parent.map(p => s.getRecord(p))
    }
    def flattenFields(implicit s: Symbols): Seq[ValDef] = {
      lookupParent.toSeq.flatMap(_.flattenFields) ++ fields
    }
    def ancestors(implicit s: Symbols): Seq[Identifier] = {
      id +: lookupParent.toSeq.flatMap(_.ancestors)
    }
    def conformsWith(ancestor: Identifier)(implicit s: Symbols): Boolean = ancestors.contains(ancestor)

    /** Wraps this [[RecordSort]] in a in [[TypedRecordSort]] with its own type parameters */
    def typed(implicit s: Symbols): TypedRecordSort = typed(tparams.map(_.tp))

    /** Wraps this [[RecordSort]] in a in [[TypedRecordSort]] with the specified type parameters */
    def typed(tps: Seq[Type])(implicit s: Symbols): TypedRecordSort = TypedRecordSort(s.getRecord(id), tps)
  }

  case class TypedRecordSort private (definition: RecordSort, tps: Seq[Type])(implicit s: Symbols) extends Tree {
    require(tps.length == definition.tparams.length)
    copiedFrom(definition)

    @inline def id: Identifier = definition.id

    @inline def tpSubst: Map[TypeParameter, Type] = _tpSubst.get
    private[this] val _tpSubst = Lazy((definition.typeArgs zip tps).toMap.filter(tt => tt._1 != tt._2))

    def flattenFields(implicit s: Symbols): Seq[ValDef] =
      definition.flattenFields.map(vd => ValDef(vd.id, typeOps.instantiateType(vd.getType, tpSubst)))

    def ancestors(implicit s: Symbols): Seq[Identifier] =
      definition.ancestors
  }

  private[wasmgen] val typeTagID = FreshIdentifier("code")
  private[wasmgen] val typeTag = ValDef(typeTagID, Int32Type())
  private[wasmgen] val funPointerId = FreshIdentifier("funP")
  import scala.collection.mutable.{Map => MMap}
  private[wasmgen] val funSortIds = MMap[FunctionType, Identifier]()
  private[wasmgen] val boxedValueId = FreshIdentifier("value")

  object AnyRefSort extends RecordSort(FreshIdentifier("anyref"), Seq(), None, Seq(typeTag), Seq())

  sealed class FunPointerSort(id: Identifier, ft: FunctionType)
    extends RecordSort(id, Seq(), Some(AnyRefSort.id), Seq(ValDef(funPointerId, ft)))

  sealed class ClosureSort(parent: Identifier, env: Seq[ValDef])
    extends RecordSort(FreshIdentifier("closure"), Seq(), Some(parent), env)

  sealed class RecordADTSort(id: Identifier, tparams: Seq[TypeParameterDef], equality: Identifier)
    extends RecordSort(id, tparams, Some(AnyRefSort.id), Seq(), Seq(HasADTEquality(equality))) // TODO: Fix type

  sealed class ConstructorSort(
    id: Identifier,
    parent: Identifier,
    val typeTag: Int,
    tparams: Seq[TypeParameterDef],
    fields: Seq[ValDef]
  ) extends RecordSort(id, tparams, Some(parent), fields)

  sealed class BoxedSort(tpe: Type)
    extends RecordSort(FreshIdentifier(tpe.asString(PrinterOptions())), Seq(), Some(AnyRefSort.id), Seq(ValDef(boxedValueId, tpe)))

  val boxedSorts: Map[Type, BoxedSort] = {
    Seq(BVType(true, 32), BVType(false, 32), BVType(true, 64), BVType(false, 64), RealType())
      .map { tpe => tpe -> new BoxedSort(tpe) }
      .toMap
  }
}
