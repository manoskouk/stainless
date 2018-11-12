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
    val fields: Seq[ValDef]
  ) extends Definition {
    assert(parent.isEmpty || tparams.isEmpty)

    val flags = Seq()

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

  private[wasmgen] val funPointerId = FreshIdentifier("funP")
  import scala.collection.mutable.{Map => MMap}
  private[wasmgen] val funSortIds = MMap[FunctionType, Identifier]()
  private[wasmgen] val adtCodeID = FreshIdentifier("code")

  sealed class FunPointerSort(id: Identifier, ft: FunctionType)
    extends RecordSort(id, Seq(), None, Seq(ValDef(funPointerId, ft)))

  sealed class ClosureSort(parent: Identifier, env: Seq[ValDef])
    extends RecordSort(FreshIdentifier("closure"), Seq(), Some(parent), env)

  sealed class RecordADTSort(id: Identifier, tparams: Seq[TypeParameterDef])
    extends RecordSort(id, tparams, None, Seq(ValDef(adtCodeID, BVType(signed = false, 32)) )) // TODO: Fix type

  sealed class ConstructorSort(
    id: Identifier,
    parent: Identifier,
    val code: Int,
    tparams: Seq[TypeParameterDef],
    fields: Seq[ValDef]
  ) extends RecordSort(id, tparams, Some(parent), fields)

}
