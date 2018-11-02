/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasm

import inox.ast.{FreshIdentifier, Identifier}

trait Definitions extends stainless.ast.Definitions { self: Trees =>

  /** A record type represents a sequence of named fields in memory.
    * The parent's fields come first, then the fields of the current record.
    * A record complies to its parent's type.
    * Implementation is left abstract:
    *   it can be implemented either in linear memory, or the heap when this is available
    */
  class RecordSort(
    id: Identifier,
    tparams: Seq[TypeParameterDef],
    parent: Option[Identifier],
    fields: Seq[ValDef]
  ) extends ADTSort(
    id,
    tparams,
    Seq(new ADTConstructor(id, id, parent.toSeq.map(par => ValDef(par, ADTType(par, tparams map (_.tp)))) ++ fields)),
    Seq()
  ) {
    def lookupParent(implicit s: Symbols): Option[RecordSort] = {
      parent.map(p => s.lookupSort(p).asInstanceOf[RecordSort])
    }
    def flattenFields: Seq[ValDef] = {
      lookupParent.toSeq.flatMap(_.flattenFields) ++ fields
    }
    def ancestors(implicit s: Symbols): Seq[Identifier] = {
      id +: lookupParent.toSeq.flatMap(_.ancestors)
    }
    def conformsWith(ancestor: Identifier): Boolean = ancestors.contains(ancestor)
  }

  def mkSingletonConstr(id: Identifier, tp: Type) = {
    new ADTConstructor(id, id, Seq(ValDef(id, tp)))
  }

  private val funPointerId = FreshIdentifier("funP")
  import scala.collection.mutable.{Map => MMap}
  private val funSortIds = MMap[FunctionType, Identifier]()
  private val adtCodeID = FreshIdentifier("code")

  sealed class FunPointerSort(ft: FunctionType)
    extends RecordSort(
      funSortIds.getOrElseUpdate(ft, FreshIdentifier(ft.asString)),
      Seq(),
      None,
      Seq(ValDef(funPointerId, ft))
    )

  sealed class ClosureSort(parent: Identifier, env: Seq[ValDef])
    extends RecordSort(FreshIdentifier("closure"), Seq(), Some(parent), env)

  sealed class RecordADTSort private (id: Identifier, tparams: Seq[TypeParameterDef])
    extends RecordSort(id, tparams, None, Seq(ValDef(adtCodeID, BVType(signed = false, 8)) ))

  object RecordADTSort {
    def apply(id: Identifier)(implicit s: Symbols) = {
      val adt = s.lookupSort(id).get
      new RecordADTSort(id.freshen, adt.tparams)
    }
  }

  class ConstructorSort(id: Identifier, parent: Identifier, tparams: Seq[TypeParameterDef], fields: Seq[ValDef])
    extends RecordSort(id, tparams, Some(parent), fields)
}
