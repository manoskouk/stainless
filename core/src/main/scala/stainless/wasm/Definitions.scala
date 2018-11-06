/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasm

import inox.ast.{FreshIdentifier, Identifier}

trait Definitions extends stainless.ast.Definitions { self: Trees =>
  override type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols extends super.AbstractSymbols { self0: Symbols =>

  }

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
  ) {
    assert(parent.isEmpty || tparams.isEmpty)

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

    /** Wraps this [[ADTSort]] in a in [[TypedADTSort]] with its own type parameters */
    def typed(implicit s: Symbols): TypedRecordSort = typed(tparams.map(_.tp))

    /** Wraps this [[ADTSort]] in a in [[TypedADTSort]] with the specified type parameters */
    def typed(tps: Seq[Type])(implicit s: Symbols): TypedRecordSort = s.getSort(id, tps)
  }

  class TypedRecordSort(sort: RecordSort, tps: Seq[Type]) {

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

  sealed class RecordADTSort(id: Identifier, tparams: Seq[TypeParameterDef])
    extends RecordSort(id, tparams, None, Seq(ValDef(adtCodeID, BVType(signed = false, 8)) ))

  class ConstructorSort(id: Identifier, parent: Identifier, tparams: Seq[TypeParameterDef], fields: Seq[ValDef])
    extends RecordSort(id, tparams, Some(parent), fields)


  class Typed

}
