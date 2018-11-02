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
  trait RecordDef extends ADTSort {
    def allFields(implicit s: Symbols): Seq[ValDef]
    val parent: Option[Identifier]
    def lookupParent(implicit s: Symbols): Option[RecordDef] = {
      parent.map(p => s.lookupSort(p).asInstanceOf[RecordDef])
    }
    def conformsWith(ancestor: Identifier): Boolean =
      this == ancestor || (parent contains ancestor)
  }
  //
  //sealed class RecordDef(
  //  id: Identifier,
  //  tparams: Seq[TypeParameterDef],
  //  parent: Option[Identifier],
  //  fields: Seq[ValDef]
  //) extends ADTSort(
  //  id,
  //  tparams,
  //  Seq(new ADTConstructor(id, id, parent.toSeq.map(par => ValDef(par, ADTType(par, tparams map (_.tp)))) ++ fields)),
  //  Seq()
  //) {
  //  def lookupParent(implicit s: Symbols): Option[RecordDef] = {
  //    parent.map(p => s.lookupSort(p).asInstanceOf[RecordDef])
  //  }
  //  def flattenFields: Seq[ValDef] = {
  //    lookupParent.toSeq.flatMap(_.flattenFields) ++ fields
  //  }
  //  def ancestors(implicit s: Symbols): Seq[Identifier] = {
  //    id +: lookupParent.toSeq.flatMap(_.ancestors)
  //  }
  //  def conformsWith(ancestor: Identifier): Boolean = ancestors.contains(ancestor)
  //}

  def mkSingletonConstr(id: Identifier, tp: Type) = {
    new ADTConstructor(id, id, Seq(ValDef(id, tp)))
  }

  sealed class FunPointerSort(ft: FunctionType) extends ADTSort(
    FreshIdentifier(ft.asString),
    Seq(),
    Seq(mkSingletonConstr(FreshIdentifier("fp"), ft)),
    Seq()
  ) with RecordDef {
    val parent = None
    def allFields(implicit s: Symbols) = constructors.head.fields
  }

  sealed class ClosureSort(parent: Identifier, env: Seq[ValDef])(implicit s: Symbols)
    extends ADTSort(
      FreshIdentifier("closure"),
      Seq(),
      Seq(new ADTConstructor(parent))

    ) {

  }
}
