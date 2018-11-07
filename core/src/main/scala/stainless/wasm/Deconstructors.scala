package stainless.wasm

import stainless.Identifier

trait TreeDeconstructor extends stainless.ast.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  // protected type Deconstructed[T <: t.Tree] = (Seq[Identifier], Seq[s.Variable], Seq[s.Expr], Seq[s.Type], Seq[s.Flag], Builder[T])
  // protected type Builder[T <: t.Tree] = (Seq[Identifier], Seq[t.Variable], Seq[t.Expr], Seq[t.Type], Seq[t.Flag]) => T

  override def deconstruct(expr: s.Expr): Deconstructed[t.Expr] = expr match {
    case s.Record(tpe, fields) => (
      NoIdentifiers, NoVariables, fields, Seq(tpe), NoFlags,
      (_, _, es, tpe, _) => t.Record(tpe.head.asInstanceOf[t.RecordType], es)
    )

    case s.RecordSelector(record, selector) => (
      Seq(selector), NoVariables, Seq(record), NoTypes, NoFlags,
      (ids, _, es, _, _) => t.RecordSelector(es.head, ids.head)
    )

    case s.FunctionPointer(id) => (
      Seq(id), NoVariables, NoExpressions, NoTypes, NoFlags,
      (ids, _, _, _, _) => t.FunctionPointer(ids.head)
    )

    case s.CastDown(e, tp) => (
      NoIdentifiers, NoVariables, Seq(e), Seq(tp), NoFlags,
      (_, _, es, tps, _) => t.CastDown(es.head, tps.head.asInstanceOf[t.RecordType])
    )

    case s.CastUp(e, tp) => (
      NoIdentifiers, NoVariables, Seq(e), Seq(tp), NoFlags,
      (_, _, es, tps, _) => t.CastUp(es.head, tps.head.asInstanceOf[t.RecordType])
    )

    case s.Output(msg) => (
      NoIdentifiers, NoVariables, Seq(msg), NoTypes, NoFlags,
      (_, _, es, _, _) => t.Output(es.head)
    )

    case s.ArrayConcat(e1, e2) => (
      NoIdentifiers, NoVariables, Seq(e1, e2), NoTypes, NoFlags,
      (_, _, es, _, _) => t.ArrayConcat(es(0), es(1))
    )

    case _ => super.deconstruct(expr)
  }

  override def deconstruct(tpe: s.Type): Deconstructed[t.Type] = tpe match {
    case s.RecordType(record, tps) => (
      Seq(record), NoVariables, NoExpressions, tps, NoFlags,
      (recs, _, _, tps, _) => t.RecordType(recs.head, tps)
    )
    case _ => super.deconstruct(tpe)
  }
}

trait Deconstructors extends stainless.ast.Deconstructors { self: Trees =>
  // FIXME: What do I have to override here?
}
