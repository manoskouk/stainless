package stainless.wasm

trait TreeDeconstructor extends stainless.ast.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  // protected type Deconstructed[T <: t.Tree] = (Seq[Identifier], Seq[s.Variable], Seq[s.Expr], Seq[s.Type], Seq[s.Flag], Builder[T])
  // protected type Builder[T <: t.Tree] = (Seq[Identifier], Seq[t.Variable], Seq[t.Expr], Seq[t.Type], Seq[t.Flag]) => T

  override def deconstruct(expr: s.Expr): Deconstructed[t.Expr] = expr match {
    //case s.Hole(tpe) => (
    //  NoIdentifiers, NoVariables, NoExpressions, Seq(tpe), NoFlags,
    //  (_, _, _, tps, _) => t.Hole(tps.head)
    //)
//
    //case s.Guide(e) => (
    //  NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
    //  (_, _, es, _, _) => t.Guide(es.head)
    //)
//
    //case s.Terminating(fi) => (
    //  NoIdentifiers, NoVariables, Seq(fi), NoTypes, NoFlags,
    //  (_, _, fis, _, _) => t.Guide(fis.head)
    //)
    //case s.Hint(e) => (
    //  NoIdentifiers, NoVariables, Seq(e), NoTypes, NoFlags,
    //  (_, _, es, _, _) => t.Guide(es.head)
    //)
    //case s.Inactive(i) => (
    //  Seq(i), NoVariables, NoExpressions, NoTypes, NoFlags,
    //  (is, _, _, _, _) => t.Inactive(is.head)
    //)
    case _ => super.deconstruct(expr)
  }
}

trait Deconstructors extends stainless.ast.Deconstructors { self: Trees =>
  // FIXME: What do I have to override here?
}
