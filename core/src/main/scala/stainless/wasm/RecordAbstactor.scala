package stainless
package wasm

trait RecordAbstactor extends inox.transformers.SymbolTransformer with DefinitionTransformer {
  import scala.collection.mutable.{Map => MMap}
  private val newFunctions = MMap[Identifier, t.FunDef]()
  private val newRecords = MMap[Identifier, t.RecordSort]()

  /** This transformer transforms expressions down to the fragment we want to compile to wasm.
    *
    * - Strings become arrays of chars
    * -
    *
    */

  class ExprTransformer extends Transformer {
    override def transform(e: s.Expr, env: Env): t.Expr = e match {
      // Strings
      case s.StringLiteral(str) =>
        t.FiniteArray(str map (c => t.CharLiteral(c)), t.CharType())
      case s.StringConcat(lhs, rhs) =>
        t.ArrayConcat(transform(lhs, env), transform(rhs, env))
      case s.SubString(expr, start, end) =>
      case s.StringLength(expr) =>

      case s.Error(tpe, description) =>
      case s.Assume(pred, body) =>
      case s.Require(pred, body) =>
      case s.Variable(id, tpe, flags) =>
      case s.Annotated(body, flags) =>
      case s.Ensuring(body, pred) =>
      case s.Let(vd, value, body) =>
      case s.Application(callee, args) =>
      case s.Assert(pred, error, body) =>
      case s.Lambda(params, body) =>
      case s.MatchExpr(scrutinee, cases) =>

      case s.FunctionInvocation(id, tps, args) =>



      case s.ADT(id, tps, args) =>
      case s.ArraySelect(array, index) =>
      case s.ArrayUpdated(array, index, value) =>
      case s.IsConstructor(expr, id) =>
      case s.ArrayLength(array) =>
      case s.ADTSelector(adt, selector) =>
      case s.Equals(lhs, rhs) =>
      case s.And(exprs) =>
      case s.Or(exprs) =>
      case s.Implies(lhs, rhs) =>
      case s.Not(expr) =>



      case s.Tuple(exprs) =>
      case s.TupleSelect(tuple, index) =>

      // Sets
      case s.FiniteSet(elements, base) =>
      case s.SetAdd(set, elem) =>
      case s.ElementOfSet(element, set) =>
      case s.SubsetOf(lhs, rhs) =>
      case s.SetIntersection(lhs, rhs) =>
      case s.SetUnion(lhs, rhs) =>
      case s.SetDifference(lhs, rhs) =>

      // Bags
      case s.FiniteBag(elements, base) =>
      case s.BagAdd(bag, elem) =>
      case s.MultiplicityInBag(element, bag) =>
      case s.BagIntersection(lhs, rhs) =>
      case s.BagUnion(lhs, rhs) =>
      case s.BagDifference(lhs, rhs) =>

      // Maps
      case s.FiniteMap(pairs, default, keyType, valueType) =>
      case s.MapApply(map, key) =>
      case s.MapUpdated(map, key, value) =>



      // We do not translate these for now
      case s.Forall(params, body) => ???
      case s.Choose(res, pred) => ???
      case s.GenericValue(tp, id) => ???

      // These should all be the same
      // case s.IfExpr(cond, thenn, elze) =>
      // case s.FiniteArray(elems, base) =>
      // case s.LargeArray(elems, default, size, base) =>
      // case s.NoTree(tpe) =>
      // case s.Plus(lhs, rhs) =>
      // case s.Minus(lhs, rhs) =>
      // case s.UMinus(expr) =>
      // case s.Times(lhs, rhs) =>
      // case s.Division(lhs, rhs) =>
      // case s.Remainder(lhs, rhs) =>
      // case s.Modulo(lhs, rhs) =>
      // case s.LessThan(lhs, rhs) =>
      // case s.GreaterThan(lhs, rhs) =>
      // case s.LessEquals(lhs, rhs) =>
      // case s.GreaterEquals(lhs, rhs) =>
      // case s.BVNot(e) =>
      // case s.BVAnd(lhs, rhs) =>
      // case s.BVOr(lhs, rhs) =>
      // case s.BVXor(lhs, rhs) =>
      // case s.BVShiftLeft(lhs, rhs) =>
      // case s.BVAShiftRight(lhs, rhs) =>
      // case s.BVLShiftRight(lhs, rhs) =>
      // case s.BVNarrowingCast(expr, newType) =>
      // case s.BVWideningCast(expr, newType) =>
      case _ => super.transform(e, env)
    }
  }


  def transform(syms: s.Symbols): t.Symbols = {
    val initSymbols = t.Symbols(
      syms.sorts flatMap { case (id, sort) => transform(sort) map (record => record.id -> record)},
      syms.functions mapValues transform
    )


    ???
  }
}

trait Transformer extends transformers.Transformer {
  val s = stainless.trees
  val t = wasm.trees
}

trait DefinitionTransformer extends Transformer {
  def initEnv: Env

  def transform(fd: s.FunDef): t.FunDef = {
    val env = initEnv

    new t.FunDef(
      transform(fd.id, env),
      fd.tparams map (transform(_, env)),
      fd.params map (transform(_, env)),
      transform(fd.returnType, env),
      transform(fd.fullBody, env),
      fd.flags map (transform(_, env))
    ).copiedFrom(fd)
  }

  def transform(sort: s.ADTSort): Seq[t.RecordSort] = {
    val env = initEnv

    val parent = new t.RecordADTSort(
      transform(sort.id, env),
      sort.tparams map (transform(_, env))
    ).copiedFrom(sort)

    val children = sort.constructors map { cons =>
      new t.ConstructorSort(
        transform(cons.id, env),
        parent.id,
        parent.tparams,
        cons.fields.map(transform(_, env))
      ).copiedFrom(cons)
    }

    parent +: children
  }
}
