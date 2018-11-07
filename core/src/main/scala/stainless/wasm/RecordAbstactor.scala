package stainless
package wasm

trait RecordAbstactor extends inox.transformers.SymbolTransformer with DefinitionTransformer {
  import scala.collection.mutable.{Map => MMap}
  private val newFunctions = MMap[Identifier, t.FunDef]()
  private val newRecords = MMap[Identifier, t.RecordSort]()
 // private val tuple


  /** This transformer transforms expressions down to the fragment we want to compile to wasm.
    *
    * - Strings become arrays of chars
    * - Arrays become mutable and i32 indexed.
    * - Booleans, Chars, and Unit become i32
    * 
    * TODOs:
    * - We do not copy for ArrayUpdated, rather we do a destructive update
    */

  class ExprTransformer(keepContracts: Boolean)(implicit sym0: s.Symbols, sym: t.Symbols) extends Transformer {
    import t._
    private val StrType = ArrayType(CharType())
    private def mkI(i: Int) = BVLiteral(false, 32, i)

    override def transform(e: s.Expr, env: Env): Expr = e match {

      // Misc.
      case s.BooleanLiteral(value) =>
        if (value) mkI(1) else mkI(0)
      case s.UnitLiteral() =>
        mkI(0)
      case s.CharLiteral(value) =>
        mkI(value.toInt)
      case s.Annotated(body, flags) =>
        transform(body, env)
      case s.Error(tpe, description) => 
        Sequence(Output(transform(s.StringLiteral(description), env)), NoTree(transform(tpe, env)))
      case me: s.MatchExpr => transform(sym0.matchToIfThenElse(me), env)
      case s.Equals(lhs, rhs) => ???
     
      // Contracts
      case s.Assume(pred, body) =>
        if (keepContracts)
          IfExpr(transform(pred, env), transform(body, env), NoTree(transform(body.getType, env)))
        else
          transform(body, env)
      case s.Require(pred, body) =>
        if (keepContracts)
          IfExpr(transform(pred, env), transform(body, env), NoTree(transform(body.getType, env)))
        else
          transform(body, env)
      case s.Ensuring(body, s.Lambda(s.ValDef(id, tp, _), lbody)) =>
        if (keepContracts) {
          val trV = Variable(id, transform(tp, env), Seq())
          Let(trV.toVal, transform(body, env),
            IfExpr(transform(lbody, env), trV, NoTree(trV.getType))
          )
        } else {
          transform(body, env)
        }
      case s.Assert(pred, error, body) =>
        if (keepContracts) 
          IfExpr(
            transform(pred, env),
            transform(body, env),
            Error(transform(body.getType, env), error getOrElse "")
          )
        else transform(body, env)

      // Higher-order
      case s.Application(callee, args) => ???
      case s.Lambda(params, body) => ???
 
      // Booleans
      case s.And(exprs) => exprs.map(transform(_, env)).reduceRight(BVAnd)
      case s.Or(exprs)  => exprs.map(transform(_, env)).reduceRight(BVOr)
      case s.Implies(lhs, rhs) => transform(s.Or(lhs, s.Not(rhs)), env)
      case s.Not(expr) => BVNot(transform(expr, env))

      // ADTs
      case s.ADT(id, tps, args) => 
        // Except constructor fields, we also store the i32 code corresponding to this constructor
        val constrCode = sym.getRecord(id).asInstanceOf[ConstructorSort].code
        val tpe = RecordType(id, tps map (transform(_, env)))
        CastUp(
          Record(tpe, mkI(constrCode) +: args.map(transform(_, env))),
          tpe.parent.get
        )
      case s.IsConstructor(expr, id) =>
        // We need to compare the constructor code of given value
        // to the code corresponding to constructor 'id'
        Equals(
          RecordSelector(transform(expr, env), adtCodeID),
          mkI(sym.getRecord(id).asInstanceOf[ConstructorSort].code)
        )
      case as@s.ADTSelector(adt, selector) =>
        val s.ADTType(parent, tps) = as.getType
        val childId = sym.childrenOf(parent).find(_.fields.exists(_.id == selector)).get.id
        RecordSelector(
          CastDown(transform(adt, env), RecordType(childId, tps map (transform(_, env)))),
          selector
        )

      // Tuples
      case s.Tuple(exprs) => ???
      case s.TupleSelect(tuple, index) => ???

      // Arrays
      case s.FiniteArray(elems, base) => ???
      case s.LargeArray(elems, default, size, base) => ???
      case s.ArraySelect(array, index) =>
        t.ArrayGet(transform(array, env), transform(index, env))
      case s.ArrayUpdated(array, index, value) => 
        // TODO: Copy functional arrays or analyze when we don't need to do so
        t.ArraySet(transform(array, env), transform(index, env), transform(value, env))
      case s.ArrayLength(array) => ArrayLength32(transform(array, env))

      // Strings
      case s.StringLiteral(str) => ???
      case s.StringConcat(lhs, rhs) =>
        val l = Variable.fresh("lhs", StrType)
        val r = Variable.fresh("rhs", StrType)
        val newArray = Variable.fresh("arr", StrType)
        Let(l.toVal, transform(lhs, env),
        Let(r.toVal, transform(rhs, env),
        Let(
          newArray.toVal,
          NewArray(
            Plus(ArrayLength32(l), ArrayLength32(r)),
            transform(s.CharLiteral(' '), env)
          ),
          Sequence(
            ArrayCopy(l, newArray, mkI(0)),
            ArrayCopy(r, newArray, ArrayLength32(l))
          )
        )))         
      case s.SubString(expr, start, end) => ???
      case s.StringLength(expr) =>
        ArrayLength32(transform(expr, env))


      // Sets
      case s.FiniteSet(elements, base) => ???
      case s.SetAdd(set, elem) => ???
      case s.ElementOfSet(element, set) => ???
      case s.SubsetOf(lhs, rhs) => ???
      case s.SetIntersection(lhs, rhs) => ???
      case s.SetUnion(lhs, rhs) => ???
      case s.SetDifference(lhs, rhs) => ???

      // Bags
      case s.FiniteBag(elements, base) => ???
      case s.BagAdd(bag, elem) => ???
      case s.MultiplicityInBag(element, bag) => ???
      case s.BagIntersection(lhs, rhs) => ???
      case s.BagUnion(lhs, rhs) => ???
      case s.BagDifference(lhs, rhs) => ???

      // Maps
      case s.FiniteMap(pairs, default, keyType, valueType) => ???
      case s.MapApply(map, key) => ???
      case s.MapUpdated(map, key, value) => ???

      // We do not translate these for now
      case s.Forall(params, body) => ???
      case s.Choose(res, pred) => ???
      case s.GenericValue(tp, id) => ???

      // These should all be the same
      // ** All other literals **
      // case s.Variable(id, tpe, flags) =>
      // case s.Let(vd, value, body) =>
      // case s.IfExpr(cond, thenn, elze) =>
      // case s.FunctionInvocation(id, tps, args) => ???
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

    val children = sort.constructors.zipWithIndex map { case (cons, ind) =>
      new t.ConstructorSort(
        transform(cons.id, env),
        parent.id,
        ind,
        parent.tparams,
        cons.fields.map(transform(_, env))
      ).copiedFrom(cons)
    }

    parent +: children
  }
}
