package stainless
package wasm

object Intermediate {

  /* Types */
  trait Typed { val getType: Type }

  trait Type extends Typed {
    def isRefType = this match {
      case I32Type | I64Type => false
      case _ => true
    }
    val getType = this
  }

  trait ArithmeticType extends Type
  case object ByteType extends Type with ArithmeticType
  case object I32Type extends Type with ArithmeticType
  case object I64Type extends Type with ArithmeticType
  /** A record type represents a sequence of named fields in memory.
    * The parent's fields come first, then the fields of the current record.
    * A record complies to its parent's type.
    * Implementation is left abstract:
    *   it can be implemented either in linear memory, or the heap when this is available
    */
  case class RecordType(name: Identifier, parent: Option[RecordType], fields: Seq[ValDef]) extends Type {
    def flatten: Seq[ValDef] = parent.toSeq.flatMap(_.flatten) ++ fields
  }
  object RecordType {
    def apply(name: Identifier, parent: RecordType, fields: Seq[ValDef]): RecordType = RecordType(name, Some(parent), fields)
    def apply(name: Identifier, fields: Seq[ValDef]): RecordType = RecordType(name, None, fields)
  }
  case class FunctionType(args: Seq[Type], retType: Type) extends Type
  object ClosureType {
    def apply(name: Identifier, ft: FunctionType, env: Seq[ValDef]): RecordType = {
      val underlying = RecordType(name, None, Seq(ValDef(name, ft)))
      if (env.isEmpty) underlying
      else RecordType(name, Some(underlying), env)
    }
  }
  case class ArrayType(elemType: Type) extends Type
  case class TypeParameter(id: Identifier) extends Type

  /* ValDef */
  case class ValDef(name: Identifier, tpe: Type) {
    def getType = tpe
    def toVariable = Variable(name, tpe)
  }

  // Shorthands
  val StringType = ArrayType(ByteType)

  /* Expressions */
  trait Expr extends Typed

  case class ByteLiteral(value: Byte)     extends Expr { val getType = ByteType   }
  case class Int32Literal(value: Int)     extends Expr { val getType = I32Type    }
  case class Int64Literal(value: Long)    extends Expr { val getType = I64Type    }
  case class StringLiteral(value: String) extends Expr { val getType = StringType }

  case class Record(tpe: RecordType, fields: Seq[Expr]) extends Expr {
    assert(tpe.flatten.zip(fields).forall{ case (tp, field) => field.getType == tp.getType })
    val getType = tpe
  }

  case class RecordField(e: Expr, name: Identifier) extends Expr {
    val getType = {
      e.getType match {
        case rt: RecordType => rt.flatten.find(_.name == name).get.getType
        case _ => sys.error("Not a record")
      }
    }
  }

  case class CastDown(e: Expr, tpe: Type) extends Expr {
    val getType = tpe
  }

  case class If(c: Expr, thenn: Expr, elze: Expr) extends Expr {
    val getType = thenn.getType
  }

  case class Variable(name: Identifier, tp: Type) extends Expr {
    val getType: Type = tp
    def toValDef = ValDef(name, tp)
  }
  case class WithLocal(id: ValDef, v: Expr, body: Expr) extends Expr {
    val getType = body.getType
  }

  case class FunctionCall(id: Identifier, retType: Type, args: Seq[Expr]) extends Expr {
    val getType = retType
  }

  case class BinaryOp(e1: Expr, op: Operator, e2: Expr) extends Expr {
    val getType = op.getType
  }

  case class UnaryOp(op: Operator, e1: Expr) extends Expr {
    val getType = op.getType
  }

  case class FunctionPointer(id: Identifier) extends Expr { val getType = ??? } // TODO
  case class DynamicCall(callee: Expr, args: Seq[Expr]) extends Expr { val getType = ??? } // TODO

  case class Print(msg: Expr) extends Expr {
    val getType = I32Type
  }
  case class Error(tpe: Type) extends Expr {
    val getType = tpe
  }
  case class Sequence(es: Expr*) extends Expr {
    assert(es.nonEmpty)
    val getType = es.last.getType
  }

  /* Operators */
  abstract class Operator(tpe: ArithmeticType) extends Typed { val getType = tpe }
  case class Add (tpe: ArithmeticType) extends Operator(tpe)
  case class Sub (tpe: ArithmeticType) extends Operator(tpe)
  case class Mul (tpe: ArithmeticType) extends Operator(tpe)
  case class Div (tpe: ArithmeticType) extends Operator(tpe)
  case class Rem (tpe: ArithmeticType) extends Operator(tpe)
  case class And (tpe: ArithmeticType) extends Operator(tpe)
  case class Or  (tpe: ArithmeticType) extends Operator(tpe)
  case class Eqz (tpe: ArithmeticType) extends Operator(tpe)
  case class Lt_s(tpe: ArithmeticType) extends Operator(tpe)
  case class Le_s(tpe: ArithmeticType) extends Operator(tpe)
  case class Eq  (tpe: ArithmeticType) extends Operator(tpe)

  /* Definitions */

  /* ADT is a collection of Records with a parent and children */
  case class ADT(tpe: RecordType, constructors: Seq[RecordType]) {
    assert(constructors.forall(_.parent == tpe))
  }

  case class Function(name: Identifier, params: Seq[ValDef], returnType: Type, body: Expr)

  case class Program(types: Seq[ADT], functions: Seq[Function])
}


object Translator {
  import stainless.{trees => S}
  import wasm.Intermediate._
  import scala.collection.mutable.{Map => MMap}

  private class TupleType {
    private def m = MMap.empty[Seq[Type], RecordType]
    def apply(bases: Seq[Type]): RecordType = m.getOrElseUpdate(
      bases,
      RecordType(
        FreshIdentifier("tuple"),
        bases.zipWithIndex.map { case (tpe, index) =>
          ValDef(FreshIdentifier(s"v$index"), tpe)
        }
      )
    )
  }


  private val functionPointer = FreshIdentifier("fptr")

  private val adtIDField = FreshIdentifier("id")
  def toIR(adt: S.ADTSort): ADT = {
    val tpe = RecordType(adt.id, Seq(ValDef(adtIDField, I32Type)))
    val constructors = adt.constructors.map{ cons =>
      RecordType(cons.id, tpe, cons.fields map toIR)
    }
    ADT(tpe, constructors)
  }

  def mkADTs(symbols: S.Symbols) = symbols.sorts mapValues toIR

  def toIR(v: S.ValDef): ValDef = {
    ValDef(v.id, toIR(v.tpe))
  }

  def toIR(tp: S.Type)(implicit symbols: S.Symbols, ctx: IRContext): Type = tp match {
    case S.Untyped => null
    case S.BooleanType() => I32Type
    case S.UnitType() => I32Type
    case S.CharType() => I32Type
    case S.IntegerType() => I64Type // TODO: Implement integer arithmetic
    case S.RealType() => ???
    case S.StringType() => StringType
    case S.BVType(signed, size) => ???
    case S.TypeParameter(id, flags) => TypeParameter(id)
    case S.TupleType(bases) => TupleType(bases map toIR)
    case S.SetType(base) => ???
    case S.BagType(base) => ???
    case S.MapType(from, to) => ???
    case S.FunctionType(from, to) => FunctionType(from map toIR, toIR(to))
    case S.ADTType(id, tps) => ctx.adts
    case S.PiType(params, to) => FunctionType(params map toIR map (_.tpe), toIR(to))
    case S.SigmaType(params, to) => FunctionType(params map toIR map (_.tpe), toIR(to))
    case S.RefinementType(vd, prop) => toIR(vd.getType)
    case S.ArrayType(base) => ArrayType(toIR(base))
  }

  case class IRContext(adts: MMap[Identifier, ADT], functions: MMap[Identifier, Function], keepContracts: Boolean) {
    def getADT(parent: Identifier, constr: Identifier): (Int, RecordType) = {
      val constructors = adts(parent).constructors
      val record = constructors.find(_.name == constr).get
      val id = constructors.indexOf(record)
      (id, record)
    }
    def addFunction(f: Function): IRContext = {
      functions += f.name -> f
      this
    }
  }

  def toIR(e: S.Expr)(implicit symbols: S.Symbols, ctx: IRContext): Expr = e match {
    /* Misc. */
    case S.NoTree(tpe) =>
      Error(toIR(tpe))
    case S.Error(tpe, description) =>
      Sequence(Print(StringLiteral(description)), Error(toIR(tpe)))
    case S.Variable(id, tpe, flags) =>
      Variable(id, toIR(tpe))
    case S.Let(vd, value, body) =>
      WithLocal(toIR(vd), toIR(value), toIR(body))
    case fc@ S.FunctionInvocation(id, tps, args) =>
      FunctionCall(id, toIR(fc.getType), args map toIR)

    /* Contracts */
    case S.Assume(pred, body) =>
      if (ctx.keepContracts) {
        If(toIR(pred), toIR(body), Error(toIR(body.getType)))
      } else {
        toIR(body)
      }
    case S.Require(pred, body) =>
      if (ctx.keepContracts) {
        If(toIR(pred), toIR(body), Error(toIR(body.getType)))
      } else {
        toIR(body)
      }
    case S.Annotated(body, flags) =>
      toIR(body)
    case e: S.Ensuring =>
      toIR(e.toAssert)
    case S.Assert(pred, error, body) =>
      if (ctx.keepContracts) {
        If(toIR(pred), toIR(body), Error(toIR(body.getType)))
      } else {
        toIR(body)
      }

    /* HOFs */
    case S.Application(callee, args) =>
      val vCallee = ValDef(FreshIdentifier("callee"), toIR(callee.getType))
      WithLocal(
        vCallee,
        toIR(callee),
        DynamicCall(
          RecordField(vCallee.toVariable, functionPointer),
          vCallee.toVariable +: (args map toIR)
        )
      )
    case S.Lambda(params, body) =>
      val fv = (S.exprOps.variablesOf(body) -- params.map(_.toVariable)).toSeq
      val irFV = params map (_.freshen) map toIR
      val funName = FreshIdentifier("lambda")
      val funType = FunctionType(params map (p => toIR(p.getType)), toIR(body.getType))
      val recordType = ClosureType(funName, funType, irFV)
      val envID = FreshIdentifier("env")

      val function = {
        def copyEnvToLocals(body: Expr) = fv.foldRight[Expr](body) { (vr, rest) =>
          WithLocal(
            ValDef(vr.id, toIR(vr.getType)),
            RecordField(Variable(envID, recordType), vr.id),
            rest
          )
        }
        val newBody = copyEnvToLocals(toIR(body))
        Function(
          funName,
          irFV,
          toIR(body.getType),
          newBody
        )
      }

      val closure = {
        Record(
          recordType,
          FunctionPointer(funName) +: irFV.map(_.toVariable)
        )
      }

      ctx.addFunction(function)
      closure

    /* Control */
    case S.IfExpr(cond, thenn, elze) =>
      If(toIR(cond), toIR(thenn), toIR(elze))
    case me: S.MatchExpr => toIR(symbols.matchToIfThenElse(me))

    /* Literals */
    case S.CharLiteral(value) =>
    case S.BVLiteral(signed, value, size) =>
    case S.IntegerLiteral(value) =>
    case S.FractionLiteral(numerator, denominator) =>
    case S.BooleanLiteral(value) =>
    case S.StringLiteral(value) =>
    case S.UnitLiteral() =>

    /* Logic */
    case S.And(exprs) => ???
    case S.Or(exprs) => ???
    case S.Implies(lhs, rhs) => ???
    case S.Not(expr) => ???

    /* Integer/Real/BV Arithmetic */
    case S.Plus(lhs, rhs) => ???
    case S.Minus(lhs, rhs) => ???
    case S.UMinus(expr) => ???
    case S.Times(lhs, rhs) => ???
    case S.Division(lhs, rhs) => ???
    case S.Remainder(lhs, rhs) => ???
    case S.Modulo(lhs, rhs) => ???
    case S.LessThan(lhs, rhs) => ???
    case S.GreaterThan(lhs, rhs) => ???
    case S.LessEquals(lhs, rhs) => ???
    case S.GreaterEquals(lhs, rhs) => ???

    /* BitVector Arithmetic */
    case S.BVNot(e) => ???
    case S.BVAnd(lhs, rhs) => ???
    case S.BVOr(lhs, rhs) => ???
    case S.BVXor(lhs, rhs) => ???
    case S.BVShiftLeft(lhs, rhs) => ???
    case S.BVAShiftRight(lhs, rhs) => ???
    case S.BVLShiftRight(lhs, rhs) => ???
    case S.BVNarrowingCast(expr, newType) => ???
    case S.BVWideningCast(expr, newType) => ???

    /* ADTs */
    case adt@S.ADT(id, tps, args) =>
      val parent = adt.getType.asInstanceOf[S.ADTType].id
      val (ind, constr) = ctx.getADT(parent, id)
      Record(constr, Int32Literal(ind) +: (args map toIR))
    case S.IsConstructor(expr, id) =>
      val getID = RecordField(toIR(expr), adtIDField)
      val parent = expr.getType.asInstanceOf[S.ADTType].id
      val (expectedInd, _) = ctx.getADT(parent, id)
      BinaryOp(getID, Eq(I32Type), Int32Literal(expectedInd))
    case S.ADTSelector(adt, selector) =>
      RecordField(toIR(adt), selector)

    /* Tuples */
    case S.Tuple(exprs) => ???
    case S.TupleSelect(tuple, index) => ???

    /* Arrays */
    case S.FiniteArray(elems, base) => ???
    case S.LargeArray(elems, default, size, base) => ???
    case S.ArraySelect(array, index) => ???
    case S.ArrayUpdated(array, index, value) => ???
    case S.ArrayLength(array) => ???
    case S.Equals(lhs, rhs) => ???

    /* Strings */
    case S.StringConcat(lhs, rhs) => ???
    case S.SubString(expr, start, end) => ???
    case S.StringLength(expr) => ???

    /* Sets */
    case S.FiniteSet(elements, base) => ???
    case S.SetAdd(set, elem) => ???
    case S.ElementOfSet(element, set) => ???
    case S.SubsetOf(lhs, rhs) => ???
    case S.SetIntersection(lhs, rhs) => ???
    case S.SetUnion(lhs, rhs) => ???
    case S.SetDifference(lhs, rhs) => ???

    /* Maps */
    case S.FiniteMap(pairs, default, keyType, valueType) => ???
    case S.MapApply(map, key) => ???
    case S.MapUpdated(map, key, value) => ???

    /* Bags */
    case S.FiniteBag(elements, base) => ???
    case S.BagAdd(bag, elem) => ???
    case S.MultiplicityInBag(element, bag) => ???
    case S.BagIntersection(lhs, rhs) => ???
    case S.BagUnion(lhs, rhs) => ???
    case S.BagDifference(lhs, rhs) => ???

    /* Untranslatable (?) */
    case S.GenericValue(tp, id) => ???
    case S.Forall(params, body) => ???
    case S.Choose(res, pred) => ???
  }

}