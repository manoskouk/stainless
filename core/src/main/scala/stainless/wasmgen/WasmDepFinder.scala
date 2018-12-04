package stainless.wasmgen

import stainless.Identifier
import stainless.trees._
import stainless.utils.{DefinitionIdFinder, DependenciesFinder}

class WasmDefIdFinder(val s: Symbols) extends DefinitionIdFinder {
  val trees = stainless.trees
  private def fun(name: String) = s.lookup[FunDef](name).id
  private def sort(name: String) = s.lookup[ADTSort](name).id

  override def traverse(expr: Expr, env: Env): Unit = {
    expr match {
      // Tuples
      case Tuple(elems) =>
        ids += sort(s"_Tuple${elems.size}_")
      case TupleSelect(tuple, _) =>
        val TupleType(ts) = tuple.getType(s)
        ids += sort(s"_Tuple${ts.size}_")
      // Sets
      case FiniteSet(_, _) =>
        ids += fun("_setAdd_")
      case SetAdd(set, elem) =>
        ids += fun("_setAdd_")
      case ElementOfSet(element, set) =>
        ids += fun("_elementOfSet_")
      case SubsetOf(lhs, rhs) =>
        ids += fun("_subsetOf_")
      case SetIntersection(lhs, rhs) =>
        ids += fun("_setIntersection_")
      case SetUnion(lhs, rhs) =>
        ids += fun("_setUnion_")
      case SetDifference(lhs, rhs) =>
        ids += fun("_setDifference_")
      // Bags
      case FiniteBag(elements, base) =>
        ids += fun("_bagAdd_")
      case BagAdd(bag, elem) =>
        ids += fun("_bagAdd_")
      case MultiplicityInBag(element, bag) =>
        ids += fun("_bagMultiplicity_")
      case BagIntersection(lhs, rhs) =>
        ids += fun("_bagIntersection_")
      case BagUnion(lhs, rhs) =>
        ids += fun("_bagUnion_")
      case BagDifference(lhs, rhs) =>
        ids += fun("_bagDifference_")
      // Maps
      case FiniteMap(pairs, default, keyType, valueType) =>
        ids += fun("_mapApply_")
      case MapApply(map, key) =>
        ids += fun("_mapApply_")
      case MapUpdated(map, key, value) =>
        ids += fun("_mapUpdated_")
      case _ =>
    }
    super.traverse(expr, env)
  }
}


class WasmDependenciesFinder extends DependenciesFinder {
  val t: stainless.trees.type = stainless.trees
  def traverser(s: Symbols): DefinitionIdFinder { val trees: t.type } = new WasmDefIdFinder(s)

  // Always add the internal _List_ sort
  override def findDependencies(roots: Set[Identifier], s: Symbols): Symbols = {
    super.findDependencies(roots, s).withSorts(Seq(s.lookup("_List_")))
  }
}




