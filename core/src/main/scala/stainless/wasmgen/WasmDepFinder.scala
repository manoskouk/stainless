package stainless.wasmgen

import stainless.Identifier
import stainless.trees._
import stainless.utils.{DefinitionIdFinder, DependenciesFinder}

class WasmDefIdFinder(val s: Symbols) extends DefinitionIdFinder {
  val trees = stainless.trees
  private def fun(name: String) = s.lookup[FunDef](name).id
  private def sort(name: String) = s.lookup[ADTSort](name).id

  private lazy val setIds = Set(sort("_Set_"), fun("__SNil_$0ToString_"), fun("__SCons_$0ToString_"))

  override def traverse(expr: Expr, env: Env): Unit = {
    expr match {
      // Tuples
      case Tuple(elems) =>
        ids += sort(s"_Tuple${elems.size}_")
      case TupleSelect(tuple, _) =>
        val TupleType(ts) = tuple.getType(s)
        ids += sort(s"_Tuple${ts.size}_")
      // Sets
      case FiniteSet(_, _) | SetAdd(_, _) =>
        ids += fun("_setAdd_")
        ids ++= setIds
      case ElementOfSet(_, _) =>
        ids += fun("_elementOfSet_")
        ids ++= setIds
      case SubsetOf(_, _) =>
        ids += fun("_subsetOf_")
        ids ++= setIds
      case SetIntersection(_, _) =>
        ids += fun("_setIntersection_")
        ids ++= setIds
      case SetUnion(_, _) =>
        ids += fun("_setUnion_")
        ids ++= setIds
      case SetDifference(_, _) =>
        ids += fun("_setDifference_")
        ids ++= setIds
      // Bags
      case FiniteBag(_, _) | BagAdd(_, _) =>
        ids += fun("_bagAdd_")
        ids += sort("_Bag_")
      case MultiplicityInBag(_, _) =>
        ids += fun("_bagMultiplicity_")
        ids += sort("_Bag_")
      case BagIntersection(_, _) =>
        ids += fun("_bagIntersection_")
        ids += sort("_Bag_")
      case BagUnion(_, _) =>
        ids += fun("_bagUnion_")
        ids += sort("_Bag_")
      case BagDifference(_, _) =>
        ids += fun("_bagDifference_")
        ids += sort("_Bag_")
      // Maps
      case FiniteMap(_, _, _, _) | MapApply(_, _) =>
        ids += fun("_mapApply_")
        ids += sort("_Map_")
      case MapUpdated(_, _, _) =>
        ids += fun("_mapUpdated_")
        ids += sort("_Map_")
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
    def fun(name: String) = s.lookup[FunDef](name)
    def sort(name: String) = s.lookup[ADTSort](name)
    super.findDependencies(roots, s)
      .withFunctions(Seq(
        "_toString_", "_digitToStringL_", "_digitToStringI_", "_i32ToString_", "_i64ToString_",
        "_f64ToString_", "_booleanToString_", "_funToString_", "_arrayToString_"
      ).map(fun))
  }
}




