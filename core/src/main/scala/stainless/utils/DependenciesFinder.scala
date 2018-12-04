package stainless
package utils

trait DefinitionIdFinder extends transformers.DefinitionTraverser {
  val s: trees.Symbols
  private val defNames = s.sorts.keys.toSet ++ s.functions.keys.toSet

  def initEnv = ()
  type Env = Unit

  protected var ids : Set[Identifier] = Set()
  override def traverse(id: Identifier, env: Env): Unit = {
    if (defNames(id)) ids += id
  }

  def doTraverse(fd: trees.FunDef): Set[Identifier] = {
    ids = Set()
    traverse(fd)
    ids
  }

  def doTraverse(sort: trees.ADTSort): Set[Identifier] = {
    ids = Set()
    traverse(sort)
    ids
  }
}

trait DependenciesFinder {
  val t: stainless.ast.Trees
  protected def traverser(s: t.Symbols): DefinitionIdFinder { val trees: t.type }

  def findDependencies(roots: Set[Identifier], s: t.Symbols): t.Symbols = {
    val tr = traverser(s)
    import inox.utils.fixpoint

    val ids = fixpoint[Set[Identifier]]{ ids =>
      s.functions.values.filter(f => ids(f.id)).toSet.flatMap((fd: t.FunDef) => tr.doTraverse(fd)) ++
      s.sorts.values.toSet.flatMap((s: t.ADTSort) => tr.doTraverse(s)) ++
      ids
    }(roots)

    t.NoSymbols
      .withFunctions(s.functions.values.toSeq.filter(f => ids(f.id)))
      .withSorts(s.sorts.values.toSeq.filter(f => ids(f.id)))
  }
}

