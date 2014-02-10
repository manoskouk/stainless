/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package intermediate

package object imperative {

  object trees extends imperative.Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition]
    ) extends SimpleSymbols with AbstractSymbols
  }
}