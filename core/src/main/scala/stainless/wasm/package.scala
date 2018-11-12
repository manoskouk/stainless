/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

package object wasm {
  object trees extends Trees { self =>
    object printer extends Printer {
      val trees: self.type = self
    }
    case class Symbols(
      records: Map[Identifier, RecordSort],
      functions: Map[Identifier, FunDef]
    ) extends AbstractSymbols {
      def withFunctions(functions: Seq[FunDef]): Symbols =
        Symbols(this.records, this.functions ++ functions.map(fd => fd.id -> fd))

      def withSorts(sorts: Seq[ADTSort]): Symbols = this

      def withRecords(records: Seq[RecordSort]): Symbols =
        Symbols(this.records ++ records.map(rec => rec.id -> rec), this.functions)
    }
    val NoSymbols: Symbols = Symbols(Map(), Map())
  }

}
