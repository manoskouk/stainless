package stainless.wasm

import inox.ast.Identifier

trait Types extends inox.ast.Types { self: Trees =>
  sealed case class RecordType(record: Identifier, tps: Seq[Type]) extends Type {
    def lookupRecord(implicit s: Symbols): Option[TypedRecordSort] = s.lookupRecord(record, tps)

    def getRecord(implicit s: Symbols): TypedRecordSort = s.getRecord(record, tps)

    def conformsWith(superType: Type)(implicit s: Symbols): Boolean = superType match {
      case RecordType(record2, tps2) =>
        (getRecord.ancestors contains record2) && tps == tps2
      case _ => false
    }
  }
}
