/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.intermediate

import inox.ast.Identifier

trait Types extends inox.ast.Types { self: Trees =>
  sealed case class RecordType(record: Identifier, tps: Seq[Type]) extends Type {
    def lookupRecord(implicit s: Symbols): Option[TypedRecordSort] = s.lookupRecord(record, tps)

    def getRecord(implicit s: Symbols): TypedRecordSort = s.getRecord(record, tps)
  
    def parent(implicit s: Symbols): Option[RecordType] = {
      s.getRecord(record).parent.map(RecordType(_, tps))
    }

    def conformsWith(superType: Type)(implicit s: Symbols): Boolean = superType match {
      case RecordType(record2, tps2) =>
        (getRecord.ancestors contains record2) && tps == tps2
      case _ => false
    }
  }

  // TODO: Extend inox class if it ceases being sealed
  sealed abstract class BVTypeExtractor2(signed: Boolean, size: Int) {
    def apply(): BVType = BVType(signed, size)
    def unapply(tpe: BVType): Boolean = tpe.signed == signed && tpe.size == size
  }

  object ByteType  extends BVTypeExtractor2(false, 8)
  object IndexType extends BVTypeExtractor2(false, 32)
}
