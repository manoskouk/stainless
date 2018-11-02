package stainless.wasm

import inox.ast.Identifier

trait Types extends inox.ast.Types { self: Trees =>
  sealed case class RecordType(sort: RecordSort, tps: Seq[Type]) extends Type
}
