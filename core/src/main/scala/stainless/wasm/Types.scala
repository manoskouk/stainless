package stainless.wasm

import inox.ast.Identifier

trait Types extends inox.ast.Types { self: Trees =>
  object RecordType {
    def apply(id: Identifier, tps: Seq[Type]) = ADTType(id, tps)
  }
}
