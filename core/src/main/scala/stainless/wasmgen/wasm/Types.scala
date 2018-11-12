package stainless.wasmgen.wasm

object Types {
  trait Type { def size: Int }
  case object i32 extends Type { def size = 32 }
  case object i64 extends Type { def size = 64 }
  case object f32 extends Type { def size = 32 }
  case object f64 extends Type { def size = 64 }
  case object void extends Type {
    def size = 0
    override def toString = ""
  }
}
