/* Copyright 2009-2018 EPFL, Lausanne */

object Assert2 {

  def foo(): Int = {
    var a = 0
    assert(a == 0)
    a += 1
    a
  }

}
