package stainless.runtime

import stainless.lang.error
import stainless.annotation.library

/* Implements set, map and bag operations on top of sorted lists */
@library
object DataStructures {

  /* Compares two elements of any type. Will be filled in by the code generator */
  @library
  @wasmRuntime
  def compare[A](a1: A, a2: A): Int = 0

  // We define our own lists to not have to load the entire scala lib
  @library
  @wasmRuntime
  sealed abstract class _List_[A] {
    @inline def ::(elem: A): _List_[A] = _Cons_(elem, this)
  }
  @library
  @wasmRuntime
  case class _Cons_[A](h: A, t: _List_[A]) extends _List_[A]
  @library
  @wasmRuntime
  case class _Nil_[A]() extends _List_[A]

  @library
  @wasmRuntime
  def setAdd[A](set: _List_[A], elem: A): _List_[A] = set match {
    case _Nil_() => elem :: _Nil_()
    case _Cons_(h, t) =>
      val c = compare(elem, h)
      if (c < 0) elem :: h :: t
      else if (c > 0) h :: setAdd(t, elem)
      else h :: t
  }
  @library
  @wasmRuntime
  def elementOfSet[A](set: _List_[A], elem: A): Boolean = set match {
    case _Nil_() => false
    case _Cons_(h, t) =>
      val c = compare(elem, h)
      if (c < 0) false
      else if (c > 0) elementOfSet(t, elem)
      else true
  }
  @library
  @wasmRuntime
  def subsetOf[A](subset: _List_[A], superset: _List_[A]): Boolean = (subset, superset) match {
    case (_Nil_(), _) => true
    case (_, _Nil_()) => false
    case (_Cons_(h1, t1), _Cons_(h2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) false
      else if (c > 0) subsetOf(subset, t2)
      else subsetOf(t1, t2)
  }
  @library
  @wasmRuntime
  def setIntersection[A](s1: _List_[A], s2: _List_[A]): _List_[A] = (s1, s2) match {
    case (_Nil_(), _) => s2
    case (_, _Nil_()) => s1
    case (_Cons_(h1, t1), _Cons_(h2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) setIntersection(t1, s2)
      else if (c > 0) setIntersection(s1, t2)
      else h1 :: setIntersection(t1, t2)
  }
  @library
  @wasmRuntime
  def setUnion[A](s1: _List_[A], s2: _List_[A]): _List_[A] = (s1, s2) match {
    case (_Nil_(), _) => s2
    case (_, _Nil_()) => s1
    case (_Cons_(h1, t1), _Cons_(h2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) h1 :: setUnion(t1, s2)
      else if (c > 0) h2 :: setUnion(s1, t2)
      else h1 :: setUnion(t1, t2)
  }
  @library
  @wasmRuntime
  def setDifference[A](s1: _List_[A], s2: _List_[A]): _List_[A] = (s1, s2) match {
    case (_Nil_(), _) => _Nil_()
    case (_, _Nil_()) => s1
    case (_Cons_(h1, t1), _Cons_(h2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) h1 :: setDifference(t1, s2)
      else if (c > 0) setDifference(s1, t2)
      else setDifference(t1, t2)
  }

  @inline def min(b1: BigInt, b2: BigInt): BigInt = if (b1 <= b2) b1 else b2
  @inline def max(b1: BigInt, b2: BigInt): BigInt = if (b1 >= b2) b1 else b2

  @library
  @wasmRuntime
  def bagAdd[A](bag: _List_[(A, BigInt)], elem: A): _List_[(A, BigInt)] = bag match {
    case _Nil_() => (elem, BigInt(1)) :: _Nil_()
    case _Cons_((h, m), t) =>
      val c = compare(elem, h)
      if (c < 0) (elem, BigInt(1)) :: bag
      else if (c > 0) (h, m) :: bagAdd(t, elem)
      else (h, m + 1) :: t
  }
  @library
  @wasmRuntime
  def bagMultiplicity[A](bag: _List_[(A, BigInt)], elem: A): BigInt = bag match {
    case _Nil_() => 0
    case _Cons_((h, m), t) =>
      val c = compare(elem, h)
      if (c < 0) 0
      else if (c > 0) bagMultiplicity(t, elem)
      else m
  }
  @library
  @wasmRuntime
  def bagIntersection[A](b1: _List_[(A, BigInt)], b2: _List_[(A, BigInt)]): _List_[(A, BigInt)] = (b1, b2) match {
    case (_Nil_(), _) => b2
    case (_, _Nil_()) => b1
    case (_Cons_((h1, m1), t1), _Cons_((h2, m2), t2)) =>
      val c = compare(h1, h2)
      if (c < 0) bagIntersection(t1, b2)
      else if (c > 0) bagIntersection(b1, t2)
      else (h1, min(m1, m2)) :: bagIntersection(t1, t2)
  }
  @library
  @wasmRuntime
  def bagUnion[A](b1: _List_[(A, BigInt)], b2: _List_[(A, BigInt)]): _List_[(A, BigInt)] = (b1, b2) match {
    case (_Nil_(), _) => b2
    case (_, _Nil_()) => b1
    case (_Cons_((h1, m1), t1), _Cons_((h2, m2), t2)) =>
      val c = compare(h1, h2)
      if (c < 0) (h1, m1) :: bagUnion(t1, b2)
      else if (c > 0) (h2, m2) :: bagUnion(b1, t2)
      else (h1, m1 + m2) :: bagUnion(t1, t2)
  }
  @library
  @wasmRuntime
  def bagDifference[A](b1: _List_[(A, BigInt)], b2: _List_[(A, BigInt)]): _List_[(A, BigInt)] = (b1, b2) match {
    case (_Nil_(), _) => _Nil_()
    case (_, _Nil_()) => b1
    case (_Cons_((h1, m1), t1), _Cons_((h2, m2), t2)) =>
      val c = compare(h1, h2)
      if (c < 0) (h1, m1) :: bagDifference(t1, b2)
      else if (c > 0) bagDifference(b1, t2)
      else (h1, max(0, m1 - m2)) :: bagDifference(t1, t2)
  }

  @library
  @wasmRuntime
  def mapApply[K, V](map: _List_[(K, V)], key: K): V = map match {
    case _Nil_() => error[V]("Key not found in map")
    case _Cons_((k, v), t) =>
      val c = compare(key, k)
      if (c < 0) error[V]("Key not found in map")
      else if (c > 0) mapApply(t, key)
      else v
  }
  @library
  @wasmRuntime
  def mapUpdated[K, V](map: _List_[(K, V)], key: K, value: V): _List_[(K, V)] = map match {
    case _Nil_() => (key, value) :: _Nil_()
    case _Cons_((k, v), t) =>
      val c = compare(key, k)
      if (c < 0) (key, value) :: map
      else if (c > 0) (k, v) :: mapUpdated(t, key, value)
      else (key, value) :: t
  }

}
