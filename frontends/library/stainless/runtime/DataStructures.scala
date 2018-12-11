package stainless.runtime

import stainless.lang.error
import stainless.annotation.library

/** Implements tuples,
  * as well as set, map and bag operations on top of sorted lists
  */
@library
object DataStructures {

  sealed case class _Tuple2_[T1, T2](e1: T1, e2: T2)
  sealed case class _Tuple3_[T1, T2, T3](e1: T1, e2: T2, e3: T3)
  sealed case class _Tuple4_[T1, T2, T3, T4](e1: T1, e2: T2, e3: T3, e4: T4)

  /* compares two elements of any type. Will be filled in by the code generator */
  @library
  def _compare_[A](a1: A, a2: A): Int = 0

  // We define our own lists to not have to load the entire scala lib
  @library
  sealed abstract class _List_[A] {
    @inline def ::(elem: A): _List_[A] = _Cons_(elem, this)
  }
  @library
  case class _Cons_[A](h: A, t: _List_[A]) extends _List_[A]
  @library
  case class _Nil_[A]() extends _List_[A]

  @library
  def _setAdd_[A](set: _List_[A], elem: A): _List_[A] = set match {
    case _Nil_() => elem :: _Nil_()
    case _Cons_(h, t) =>
      val c = _compare_(elem, h)
      if (c < 0) elem :: h :: t
      else if (c > 0) h :: _setAdd_(t, elem)
      else h :: t
  }
  @library
  def _elementOfSet_[A](set: _List_[A], elem: A): Boolean = set match {
    case _Nil_() => false
    case _Cons_(h, t) =>
      val c = _compare_(elem, h)
      if (c < 0) false
      else if (c > 0) _elementOfSet_(t, elem)
      else true
  }
  @library
  def _subsetOf_[A](subset: _List_[A], superset: _List_[A]): Boolean = (subset, superset) match {
    case (_Nil_(), _) => true
    case (_, _Nil_()) => false
    case (_Cons_(h1, t1), _Cons_(h2, t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) false
      else if (c > 0) _subsetOf_(subset, t2)
      else _subsetOf_(t1, t2)
  }
  @library
  def _setIntersection_[A](s1: _List_[A], s2: _List_[A]): _List_[A] = (s1, s2) match {
    case (_Nil_(), _) => s2
    case (_, _Nil_()) => s1
    case (_Cons_(h1, t1), _Cons_(h2, t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) _setIntersection_(t1, s2)
      else if (c > 0) _setIntersection_(s1, t2)
      else h1 :: _setIntersection_(t1, t2)
  }
  @library
  def _setUnion_[A](s1: _List_[A], s2: _List_[A]): _List_[A] = (s1, s2) match {
    case (_Nil_(), _) => s2
    case (_, _Nil_()) => s1
    case (_Cons_(h1, t1), _Cons_(h2, t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) h1 :: _setUnion_(t1, s2)
      else if (c > 0) h2 :: _setUnion_(s1, t2)
      else h1 :: _setUnion_(t1, t2)
  }
  @library
  def _setDifference_[A](s1: _List_[A], s2: _List_[A]): _List_[A] = (s1, s2) match {
    case (_Nil_(), _) => _Nil_()
    case (_, _Nil_()) => s1
    case (_Cons_(h1, t1), _Cons_(h2, t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) h1 :: _setDifference_(t1, s2)
      else if (c > 0) _setDifference_(s1, t2)
      else _setDifference_(t1, t2)
  }

  @library @inline def min(b1: BigInt, b2: BigInt): BigInt = if (b1 <= b2) b1 else b2
  @library @inline def max(b1: BigInt, b2: BigInt): BigInt = if (b1 >= b2) b1 else b2

  @library
  def _bagAdd_[A](bag: _List_[(A, BigInt)], elem: A, mult: BigInt): _List_[(A, BigInt)] = bag match {
    case _Nil_() => (elem, mult) :: _Nil_()
    case _Cons_((h, m), t) =>
      val c = _compare_(elem, h)
      if (c < 0) (elem, mult) :: bag
      else if (c > 0) (h, m) :: _bagAdd_(t, elem, mult)
      else (h, m + mult) :: t
  }
  @library
  def _bagMultiplicity_[A](bag: _List_[(A, BigInt)], elem: A): BigInt = bag match {
    case _Nil_() => 0
    case _Cons_((h, m), t) =>
      val c = _compare_(elem, h)
      if (c < 0) 0
      else if (c > 0) _bagMultiplicity_(t, elem)
      else m
  }
  @library
  def _bagIntersection_[A](b1: _List_[(A, BigInt)], b2: _List_[(A, BigInt)]): _List_[(A, BigInt)] = (b1, b2) match {
    case (_Nil_(), _) => b2
    case (_, _Nil_()) => b1
    case (_Cons_((h1, m1), t1), _Cons_((h2, m2), t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) _bagIntersection_(t1, b2)
      else if (c > 0) _bagIntersection_(b1, t2)
      else (h1, min(m1, m2)) :: _bagIntersection_(t1, t2)
  }
  @library
  def _bagUnion_[A](b1: _List_[(A, BigInt)], b2: _List_[(A, BigInt)]): _List_[(A, BigInt)] = (b1, b2) match {
    case (_Nil_(), _) => b2
    case (_, _Nil_()) => b1
    case (_Cons_((h1, m1), t1), _Cons_((h2, m2), t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) (h1, m1) :: _bagUnion_(t1, b2)
      else if (c > 0) (h2, m2) :: _bagUnion_(b1, t2)
      else (h1, m1 + m2) :: _bagUnion_(t1, t2)
  }
  @library
  def _bagDifference_[A](b1: _List_[(A, BigInt)], b2: _List_[(A, BigInt)]): _List_[(A, BigInt)] = (b1, b2) match {
    case (_Nil_(), _) => _Nil_()
    case (_, _Nil_()) => b1
    case (_Cons_((h1, m1), t1), _Cons_((h2, m2), t2)) =>
      val c = _compare_(h1, h2)
      if (c < 0) (h1, m1) :: _bagDifference_(t1, b2)
      else if (c > 0) _bagDifference_(b1, t2)
      else (h1, max(0, m1 - m2)) :: _bagDifference_(t1, t2)
  }

  @library
  def _mapApply_[K, V](map: (_List_[(K, V)], V), key: K): V = map._1 match {
    case _Nil_() => map._2
    case _Cons_((k, v), t) =>
      val c = _compare_(key, k)
      if (c < 0) map._2
      else if (c > 0) _mapApply_((t, map._2), key)
      else v
  }
  @library
  def _mapUpdated_[K, V](map: (_List_[(K, V)], V), key: K, value: V): (_List_[(K, V)], V) = {
    def rec(pairs: _List_[(K, V)]): _List_[(K, V)] = pairs match {
      case _Nil_() => (key, value) :: _Nil_()
      case _Cons_((k, v), t) =>
        val c = _compare_(key, k)
        if (c < 0) (key, value) :: pairs
        else if (c > 0) (k, v) :: rec(t)
        else (key, value) :: t
    }
    (rec(map._1), map._2)
  }

}
