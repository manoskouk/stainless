package stainless.runtime

import stainless.lang.error

/* Implements sets, maps and bags with sorted lists */
object DataStructures {

  /* Compares two elements of any type. Will be filled in by the code generator */
  def compare[A](a1: A, a2: A): Int = 0

  // We define our own lists to not have to load the entire scala lib
  sealed abstract class List[A] {
    @inline def ::(elem: A): List[A] = Cons(elem, this)
  }
  case class Cons[A](h: A, t: List[A]) extends List[A]
  case class Nil[A]() extends List[A]

  def setEmpty[A]: List[A] = Nil()
  def setAdd[A](set: List[A], elem: A): List[A] = set match {
    case Nil() => elem :: Nil()
    case Cons(h, t) =>
      val c = compare(elem, h)
      if (c < 0) elem :: h :: t
      else if (c > 0) h :: setAdd(t, elem)
      else h :: t
  }
  def elementOfSet[A](set: List[A], elem: A): Boolean = set match {
    case Nil() => false
    case Cons(h, t) =>
      val c = compare(elem, h)
      if (c < 0) false
      else if (c > 0) elementOfSet(t, elem)
      else true
  }
  def subsetOf[A](subset: List[A], superset: List[A]): Boolean = (subset, superset) match {
    case (Nil(), _) => true
    case (_, Nil()) => false
    case (Cons(h1, t1), Cons(h2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) false
      else if (c > 0) subsetOf(subset, t2)
      else subsetOf(t1, t2)
  }
  def setIntersection[A](s1: List[A], s2: List[A]): List[A] = (s1, s2) match {
    case (Nil(), _) => s2
    case (_, Nil()) => s1
    case (Cons(h1, t1), Cons(h2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) setIntersection(t1, s2)
      else if (c > 0) setIntersection(s1, t2)
      else h1 :: setIntersection(t1, t2)
  }
  def setUnion[A](s1: List[A], s2: List[A]): List[A] = (s1, s2) match {
    case (Nil(), _) => s2
    case (_, Nil()) => s1
    case (Cons(h1, t1), Cons(h2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) h1 :: setUnion(t1, s2)
      else if (c > 0) h2 :: setUnion(s1, t2)
      else h1 :: setUnion(t1, t2)
  }
  def setDifference[A](s1: List[A], s2: List[A]): List[A] = (s1, s2) match {
    case (Nil(), _) => Nil()
    case (_, Nil()) => s1
    case (Cons(h1, t1), Cons(h2, t2)) =>
      val c = compare(h1, h2)
      if (c < 0) h1 :: setDifference(t1, s2)
      else if (c > 0) setDifference(s1, t2)
      else setDifference(t1, t2)
  }

  @inline def min(b1: BigInt, b2: BigInt): BigInt = if (b1 <= b2) b1 else b2
  @inline def max(b1: BigInt, b2: BigInt): BigInt = if (b1 >= b2) b1 else b2

  def bagEmpty[A]: List[(A, BigInt)] = Nil()
  def bagAdd[A](bag: List[(A, BigInt)], elem: A): List[(A, BigInt)] = bag match {
    case Nil() => (elem, BigInt(1)) :: Nil()
    case Cons((h, m), t) =>
      val c = compare(elem, h)
      if (c < 0) (elem, BigInt(1)) :: bag
      else if (c > 0) (h, m) :: bagAdd(t, elem)
      else (h, m + 1) :: t
  }
  def bagMultiplicity[A](bag: List[(A, BigInt)], elem: A): BigInt = bag match {
    case Nil() => 0
    case Cons((h, m), t) =>
      val c = compare(elem, h)
      if (c < 0) 0
      else if (c > 0) bagMultiplicity(t, elem)
      else m
  }
  def bagIntersection[A](b1: List[(A, BigInt)], b2: List[(A, BigInt)]): List[(A, BigInt)] = (b1, b2) match {
    case (Nil(), _) => b2
    case (_, Nil()) => b1
    case (Cons((h1, m1), t1), Cons((h2, m2), t2)) =>
      val c = compare(h1, h2)
      if (c < 0) bagIntersection(t1, b2)
      else if (c > 0) bagIntersection(b1, t2)
      else (h1, min(m1, m2)) :: bagIntersection(t1, t2)
  }
  def bagUnion[A](b1: List[(A, BigInt)], b2: List[(A, BigInt)]): List[(A, BigInt)] = (b1, b2) match {
    case (Nil(), _) => b2
    case (_, Nil()) => b1
    case (Cons((h1, m1), t1), Cons((h2, m2), t2)) =>
      val c = compare(h1, h2)
      if (c < 0) (h1, m1) :: bagUnion(t1, b2)
      else if (c > 0) (h2, m2) :: bagUnion(b1, t2)
      else (h1, m1 + m2) :: bagUnion(t1, t2)
  }
  def bagDifference[A](b1: List[(A, BigInt)], b2: List[(A, BigInt)]): List[(A, BigInt)] = (b1, b2) match {
    case (Nil(), _) => Nil()
    case (_, Nil()) => b1
    case (Cons((h1, m1), t1), Cons((h2, m2), t2)) =>
      val c = compare(h1, h2)
      if (c < 0) (h1, m1) :: bagDifference(t1, b2)
      else if (c > 0) bagDifference(b1, t2)
      else (h1, max(0, m1 - m2)) :: bagDifference(t1, t2)
  }

  def mapEmpty[K, V]: List[(K, V)] = Nil()
  def mapApply[K, V](map: List[(K, V)], key: K): V = map match {
    case Nil() => error[V]("Key not found in map")
    case Cons((k, v), t) =>
      val c = compare(key, k)
      if (c < 0) error[V]("Key not found in map")
      else if (c > 0) mapApply(t, key)
      else v
  }
  def mapUpdated[K, V](map: List[(K, V)], key: K, value: V): List[(K, V)] = map match {
    case Nil() => (key, value) :: Nil()
    case Cons((k, v), t) =>
      val c = compare(key, k)
      if (c < 0) (key, value) :: map
      else if (c > 0) (k, v) :: mapUpdated(t, key, value)
      else (key, value) :: t
  }

}