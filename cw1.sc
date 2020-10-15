// Compilers & Formal Languages Coursework 1
// Nerius Ilmonas, King's ID: K1889934, Student ID: 1802769

// Regular expression definitions
abstract class Regexp
case object ZERO extends Regexp
case object ONE extends Regexp
case class CHAR(c: Char) extends Regexp
case class ALT(r1: Regexp, r2: Regexp) extends Regexp
case class SEQ(r1: Regexp, r2: Regexp) extends Regexp
case class STAR(r: Regexp) extends Regexp
case class RANGE(cs: Set[Char]) extends Regexp
case class PLUS(r: Regexp) extends Regexp
case class OPTIONAL(r: Regexp) extends Regexp
case class NTIMES(r: Regexp, n: Int) extends Regexp
case class UPTO(r: Regexp, m: Int) extends Regexp
case class FROM(r: Regexp, n: Int) extends Regexp
case class BETWEEN(r: Regexp, n: Int, m: Int) extends Regexp
case class NOT(r: Regexp) extends Regexp
case class CFUN(f: Char => Boolean) extends Regexp

// CFUN Lambda definitions
val CFUNCHAR = (c: Char) => CFUN((d: Char) => c == d)
val CFUNRANGE = (cs: Set[Char]) => CFUN((c: Char) => cs.contains(c))
val CFUNALL = () => CFUN((_) => true)

// Function to check whether the regular expression can match on the empty string.
def nullable(r: Regexp): Boolean =
  r match {
    case ZERO             => false
    case ONE              => true
    case CHAR(_)          => false
    case ALT(r1, r2)      => nullable(r1) || nullable(r2)
    case SEQ(r1, r2)      => nullable(r1) && nullable(r2)
    case STAR(_)          => true
    case RANGE(cs)        => false
    case PLUS(r)          => nullable(r)
    case OPTIONAL(r)      => true
    case NTIMES(r, n)     => if (n == 0) true else nullable(r)
    case UPTO(r, m)       => true
    case FROM(r, n)       => if (n == 0) true else nullable(r)
    case BETWEEN(r, n, m) => if (n == 0) true else nullable(r)
    case NOT(r)           => !nullable(r)
    case CFUN(_)          => false
  }

// Function to calculate the derivative of a given regular expression w.r.t a character
def der(c: Char, r: Regexp): Regexp =
  r match {
    case ZERO        => ZERO
    case ONE         => ZERO
    case CHAR(d)     => if (c == d) ONE else ZERO
    case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
    case SEQ(r1, r2) =>
      if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
      else SEQ(der(c, r1), r2)
    case STAR(r)     => SEQ(der(c, r), STAR(r))
    case RANGE(cs)   => if (cs.contains(c)) ONE else ZERO
    case PLUS(r)     => ALT(der(c, r), SEQ(der(c, r), PLUS(r)))
    case OPTIONAL(r) => der(c, r)
    case NTIMES(r, n) =>
      if (n == 0) ZERO else SEQ(der(c, r), NTIMES(r, n - 1))
    case UPTO(r, m) => if (m == 0) ZERO else SEQ(der(c, r), UPTO(r, m - 1))
    case FROM(r, n) =>
      if (n == 0) der(c, STAR(r)) else SEQ(der(c, r), FROM(r, n - 1))
    case BETWEEN(r, n, m) =>
      if (n == 0) der(c, UPTO(r, m))
      else SEQ(der(c, r), BETWEEN(r, n - 1, m - 1))
    case NOT(r)  => NOT(der(c, r))
    case CFUN(f) => if (f(c)) ONE else ZERO
  }

// Function to simplify the given regular expression
def simp(r: Regexp): Regexp =
  r match {
    case ALT(r1, r2) =>
      (simp(r1), simp(r2)) match {
        case (ZERO, r2s) => r2s
        case (r1s, ZERO) => r1s
        case (r1s, r2s)  => if (r1s == r2s) r1s else ALT(r1s, r2s)
      }
    case SEQ(r1, r2) =>
      (simp(r1), simp(r2)) match {
        case (ZERO, _)  => ZERO
        case (_, ZERO)  => ZERO
        case (ONE, r2s) => r2s
        case (r1s, ONE) => r1s
        case (r1s, r2s) => SEQ(r1s, r2s)
      }
    case r => r
  }

// Function to calculate the derivative of a given regular expression w.r.t a string s
def ders(s: List[Char], r: Regexp): Regexp =
  s match {
    case Nil    => r
    case c :: s => ders(s, simp(der(c, r)))
  }

// Main matcher function
def matcher(r: Regexp, s: String): Boolean =
  nullable(ders(s.toList, r))

// List of regexps to test
val regexps = List(
  OPTIONAL(CHAR('a')),
  NOT(CHAR('a')),
  NTIMES(CHAR('a'), 3),
  NTIMES(OPTIONAL(CHAR('a')), 3),
  UPTO(CHAR('a'), 3),
  UPTO(OPTIONAL(CHAR('a')), 3),
  BETWEEN(CHAR('a'), 3, 5),
  OPTIONAL(BETWEEN(CHAR('a'), 3, 5)),
  PLUS(CHAR('a')),
  RANGE(Set('a', 'b', 'c')),
  CFUNCHAR('a'),
  CFUNRANGE(Set('a', 'b', 'c')),
  CFUNALL()
)

// List of strings to test against
val strings = List(
  "",
  "a",
  "aa",
  "aaa",
  "aaaaa",
  "aaaaaa"
)

@main
def test() = {
  // Test regexps against strings
  for (i <- 0 to regexps.size - 1) {
    for (j <- 0 to strings.size - 1) {
      println(f"Testing ${regexps(i)} against ${strings(j)}")
      println(f"Result: ${matcher(regexps(i), strings(j))}")
    }
  }
}

@main
def email() = {
  // Regexp to match emails from Q5
  val emailRegexp =
    SEQ(
      SEQ(
        SEQ(
          SEQ(
            PLUS(
              RANGE("abcdefghijklmnopqrstuvxyz0123456789_.-".toSet)
            ),
            CHAR('@')
          ),
          PLUS(RANGE("abcdefghijklmnopqrstuvxyz0123456789_.-".toSet))
        ),
        CHAR('.')
      ),
      BETWEEN(RANGE("abcdefghijklmnopqrstuvxyz".toSet), 2, 6)
    )
  val email = "neriusilmonas@gmail.com"
  println(f"Result: ${matcher(emailRegexp, email)}")
  println(f"Derivative: ${ders(email.toList, emailRegexp)}")
}
