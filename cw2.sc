// Compilers & Formal Languages Coursework 2
// Nerius Ilmonas, King's ID: K1889934, Student ID: 1802769

// Global Definitions

// Regular expressions
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
case class REC(s: String, r: Regexp) extends Regexp

// Function to check whether the regular expression can match on the empty string.
def nullable(r: Regexp): Boolean =
  r match {
    case ZERO         => false
    case ONE          => true
    case CHAR(_)      => false
    case ALT(r1, r2)  => nullable(r1) || nullable(r2)
    case SEQ(r1, r2)  => nullable(r1) && nullable(r2)
    case STAR(_)      => true
    case RANGE(cs)    => false
    case PLUS(r)      => nullable(r)
    case OPTIONAL(r)  => true
    case NTIMES(r, n) => if (n == 0) true else nullable(r)
    case REC(_, r)    => nullable(r)
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
    case PLUS(r)     => SEQ(der(c, r), STAR(r))
    case OPTIONAL(r) => der(c, r)
    case NTIMES(r, n) =>
      if (n == 0) ZERO else SEQ(der(c, r), NTIMES(r, n - 1))
    case REC(_, r) => der(c, r)
  }

// Some convenience for typing in regular expressions
def charlist2Regexp(s: List[Char]): Regexp =
  s match {
    case Nil      => ONE
    case c :: Nil => CHAR(c)
    case c :: s   => SEQ(CHAR(c), charlist2Regexp(s))
  }

implicit def string2Regexp(s: String): Regexp =
  charlist2Regexp(s.toList)

implicit def RegexpOps(r: Regexp) =
  new {
    def |(s: Regexp) = ALT(r, s)
    def % = STAR(r)
    def ~(s: Regexp) = SEQ(r, s)
  }

implicit def stringOps(s: String) =
  new {
    def |(r: Regexp) = ALT(s, r)
    def |(r: String) = ALT(s, r)
    def % = STAR(s)
    def ~(r: Regexp) = SEQ(s, r)
    def ~(r: String) = SEQ(s, r)
    def $(r: Regexp) = REC(s, r)
  }

// Question 1

// Regular expressions for syntatic entities of the WHILE language
val KEYWORD: Regexp =
  "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "false" | "read" | "write" | "skip"
val OPERATOR: Regexp =
  "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | "<=" | ">=" | ":=" | "&&" | "||"
val LETTER: Regexp =
  RANGE("ABCDEFGHIJKLMNOPQRSTUVWXYZ".toSet) | RANGE(
    "abcdefghijklmnopqrstuvwxyz".toSet
  )
val SYMBOL: Regexp = LETTER | RANGE("._><=;,:\\".toSet)
val PARENTHESIS: Regexp = RANGE("(){}".toSet)
val SEMICOLON: Regexp = ";"
val WHITESPACE: Regexp = " " | "\n" | "\t"
val DIGIT: Regexp = RANGE("0123456789".toSet)
val NONZERODIGIT: Regexp = RANGE("123456789".toSet)
val STRING: Regexp = "\"" ~ PLUS(SYMBOL | WHITESPACE | DIGIT) ~ "\""
val IDENTIFIER: Regexp = LETTER ~ PLUS("_" | LETTER | DIGIT)
val NUMBER: Regexp = DIGIT ~ NONZERODIGIT.%
val COMMENT: Regexp = "//" ~ (SYMBOL | " " | DIGIT).% ~ "\n"
