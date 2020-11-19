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

// Value definitions
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val

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

// Extracts a string from a value
def flatten(v: Val): String =
  v match {
    case Empty        => ""
    case Chr(c)       => c.toString
    case Left(v)      => flatten(v)
    case Right(v)     => flatten(v)
    case Sequ(v1, v2) => flatten(v1) ++ flatten(v2)
    case Stars(vs)    => vs.map(flatten).mkString
    case Rec(_, v)    => flatten(v)
  }

// Extracts an environment from a value
// Used for tokenising a string
def env(v: Val): List[(String, String)] =
  v match {
    case Empty        => Nil
    case Chr(c)       => Nil
    case Left(v)      => env(v)
    case Right(v)     => env(v)
    case Sequ(v1, v2) => env(v1) ::: env(v2)
    case Stars(vs)    => vs.flatMap(env)
    case Rec(x, v)    => (x, flatten(v)) :: env(v)
  }
// Question 1

// Regular expressions for syntatic entities of the WHILE language
val KEYWORD: Regexp =
  "while" | "if" | "then" | "else" | "do" | "for" | "to" | "true" | "false" | "read" | "write" | "skip"
val OPERATOR: Regexp =
  "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | "<=" | ">=" | ":=" | "&&" | "||"
val LETTER: Regexp =
  RANGE("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".toSet)
val SYMBOL: Regexp = LETTER | RANGE("._><=;,:\\".toSet)
val PARENTHESIS: Regexp = RANGE("(){}".toSet)
val SEMICOLON: Regexp = ";"
val WHITESPACE: Regexp = PLUS(" " | "\n" | "\t")
val DIGIT: Regexp = RANGE("0123456789".toSet)
val NONZERODIGIT: Regexp = RANGE("123456789".toSet)
val NUMBER: Regexp = CHAR('0') | NONZERODIGIT ~ DIGIT.%
val STRING: Regexp = "\"" ~ (SYMBOL | WHITESPACE | DIGIT).% ~ "\""
val IDENTIFIER: Regexp = LETTER ~ ("_" | LETTER | DIGIT).%
val COMMENT: Regexp = "//" ~ (SYMBOL | " " | DIGIT).% ~ "\n"

val LANGUAGE: Regexp = (
  ("keyword" $ KEYWORD) |
    ("operator" $ OPERATOR) |
    ("semicolon" $ SEMICOLON) |
    ("parenthesis" $ PARENTHESIS) |
    ("whitespace" $ WHITESPACE) |
    ("string" $ STRING) |
    ("identifier" $ IDENTIFIER) |
    ("number" $ NUMBER) |
    ("comment" $ COMMENT)
).%

// Question 2

// This function tells us "how" a regular expression has matched the empty string
def mkeps(r: Regexp): Val =
  r match {
    case ONE => Empty
    case ALT(r1, r2) =>
      if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
    case SEQ(r1, r2)  => Sequ(mkeps(r1), mkeps(r2))
    case STAR(r)      => Stars(Nil)
    case REC(x, r)    => Rec(x, mkeps(r))
    case PLUS(r)      => mkeps(r)
    case OPTIONAL(r)  => Empty
    case NTIMES(r, n) => if (n == 0) Stars(Nil) else Stars(List(mkeps(r)))
  }

// This function calculates "how" the derivative of a regular
// expression has matched a string
def inj(r: Regexp, c: Char, v: Val): Val =
  (r, v) match {
    case (STAR(r), Sequ(v, Stars(vs)))      => Stars(inj(r, c, v) :: vs)
    case (SEQ(r1, r2), Sequ(v1, v2))        => Sequ(inj(r1, c, v1), v2)
    case (SEQ(r1, r2), Left(Sequ(v1, v2)))  => Sequ(inj(r1, c, v1), v2)
    case (SEQ(r1, r2), Right(v))            => Sequ(mkeps(r1), inj(r2, c, v))
    case (ALT(r1, r2), Left(v))             => Left(inj(r1, c, v))
    case (ALT(r1, r2), Right(v))            => Right(inj(r2, c, v))
    case (CHAR(d), Empty)                   => Chr(c)
    case (REC(x, r1), _)                    => Rec(x, inj(r1, c, v))
    case (RANGE(_), Empty)                  => Chr(c)
    case (PLUS(r), Sequ(v, Stars(vs)))      => Stars(inj(r, c, v) :: vs)
    case (OPTIONAL(r), v)                   => inj(r, c, v)
    case (NTIMES(r, _), Sequ(v, Stars(vs))) => Stars(inj(r, c, v) :: vs)
  }

// Lexing functions
def lex(r: Regexp, s: List[Char]): Val =
  s match {
    case Nil =>
      if (nullable(r)) mkeps(r) else { throw new Exception("lexing error") }
    case c :: cs => inj(r, c, lex(der(c, r), cs))
  }

def lexing(r: Regexp, s: String, e: Boolean) =
  if (e) env(lex(r, s.toList)) else lex(r, s.toList)

@main
def q2test() = {
  println(f"Result: ${lexing(NTIMES("a", 3), "aaa", false)}")
  println(f"Result: ${lexing(NTIMES("a" | ONE, 3), "aa", false)}")
  println(f"Result: ${lexing(LANGUAGE, "read n;", true)}")
}

// Question 3

// Lexing simplifications
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v: Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v: Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) =
  (v: Val) =>
    v match {
      case Right(v) => Right(f2(v))
      case Left(v)  => Left(f1(v))
    }
def F_SEQ(f1: Val => Val, f2: Val => Val) =
  (v: Val) =>
    v match {
      case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
    }
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) =
  (v: Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) =
  (v: Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) =
  (v: Val) =>
    v match {
      case Rec(x, v) => Rec(x, f(v))
    }
def F_ERROR(v: Val): Val = throw new Exception("error")

def simp(r: Regexp): (Regexp, Val => Val) =
  r match {
    case ALT(r1, r2) => {
      val (r1s, f1s) = simp(r1)
      val (r2s, f2s) = simp(r2)
      (r1s, r2s) match {
        case (ZERO, _) => (r2s, F_RIGHT(f2s))
        case (_, ZERO) => (r1s, F_LEFT(f1s))
        case _ =>
          if (r1s == r2s) (r1s, F_LEFT(f1s))
          else (ALT(r1s, r2s), F_ALT(f1s, f2s))
      }
    }
    case SEQ(r1, r2) => {
      val (r1s, f1s) = simp(r1)
      val (r2s, f2s) = simp(r2)
      (r1s, r2s) match {
        case (ZERO, _) => (ZERO, F_ERROR)
        case (_, ZERO) => (ZERO, F_ERROR)
        case (ONE, _)  => (r2s, F_SEQ_Empty1(f1s, f2s))
        case (_, ONE)  => (r1s, F_SEQ_Empty2(f1s, f2s))
        case _         => (SEQ(r1s, r2s), F_SEQ(f1s, f2s))
      }
    }
    case r => (r, F_ID)
  }

def lex_simp(r: Regexp, s: List[Char]): Val =
  s match {
    case Nil =>
      if (nullable(r)) mkeps(r) else { throw new Exception("lexing error") }
    case c :: cs => {
      val (r_simp, f_simp) = simp(der(c, r))
      inj(r, c, f_simp(lex_simp(r_simp, cs)))
    }
  }

def lexing_simp(r: Regexp, s: String) =
  env(lex_simp(r, s.toList))

def esc(raw: String): String = {
  import scala.reflect.runtime.universe._
  Literal(Constant(raw)).toString
}

def escape(tks: List[(String, String)]) =
  tks.map { case (s1, s2) => (s1, esc(s2)) }

// Function to filter out the whitespace from the list of tokens
def rmv_whitespace(l: List[(String, String)]): List[(String, String)] = {
  l.filter({ case (k, v) => k != "whitespace" })
}

@main
def q3test() = {
  // Fibonnaci
  val fib =
    """write "Fib";
  read n;
  minus1 := 0;
  minus2 := 1;
  while n > 0 do {
    temp := minus2;
    minus2 := minus1 + minus2;
    minus1 := temp;
    n := n - 1
  };
  write "Result";
  write minus2"""
  println(
    f"Lexing fib: ${rmv_whitespace(escape(lexing_simp(LANGUAGE, fib))).mkString("\n")}"
  )

  // Three nested loops
  val loops =
    """start := 1000;
  x := start;
  y := start;
  z := start;
  while 0 < x do {
    while 0 < y do {
      while 0 < z do { z := z - 1 };
      z := start;
      y := y - 1
    };
    y := start;
    x := x - 1
  }
  """
  println(
    f"Lexing loops: ${rmv_whitespace(escape(lexing_simp(LANGUAGE, loops))).mkString("\n")}"
  )

  val factors =
    """// Find all factors of a given input number
  // by J.R. Cordy August 2005
  write "Input n please";
  read n;
  write "The factors of n are";
  f := 2;
  while n != 1 do {
    while (n / f) * f == n do {
      write f;
      n := n / f 
    };
    f := f + 1
  }
  """
  println(
    f"Lexing factors: ${rmv_whitespace(escape(lexing_simp(LANGUAGE, factors))).mkString("\n")}"
  )

  val collatz =
    """// Collatz series
  //
  // needs writing of strings and numbers; comments
  bnd := 1;
  while bnd < 101 do {
    write bnd;
    write ": ";
    n := bnd;
    cnt := 0;
    while n > 1 do {
      write n;
      write ",";
      if n % 2 == 0 then n := n / 2 else n := 3 * n+1;
      cnt := cnt + 1 
    };
    write " => ";
    write cnt;
    write "\n";
    bnd := bnd + 1
  }
  """
  println(
    f"Lexing collatz: ${rmv_whitespace(escape(lexing_simp(LANGUAGE, collatz))).mkString("\n")}"
  )
}
