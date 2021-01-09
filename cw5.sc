// Compiler & Formal Languages Coursework 5
// Nerius Ilmonas, King's ID: K1889934, Student ID: 1802769

// Lexer from CW2

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
    def + = PLUS(r)
    def ? = OPTIONAL(r)
  }

implicit def stringOps(s: String) =
  new {
    def |(r: Regexp) = ALT(s, r)
    def |(r: String) = ALT(s, r)
    def % = STAR(s)
    def + = PLUS(s)
    def ? = OPTIONAL(s)
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

// Token types
type Token = (String, String)
type Tokens = List[Token]

// Extracts an environment from a value
// Used for tokenising a string
def env(v: Val): Tokens =
  v match {
    case Empty        => Nil
    case Chr(c)       => Nil
    case Left(v)      => env(v)
    case Right(v)     => env(v)
    case Sequ(v1, v2) => env(v1) ::: env(v2)
    case Stars(vs)    => vs.flatMap(env)
    case Rec(x, v)    => (x, flatten(v)) :: env(v)
  }

// Regular expressions for syntatic entities of the FUN language
val KEYWORD: Regexp =
  "def" | "val" | "if" | "then" | "else"
val OPERATOR: Regexp =
  "+" | "-" | "*" | "/" | "%" | "==" | "!=" | ">" | "<" | "<=" | ">=" | "=" | ":" | ","
val TYPE: Regexp = "Int" | "Double" | "Void"
val LETTER: Regexp =
  RANGE("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".toSet)
val SYMBOL: Regexp = LETTER | RANGE("._><=;,:\\".toSet)
val PARENTHESIS: Regexp = RANGE("(){}".toSet)
val SEMICOLON: Regexp = ";"
val WHITESPACE: Regexp = PLUS(" " | "\n" | "\t")
val DIGIT: Regexp = RANGE("0123456789".toSet)
val NONZERODIGIT: Regexp = RANGE("123456789".toSet)
val NONZERONUMBER: Regexp = NONZERODIGIT ~ DIGIT.%
val DECIMALNUMBER: Regexp = ("0" | NONZERONUMBER) ~ "." ~ DIGIT.+
val NUMBER: Regexp =
  "0" | "-".? ~ (NONZERONUMBER | DECIMALNUMBER)
val STRING: Regexp = "\"" ~ (SYMBOL | WHITESPACE | DIGIT).% ~ "\""
val IDENTIFIER: Regexp = LETTER ~ ("_" | LETTER | DIGIT).%
val COMMENT: Regexp = "//" ~ (SYMBOL | " " | DIGIT).% ~ "\n"

val LANGUAGE: Regexp = (
  ("keyword" $ KEYWORD) |
    ("operator" $ OPERATOR) |
    ("type" $ TYPE) |
    ("semicolon" $ SEMICOLON) |
    ("parenthesis" $ PARENTHESIS) |
    ("whitespace" $ WHITESPACE) |
    ("string" $ STRING) |
    ("identifier" $ IDENTIFIER) |
    ("number" $ NUMBER) |
    ("comment" $ COMMENT)
).%

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

// CW3

// Function to filter out the whitespaces and comments from the list of tokens and escape literals
def filter_tokens(tks: Tokens): Tokens = {
  tks
    .filter(tk => tk._1 != "whitespace" && tk._1 != "comment")
    .map(tk =>
      if (tk._1 == "string")
        (tk._1, StringContext treatEscapes tk._2 replaceAll ("\"", ""))
      else tk
    )
}

case class ~[+A, +B](x: A, y: B)

type IsSeq[A] = A => Seq[_]

// Main Parser class definition
abstract class Parser[I: IsSeq, T] {
  def parse(in: I): Set[(T, I)]

  def parse_all(in: I): Set[T] =
    for ((head, tail) <- parse(in); if tail.isEmpty)
      yield head
}

// Parser Combinators

// Sequence Parser
class SeqParser[I: IsSeq, T, S](p: => Parser[I, T], q: => Parser[I, S])
    extends Parser[I, ~[T, S]] {
  def parse(in: I) =
    for (
      (hd1, tl1) <- p.parse(in);
      (hd2, tl2) <- q.parse(tl1)
    ) yield (new ~(hd1, hd2), tl2)
}

// Alternative Parser
class AltParser[I: IsSeq, T](p: => Parser[I, T], q: => Parser[I, T])
    extends Parser[I, T] {
  def parse(in: I) = p.parse(in) ++ q.parse(in)
}

// Map Parser
class MapParser[I: IsSeq, T, S](p: => Parser[I, T], f: T => S)
    extends Parser[I, S] {
  def parse(in: I) = for ((hd, tl) <- p.parse(in)) yield (f(hd), tl)
}

// More convenient syntax for parser combinators
implicit def ParserOps[I: IsSeq, T](p: Parser[I, T]) =
  new {
    def ||(q: => Parser[I, T]) = new AltParser[I, T](p, q)
    def ~[S](q: => Parser[I, S]) = new SeqParser[I, T, S](p, q)
    def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
  }

// Token Parsers
case class TokenParser(s: String) extends Parser[Tokens, String] {
  def parse(in: Tokens) = {
    if (in.nonEmpty && in.head._2 == s) Set((s, in.tail)) else Set()
  }
}

case object IdentifierParser extends Parser[Tokens, String] {
  def parse(in: Tokens) = {
    if (in.nonEmpty && in.head._1 == "identifier") Set((in.head._2, in.tail))
    else Set()
  }
}

// Hacking the NumberParser a bit so it works with both integers and floats
import scala.util.Try

case object NumberParser extends Parser[Tokens, AnyVal] {
  def parse(in: Tokens) = {
    if (in.nonEmpty && in.head._1 == "number")
      Set((Try(in.head._2.toInt).getOrElse(in.head._2.toFloat), in.tail))
    else Set()
  }
}

case object StringParser extends Parser[Tokens, String] {
  def parse(in: Tokens) = {
    if (in.nonEmpty && in.head._1 == "string") Set((in.head._2, in.tail))
    else Set()
  }
}

implicit def parser_interpolation(sc: StringContext) =
  new {
    def p(args: Any*) = TokenParser(sc.s(args: _*))
  }

// CW 5

// AST For FUN language
abstract class Expression
abstract class BooleanExpression
abstract class Decleration

// Declerations
case class Def(
    name: String,
    args: List[(String, String)],
    typeof: String,
    body: Expression
) extends Decleration
case class Main(e: Expression) extends Decleration
case class ConstIntegerDecleration(name: String, i: Int) extends Decleration
case class ConstFloatDecleration(name: String, d: Float) extends Decleration

// Expressions
case class Call(name: String, args: List[Expression]) extends Expression
case class If(cond: BooleanExpression, e1: Expression, e2: Expression)
    extends Expression
case class Write(e: Expression) extends Expression
case class Variable(s: String) extends Expression
case class ConstInteger(i: Int) extends Expression
case class ConstFloat(d: Float) extends Expression
case class ArithmeticOperation(op: String, a1: Expression, a2: Expression)
    extends Expression
case class Sequence(e1: Expression, e2: Expression) extends Expression

// Boolean Expressions
case class BooleanOperation(op: String, a1: Expression, a2: Expression)
    extends BooleanExpression

// Parsing

@main
def mandelbrot() = {
  val mandelbrot = """
    // Mandelbrot program

    val Ymin: Double = -1.3;
    val Ymax: Double = 1.3;
    val YStep: Double = 0.05;   //0.025;

    val Xmin: Double = -2.1;
    val Xmax: Double = 1.1;
    val Xstep: Double = 0.02;   //0.01;

    val Maxiters: Int = 1000;

    def m_iter(m: Int, x: Double, y: Double,
                        zr: Double, zi: Double) : Void = {
        if Maxiters <= m
        then print_star()
        else {
            if 4.0 <= zi*zi+zr*zr then print_space()
            else m_iter(m + 1, x, y, x+zr*zr-zi*zi, 2.0*zr*zr+y)
        }
    };

    def x_iter(x: Double, y: Double) : Void = {
        if x <= Xmax
        then { m_iter(0, x, y, 0.0, 0.0) ; x_iter(x + Xstep, y) }
        else skip()
    };

    def y_iter(y: Double) : Void = {
        if y <= Ymax
        then { x_iter(Xmin, y) ; new_line() ; y_iter(y + Ystep) }
        else skip()
    };

    y_iter(Ymin)
    """
  println(filter_tokens(lexing_simp(LANGUAGE, mandelbrot)).mkString("\n"))
}
