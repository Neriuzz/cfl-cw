// Compiler & Formal Languages Coursework 3
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

case object NumberParser extends Parser[Tokens, Int] {
  def parse(in: Tokens) = {
    if (in.nonEmpty && in.head._1 == "number") Set((in.head._2.toInt, in.tail))
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

// AST For the WHILE language
abstract class Statement
abstract class ArithmeticExpression
abstract class BooleanExpression

type Block = List[Statement]

case object Skip extends Statement
case class If(cond: BooleanExpression, bl1: Block, bl2: Block) extends Statement
case class While(cond: BooleanExpression, bl: Block) extends Statement
case class Assign(s: String, a: ArithmeticExpression) extends Statement
case class Read(s: String) extends Statement
case class WriteVar(s: String) extends Statement
case class WriteStr(s: String) extends Statement

case class Variable(s: String) extends ArithmeticExpression
case class Number(i: Int) extends ArithmeticExpression
case class ArithmeticOperation(
    op: String,
    a1: ArithmeticExpression,
    a2: ArithmeticExpression
) extends ArithmeticExpression

case object True extends BooleanExpression
case object False extends BooleanExpression
case class BooleanOperation(
    op: String,
    a1: ArithmeticExpression,
    a2: ArithmeticExpression
) extends BooleanExpression
case class LogicalOperation(
    op: String,
    b1: BooleanExpression,
    b2: BooleanExpression
) extends BooleanExpression

// Arithmetic Expressions
lazy val ArithmeticExpression: Parser[Tokens, ArithmeticExpression] =
  (Term ~ p"+" ~ ArithmeticExpression)
    .map[ArithmeticExpression] {
      case x ~ _ ~ z => ArithmeticOperation("+", x, z)
    } ||
    (Term ~ p"-" ~ ArithmeticExpression)
      .map[ArithmeticExpression] {
        case x ~ _ ~ z => ArithmeticOperation("-", x, z)
      } ||
    Term
lazy val Term: Parser[Tokens, ArithmeticExpression] =
  (Factor ~ p"*" ~ Term).map[ArithmeticExpression] {
    case x ~ _ ~ z => ArithmeticOperation("*", x, z)
  } ||
    (Factor ~ p"/" ~ Term).map[ArithmeticExpression] {
      case x ~ _ ~ z => ArithmeticOperation("/", x, z)
    } ||
    (Factor ~ p"%" ~ Term).map[ArithmeticExpression] {
      case x ~ _ ~ z => ArithmeticOperation("%", x, z)
    } ||
    Factor
lazy val Factor: Parser[Tokens, ArithmeticExpression] =
  (p"(" ~ ArithmeticExpression ~ p")")
    .map[ArithmeticExpression] { case _ ~ y ~ _ => y } ||
    IdentifierParser.map(Variable) ||
    NumberParser.map(Number)

// Boolean Expressions
lazy val BooleanExpression: Parser[Tokens, BooleanExpression] =
  (Comparison ~ p"&&" ~ BooleanExpression).map[BooleanExpression] {
    case x ~ _ ~ z => LogicalOperation("&&", x, z)
  } ||
    (Comparison ~ p"||" ~ BooleanExpression).map[BooleanExpression] {
      case x ~ _ ~ z => LogicalOperation("||", x, z)
    } ||
    Comparison
lazy val Comparison: Parser[Tokens, BooleanExpression] =
  (ArithmeticExpression ~ p"==" ~ ArithmeticExpression).map[BooleanExpression] {
    case x ~ _ ~ z => BooleanOperation("==", x, z);
  } ||
    (ArithmeticExpression ~ p"!=" ~ ArithmeticExpression)
      .map[BooleanExpression] {
        case x ~ _ ~ z => BooleanOperation("!=", x, z);
      } ||
    (ArithmeticExpression ~ p">" ~ ArithmeticExpression)
      .map[BooleanExpression] {
        case x ~ _ ~ z => BooleanOperation(">", x, z);
      } ||
    (ArithmeticExpression ~ p">=" ~ ArithmeticExpression)
      .map[BooleanExpression] {
        case x ~ _ ~ z => BooleanOperation(">=", x, z);
      } ||
    (ArithmeticExpression ~ p"<" ~ ArithmeticExpression)
      .map[BooleanExpression] {
        case x ~ _ ~ z => BooleanOperation("<", x, z);
      } ||
    (ArithmeticExpression ~ p"<=" ~ ArithmeticExpression)
      .map[BooleanExpression] {
        case x ~ _ ~ z => BooleanOperation("<=", x, z);
      } || Boolean
lazy val Boolean: Parser[Tokens, BooleanExpression] =
  (p"true".map[BooleanExpression] { _ => True }) ||
    (p"false".map[BooleanExpression] { _ => False }) ||
    (p"(" ~ BooleanExpression ~ p")").map[BooleanExpression] {
      case _ ~ y ~ _ => y
    }

// A single statement
lazy val Statement: Parser[Tokens, Statement] =
  (p"skip".map[Statement] { _ => Skip }) ||
    (IdentifierParser ~ p":=" ~ ArithmeticExpression).map[Statement] {
      case x ~ _ ~ z => Assign(x, z)
    } ||
    (p"read" ~ p"(" ~ IdentifierParser ~ p")").map[Statement] {
      case _ ~ _ ~ z ~ _ => Read(z)
    } ||
    (p"read" ~ IdentifierParser).map[Statement] { case _ ~ y => Read(y) } ||
    (p"write" ~ p"(" ~ IdentifierParser ~ p")").map[Statement] {
      case _ ~ _ ~ z ~ _ => WriteVar(z)
    } ||
    (p"write" ~ p"(" ~ StringParser ~ p")").map[Statement] {
      case _ ~ _ ~ z ~ _ => WriteStr(z)
    } ||
    (p"write" ~ IdentifierParser).map[Statement] {
      case _ ~ y => WriteVar(y)
    } ||
    (p"write" ~ StringParser).map[Statement] { case _ ~ y => WriteStr(y) } ||
    (p"if" ~ BooleanExpression ~ p"then" ~ Block ~ p"else" ~ Block)
      .map[Statement] { case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w) } ||
    (p"while" ~ BooleanExpression ~ p"do" ~ Block).map[Statement] {
      case _ ~ y ~ _ ~ w => While(y, w)
    }

// Statements
lazy val Statements: Parser[Tokens, Block] =
  (Statement ~ p";" ~ Statements).map[Block] {
    case x ~ _ ~ z => x :: z
  } ||
    (Statement.map[Block] { s => List(s) })

// Blocks
lazy val Block: Parser[Tokens, Block] =
  ((p"{" ~ Statements ~ p"}").map {
    case _ ~ y ~ _ => y
  } ||
    (Statement.map[Block](s => List(s))))

@main
def q2test() = {
  println(
    Statements.parse_all(
      filter_tokens(
        lexing_simp(LANGUAGE, "if (a < b) then skip else a := a * b + 1")
      )
    )
  )
}

// Question 3

// An interpreter for the WHILE language
type Env = Map[String, Int]

// Function to evaluate arithmetic expressions
def eval_ArithmeticExpression(a: ArithmeticExpression, env: Env): Int =
  a match {
    case Number(i)   => i
    case Variable(s) => env(s)
    case ArithmeticOperation("+", a1, a2) =>
      eval_ArithmeticExpression(a1, env) + eval_ArithmeticExpression(a2, env)
    case ArithmeticOperation("-", a1, a2) =>
      eval_ArithmeticExpression(a1, env) - eval_ArithmeticExpression(a2, env)
    case ArithmeticOperation("*", a1, a2) =>
      eval_ArithmeticExpression(a1, env) * eval_ArithmeticExpression(a2, env)
    case ArithmeticOperation("/", a1, a2) =>
      eval_ArithmeticExpression(a1, env) / eval_ArithmeticExpression(a2, env)
    case ArithmeticOperation("%", a1, a2) =>
      eval_ArithmeticExpression(a1, env) % eval_ArithmeticExpression(a2, env)
  }

// Function to evaluate boolean & logical expressions
def eval_bexp(b: BooleanExpression, env: Env): Boolean =
  b match {
    case True  => true
    case False => false
    case BooleanOperation("==", a1, a2) =>
      eval_ArithmeticExpression(a1, env) == eval_ArithmeticExpression(a2, env)
    case BooleanOperation("!=", a1, a2) =>
      eval_ArithmeticExpression(a1, env) != eval_ArithmeticExpression(a2, env)
    case BooleanOperation(">", a1, a2) =>
      eval_ArithmeticExpression(a1, env) > eval_ArithmeticExpression(a2, env)
    case BooleanOperation("<", a1, a2) =>
      eval_ArithmeticExpression(a1, env) < eval_ArithmeticExpression(a2, env)
    case BooleanOperation(">=", a1, a2) =>
      eval_ArithmeticExpression(a1, env) >= eval_ArithmeticExpression(a2, env)
    case BooleanOperation("<=", a1, a2) =>
      eval_ArithmeticExpression(a1, env) <= eval_ArithmeticExpression(a2, env)
    case LogicalOperation("&&", b1, b2) =>
      eval_bexp(b1, env) && eval_bexp(b2, env)
    case LogicalOperation("||", b1, b2) =>
      eval_bexp(b1, env) || eval_bexp(b2, env)
  }

// Function to evaluate a single statement
def eval_stmt(s: Statement, env: Env): Env =
  s match {
    case Skip         => env
    case Assign(x, a) => env + (x -> eval_ArithmeticExpression(a, env))
    case If(b, bl1, bl2) =>
      if (eval_bexp(b, env)) eval_bl(bl1, env) else eval_bl(bl2, env)
    case While(b, bl) =>
      if (eval_bexp(b, env)) eval_stmt(While(b, bl), eval_bl(bl, env)) else env
    case Read(s)     => env + (s -> scala.io.StdIn.readInt())
    case WriteVar(s) => { print(env(s)); env }
    case WriteStr(s) => { print(s); env }
  }

// Function to evaluate a block
def eval_bl(bl: Block, env: Env): Env =
  bl match {
    case Nil     => env
    case s :: bl => eval_bl(bl, eval_stmt(s, env))
  }

// General eval function
def eval(bl: Block): Env = eval_bl(bl, Map())

@main
def fib() = {
  val fib =
    """write "Fib\n";
  read n;
  minus1 := 0;
  minus2 := 1;
  while n > 0 do {
    temp := minus2;
    minus2 := minus1 + minus2;
    minus1 := temp;
    n := n - 1
  };
  write "Result\n";
  write minus2\n"""
  println(
    eval(Statements.parse_all(filter_tokens(lexing_simp(LANGUAGE, fib))).head)
  )
}

@main
def loops() = {
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
    eval(Statements.parse_all(filter_tokens(lexing_simp(LANGUAGE, loops))).head)
  )
}

@main
def primes() = {
  val primes =
    """
  // prints out prime numbers from 2 to 100

  end := 100;
  n := 2;
  while ( n < end) do {
    f := 2;
    tmp := 0;
    while ((f < n / 2 + 1) && (tmp == 0)) do {
      if ((n / f) * f == n) then { tmp := 1 } else { skip };
      f := f + 1
    };
    if (tmp == 0) then { write(n); write("\n") } else { skip };
    n  := n + 1
  }
  """
  println(
    eval(
      Statements
        .parse_all(filter_tokens(lexing_simp(LANGUAGE, primes)))
        .head
    )
  )

}

@main
def collatz() = {
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

      if n % 2 == 0 
      then n := n / 2 
      else n := 3 * n+1;

      cnt := cnt + 1
    };

    write " => ";
    write cnt;
    write "\n";
    bnd := bnd + 1
  }
  """
  println(
    eval(
      Statements.parse_all(filter_tokens(lexing_simp(LANGUAGE, collatz))).head
    )
  )
}

// Benchmark for the loops program
def time_needed[T](code: => T) = {
  val start = System.nanoTime()
  code
  val end = System.nanoTime()
  (end - start) / 1.0e9
}

@main
def time_loops() = {
  println(f"${time_needed(loops())}%.2f seconds")
}
