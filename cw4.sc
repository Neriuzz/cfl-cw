// Compiler & Formal Languages Coursework 4
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

// Coursework 4 Compiler

// Compiler headers needed for the JVM
val beginning = """
.class public XXX.XXX
.super java/lang/Object

.method public static write(I)V 
    .limit locals 1 
    .limit stack 2 
    getstatic java/lang/System/out Ljava/io/PrintStream; 
    iload 0
    invokevirtual java/io/PrintStream/println(I)V 
    return 
.end method

.method public static writes(Ljava/lang/String;)V
    .limit stack 2
    .limit locals 1
    getstatic java/lang/System/out Ljava/io/PrintStream;
    aload 0
    invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V
    return
.end method

.method public static read()I
    .limit locals 10
    .limit stack 10

    ldc 0
    istore 1
Label1:
    getstatic java/lang/System/in Ljava/io/InputStream;
    invokevirtual java/io/InputStream/read()I
    istore 2
    iload 2
    ldc 10
    isub
    ifeq Label2
    iload 2
    ldc 32
    isub
    ifeq Label2
    iload 2
    ldc 48
    isub
    ldc 10
    iload 1
    imul
    iadd
    istore 1
    goto Label1
Label2:
    iload 1
    ireturn
.end method

.method public static main([Ljava/lang/String;)V
   .limit locals 200
   .limit stack 200

; COMPILED CODE STARTS

"""

val ending = """
; COMPILED CODE ENDS
   return

.end method
"""

// For generating labels
var counter = -1

def generate_label(s: String) = {
  counter += 1
  s ++ "_" ++ counter.toString()
}

// Convenient string interpolations
import scala.language.implicitConversions
import scala.language.reflectiveCalls

implicit def string_inters(sc: StringContext) =
  new {
    def i(args: Any*): String = "   " ++ sc.s(args: _*) ++ "\n"
    def l(args: Any*): String = sc.s(args: _*) ++ ":\n"
  }

// Environment
type Environment = Map[String, Int]

// Compilation

// Compiling operators
def compile_operator(op: String) =
  op match {
    case "+" => i"iadd"
    case "-" => i"isub"
    case "*" => i"imul"
    case "/" => i"idiv"
    case "%" => i"irem"
  }

// Compiling arithmetic expressions
def compile_arithmetic_expression(
    a: ArithmeticExpression,
    env: Environment
): String =
  a match {
    case Number(i)   => i"ldc $i"
    case Variable(x) => i"iload ${env(x)} \t\t; $x"
    case ArithmeticOperation(op, a1, a2) =>
      compile_arithmetic_expression(a1, env) ++ compile_arithmetic_expression(
        a2,
        env
      ) ++ compile_operator(op)
  }

// Compiling boolean expressions
def compile_boolean_expression(
    b: BooleanExpression,
    env: Environment,
    jmp: String
): String =
  b match {
    case True  => ""
    case False => i"goto $jmp"
    case BooleanOperation("==", a1, a2) =>
      compile_arithmetic_expression(a1, env) ++ compile_arithmetic_expression(
        a2,
        env
      ) ++ i"if_icmpne $jmp"
    case BooleanOperation("!=", a1, a2) =>
      compile_arithmetic_expression(a1, env) ++ compile_arithmetic_expression(
        a2,
        env
      ) ++ i"if_icmpeq $jmp"
    case BooleanOperation(">", a1, a2) =>
      compile_arithmetic_expression(a1, env) ++ compile_arithmetic_expression(
        a2,
        env
      ) ++ i"if_icmple $jmp"
    case BooleanOperation(">=", a1, a2) =>
      compile_arithmetic_expression(a1, env) ++ compile_arithmetic_expression(
        a2,
        env
      ) ++ i"if_icmplt $jmp"
    case BooleanOperation("<", a1, a2) =>
      compile_arithmetic_expression(a1, env) ++ compile_arithmetic_expression(
        a2,
        env
      ) ++ i"if_icmpge $jmp"
    case BooleanOperation("<=", a1, a2) =>
      compile_arithmetic_expression(a1, env) ++ compile_arithmetic_expression(
        a2,
        env
      ) ++ i"if_icmpgt $jmp"
    case LogicalOperation("&&", b1, b2) =>
      compile_boolean_expression(b1, env, jmp) ++ compile_boolean_expression(
        b2,
        env,
        jmp
      )
    case LogicalOperation("||", b1, b2) => {
      val jmp_true = generate_label("jmp_true")
      val jmp_false = generate_label("jmp_false")
      compile_boolean_expression(
        b1,
        env,
        jmp_false
      ) ++ i"goto $jmp_true" ++ l"$jmp_false" ++ compile_boolean_expression(
        b2,
        env,
        jmp
      ) ++ l"$jmp_true"
    }
  }

// Compiling statements
def compile_statement(s: Statement, env: Environment): (String, Environment) =
  s match {
    case Skip => ("", env)
    case Assign(x, a) => {
      val index = env.getOrElse(x, env.keys.size)
      (
        compile_arithmetic_expression(a, env) ++ i"istore $index \t\t; $x",
        env + (x -> index)
      )
    }
    case If(cond, bl1, bl2) => {
      val if_else = generate_label("if_else")
      val if_end = generate_label("if_end")
      val (instructions1, env1) = compile_block(bl1, env)
      val (instructions2, env2) = compile_block(bl2, env1)
      (
        compile_boolean_expression(
          cond,
          env,
          if_else
        ) ++ instructions1 ++ i"goto $if_end" ++ l"$if_else" ++ instructions2 ++ l"$if_end",
        env2
      )
    }
    case While(cond, bl) => {
      val loop_begin = generate_label("loop_begin")
      val loop_end = generate_label("loop_end")
      val (instructions1, env1) = compile_block(bl, env)
      (
        l"$loop_begin" ++ compile_boolean_expression(
          cond,
          env,
          loop_end
        ) ++ instructions1 ++ i"goto $loop_begin" ++ l"$loop_end",
        env1
      )
    }
    case WriteVar(s) =>
      (i"iload ${env(s)} \t\t; $s" ++ i"invokestatic XXX/XXX/write(I)V", env)
    case WriteStr(s) =>
      (i"ldc $s" ++ i"invokestatic XXX/XXX/writes(Ljava/lang/String;)V", env)
    case Read(s) => {
      val index = env.getOrElse(s, env.keys.size)
      (
        i"invokestatic XXX/XXX/read()I" ++ i"istore ${index} \t\t; $s",
        env + (s -> index)
      )
    }
  }

// Compiling blocks
def compile_block(bl: Block, env: Environment): (String, Environment) =
  bl match {
    case Nil => ("", env)
    case s :: bl => {
      val (instructions1, env1) = compile_statement(s, env)
      val (instructions2, env2) = compile_block(bl, env1)
      (instructions1 ++ instructions2, env2)
    }
  }

// Main compilation function
def compile(bl: Block, class_name: String): String = {
  val instructions = compile_block(bl, Map.empty)._1
  (beginning ++ instructions ++ ending).replaceAll("XXX", class_name)
}

// Function to compile and run .j files
def run(bl: Block, class_name: String) = {
  val code = compile(bl, class_name)
  os.write.over(os.pwd / s"$class_name.j", code)
  os.proc("java", "-jar", "jasmin.jar", s"$class_name.j").call()
  os.proc("jasa", s"$class_name/$class_name")
    .call(stdout = os.Inherit, stdin = os.Inherit)
}
