# Compilers & Formal Languages CW1

###### By Nerius Ilmonas (K1889934)

---

#### Question 1  

My email is k1889934@kcl.ac.uk and I will be mainly studying from home.

#### Question 2

- Python
  
- Javascript
  
- Java
  
- CPP
  
- C
  

#### Question 3

Nullable definitions are as follows:

$nullable([c_1, c_2, ... ,c_n]) \stackrel{\mathrm def}{=} \textrm{false}$

$nullable(r^+) \stackrel{\mathrm def}{=} nullable(r)$

$nullable(r^?) \stackrel{\mathrm def}{=} \textrm{true}$

$nullable(r^{\{n\}}) \stackrel{\mathrm def}{=} \textrm {if (n == 0) true else } nullable(r)$

$nullable(r^{\{..m\}}) \stackrel{\mathrm def}{=} \textrm{true}$

$nullable(r^{\{n..\}}) \stackrel{\mathrm def}{=} \textrm {if (n == 0) true else } nullable(r)$

$nullable(r^{\{n..m\}}) \stackrel{\mathrm def}{=} \textrm {if (n == 0) true else } nullable(r)$

$nullable(\neg r) \stackrel{\mathrm def}{=} \hspace{.1cm} !nullable(r)$

Derivative definitions are as follows:

$der \hspace{.1cm}c([c_1, c_2, ... ,c_n]) \stackrel{\mathrm def}{=} \textrm {if (cs.contains(c))} \hspace{.1cm} 1 \hspace{.1cm} \textrm{else} \hspace{.1cm} 0$

$der \hspace{.1cm}c(r^+) \stackrel{\mathrm def}{=} der \hspace{.1cm} c(r) \hspace{.1cm} . \hspace{.1cm} r^*$

$der \hspace{.1cm}c(r^?) \stackrel{\mathrm def}{=} der \hspace{.1cm} c(r)$

$der \hspace{.1cm}c(r^{{n}}) \stackrel{\mathrm def}{=} \textrm{if (n == 0)} \hspace{.1cm} der \hspace{.1cm} c(r^*) \hspace{.1cm} \textrm{else} \hspace{.1cm} der \hspace{.1cm}c(r) \hspace{.1cm} . \hspace{.1cm} r^{\{n-1\}}$

$der \hspace{.1cm}c(r^{{..m}}) \stackrel{\mathrm def}{=} \textrm{if (m == 0)} \hspace{.1cm} 0 \hspace{.1cm} \textrm{else} \hspace{.1cm} der \hspace{.1cm} c(r) \hspace{.1cm}. \hspace{.1cm} r^{\{..m\}}$

$der \hspace{.1cm}c(r^{{n..}}) \stackrel{\mathrm def}{=} \textrm{if (n == 0)} \hspace{.1cm} der \hspace{.1cm} c(r^*) \hspace{.1cm} \textrm{else} \hspace{.1cm} der \hspace{.1cm} c(r) \hspace{.1cm}. \hspace{.1cm} r^{\{n-1..\}}$

$der \hspace{.1cm}c(r^{{n..m}}) \stackrel{\mathrm def}{=} \textrm{if (n == 0)} \hspace{.1cm} der \hspace{.1cm} c(r^{\{...m\}}) \hspace{.1cm} \textrm{else} \hspace{.1cm} der \hspace{.1cm}c(r) \hspace{.1cm} . \hspace{.1cm} r^{\{n-1..m-1\}}$

$der \hspace{.1cm}c(\neg r) \stackrel{\mathrm def}{=} \neg der \hspace{.1cm} c(r)$

#### Question 4

For this question I defined three lambda functions (CFUNCHAR, CFUNRANGE, CFUNALL) which generated a CFUN object.

$nullable(CFUN(f))$ would always return false because neither CHAR, RANGE or ALL can contain the empty string.

$der \hspace{.1cm}c(CFUN(f))$ was defined as ONE if the function $f(c)$ returns true, else ZERO. This is because if $f(c)$ returns true then it means that the character, $c$ is contained in CHAR, RANGE or ALL and therefore performing a derivation on it would yield ONE.

#### Question 5

Simplified derivative: $([a-z0-9.-]*.(.).[a-z.]\{2,6\}) + [a-z.]\{0,4\} + [a-z.]?$

where $(.)$ is the literal character "."

#### Question 6

| String | Matched? |
| --- | --- |
| /\*\*/ | Yes |
| /*foobar\*/ | Yes |
| /\*test\*/test\*/ | No  |
| /\*test/\*test\*/ | Yes |

#### Question 7

| String | $r_1$ Matched? | $r_2$ Matched? |
| --- | --- | --- |
| 5   | Yes | Yes |
| 6   | No  | No  |
| 7   | No  | Yes |