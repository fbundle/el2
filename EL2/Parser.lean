import EL2.Typer

namespace EL2.Parser.Combinator

def Parser χ α  := χ → Option (χ × α)

def fail : Parser χ α := λ _ => none

def pure (a: α): Parser χ α := λ xs =>
  some (xs, a)

def Parser.bind (p: Parser χ α) (f: α → Parser χ β): Parser χ β := λ xs => do
  let (xs, a) ← p xs
  f a xs

instance: Monad (Parser α) where
  pure := pure
  bind := Parser.bind

def Parser.filter (p: Parser χ α) (f: α → Bool): Parser χ α :=
  p.bind (λ a => if f a then pure a else fail)

def Parser.map (p: Parser χ α) (f: α → β): Parser χ β :=
  p.bind (λ a => pure (f a))

def Parser.concat (p1: Parser χ α) (p2: Parser χ β): Parser χ (α × β) := λ xs => do
  let (xs, a) ← p1 xs
  let (xs, b) ← p2 xs
  some (xs, (a, b))

infixr: 60 " ++ " => Parser.concat

def Parser.either (p1: Parser χ α) (p2: Parser χ α): Parser χ α := λ xs =>
  match p1 xs with
    | some (xs, a) => some (xs, a)
    | none => p2 xs

infixr: 50 " || " => Parser.either -- lower precedence than concat

partial def Parser.many (p: Parser χ α): Parser χ (List α) := λ xs =>
  let rec loop (as: Array α) (xs: χ): Option (χ × List α) :=
    match p xs with
      | none => some (xs, as.toList)
      | some (rest, a) => loop (as.push a) rest
  loop #[] xs

def Parser.many1 (p: Parser χ α): Parser χ (List α) := λ xs => do
  let (xs, as) ← p.many xs
  if as.length = 0 then
    none
  else
    some (xs, as)

def Parser.transpose (ps: List (Parser χ α)): Parser χ (List α) := λ xs =>
  let rec loop (ys: Array α) (ps: List (Parser χ α)) (xs: χ): Option (χ × List α) :=
    match ps with
      | [] => some (xs, ys.toList)
      | p :: ps =>
        match p xs with
          | none => none
          | some (xs, y) =>
            loop (ys.push y) ps xs
  loop #[] ps xs


def pred (p: χ → Bool): Parser (List χ) χ := λ xs =>
  match xs with
    | [] => none
    | x :: xs =>
      if p x then
        some (xs, x)
      else
        none

def exact [BEq χ] (y: χ): Parser (List χ) χ := pred (· == y)

def exactList [BEq χ] (ys: List χ): Parser (List χ) (List χ) :=
  Parser.transpose (ys.map exact)

namespace String

def toStringParser (p: Parser (List Char) (List Char)): Parser (List Char) String :=
  p.map (String.mk ·)

def whitespaceWeak : Parser (List Char) String :=
  -- parse any whitespace
  -- empty whitespace is ok
  toStringParser (pred (·.isWhitespace)).many

def whiteSpaceWithoutNewLineWeak : Parser (List Char) String :=
  -- parse any whitespace but not new line
  -- empty whitespace is ok
  toStringParser (pred (λ c => c.isWhitespace ∧ (¬ c = '\n'))).many


def whitespace : Parser (List Char) String :=
  -- parse some whitespace
  -- empty whitespace is not ok
  toStringParser (pred (·.isWhitespace)).many1

def exact (ys: String): Parser (List Char) String :=
  toStringParser (exactList ys.toList)

end String

end EL2.Parser.Combinator

namespace EL2.Parser
open EL2
open EL2.Parser.Combinator

def parseLineBreak :=
  -- <whitespace_without_newline> <newline> <writespace>
  String.whiteSpaceWithoutNewLineWeak ++
  (String.exact "\n" || String.exact ";") ++
  String.whitespaceWeak

def chainCmd (cmd: Exp) (args: List Exp): Exp :=
  match args with
    | [] => cmd
    | arg :: args =>
      chainCmd (Exp.app cmd arg) args

def chainPi (anns: List (String × Exp)) (last: Exp): Exp :=
  match anns with
    | [] => last
    | (name, type) :: anns =>
      Exp.pi name type (chainPi anns last)

def chainLam (names: List String) (body: Exp): Exp :=
  match names with
    | [] => body
    | name :: names =>
      Exp.lam name (chainLam names body)

def parseName: Parser (List Char) String :=
  String.toStringParser $ (pred ("1234567890abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_.".contains ·)).many1


mutual

partial def parseApp: Parser (List Char) Exp :=
  -- parse any thing starts with (
  (
    String.exact "(" ++
    String.whitespaceWeak ++
    parse ++
    (String.whitespace ++ parse).many ++
    String.whitespaceWeak ++
    String.exact ")"
  ).map (λ (_, _, cmd, args, _, _) =>
    chainCmd cmd (args.map Prod.snd)
  )

partial def parseHom: Parser (List Char) Exp :=
  let parseAnn: Parser (List Char) (String × Exp) :=
      (
        String.exact "(" ++
        String.whitespaceWeak ++
        parseName ++
        String.whitespaceWeak ++
        String.exact ":" ++
        String.whitespaceWeak ++
        parse ++
        String.whitespaceWeak ++
        String.exact ")"
      ).map (λ (_, _, name, _, _, _, type, _, _) => (name, type))

      || parse.map (λ e => ("_", e))

  (
    String.exact "hom" ++
    (String.whitespaceWeak ++ parseAnn).many ++
    String.whitespaceWeak ++
    String.exact "->" ++
    String.whitespaceWeak ++
    parse
  ).map (λ (_, params, _, _, _, typeB) =>
    chainPi (params.map (λ (_, name, typeA) => (name, typeA))) typeB
  )

partial def parseLam: Parser (List Char) Exp :=
  -- parse anything starts with lam
  -- lam name [ name]^n => body
  (
    String.exact "lam" ++
    (String.whitespace ++ parseName).many ++
    String.whitespace ++
    String.exact "=>" ++
    String.whitespace ++
    parse
  ).map (λ (_, names, _, _, _, body) =>
    chainLam (names.map Prod.snd) body
  )

partial def parseUniv: Parser (List Char) Exp := λ xs => do
  let (rest, name) ← parseName xs
  if "Type".isPrefixOf name then
    let levelStr := name.stripPrefix "Type"
    match levelStr.toNat? with
      | none => none
      | some level =>
        some (rest, Exp.typ level)
  else
    none

partial def parseVar: Parser (List Char) Exp := parseName
  |> (·.filter (λ name =>
    let specialNames := [
      "lam", "let", "inh", "hom"
    ]
    ¬ specialNames.contains name
  ))
  |> (·.map (λ name => Exp.var name))


partial def parseBnd: Parser (List Char) Exp :=
  -- parse anything starts with let
  -- typed let
  (
    String.exact "let" ++
    String.whitespaceWeak ++
    parseName ++
    String.whitespaceWeak ++
    String.exact ":" ++
    String.whitespaceWeak ++
    parse ++
    String.whitespaceWeak ++
    String.exact ":=" ++
    String.whitespaceWeak ++
    parse ++
    parseLineBreak ++
    parse
  ).map (λ (_, _, name, _, _, _, type, _, _, _, value, _, body) =>
    Exp.bnd name value type body
  )
  ||

  -- untyped let
  (
    String.exact "let" ++
    String.whitespaceWeak ++
    parseName ++
    String.whitespaceWeak ++
    String.exact ":=" ++
    String.whitespaceWeak ++
    parse ++
    parseLineBreak ++
    parse
  ).map (λ (_, _, name, _, _, _, value, _, body) =>
    Exp.app (Exp.lam name body) value
  )

partial def parseInh: Parser (List Char) Exp :=
  -- parse anything starts with inh
  (
    String.exact "inh" ++
    String.whitespaceWeak ++
    parseName ++
    String.whitespaceWeak ++
    String.exact ":" ++
    String.whitespaceWeak ++
    parse ++
    parseLineBreak ++
    parse
  ).map (λ (_, _, name, _, _, _, type, _, body) =>
    Exp.inh name type body
  )

partial def parse: Parser (List Char) Exp := λ xs =>
  --dbg_trace s!"[DBG_TRACE] parsing {repr xs}"
  xs |>
  (
    parseUniv ||-- starts with Type
    parseApp || -- starts with (
    parseLam || -- starts with lam
    parseHom || -- starts with hom
    parseBnd || -- starts with let
    parseInh || -- starts with inh
    parseHole || -- starts with ?
    parseVar    -- everything else
  )

partial def parseHole: Parser (List Char) Exp :=
  (String.exact "?" ++ (parseName.either (Combinator.pure ""))).map (λ (_, _) =>
    Exp.hole 0
  )

end


end EL2.Parser

namespace EL2
open EL2
open EL2.Parser.Combinator

private inductive state where
  | normal: Array Char → state
  | inComment: Array Char → state

private def removeComments (xs: List Char): List Char :=
  let s := String.mk xs
  let lines := s.splitOn "\n"
  let lines := lines.map (λ line =>
    let parts := line.splitOn "--"
    parts.head!
  )
  let linesWithNL := lines.map (· ++ "\n")
  let s := String.join linesWithNL
  s.toList

#eval String.mk (removeComments "
hello this is --some comment
an mesage with line comment -- everythign after double dashes is ignore


heheh
".toList)

def parse: Parser (List Char) Exp := λ xs =>
  xs |> removeComments |>
  (
    String.whitespaceWeak ++
    Parser.parse ++
    String.whitespaceWeak
  ).map (λ (_, e, _) => e)


#eval parse "
  inh Nat_rec : hom
    (P : hom Nat -> Type0)
    (P zero)
    (hom (n : Nat) (P n) -> (P (succ n)))
    (n : Nat) -> (P n)
body
".toList



end EL2
