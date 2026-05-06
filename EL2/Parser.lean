import EL2.ParserCombinator
import EL2.Typer

namespace EL2.Parser
open EL2.ParserCombinator

def parseLineBreak :=
  -- <whitespace_without_newline> <newline> <writespace>
  String.anyWsNoNL ++
  (String.exact "\n" || String.exact ";") ++
  String.anyWs

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

def parseName: ParseFunc (List Char) String :=
  String.toStringParseFunc $ (pred ("1234567890abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_.".contains ·)).repeatSome


mutual

partial def parseApp: ParseFunc (List Char) Exp :=
  -- parse any thing starts with (
  (
    String.exact "(" ++
    String.whitespaceWeak ++
    parse ++
    (String.whitespace ++ parse).repeatAny ++
    String.whitespaceWeak ++
    String.exact ")"
  ).map (λ (_, _, cmd, args, _, _) =>
    chainCmd cmd (args.map Prod.snd)
  )

partial def parseHom: ParseFunc (List Char) Exp :=
  let parseAnn: ParseFunc (List Char) (String × Exp) :=
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
    (String.whitespaceWeak ++ parseAnn).repeatAny ++
    String.whitespaceWeak ++
    String.exact "->" ++
    String.whitespaceWeak ++
    parse
  ).map (λ (_, params, _, _, _, typeB) =>
    chainPi (params.map (λ (_, name, typeA) => (name, typeA))) typeB
  )

partial def parseLam: ParseFunc (List Char) Exp :=
  -- parse anything starts with lam
  -- lam name [ name]^n => body
  (
    String.exact "lam" ++
    (String.whitespace ++ parseName).repeatAny ++
    String.whitespace ++
    String.exact "=>" ++
    String.whitespace ++
    parse
  ).map (λ (_, names, _, _, _, body) =>
    chainLam (names.map Prod.snd) body
  )

partial def parseUniv: ParseFunc (List Char) Exp := λ xs => do
  let (rest, name) ← parseName xs
  if "Type".isPrefixOf name then
    let levelStr := name.stripPrefix "Type"
    match levelStr.toNat? with
      | none => none
      | some level =>
        some (rest, Exp.typ level)
  else
    none

partial def parseVar: ParseFunc (List Char) Exp := parseName
  |> (·.filter (λ name =>
    let specialNames := [
      "lam", "let", "inh", "hom"
    ]
    ¬ specialNames.contains name
  ))
  |> (·.map (λ name => Exp.var name))


partial def parseBnd: ParseFunc (List Char) Exp :=
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

partial def parseInh: ParseFunc (List Char) Exp :=
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

partial def parse: ParseFunc (List Char) Exp := λ xs =>
  --dbg_trace s!"[DBG_TRACE] parsing {repr xs}"
  xs |>
  (
    parseUniv ||-- starts with Type
    parseApp || -- starts with (
    parseLam || -- starts with lam
    parseHom || -- starts with hom
    parseBnd || -- starts with let
    parseInh || -- starts with inh
    parseVar    -- everything else
  )

end


end EL2.ParseFunc

namespace EL2
open EL2
open EL2.ParseFuncCombinator

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

def parse: ParseFunc (List Char) Exp := λ xs =>
  xs |> removeComments |>
  (
    String.whitespaceWeak ++
    ParseFunc.parse ++
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
