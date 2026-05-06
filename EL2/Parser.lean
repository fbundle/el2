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
  let parseChar: ParseFunc (List Char) Char := pred ("1234567890abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_.".contains ·)
  String.toStringParseFunc $ parseChar.repeatSome


mutual

partial def parseApp: ParseFunc (List Char) Exp :=
  -- parse any thing starts with (
  (
    String.exact "(" ++ String.anyWs ++
    parseExp ++ (String.someWs ++ parseExp).repeatAny ++
    String.anyWs ++ String.exact ")"
  ).map (λ (_, _, cmd, args, _, _) =>
    chainCmd cmd (args.map Prod.snd)
  )

partial def parseHom: ParseFunc (List Char) Exp :=
  let parseAnn: ParseFunc (List Char) (String × Exp) :=
    -- either (name: type) or type
    (
      String.exact "("++
      String.anyWs ++
      parseName ++
      String.anyWs ++
      String.exact ":" ++
      String.anyWs ++
      parseExp ++
      String.anyWs ++
      String.exact ")"
    ).map (λ (_, _, name, _, _, _, type, _, _) => (name, type))

    || parseExp.map (λ e => ("_", e))

  -- hom ann^n typeB
  (
    String.exact "hom" ++
    (String.anyWs ++ parseAnn).repeatAny ++
    String.anyWs ++
    String.exact "->" ++
    String.anyWs ++
    parseExp
  ).map (λ (_, params, _, _, _, typeB) =>
    chainPi (params.map (λ (_, (name, typeA)) => (name, typeA))) typeB
  )

partial def parseLam: ParseFunc (List Char) Exp :=
  -- parse anything starts with lam
  -- lam name [ name]^n => body
  (
    String.exact "lam" ++
    (String.someWs ++ parseName).repeatAny ++
    String.someWs ++
    String.exact "=>" ++
    String.someWs ++
    parseExp
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

partial def parseVar: ParseFunc (List Char) Exp :=
  let specialNames := [
    "lam", "let", "inh", "hom"
  ]
  parseName
  |> (·.filter (λ name =>
    ¬ specialNames.contains name
  ))
  |> (·.map (λ name => Exp.var name))


partial def parseBnd: ParseFunc (List Char) Exp :=
  -- parse anything starts with let
  -- typed let
  let x: ParseFunc (List Char) Exp := (
    String.exact "let" ++
    String.anyWs ++
    parseName ++
    String.anyWs ++
    String.exact ":" ++
    String.anyWs ++
    parseExp ++
    String.anyWs ++
    String.exact ":=" ++
    String.anyWs ++
    parseExp ++
    parseLineBreak ++
    parseExp
  ).map (λ (_, _, name, _, _, _, type, _, _, _, value, _, body) =>
    Exp.bnd name value type body
  )

  -- untyped let
  let y: ParseFunc (List Char) Exp := (
    String.exact "let" ++
    String.anyWs ++
    parseName ++
    String.anyWs ++
    String.exact ":=" ++
    String.anyWs ++
    parseExp ++
    parseLineBreak ++
    parseExp
  ).map (λ (_, _, name, _, _, _, value, _, body) =>
    Exp.app (Exp.lam name body) value
  )

  x || y

partial def parseInh: ParseFunc (List Char) Exp :=
  -- parse anything starts with inh
  (
    String.exact "inh" ++
    String.anyWs ++
    parseName ++
    String.anyWs ++
    String.exact ":" ++
    String.anyWs ++
    parseExp ++
    parseLineBreak ++
    parseExp
  ).map (λ (_, _, name, _, _, _, type, _, body) =>
    Exp.inh name type body
  )

partial def parseExp: ParseFunc (List Char) Exp := λ xs =>
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


end EL2.Parser

namespace EL2
open EL2
open EL2.ParserCombinator

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
    String.anyWs ++
    Parser.parseExp ++
    String.anyWs
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
