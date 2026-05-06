import EL2.Parser
import EL2.Typer
import EL2.Reducer



def t := EL2.Exp.typ 1

def lift (err: String) (o?: Option α) : Except String α :=
  match o? with
    | none => Except.error err
    | some v => Except.ok v

def parseCheckAndReduce (source: String): Except String String := do
  let (xs, e) ← lift "parse_error" $ EL2.parse source.toList
  let b ← lift "type_error" $ EL2.typeCheck? e t
  if ¬ b then
    Except.error "type_error"
  else
  let re ← lift "reduce_error" $ EL2.reduce? e
  Except.ok s!"[OK] {re}\n[REMAINING] {xs}"

def main (args : List String): IO Unit := do
  IO.println "-------------------------------------------------------------------"
  match args with
    | [] => IO.println "args_empty: use `lake exe CheckAndReduce.lean <filename>`"
    | filename :: _ =>
      let source ← IO.FS.readFile filename
      match parseCheckAndReduce source with
        | Except.ok s => IO.println s
        | Except.error err => IO.println err
