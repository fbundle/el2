import EL2.Parser
import EL2.Typer
import EL2.Tactic
import EL2.REPL
import REPL.REPL

open EL2

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => 
    IO.println "Usage: lake exe TacticREPL <filename.el2>"
    pure 1
  | filename :: _ =>
    let source ← IO.FS.readFile filename
    match parse source.toList with
    | none => 
      IO.println "Parse error"
      pure 1
    | some (_, e) =>
      let initialState := EL2.REPL.init e
      let finalStep ← REPL.run EL2.REPL.trans (EL2.REPL.getStep initialState)
      
      let finalState := finalStep.state
      match finalState.proofStates with
      | [ps] =>
        if ps.goals.isEmpty then
          let finalProof := ps.builder []
          let (finalExp, _) := EL2.Tactic.fillHoles finalState.rootExp [finalProof]
          IO.println "\n[COMPLETE] Resulting code:"
          IO.println s!"{finalExp}"
        else
          IO.println "\n[INCOMPLETE] Some goals remain."
      | _ => 
        IO.println "\n[COMPLETED or MULTIPLE STATES]"
      
      pure finalStep.code
