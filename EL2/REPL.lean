import EL2.Typer
import EL2.Parser
import EL2.Tactic
import REPL.REPL

namespace EL2.REPL

open EL2
open EL2.Typer
open EL2.Tactic

structure State where
  rootExp : Exp
  proofStates : List ProofState
  history : List (Exp × List ProofState)

def init (e : Exp) : State :=
  let goals := findGoals emptyCtx e (Val.typ 0) -- Assumes file is Type0
  let ps := { goals := goals, builder := λ exps => match exps with | [] => Exp.var "empty" | e::_ => e } -- simplified
  { rootExp := e, proofStates := [ps], history := [] }

def State.push (s : State) : State :=
  { s with history := (s.rootExp, s.proofStates) :: s.history }

def State.pop (s : State) : State :=
  match s.history with
  | [] => s
  | (e, ps) :: rest => { rootExp := e, proofStates := ps, history := rest }

def getStep (s : State) (msg : Option String := none) : REPL.Step State :=
  let help := [
    "EL2 Tactic REPL",
    "Available tactics:",
    "  intro <name>  - Introduce a variable from a Pi type",
    "  exact <term>  - Close the goal with a specific term",
    "  assumption    - Automatically find a variable in context",
    "  undo          - Undo the last tactic",
    ""
  ]
  let out : List String :=
    (if s.history.isEmpty then help else []) ++
    match s.proofStates with
    | [] => ["All goals accomplished!"]
    | ps :: _ =>
      match ps.goals with
      | [] => ["Current proof state finished."]
      | g :: _ =>
        let hyps := g.ctx.Γ.reverse.map (λ (n, v) => s!"{n} : {v}")
        let target := s!"\n-------------------------------------------------------------------\n⊢ {g.target}"
        hyps ++ [target]
  
  let err := match msg with | some m => [m] | none => []
  
  {
    state := s,
    code := if s.proofStates.isEmpty then 0 else 1,
    err := err,
    out := out
  }

def parseTactic (input : String) : Option Tactic :=
  let input := input.trim
  if input.startsWith "intro " then
    some (Tactic.intro (input.stripPrefix "intro ").trim)
  else if input.startsWith "exact " then
    -- Very simple parser for exact
    match (Parser.parse (input.stripPrefix "exact ").trim.toList) with
    | some (_, e) => some (Tactic.exact e)
    | none => none
  else if input == "assumption" then
    some Tactic.assumption
  else
    none

def trans (s : State) (input : String) : REPL.Step State :=
  let input := input.trim
  if input == "undo" then
    getStep s.pop
  else
    match s.proofStates with
    | [] => getStep s (some "No active goals")
    | ps :: psRest =>
      match ps.goals with
      | [] => getStep { s with proofStates := psRest } -- Move to next ProofState if any
      | g :: gRest =>
        match parseTactic input with
        | some tac =>
          match applyTactic tac g with
          | Except.ok (newGoals, builder) =>
            let newPs := { goals := newGoals ++ gRest, builder := (λ exps => 
              let (firstExps, restExps) := exps.splitAt newGoals.length
              ps.builder (builder firstExps :: restExps))
            }
            let s' := s.push
            let newState := { s' with proofStates := newPs :: psRest }
            if newPs.goals.isEmpty then
               -- If this proof state is done, we might want to fill the hole in rootExp
               -- For now, let's just keep it in psRest
               getStep newState (some "Goal closed")
            else
               getStep newState
          | Except.error e => getStep s (some s!"Tactic error: {e}")
        | none => getStep s (some "Unknown tactic or parse error")

end EL2.REPL
