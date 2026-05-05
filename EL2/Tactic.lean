import EL2.Typer
import EL2.Parser

namespace EL2.Tactic

open EL2
open EL2.Typer

structure Goal where
  name : String
  ctx : Ctx
  target : Val
  deriving Repr

structure ProofState where
  goals : List Goal
  builder : List Exp → Exp

/-
  Traverse an Exp with holes and extract goals.
  This is essentially a partial type checker that stops at holes.
-/
mutual
partial def findGoals (ctx : Ctx) (exp : Exp) (expected : Val) : List Goal :=
  match exp with
  | Exp.hole _ => [{ name := "unnamed", ctx := ctx, target := expected }]
  
  | Exp.pi name typeA typeB =>
    match expected with
    | Val.typ n =>
      -- This is a bit complex because we need to check typeA and then typeB
      -- For now, let's assume we don't put holes in Pi types themselves often
      findGoals ctx typeA (Val.typ ctx.maxN) ++ 
      (match eval? ctx.ρ typeA with
       | some vA => 
         let (subCtx, _) := ctx.intro name vA
         findGoals subCtx typeB (Val.typ n)
       | none => [])
    | _ => []

  | Exp.lam name body =>
    match expected with
    | Val.clos env (Exp.pi _ typeA typeB) =>
      match eval? env typeA with
      | some vA =>
        let (subCtx, v) := ctx.intro name vA
        let subEnv := update env name v
        match eval? subEnv typeB with
        | some vB => findGoals subCtx body vB
        | none => []
      | none => []
    | _ => []

  | Exp.bnd name value type body =>
    findGoals ctx value (match eval? ctx.ρ type with | some v => v | none => Val.typ 0) ++ -- simplified
    (match eval? ctx.ρ value, eval? ctx.ρ type with
     | some vVal, some vType =>
       let subCtx := ctx.bind name vVal vType
       findGoals subCtx body expected
     | _, _ => [])

  | Exp.app (Exp.lam name body) arg =>
    -- Desugared untyped let
    match inferExpWeak? ctx arg with
    | some vType =>
      match eval? ctx.ρ arg with
      | some vVal =>
        let subCtx := ctx.bind name vVal vType
        findGoals subCtx body expected
      | none => []
    | none => findGoals ctx arg (Val.typ 0) ++ findGoals ctx exp expected -- Very rough

  | Exp.app cmd arg =>
    match inferExpWeak? ctx cmd with
    | some (Val.clos env (Exp.pi name typeA typeB)) =>
      findGoals ctx arg (match eval? env typeA with | some v => v | none => Val.typ 0)
    | _ => [] -- Can't easily find goals in nested apps without more info

  | _ => []
end

/-
  Substitute holes with terms.
-/
partial def fillHoles (exp : Exp) (fillers : List Exp) : Exp × List Exp :=
  match exp with
  | Exp.hole _ => 
    match fillers with
    | [] => (exp, [])
    | f :: fs => (f, fs)
  | Exp.app cmd arg =>
    let (cmd', fillers') := fillHoles cmd fillers
    let (arg', fillers'') := fillHoles arg fillers'
    (Exp.app cmd' arg', fillers'')
  | Exp.pi name typeA typeB =>
    let (typeA', fillers') := fillHoles typeA fillers
    let (typeB', fillers'') := fillHoles typeB fillers'
    (Exp.pi name typeA' typeB', fillers'')
  | Exp.lam name body =>
    let (body', fillers') := fillHoles body fillers
    (Exp.lam name body', fillers')
  | Exp.bnd name value type body =>
    let (value', fillers') := fillHoles value fillers
    let (type', fillers'') := fillHoles type fillers'
    let (body', fillers''') := fillHoles body fillers''
    (Exp.bnd name value' type' body', fillers''')
  | Exp.inh name type body =>
    let (type', fillers') := fillHoles type fillers
    let (body', fillers'') := fillHoles body fillers'
    (Exp.inh name type' body', fillers'')
  | _ => (exp, fillers)

inductive Tactic where
  | intro (name : String)
  | exact (term : Exp)
  | assumption
  deriving Repr

def applyTactic (t : Tactic) (g : Goal) : Except String (List Goal × (List Exp → Exp)) :=
  match t with
  | Tactic.intro name =>
    match g.target with
    | Val.clos env (Exp.pi _ typeA typeB) =>
      match eval? env typeA with
      | some vA =>
        let (subCtx, v) := g.ctx.intro name vA
        let subEnv := update env name v
        match eval? subEnv typeB with
        | some vB =>
          let newGoal := { name := name, ctx := subCtx, target := vB }
          Except.ok ([newGoal], λ exps => match exps with | [e] => Exp.lam name e | _ => Exp.var "error")
        | none => Except.error "Failed to evaluate target body"
      | none => Except.error "Failed to evaluate parameter type"
    | _ => Except.error "Goal is not a Pi type"

  | Tactic.exact term =>
    match checkExp? g.ctx term g.target with
    | some true => Except.ok ([], λ _ => term)
    | _ => Except.error "Term does not match goal"

  | Tactic.assumption =>
    let rec find (Γ : List (String × Val)) : Option String :=
      match Γ with
      | [] => none
      | (name, type) :: rest =>
        match eqVal? g.ctx.k type g.target with
        | some true => some name
        | _ => find rest
    match find g.ctx.Γ with
    | some name => Except.ok ([], λ _ => Exp.var name)
    | none => Except.error "No matching assumption"

end EL2.Tactic
