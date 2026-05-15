-- extended from (Thierry Coquand - An algorithm for type-checking dependent types)
-- the algorithm is able to type check dependently-typed λ-calculus
-- with type universe (type_0, type_1, ...) and inhabit

namespace EL2

inductive Exp where
  -- typ 0 is type of small types: Nat, Pi, etc.
  -- typ 0 is at level 2
  -- typ N is at level N + 2
  -- small types are at level 1
  -- terms are at level 0
  | typ : (level: Nat) → Exp
  -- variable
  | var: (name: String) → Exp
  -- application
  | app: (cmd: Exp) → (arg: Exp) → Exp
  -- Π type: Π (name: type) body - type of abs
  | pi:  (name: String) → (typeA: Exp) → (typeB: Exp) → Exp
  -- λ abstraction
  | lam: (name: String) → (body: Exp) → Exp
  -- let binding: let name: type := value
  | bnd: (name: String) → (value: Exp) → (type: Exp) → (body: Exp) → Exp
  -- inh - const
  | inh: (name: String) → (type: Exp) → (body: Exp) → Exp
  deriving Repr

end EL2

namespace EL2.Typer

inductive Val where
  -- typ_n
  | typ : (n: Nat) → Val
  -- generic value
  | gen: (i: Nat) → Val
  -- application
  | app: (cmd: Val) → (arg: Val) → Val
  -- with closure - a future value - evaluated by eval?
  | clos: (env: List (String × Val)) → (exp: Exp) → Val
  deriving Repr

-- Util
partial def lookup? (env: List (String × α)) (query: String): Option α :=
  match env with
    | [] => none
    | (key, val) :: rest =>
      if query = key then
        some val
      else
        lookup? rest query

partial def update (env: List (String × α)) (name: String) (val: α): List (String × α) :=
  (name, val) :: env

def emptyEnv: List (String × α) := []

-- WHNF
mutual
partial def whnf? (cmd: Val) (arg: Val): Option Val :=
  -- weak head normal form
  -- reduce (Val.app cmd arg)
  match cmd with
    | Val.clos env (Exp.lam name body) =>
      eval? (update env name arg) body
    | _ =>
      (Val.app cmd arg)

partial def eval? (env: List (String × Val)) (exp: Exp): Option Val := do
  -- reduce (Val.clos env exp)
  match exp with
    | Exp.typ n =>
      pure (Val.typ n)

    | Exp.var name =>
      lookup? env name

    | Exp.app cmd arg =>
      whnf? (← eval? env cmd) (← eval? env arg)

    | Exp.bnd name val _ body =>
      eval? (update env name (← eval? env val)) body

    | _ =>
      pure (Val.clos env exp) -- skip lam pi inh
end

-- DEFINITIONAL EQUALITY
partial def eqVal? (k: Nat) (u1: Val) (u2: Val): Option Bool := do
    match (u1, u2) with
      | (Val.typ n1, Val.typ n2) =>
        pure (n1 = n2)

      | (Val.gen k1, Val.gen k2) =>
        pure (k1 = k2)

      | (Val.app cmd1 arg1, Val.app cmd2 arg2) =>
        pure ((← eqVal? k cmd1 cmd2) ∧ (← eqVal? k arg1 arg2))

      | (Val.clos env1 (Exp.lam name1 body1), Val.clos env2 (Exp.lam name2 body2)) =>
        eqVal? (k + 1)
          (← eval? (update env1 name1 (Val.gen k)) body1)
          (← eval? (update env2 name2 (Val.gen k)) body2)

      | (Val.clos env1 (Exp.pi name1 typeA1 typeB1), Val.clos env2 (Exp.pi name2 typeA2 typeB2)) =>
        pure (
          (← eqVal? k (← eval? env1 typeA1) (← eval? env2 typeA2))
            ∧
          (
            ← eqVal? (k + 1)
            (← eval? (update env1 name1 (Val.gen k)) typeB1)
            (← eval? (update env2 name2 (Val.gen k)) typeB2)
          )
        )

      | _ => pure false

-- TYPE CHECKING
structure Ctx where
  maxN: Nat     -- max universe level
  debug: Bool   -- whether to dbg_trace

  k: Nat
  ρ: List (String × Val)   -- name -> value
  Γ: List (String × Val)    -- name -> type
  deriving Repr

def Ctx.bind (ctx: Ctx) (name: String) (val: Val) (type: Val) : Ctx :=
  {
    ctx with
    ρ := update ctx.ρ name val,
    Γ := update ctx.Γ name type,
  }

def Ctx.intro (ctx: Ctx) (name: String) (type: Val) : Ctx × Val :=
  let val := Val.gen ctx.k
  ({
    ctx with
    k := ctx.k + 1,
    ρ := update ctx.ρ name val,
    Γ := update ctx.Γ name type,
  }, val)

def Ctx.nodebug (ctx: Ctx) : Ctx :=
  {ctx with debug := false}

def Ctx.printIfNone (ctx: Ctx) (msg: String) (o?: Option α): Option α :=
  match (o?, ctx.debug) with
    | (none, true) => dbg_trace msg; none
    | _ => o?

def Ctx.printIfFalse (ctx: Ctx) (msg: String) (o?: Option Bool): Option Bool :=
  if (o? ≠ true) ∧ (ctx.debug) then
    dbg_trace msg; none
  else
    o?


def emptyCtx: Ctx := {
  maxN := 5,
  debug := true,

  k := 0,
  ρ := emptyEnv,
  Γ := emptyEnv
}

mutual
partial def checkTypLevel? (ctx: Ctx) (exp: Exp) (maxN: Nat): Option Nat :=
  -- if exp is of type TypeN for 0 ≤ N ≤ maxN
  -- return N
  ctx.printIfNone s!"[DBG_TRACE] checkTypLevel? {repr ctx}\n\texp = {repr exp}\n\tmaxLevel = {maxN}" do
  let rec loop (n: Nat): Option Nat := do
    if n > maxN then
      none
    else
      let b ← checkExp? ctx.nodebug exp (Val.typ n)
      if b then
        pure n
      else
        loop (n + 1)
  loop 0

partial def inferExpWeak? (ctx: Ctx) (exp: Exp): Option Val :=
  -- infer the type of exp weakly
  ctx.printIfNone s!"[DBG_TRACE] inferExpWeak? {repr ctx}\n\texp = {repr exp}" do
    match exp with
      | Exp.typ n => pure (Val.typ (n + 1))
      | Exp.var name => lookup? ctx.Γ name

      | Exp.app cmd arg => -- for Exp.app, cmd should be typ, var, or app
        match ← inferExpWeak? ctx cmd with
          | Val.clos env (Exp.pi name typeA typeB) =>
            if ¬ (← checkExp? ctx arg (← eval? env typeA)) then
              none
            else
              let argValue ← eval? ctx.ρ arg
              let subEnv := update env name argValue
              pure (← eval? subEnv typeB)
          | _ => none

      | _ => none -- ignore these

partial def checkExp? (ctx: Ctx) (exp: Exp) (val: Val): Option Bool :=
  -- check if type of exp is val
  -- ctx.printIfFalse s!"[DBG_TRACE] checkExp? {repr ctx}\n\texp = {repr exp}\n\tval = {repr val}" do
  ctx.printIfFalse s!"[DBG_TRACE] checkExp? \n\texp = {repr exp}\n\tval = {repr val}" do
    match exp with
      | Exp.pi name typeA typeB =>
        match val with
          | Val.typ n =>
            let i ← checkTypLevel? ctx typeA ctx.maxN
            let (subCtx, _) := ctx.intro name (← eval? ctx.ρ typeA)
            let j ← checkTypLevel? subCtx typeB ctx.maxN
            pure ((max i j) ≤ n)
          | _ => none

      | Exp.lam name1 body1 =>
        match val with
          | Val.clos env2 (Exp.pi name2 typeA2 typeB2) =>
            let (subCtx, v) := ctx.intro name1 (← eval? env2 typeA2)
            let subEnv2 := update env2 name2 v
            checkExp? subCtx body1 (← eval? subEnv2 typeB2)
          | _ => none

      | Exp.bnd name value type body =>
        let _ ← checkTypLevel? ctx type ctx.maxN
        if ¬ (← checkExp? ctx value (← eval? ctx.ρ type)) then
          none
        else
          let subCtx := ctx.bind name
            (← eval? ctx.ρ value)
            (← eval? ctx.ρ type)

          checkExp? subCtx body val

      | Exp.inh name type body =>
        let _ ← checkTypLevel? ctx type ctx.maxN
        let (subCtx, _) := ctx.intro name (← eval? ctx.ρ type)
        checkExp? subCtx body val

      -- desugar untyped lam (λx.y z)
      | Exp.app (Exp.lam name body) arg =>
        let argType ← inferExpWeak? ctx arg
        let argValue ← eval? ctx.ρ arg

        let subCtx := ctx.bind name argValue argType
        checkExp? subCtx body val

      | _ => eqVal? ctx.k (← inferExpWeak? ctx exp) val
end

end EL2.Typer

namespace EL2

open Typer

def typeCheck? (exp: Exp) (type: Exp): Option Bool := do
  -- typeCheck?
  -- some false - type check error
  -- none - parse error
  checkExp? emptyCtx exp (← eval? emptyEnv type)

def test1 :=
  typeCheck?
    (Exp.lam "B" (Exp.lam "y" (Exp.var "y")))
    (Exp.pi "A" (Exp.typ 0) (Exp.pi "x" (Exp.var "A") (Exp.var "A")))

def test2 :=
  typeCheck?
    (Exp.pi "A" (Exp.typ 0) (Exp.pi "x" (Exp.var "A") (Exp.var "A")))
    (Exp.typ 1)


def test3 :=
  typeCheck? (Exp.typ 0) (Exp.typ 1)


def test4 :=
  typeCheck?
    (Exp.pi "A" (Exp.typ 0) (Exp.pi "x" (Exp.var "A") (Exp.var "A")))
    (Exp.typ 1)

def test5 :=
  typeCheck?
    (Exp.app (Exp.lam "x" (Exp.var "x")) (Exp.typ 0))
    (Exp.typ 1)

def piMany (params: List (String × Exp)) (typeB: Exp): Exp :=
  match params with
    | [] => typeB
    | (name, typeA) :: rest =>
      Exp.pi name typeA (piMany rest typeB)

def appMany (cmd: Exp) (args: List Exp): Exp :=
  match args with
    | [] => cmd
    | arg :: rest =>
      appMany (Exp.app cmd arg) rest

def lamMany (params: List String) (body: Exp): Exp :=
  match params with
    | [] => body
    | name :: rest =>
      Exp.lam name (lamMany rest body)

def test6 :=
  let e: Exp := ( id
    $ .inh "Nat" (.typ 0)
    $ .inh "zero" (.var "Nat")
    $ .inh "succ" (.pi "n" (.var "Nat") (.var "Nat"))
    $ .inh "Nat_rec" (piMany [
        ("P", .pi "_" (.var "Nat") (.typ 0)), -- (P : Nat -> Type0) ->
        ("_", .app (.var "P") (.var "zero")), -- (P zero) ->
        (
          "_", piMany [ -- ((n : Nat) -> (P n) -> (P (succ n))) ->
            ("n", .var "Nat"), ("_", (.app (.var "P") (.var "n"))),
          ]
          (.app (.var "P") (.app (.var "succ") (.var "n")))
        ),
        ("n", .var "Nat"), -- (n : Nat)
    ] (.app (.var "P") (.var "n"))) ---> (P n)
    $ .inh "Vec" (piMany [("n", .var "Nat"), ("T", .typ 0)] (.typ 0))
    $ .inh "nil" (piMany [("T", .typ 0)] (appMany (.var "Vec") [.var "zero", .var "T"]))
    $ .inh "push" (
      piMany [
        ("n", .var "Nat"),
        ("T", .typ 0),
        ("v", (appMany (.var "Vec") [.var "n", .var "T"])),
        ("x", .var "T"),
      ]
      (appMany (.var "Vec") [.app (.var "succ") (.var "n"), .var "T"])
    )
    $ .bnd "one" (.app (.var "succ") (.var "zero")) (.var "Nat")
    $ .bnd "is_pos" (  -- let is_pos : Nat -> Nat := match n with | zero => zero | succ m => one
      .lam "n" (
        appMany (.var "Nat_rec") [
          .lam "_" (.var "Nat"),
          (.var "zero"),
          (lamMany ["m", "rec"] (.var "one")),
          (.var "n")
        ]
      )
    ) (.pi "_" (.var "Nat") (.var "Nat"))
    $ .bnd "singleton" (appMany (.var "push") [
      .var "zero",
      .var "Nat",
      (.app (.var "nil") (.var "Nat")),
      .var "zero",
    ]) (appMany (.var "Vec") [.var "one", .var "Nat"])
    $ .typ 0
  )
  let t := Exp.typ 1
  typeCheck? e t

#eval test1
#eval test2
#eval test3
#eval test4
#eval test6

end EL2
