import EL2.Typer

namespace EL2
inductive Val where
  -- type
  | typ : (level: Nat) → Val
  -- application
  | app: (cmd: Val) → (arg: Val) → Val
  -- Π type: Π (name: type) body - type of abs
  | pi:  (name: String) → (typeA: Val) → (typeB: Val) → Val
  -- λ abstraction
  | lam: (name: String) → (body: Val) → Val
  -- inh - const
  | const: (name: String) → Val
  --
  | clos: (env: List (String × Val)) → (exp: Exp) → Val
  deriving Repr


def Val.toString (re: Val): String :=
  match re with
    | Val.typ level => s!"Type{level}"
    | Val.app cmd arg =>
      s!"({Val.toString cmd} {Val.toString arg})"
    | Val.pi name typeA typeB =>
      match name with
        | "_" => s!"Π {Val.toString typeA} → {Val.toString typeB}"
        | _   => s!"Π ({name}: {Val.toString typeA}) → {Val.toString typeB}"
    | Val.lam name body =>
      s!"λ {name} => {Val.toString body}"
    | Val.const name => name
    | Val.clos env exp => "<closure>" -- s!"clos(env={repr env}, exp={repr exp}})"

instance: ToString Val where
  toString := Val.toString

end EL2

namespace EL2.Reducer
open EL2

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

def printOption (msg: α → String) (o?: Option α): Option α :=
  match o? with
    | none => none
    | some a =>
        dbg_trace msg a ; some a

def printNone (msg: String) (o?: Option α): Option α :=
  match o? with
    | none => dbg_trace msg; none
    | some a => some a

partial def reduce? (env: List (String × Val)) (e: Exp): Option Val :=
  printNone s!"[DBG_TRACE] \n\tenv={env}\n\tre={repr e}" do
  match e with
    | Exp.typ level => Val.typ level
    | Exp.var name => lookup? env name
    | Exp.app cmd arg =>
      let cmd ← reduce? env cmd
      let arg ← reduce? env arg
      match cmd with
        | Val.clos env1 (Exp.lam name body) =>
          reduce? (update env1 name arg) body
        | _ =>
          Val.app cmd arg
    | Exp.pi _ _ _ => Val.clos env e
    | Exp.lam _ _ => Val.clos env e
    | Exp.bnd name value _ body =>
      let value ←  printOption (λ a => s!"[REDUCE] {name} = {a}") $ reduce? env value
      reduce? (update env name value) body
    | Exp.inh name _ body =>
      let value := Val.const name
      reduce? (update env name value) body

    | Exp.hole _ => none

end EL2.Reducer

namespace EL2
def reduce? (e: Exp): Option Val :=
  Reducer.reduce? [] e

end EL2
