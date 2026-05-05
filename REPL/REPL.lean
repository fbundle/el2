
namespace REPL

structure Step (α : Type) where
  state: α
  code: UInt32
  err: List String
  out: List String

def Step.map {α β : Type} (s: Step α) (f: α → β): Step β :=
  {
    state := f s.state,
    code := s.code,
    err := s.err,
    out := s.out,
  }

abbrev Transition (α : Type) := α → String → Step α

partial def run {α : Type} (trans: Transition α) (prev: Step α)
  (errPrefix: String := "-- ")
  (outPrefix: String := "")
  (prompt: String := "> ")
: IO (Step α) := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  let err := String.intercalate "" (prev.err.map (λ line => errPrefix ++ line ++ "\n"))
  let out := String.intercalate "" (prev.out.map (λ line => outPrefix ++ line ++ "\n"))

  stderr.putStr err
  stdout.putStr out
  stderr.flush
  stdout.flush

  stderr.putStr prompt
  stderr.flush
  let line ← stdin.getLine
  if line.isEmpty then
    -- EOF: no more input
    pure prev
  else
    let current := trans prev.state line
    run trans current errPrefix outPrefix prompt

end REPL
