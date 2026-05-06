namespace EL2.ParserCombinator

def ParseFunc χ α  := χ → Option (χ × α)

def fail : ParseFunc χ α := λ _ => none

def pure (a: α): ParseFunc χ α := λ xs =>
  some (xs, a)

def ParseFunc.bind (p: ParseFunc χ α) (f: α → ParseFunc χ β): ParseFunc χ β := λ xs => do
  let (xs, a) ← p xs
  f a xs

instance: Monad (ParseFunc χ) where
  pure := pure
  bind := ParseFunc.bind

def ParseFunc.filter (p: ParseFunc χ α) (f: α → Bool): ParseFunc χ α :=
  p.bind (λ a => if f a then pure a else fail)

def ParseFunc.map (p: ParseFunc χ α) (f: α → β): ParseFunc χ β :=
  p.bind (λ a => pure (f a))

def ParseFunc.concat (p1: ParseFunc χ α) (p2: ParseFunc χ β): ParseFunc χ (α × β) := λ xs => do
  let (xs, a) ← p1 xs
  let (xs, b) ← p2 xs
  some (xs, (a, b))

infixr: 60 " ++ " => ParseFunc.concat

def ParseFunc.either (p1: ParseFunc χ α) (p2: ParseFunc χ α): ParseFunc χ α := λ xs =>
  match p1 xs with
    | some (xs, a) => some (xs, a)
    | none => p2 xs

infixr: 50 " || " => ParseFunc.either -- lower precedence than concat

partial def ParseFunc.repeatAny (p: ParseFunc χ α): ParseFunc χ (List α) := λ xs =>
  let rec loop (as: Array α) (xs: χ): Option (χ × List α) :=
    match p xs with
      | none => some (xs, as.toList)
      | some (rest, a) => loop (as.push a) rest
  loop #[] xs

def ParseFunc.repeatSome (p: ParseFunc χ α): ParseFunc χ (List α) := λ xs => do
  let (xs, as) ← p.repeatAny xs
  if as.length = 0 then
    none
  else
    some (xs, as)

def transpose (ps: List (ParseFunc χ α)): ParseFunc χ (List α) := λ xs =>
  let rec loop (ys: Array α) (ps: List (ParseFunc χ α)) (xs: χ): Option (χ × List α) :=
    match ps with
      | [] => some (xs, ys.toList)
      | p :: ps =>
        match p xs with
          | none => none
          | some (xs, y) =>
            loop (ys.push y) ps xs
  loop #[] ps xs


def pred (p: χ → Bool): ParseFunc (List χ) χ := λ xs =>
  match xs with
    | [] => none
    | x :: xs =>
      if p x then
        some (xs, x)
      else
        none

def exact [BEq χ] (y: χ): ParseFunc (List χ) χ := pred (· == y)

def exactList [BEq χ] (ys: List χ): ParseFunc (List χ) (List χ) :=
  transpose (ys.map exact)

namespace String

def toStringParseFunc (p: ParseFunc (List Char) (List Char)): ParseFunc (List Char) String :=
  p.map (String.mk ·)

def whitespaceAny : ParseFunc (List Char) String :=
  -- parse any whitespace or empty string
  toStringParseFunc (pred (·.isWhitespace)).repeatAny

def whiteSpaceWithoutNewLineAny : ParseFunc (List Char) String :=
  -- parse any whitespace without new line or empty string
  toStringParseFunc (pred (λ c => c.isWhitespace ∧ (¬ c = '\n'))).repeatAny


def whitespaceSome : ParseFunc (List Char) String :=
  -- parse some whitespace
  toStringParseFunc (pred (·.isWhitespace)).repeatSome

def exact (ys: String): ParseFunc (List Char) String :=
  toStringParseFunc (exactList ys.toList)

end String

end EL2.ParserCombinator
