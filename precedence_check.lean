import EL2.ParserCombinator

open EL2.ParserCombinator

def checkPrecedence (p1 p2 p3 : ParseFunc (List Char) String) :=
  p1 ++ p2 || p3

#check @OrElse.orElse
#check (· <|> ·)
