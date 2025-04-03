import LeanYjs

def main : IO Unit :=
  let hello := "world"
  IO.println s!"Hello, {hello}!"
