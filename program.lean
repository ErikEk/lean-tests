
def twice (action : IO Unit) : IO Unit := do
  action
  action
def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "Howdddd?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"
  twice (IO.println "shy")

#eval "Hello...   ".dropRightWhile (fun c => not (c.isAlphanum))

#eval nTimes (IO.println "hello") 3
