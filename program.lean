
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

def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blask of!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def from5 : List (IO Unit) := countdown 4
#eval from5.length

def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions

#eval runActions from5
