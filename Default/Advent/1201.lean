def sort (l: List Nat) : List Nat :=
  l.mergeSort (· < ·)

def zip (l1: List Nat) (l2: List Nat) : List (Nat × Nat) :=
  l1.zip l2

def distance_pair (pair: Nat × Nat) : Nat :=
  if pair.1 > pair.2 then pair.1 - pair.2 else pair.2 - pair.1

def distance (zipped: List (Nat × Nat)) : Nat :=
  zipped.foldl (fun acc (x, y) => acc + distance_pair (x, y)) 0

def read_input : IO String := IO.FS.readFile "Default/Advent/1201.txt"

def parse_input (input: String) : ((List Nat) × (List Nat)) :=
  let lines := (input.splitOn "\n").map
    (fun line =>
      let parts := (line.splitOn "   ").map String.toNat!
      (parts.get! 0, parts.get! 1))
  let l1 := lines.map (fun (x, _) => x)
  let l2 := lines.map (fun (_, y) => y)
  (l1, l2)

def main : IO Unit := do
  let input ← read_input
  let (l1, l2) := parse_input input
  let answer := (sort l1, sort l2) |> Function.uncurry zip |> distance
  IO.println answer

#eval main
