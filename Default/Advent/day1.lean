import Std.Data.HashMap

-- Part 1

def sort (l: List Nat) : List Nat :=
  l.mergeSort (· < ·)

def distance_pair (pair: Nat × Nat) : Nat :=
  if pair.1 > pair.2 then pair.1 - pair.2 else pair.2 - pair.1

def distance (zipped: List (Nat × Nat)) : Nat :=
  zipped.foldl (fun acc (x, y) => acc + distance_pair (x, y)) 0

-- Part 2

def frequency_map (list: List Nat): Std.HashMap Nat Nat :=
  list.foldl (fun acc x => acc.insert x (acc.getD x 0 + 1)) {}

-- Read input

def read_input : IO String := IO.FS.readFile "Default/Advent/day1.txt"

def parse_input (input: String) : ((List Nat) × (List Nat)) :=
  let lines := (input.splitOn "\n").map
    (fun line =>
      let parts := (line.splitOn "   ").map String.toNat!
      (parts.get! 0, parts.get! 1))
  List.unzip lines

def part1 : IO Unit := do
  let input ← read_input
  let (l1, l2) := parse_input input
  let answer := (sort l1, sort l2) |> Function.uncurry List.zip |> distance
  IO.println answer

def part2 : IO Unit := do
  let input ← read_input
  let (l1, l2) := parse_input input
  let l1map := frequency_map l1
  let l2map := frequency_map l2

  let similarity_score := l1map.fold (fun acc => fun k => fun v => acc + (k * v * (l2map.getD k 0))) 0
  IO.println similarity_score

#eval part1
#eval part2
