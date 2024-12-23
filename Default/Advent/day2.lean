-- Input

def read_input : IO String := IO.FS.readFile "Default/Advent/day2.txt"

def parse_line (line: String) : List Nat :=
  (line.splitOn " ").map String.toNat!

def parse_input (input: String) : List (List Nat) :=
  (input.splitOn "\n").map parse_line
  |>.filter (fun line => !line.isEmpty)

-- Part 1

def is_down_trend (ns: List Nat) : Bool :=
  ns.foldr (fun (n: Nat) (acc: Nat × Bool) =>
    match acc with
    | (_, false) => (n, false)
    | (prev, true) => (n, prev < n)
  ) (0, true) |> Prod.snd

def is_up_trend (ns: List Nat) : Bool :=
  ns.foldl (fun (acc: Nat × Bool) (n: Nat) =>
    match acc with
    | (_, false) => (n, false)
    | (prev, true) => (n, prev < n)
  ) (0, true) |> Prod.snd

def is_trend (ns: List Nat) : Bool :=
  is_down_trend ns || is_up_trend ns

def nat_diff (pair: Nat × Nat) : Nat :=
  let (a, b) := pair
  if a > b then a - b else b - a

def max_diff (ns: List Nat) : Nat :=
  ns.zip ns.tail
    |>.map nat_diff
    |>.foldl Nat.max 0

def is_safe (ns: List Nat) : Bool :=
  is_trend ns && max_diff ns < 4

def part1 : IO Unit := do
  let input ← read_input
  let lines := parse_input input
  let count := lines.filter is_safe |>.length
  IO.println count

#eval part1

-- Part 2

def List.mapIdx {α β} (f : Nat → α → β) : List α → List β
  | [] => []
  | x :: xs => f 0 x :: List.mapIdx (fun i x => f (i + 1) x) xs

/-- Get all possible lists by removing one element from the input list -/
def one_removed_lists (ns: List Nat) : List (List Nat) :=
  ns.mapIdx (fun i _ => ns.take i ++ ns.drop (i + 1))

/-- List is safe if any of its sublists by one_removed_lists is safe -/
def is_safe2 (ns: List Nat) : Bool :=
  (one_removed_lists ns).any is_safe

def part2 : IO Unit := do
  let input ← read_input
  let lines := parse_input input
  let count := lines.filter is_safe2 |>.length
  IO.println count

#eval part2
