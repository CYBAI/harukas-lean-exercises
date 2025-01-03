import Mathlib.Tactic.ByContra

-- valid pattern: mul(2,4)

-- Input

def read_input : IO String := IO.FS.readFile "Default/Advent/day3.txt"

-- General

def String.Iterator.atEnd_of_sizeOf_zero (it : String.Iterator) (h : sizeOf it = 0) : it.atEnd := by
  apply Classical.not_not.mp
  intro h_not_end
  have : sizeOf it.next < sizeOf it := String.Iterator.sizeOf_next_lt_of_atEnd it h_not_end
  rw [h] at this
  exact Nat.not_succ_le_zero (sizeOf it.next) this

-- Extensions

instance : LT String.Iterator where
  lt := fun it1 it2 => sizeOf it1 < sizeOf it2

instance : LE String.Iterator where
  le := fun it1 it2 => sizeOf it1 ≤ sizeOf it2

theorem iter_lt_trans {it1 it2 it3 : String.Iterator}
    (h1 : it1 < it2) (h2 : it2 < it3) : it1 < it3 :=
  Nat.lt_trans h1 h2

theorem iter_lt_of_le_lt {it1 it2 it3 : String.Iterator}
    (h1 : it1 ≤ it2) (h2 : it2 < it3) : it1 < it3 :=
  Nat.lt_of_le_of_lt h1 h2

theorem iter_le_of_eq {it1 it2 : String.Iterator}
    (h : it1 = it2) : it1 ≤ it2 :=
  Nat.le_of_eq (congrArg sizeOf h)

theorem iter_le_of_lt {it1 it2 : String.Iterator}
    (h : it1 < it2) : it1 ≤ it2 :=
  Nat.le_of_lt h

-- Parser

structure Text where
  content : String
  cursor  : String.Iterator
  deriving Repr

def Text.next (text : Text) : Text :=
  { text with cursor := text.cursor.next }

def Text.from (content : String) : Text :=
  { content := content, cursor := content.iter }

theorem String.Iterator.iter_lt_next (it : String.Iterator) (h : ¬it.atEnd = true) : it.next < it :=
  String.Iterator.sizeOf_next_lt_of_atEnd it h

theorem Text.cursor_lt_next (t : Text) (h : ¬t.cursor.atEnd = true) : t.next.cursor < t.cursor :=
  String.Iterator.iter_lt_next t.cursor h

structure Parser (α : Type) where
  /-- Run the parser. -/
  parse : Text → Option (α × Text)
  /-- The cursor should move forward if the parser succeeds, which means something in cursor should be consumed. -/
  cursor_moves_forward : ∀ (t : Text) (a : α) (t' : Text), parse t = some (a, t') → t'.cursor < t.cursor
  /-- If the cursor is at the end, the parser should return none. -/
  none_of_cursor_atEnd : ∀ (t : Text), t.cursor.atEnd → parse t = none

example {α : Type} (parser : Parser α) : parser.parse { content := "", cursor := "".iter } = none := by
  exact parser.none_of_cursor_atEnd { content := "", cursor := "".iter } rfl

/-- Parse a single character. -/
def char (char : Char) : Parser Char where
  parse := fun text => do
    let ⟨content, cursor⟩ := text
    if cursor.atEnd then none
    let c := content.get cursor.pos
    if c != char then none
    some (c, text.next)
  cursor_moves_forward := fun t a t' h =>
    by
      simp at h
      -- Break down `h` into atomic props to make is available for `assumption`.
      let ⟨_, _, _, _⟩ := h
      have not_end: ¬t.cursor.atEnd := by
        simp
        assumption
      have : t.next = t' := by
        assumption
      rw [←this]
      exact Text.cursor_lt_next t not_end
  none_of_cursor_atEnd := fun t h =>
    by
      simp [h]

example : let text := Text.from "a"
  (char 'a').parse text
   = some ('a', text.next) := by rfl

/-- Parse a single digit character `0-9`. -/
def digit : Parser Char where
  parse := fun text => do
    let ⟨content, cursor⟩ := text
    if cursor.atEnd then none
    let c := content.get cursor.pos
    if !c.isDigit then none
    some (c, text.next)
  cursor_moves_forward := fun t a t' h =>
    by
      simp at h
      -- Break down `h` into atomic props to make is available for `assumption`.
      let ⟨_, _, _, _⟩ := h
      have not_end: ¬t.cursor.atEnd := by
        simp
        assumption
      have : t.next = t' := by
        assumption
      rw [←this]
      exact Text.cursor_lt_next t not_end
  none_of_cursor_atEnd := fun t h =>
    by
      simp [h]

example :
  let text := Text.from "1"
  digit.parse text = some ('1', text.next) := by rfl

def nonZeroDigit : Parser Char where
  parse := fun text => do
    let ⟨content, cursor⟩ := text
    if cursor.atEnd then none
    let c := content.get cursor.pos
    if !c.isDigit || c = '0' then none
    some (c, text.next)
  cursor_moves_forward := fun t a t' h =>
    by
      simp at h
      -- Break down `h` into atomic props to make is available for `assumption`.
      let ⟨_, _, _, _⟩ := h
      have not_end: ¬t.cursor.atEnd := by
        simp
        assumption
      have : t.next = t' := by
        assumption
      rw [←this]
      exact Text.cursor_lt_next t not_end
  none_of_cursor_atEnd := fun t h =>
    by
      simp [h]

def anyChar : Parser Unit where
  parse := fun text => do
    let ⟨_, cursor⟩ := text
    if cursor.atEnd then none
    some ((), text.next)
  cursor_moves_forward := fun t a t' h =>
    by
      simp at h
      let ⟨_, _⟩ := h
      have not_end: ¬t.cursor.atEnd := by
        simp
        assumption
      have : t.next = t' := by
        assumption
      rw [←this]
      exact Text.cursor_lt_next t not_end
  none_of_cursor_atEnd := fun t h =>
    by
      simp [h]

example :
  let text := Text.from "a"
  anyChar.parse text = some ((), text.next) := by rfl

-- Parser combinators

def manyRunAux (parser : Parser α) (acc : List α) (t : Text) : List α × Text :=
  -- Somehow `decreasing_by` doesn't recognize how `rest` is constructed when using `match`.
  -- So, we need to use `let` and `if` instead.
  let p := parser.parse t
  if hsome: p.isSome then
    let x := (p.get hsome).fst
    let rest := (p.get hsome).snd
    manyRunAux parser (acc ++ [x]) rest
  else
    (acc, t)
  termination_by t.cursor
  decreasing_by
    have : parser.parse t = some ((p.get hsome).fst, (p.get hsome).snd) := by
      have : (parser.parse t).isSome = true := hsome
      have : parser.parse t = some ((parser.parse t).get this) := Option.eq_some_of_isSome this
      exact this
    exact parser.cursor_moves_forward t (p.get hsome).fst (p.get hsome).snd this

def manyRun (parser : Parser α) (t : Text) : Option (List α × Text) := do
  let ⟨x, rest⟩ ← parser.parse t
  manyRunAux parser [x] rest

#eval! manyRun digit (Text.from "123,4")

theorem manyRunAux_cursor_moves_forward_weak (n : ℕ) : ∀ (parser : Parser α) (l : List α) (t : Text) (l' : List α) (t' : Text) (_ : sizeOf t.cursor = n),
  manyRunAux parser l t = (l', t') → t'.cursor ≤ t.cursor :=
  Nat.strongRecOn n fun n ih parser l t l' t' hn h => by
    match hp : parser.parse t with
    | some (x, rest) =>
      unfold manyRunAux at h
      simp [hp] at h
      have t'_lt_rest : t'.cursor ≤ rest.cursor := by
        apply ih (sizeOf rest.cursor)
        . show sizeOf rest.cursor < n
          rw [←hn]
          apply parser.cursor_moves_forward
          exact hp
        . show sizeOf rest.cursor = sizeOf rest.cursor
          rfl
        . show manyRunAux ?parser ?l rest = (?l', t')
          exact h
      have rest_lt_t : rest.cursor < t.cursor := by
        exact parser.cursor_moves_forward t x rest hp
      have t'_lt_t : t'.cursor < t.cursor := by
        exact iter_lt_of_le_lt t'_lt_rest rest_lt_t
      exact iter_le_of_lt t'_lt_t
    | none =>
      have : manyRunAux parser l t = (l, t) := by
        unfold manyRunAux
        simp [hp]
      rw [this] at h
      have : t = t' := by
        injection h
      rw [this]
      exact iter_le_of_eq rfl

theorem many_cursor_moves_foward_n (n : ℕ) : ∀ (t : Text) (l : List α) (t' : Text) (_ : sizeOf t.cursor = n),
  manyRun parser t = some (l, t') → t'.cursor < t.cursor := by
    intro t l t' _ h
    match hp : parser.parse t with
    | some (x, rest) =>
      unfold manyRun at h
      simp [hp] at h
      have t'_lt_rest : t'.cursor ≤ rest.cursor := by
        exact manyRunAux_cursor_moves_forward_weak (sizeOf rest.cursor) parser [x] rest l t' rfl h
      have rest_lt_t : rest.cursor < t.cursor := by
        exact parser.cursor_moves_forward t x rest hp
      exact iter_lt_of_le_lt t'_lt_rest rest_lt_t
    | none =>
      have : manyRun parser t = none := by
        unfold manyRun
        simp [hp]
      rw [this] at h
      contradiction

theorem many_cursor_moves_forward : ∀ (t : Text) (l : List α) (t' : Text),
  manyRun parser t = some (l, t') → t'.cursor < t.cursor := by
  exact fun t l t' a => many_cursor_moves_foward_n (sizeOf t.cursor) t l t' rfl a

theorem many_none_of_cursor_atEnd : ∀ (t : Text), t.cursor.atEnd → manyRun parser t = none := by
  intro t h
  unfold manyRun
  simp [parser.none_of_cursor_atEnd t h]

/-- Parser combinator that runs the given parser one or more times until it fails. -/
def many (parser : Parser α) : Parser (List α) where
  parse := manyRun parser
  cursor_moves_forward := many_cursor_moves_forward
  none_of_cursor_atEnd := many_none_of_cursor_atEnd

/-- Parser combinator that concatenates two parsers. -/
def concat (p1 : Parser α) (p2 : Parser β) : Parser (α × β) where
  parse := fun t =>
    match p1.parse t with
    | some (a, t') =>
      match p2.parse t' with
      | some (b, t'') => some ((a, b), t'')
      | none => none
    | none => none
  cursor_moves_forward := by
    intro t prod t'' h
    match hp1 : p1.parse t with
    | some (a2, t') =>
      match hp2 : p2.parse t' with
      | some (b2, t2'') =>
        let ⟨a, b⟩ := prod
        simp [hp1, hp2] at h
        rw [h.left.left] at hp1
        rw [h.right, h.left.right] at hp2
        have lt1: t''.cursor < t'.cursor := by
          exact p2.cursor_moves_forward t' b t'' hp2
        have lt2: t'.cursor < t.cursor := by
          exact p1.cursor_moves_forward t a t' hp1
        exact iter_lt_trans lt1 lt2
      | none =>
        simp [hp1, hp2] at h
    | none =>
      simp [hp1] at h
  none_of_cursor_atEnd := by
    intro t h
    simp
    rw [p1.none_of_cursor_atEnd t h]

infixl:65 " ++ " => concat

/-- Parser combinator that concatenates two parsers. The second parser can fail. -/
def concatOpt (p1 : Parser α) (p2 : Parser β) : Parser (α × Option β) where
  parse := fun t =>
    match p1.parse t with
    | some (a, t') =>
      match p2.parse t' with
      | some (b, t'') => some ((a, some b), t'')
      | none => some ((a, none), t')
    | none => none
  cursor_moves_forward := by
    intro t prod t'' h
    match hp1 : p1.parse t with
    | some (a2, t') =>
      match hp2 : p2.parse t' with
      | some (b2, t2'') =>
        let ⟨a, b⟩ := prod
        simp [hp1, hp2] at h
        rw [h.left.left] at hp1
        rw [h.right] at hp2
        have lt1: t''.cursor < t'.cursor := by
          exact p2.cursor_moves_forward t' b2 t'' hp2
        have lt2: t'.cursor < t.cursor := by
          exact p1.cursor_moves_forward t a t' hp1
        exact iter_lt_trans lt1 lt2
      | none =>
        simp [hp1, hp2] at h
        rw [←h.right]
        exact p1.cursor_moves_forward t a2 t' hp1
    | none =>
      simp [hp1] at h
  none_of_cursor_atEnd := by
    intro t h
    simp
    rw [p1.none_of_cursor_atEnd t h]

def fallback (p1 : Parser α) (p2 : Parser β) : Parser (Sum α β) where
  parse := fun t =>
    match p1.parse t with
    | some (a, t') => some (Sum.inl a, t')
    | none =>
      match p2.parse t with
      | some (b, t') => some (Sum.inr b, t')
      | none => none
  cursor_moves_forward := by
    intro t sum t' h
    match hp1 : p1.parse t with
    | some (a, _) =>
      simp [hp1] at h
      rw [h.right] at hp1
      exact p1.cursor_moves_forward t a t' hp1
    | none =>
      match hp2 : p2.parse t with
      | some (b, _) =>
        simp [hp1, hp2] at h
        rw [h.right] at hp2
        exact p2.cursor_moves_forward t b t' hp2
      | none =>
        simp [hp1, hp2] at h
  none_of_cursor_atEnd := by
    intro t h
    simp
    rw [p1.none_of_cursor_atEnd t h]
    simp
    rw [p2.none_of_cursor_atEnd t h]

#eval (fallback (char 'a') (char 'b')).parse (Text.from "b")

def map {α β} (f : α → β) (parser : Parser α) : Parser β where
  parse := fun t => do
    let ⟨a, t'⟩ ← parser.parse t
    some (f a, t')
  cursor_moves_forward := by
    intro t a t' h
    match hp : parser.parse t with
    | some (a2, t2) =>
      simp [hp] at h
      rw [h.right] at hp
      exact parser.cursor_moves_forward t a2 t' hp
    | none =>
      simp [hp] at h
  none_of_cursor_atEnd := by
    intro t h
    simp
    rw [parser.none_of_cursor_atEnd t h]
    simp

-- Parsers

/--
 Convert a string of digits to a natural number.
 e.g. "123" -> 123
-/
def toNat (chars : Char × Option (List Char)) : Nat :=
  let ⟨head, rest⟩ := chars
  let headNat := head.toNat - '0'.toNat
  match rest with
  | some digits => digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) headNat
  | none => headNat

/--
 Parse a natural number.
-/
def number : Parser Nat := map toNat (concatOpt nonZeroDigit (many digit))

def mulHead : Parser Unit := map (fun _ => ()) (char 'm' ++ char 'u' ++ char 'l' ++ char '(')

def mulRaw : Parser ((((Unit × Nat) × Char) × Nat) × Char) := mulHead ++ number ++ char ',' ++ number ++ char ')'

/--
 Parse a pair of natural numbers.
 e.g. "mul(2,4)" -> (2, 4)
-/
def mul : Parser (Nat × Nat) := map (fun ((((_, a), _), b), _) => (a, b)) mulRaw

-- #eval mul.parse (Text.from "mul(2,4)")

def mulRepeat := many (fallback mul anyChar)

def part1: IO Nat := do
  let input ← read_input
  let text := Text.from input
  if let some (muls, _) := mulRepeat.parse text then
    let m : List (Nat × Nat) := muls.filterMap fun
      | Sum.inl mul => some mul
      | Sum.inr _ => none
    let prodSum : Nat := m.foldl (fun acc (a, b) => acc + a * b) 0
    return prodSum
  else
    return 0

#eval part1
