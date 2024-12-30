import Mathlib.Tactic.ByContra

-- valid pattern: mul(2,4)

-- Input

def read_input : IO String := IO.FS.readFile "Default/Advent/day2.txt"

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

theorem iter_lt_trans {it1 it2 it3 : String.Iterator}
    (h1 : it1 < it2) (h2 : it2 < it3) : it1 < it3 :=
  Nat.lt_trans h1 h2

-- Parser

structure Text where
  content : String
  cursor  : String.Iterator
  deriving Repr

def Text.next (text : Text) : Text :=
  { text with cursor := text.cursor.next }

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

/-- Parse a single character. -/
def charParser (char : Char) : Parser Char where
  parse := fun text =>
    let ⟨content, cursor⟩ := text
    let c := content.get cursor.pos
    if ¬cursor.atEnd ∧ c = char then
      some (c, text.next)
    else
      none
  cursor_moves_forward := fun t a t' h =>
    by
      simp at h
      -- Break down `h` into atomic props to make is available for `assumption`.
      let ⟨⟨_, _⟩, _, _⟩ := h
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

/-- Parse a single digit character `0-9`. -/
def digitParser : Parser Char where
  parse := fun text =>
    let ⟨content, cursor⟩ := text
    let c := content.get cursor.pos
    if ¬cursor.atEnd ∧ c.isDigit then
      some (c, text.next)
    else
      none
  cursor_moves_forward := fun t a t' h =>
    by
      simp at h
      -- Break down `h` into atomic props to make is available for `assumption`.
      let ⟨⟨_, _⟩, _, _⟩ := h
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

-- #eval digitParser.run (Text.mk "123" "123".iter)

def manyRun (parser : Parser α) (t : Text) : Option (List α × Text) :=
  -- Somehow `decreasing_by` doesn't recognize how `rest` is constructed when using `match`.
  -- So, we need to use `let` and `if` instead.
  let p := parser.parse t
  if hsome: p.isSome then
    let x := (p.get hsome).fst
    let rest := (p.get hsome).snd
    match manyRun parser rest with
      | some (xs, rest') => some (x :: xs, rest')
      | none => some ([x], rest)
  else
    none
  termination_by t.cursor
  decreasing_by
    have : parser.parse t = some ((p.get hsome).fst, (p.get hsome).snd) := by
      have : (parser.parse t).isSome = true := hsome
      have : parser.parse t = some ((parser.parse t).get this) := Option.eq_some_of_isSome this
      exact this
    exact parser.cursor_moves_forward t (p.get hsome).fst (p.get hsome).snd this

theorem many_some_none_empty :
  ∀ (t : Text) (l : List α) (t' : Text),
  manyRun parser t = some (l, t') → ¬ l.isEmpty := by
    intro t l t' h
    match hp : parser.parse t with
    | some (x, rest) =>
      unfold manyRun at h
      simp [hp] at h
      match hr : manyRun parser rest with
      | some (xs, rest') =>
        simp [hr] at h
        have l_gt_zero : 0 < l.length := by
          exact List.length_pos_iff_exists_cons.mpr ⟨x, xs, h.left.symm⟩
        intro h_empty
        have : l.length = 0 := by
          rw [List.isEmpty_iff_length_eq_zero] at h_empty
          exact h_empty
        rw [this] at l_gt_zero
        contradiction
      | none =>
        simp [hr] at h
        have : l = [x] := by exact h.left.symm
        rw [this]
        intro h
        contradiction
    | none =>
      have : manyRun parser t = none := by
        unfold manyRun
        simp [hp]
      rw [this] at h
      contradiction

theorem many_cursor_moves_foward_n (n : ℕ) : ∀ (t : Text) (l : List α) (t' : Text) (_ : sizeOf t.cursor = n),
  manyRun parser t = some (l, t') → t'.cursor < t.cursor :=
  Nat.strongRecOn n fun n ih t l t' hn h => by
    match hp : parser.parse t with
    | some (x, rest) =>
      unfold manyRun at h
      simp [hp] at h
      match hr : manyRun parser rest with
      | some (xs, rest') =>
        simp [hr] at h
        have : l = x :: xs := by exact h.left.symm
        rw [this] at h
        rw [h.right] at hr
        have t'_lt_rest : t'.cursor < rest.cursor := by
          apply ih (sizeOf rest.cursor)
          . show sizeOf rest.cursor < n
            rw [←hn]
            have : rest.cursor < t.cursor := by
              exact parser.cursor_moves_forward t x rest hp
            exact this
          . show sizeOf rest.cursor = sizeOf rest.cursor
            rfl
          . show manyRun parser rest = some (?l, t')
            exact hr
        have rest_lt_t : rest.cursor < t.cursor := by
          exact parser.cursor_moves_forward t x rest hp
        exact iter_lt_trans t'_lt_rest rest_lt_t
      | none =>
        simp [hr] at h
        rw [h.right] at hp
        exact parser.cursor_moves_forward t x t' hp
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

def many (parser : Parser α) : Parser (List α) where
  parse := manyRun parser
  cursor_moves_forward := many_cursor_moves_forward
  none_of_cursor_atEnd := many_none_of_cursor_atEnd

-- #eval! (many digitParser).run (Text.mk "123c" "123c".iter)
-- #eval! (many digitParser).run (Text.mk "c123" "c123".iter.toEnd)

-- def many2 (p : Parser α) : Parser (List α) :=
--   fun text =>
--     let rec loop (text : Text) (acc : List α) : List α × Text :=
--       match p text with
--       | some (a, text') => loop text' (a :: acc)
--       | none => (acc.reverse, text)
--     loop text []

-- inductive NatScanResult where
--   | invalid
--   | nat (n : Nat)
--   deriving Repr

-- inductive NatScanMatch where
--   /-- no match yet -/
--   | init
--   /-- digits -/
--   | digits (chars : List Char)
--   /-- final result -/
--   | finished (result : NatScanResult)
--   deriving Repr

-- structure NatScanner where
--   cursor : String.Iterator
--   matching : NatScanMatch
--   deriving Repr

-- def scan_nat_step (text: String) (scanner : NatScanner) : NatScanner :=
--   let ⟨cursor, matching⟩ := scanner
--   match matching with
--   | .init =>
--     let c := text.get cursor.pos
--     if c.isDigit && c ≠ '0' then
--       { cursor := cursor.next, matching := .digits [c] }
--     else
--       { scanner with matching := .finished .invalid }
--   | .digits chars =>
--     let c := text.get cursor.pos
--     if c.isDigit then
--       { cursor := cursor.next, matching := .digits (chars ++ [c]) }
--     else
--       let n := chars.asString |>.toNat!
--       { cursor := cursor, matching := .finished (.nat n) }
--   | .finished _ =>
--     scanner

-- -- Scan a natural number from the given text until a non-digit character is found or the end of the text is reached.
-- def scan_nat (text: String) (cursor : String.Iterator) : String.Iterator × NatScanResult :=
--   let scanner := NatScanner.mk cursor NatScanMatch.init
--   let scanner' := scan_nat_step text scanner
--   match scanner'.matching with
--   | NatScanMatch.finished result => (scanner'.cursor, result)
--   | _ => (cursor, NatScanResult.invalid)

-- inductive ScanMatch where
--   /-- no match yet -/
--   | none
--   /-- "mul(" -/
--   | mul_found
--   /-- "mul(" + number -/
--   | mul1 (n : Nat)
--   /-- "mul(" + number + "," -/
--   | mul1_comma (n : Nat)
--   /-- "mul(" + number + "," + number -/
--   | mul2 (n1 n2 : Nat)
--   /-- "mul(" + number + "," + number + ")" -/
--   | mul_end (n1 n2 : Nat)

-- structure Scanner where
--   cursor : String.Iterator
--   matching : ScanMatch
--   results : List (Nat × Nat)

-- def scan (text: String) (state : Scanner) : Scanner :=
--   let ⟨cursor, matching, results⟩ := state

--   match matching with
--   | ScanMatch.none =>
--     let next_cursor := cursor.nextn 4
--     if text.extract cursor.pos next_cursor.pos == "mul(" then
--       { state with cursor := next_cursor, matching := ScanMatch.mul_found }
--     else
--       { state with cursor := cursor.next }

--   | ScanMatch.mul_found =>
--     let (newCursor, number) := scan_nat text cursor
--     if number > 0 then
--       { state with cursor := newCursor, matching := ScanMatch.mul1 number }
--     else
--       { state with cursor := cursor.next, matching := ScanMatch.none }

--   | ScanMatch.mul1 n =>
--     let c := text.get cursor.pos
--     if c == ',' then
--       { state with cursor := cursor.next, matching := ScanMatch.mul1_comma n }
--     else
--       { state with cursor := cursor.next, matching := ScanMatch.none }

--   | ScanMatch.mul1_comma n =>
--     let c := text.get cursor.pos
--     if c.isDigit then
--       { state with cursor := cursor.next, matching := ScanMatch.mul2 n (c.toNat - '0'.toNat) }
--     else
--       { state with cursor := cursor.next, matching := ScanMatch.none }

--   | ScanMatch.mul2 n1 n2 =>
--     let c := text.get cursor.pos
--     if c == ')' then
--       { state with cursor := cursor.next, matching := ScanMatch.mul_end n1 n2, results := (n1, n2) :: results }
--     else
--       { state with cursor := cursor.next, matching := ScanMatch.none }

--   | ScanMatch.mul_end n1 n2 =>
--     { state with cursor := cursor.next, matching := ScanMatch.none, results := (n1, n2) :: results }
