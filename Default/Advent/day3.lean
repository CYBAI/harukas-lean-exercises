-- valid pattern: mul(2,4)

-- Input

def read_input : IO String := IO.FS.readFile "Default/Advent/day2.txt"

-- Extensions

instance : LT String.Iterator where
  lt := fun it1 it2 => sizeOf it1 < sizeOf it2

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
  run : Text → Option (α × Text)
  /-- The cursor should move forward if the parser succeeds, which means something in cursor should be consumed. -/
  cursor_moves_forward : ∀ (t : Text) (a : α) (t' : Text), run t = some (a, t') → t'.cursor < t.cursor

def digitParser : Parser Char where
  run := fun text =>
    let ⟨content, cursor⟩ := text
    let c := content.get cursor.pos
    if ¬cursor.atEnd ∧ c.isDigit then
      some (c, text.next)
    else
      none
  cursor_moves_forward := fun t a t' h =>
    by
      simp at h
      have not_end: ¬t.cursor.atEnd := by
        simp
        exact h.left.left
      have : t.next = t' := by
        exact h.right.right
      rw [←this]
      exact Text.cursor_lt_next t not_end

#eval digitParser.run (Text.mk "123" "123".iter)

def many (parser : Parser α) : Parser (List α) where
  run := fun text =>
    match parser.run text with
    | some (x, rest) =>
      match (many parser).run rest with
      | some (xs, rest') => some (x :: xs, rest')
      | none => none
    | none =>
      some ([], text)
  cursor_moves_forward := sorry

#eval! (many digitParser).run (Text.mk "123c" "123c".iter)

-- def many2 (p : Parser α) : Parser (List α) :=
--   fun text =>
--     let rec loop (text : Text) (acc : List α) : List α × Text :=
--       match p text with
--       | some (a, text') => loop text' (a :: acc)
--       | none => (acc.reverse, text)
--     loop text []

inductive NatScanResult where
  | invalid
  | nat (n : Nat)
  deriving Repr

inductive NatScanMatch where
  /-- no match yet -/
  | init
  /-- digits -/
  | digits (chars : List Char)
  /-- final result -/
  | finished (result : NatScanResult)
  deriving Repr

structure NatScanner where
  cursor : String.Iterator
  matching : NatScanMatch
  deriving Repr

def scan_nat_step (text: String) (scanner : NatScanner) : NatScanner :=
  let ⟨cursor, matching⟩ := scanner
  match matching with
  | .init =>
    let c := text.get cursor.pos
    if c.isDigit && c ≠ '0' then
      { cursor := cursor.next, matching := .digits [c] }
    else
      { scanner with matching := .finished .invalid }
  | .digits chars =>
    let c := text.get cursor.pos
    if c.isDigit then
      { cursor := cursor.next, matching := .digits (chars ++ [c]) }
    else
      let n := chars.asString |>.toNat!
      { cursor := cursor, matching := .finished (.nat n) }
  | .finished _ =>
    scanner

-- Scan a natural number from the given text until a non-digit character is found or the end of the text is reached.
def scan_nat (text: String) (cursor : String.Iterator) : String.Iterator × NatScanResult :=
  let scanner := NatScanner.mk cursor NatScanMatch.init
  let scanner' := scan_nat_step text scanner
  match scanner'.matching with
  | NatScanMatch.finished result => (scanner'.cursor, result)
  | _ => (cursor, NatScanResult.invalid)

inductive ScanMatch where
  /-- no match yet -/
  | none
  /-- "mul(" -/
  | mul_found
  /-- "mul(" + number -/
  | mul1 (n : Nat)
  /-- "mul(" + number + "," -/
  | mul1_comma (n : Nat)
  /-- "mul(" + number + "," + number -/
  | mul2 (n1 n2 : Nat)
  /-- "mul(" + number + "," + number + ")" -/
  | mul_end (n1 n2 : Nat)

structure Scanner where
  cursor : String.Iterator
  matching : ScanMatch
  results : List (Nat × Nat)

def scan (text: String) (state : Scanner) : Scanner :=
  let ⟨cursor, matching, results⟩ := state

  match matching with
  | ScanMatch.none =>
    let next_cursor := cursor.nextn 4
    if text.extract cursor.pos next_cursor.pos == "mul(" then
      { state with cursor := next_cursor, matching := ScanMatch.mul_found }
    else
      { state with cursor := cursor.next }

  | ScanMatch.mul_found =>
    let (newCursor, number) := scan_nat text cursor
    if number > 0 then
      { state with cursor := newCursor, matching := ScanMatch.mul1 number }
    else
      { state with cursor := cursor.next, matching := ScanMatch.none }

  | ScanMatch.mul1 n =>
    let c := text.get cursor.pos
    if c == ',' then
      { state with cursor := cursor.next, matching := ScanMatch.mul1_comma n }
    else
      { state with cursor := cursor.next, matching := ScanMatch.none }

  | ScanMatch.mul1_comma n =>
    let c := text.get cursor.pos
    if c.isDigit then
      { state with cursor := cursor.next, matching := ScanMatch.mul2 n (c.toNat - '0'.toNat) }
    else
      { state with cursor := cursor.next, matching := ScanMatch.none }

  | ScanMatch.mul2 n1 n2 =>
    let c := text.get cursor.pos
    if c == ')' then
      { state with cursor := cursor.next, matching := ScanMatch.mul_end n1 n2, results := (n1, n2) :: results }
    else
      { state with cursor := cursor.next, matching := ScanMatch.none }

  | ScanMatch.mul_end n1 n2 =>
    { state with cursor := cursor.next, matching := ScanMatch.none, results := (n1, n2) :: results }
