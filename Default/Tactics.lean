example (p q: Prop) (hp: p) (hq: q): p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

example (p q: Prop) (hp: p) (hq: q): p ∧ q ∧ p := by
  apply And.intro hp
  apply And.intro hq hp

example (p q: Prop) (hp: p) (hq: q): p ∧ q ∧ p := by
  apply And.intro
  case left =>
    exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

example (p q: Prop) (hp: p) (hq: q): p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

-- Basic Tactics

example (p q r: Prop): p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr

example (α: Type): α → α := by
  intro a
  exact a

example (α: Type): ∀ x: α, x = x := by
  intro x
  rfl

example : ∀ a b c: Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁

example (α: Type) (p q: α → Prop): (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

example (α: Type) (p q: α → Prop): (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ =>
    exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ =>
    exact ⟨w, Or.inl h⟩

example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro h
  let ⟨w, hpq⟩ := h
  apply Or.elim hpq
  . intro hp
    exact ⟨w, Or.inr hp⟩
  . intro hq
    exact ⟨w, Or.inl hq⟩

example (x y z w: Nat) (h₁: x = y) (h₂: y = z) (h₃: z = w): x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption

example (x y z w: Nat) (h₁: x = y) (h₂: y = z) (h₃: z = w): x = w := by
  apply Eq.trans
  assumption
  apply Eq.trans
  assumption
  assumption

example : ∀ a b c: Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

example (y: Nat): (fun x: Nat => 0) y = 0 := by
  rfl

example (y: Nat): (fun x: Nat => 0) y = 0 := by
  exact Eq.refl _

example : ∀ a b c: Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

example (x: Nat): x = x := by
  revert x
  intro y
  rfl

example (x y: Nat) (h: x = y): y = x := by
  revert h
  intro h₁
  apply Eq.symm
  assumption

example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl

-- admit is short hand for `exact sorry`
example : 3 = 3 := by
  admit

example : 2 + 3 = 5 := by
  generalize h: 3 = x
  -- goal is ⊢ 2 + x = 5
  rw [← h]

-- More tactics

example (p q: Prop): p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp =>
    apply Or.inr
    exact hp
  | inr hq =>
    apply Or.inl
    exact hq

example (p: Prop): p ∨ p → p := by
  intro h
  cases h
  repeat assumption

example (p q: Prop): p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq =>
    constructor
    exact hq
    exact hp

example (p q: Prop): p ∧ q → q ∧ p := by
  intro h
  cases h
  apply And.intro
  assumption
  assumption

example (p q: Prop): p ∧ q → q ∧ p := by
  intro h
  cases h
  constructor
  repeat assumption

example (p q: Prop): p ∧ q → q ∧ p := by
  intro h
  cases h
  . constructor
    assumption
    assumption


example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px

example (p q: Nat → Prop): (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x


def swap_pair: α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

def swap_sum: Sum α β → Sum β α := by
  intro p
  cases p
  -- case inr =>
  --   apply Sum.inl
  --   assumption
  -- case inl =>
  --   apply Sum.inr
  --   assumption
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption

section

open Nat

example (P: Nat → Prop) (h₀: P 0) (h₁: ∀ n, P (succ n)) (m: Nat): P m := by
  cases m with
  | zero =>
    exact h₀
  | succ m' =>
    exact h₁ m'

end

-- contradiction tactic
example (p q: Prop): p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction

-- match expression can be used in tactic blocks
example (p q r: Prop): p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ =>
      apply Or.inl
      constructor <;> assumption
    | ⟨_, Or.inr _⟩ =>
      apply Or.inr
      constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ =>
      constructor
      assumption
      apply Or.inl
      assumption
    | Or.inr ⟨hp, hr⟩ =>
      constructor
      assumption
      apply Or.inr
      assumption

-- Structuring Tactic Proofs

example (p q r: Prop): p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show p ∧ q ∨ p ∧ r
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show p ∧ q ∨ p ∧ r
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩

-- Tactic combinators

-- normal proof
example (p q: Prop) (hp: p) (hq: q): p ∧ q := by
  apply And.intro
  case left =>
    exact hp
  case right =>
    exact hq

-- dot block
example (p q: Prop) (hp: p) (hq: q): p ∧ q := by
  apply And.intro
  . exact hp
  . exact hq

-- combinator <;> is like `map` function iterating each goal
example (p q: Prop) (hp: p) (hq: q): p ∧ q := by
  constructor <;> assumption

example (p q r: Prop) (hp: p) (hq: q) (hr: r): p ∧ q ∧ r := by
  constructor
  <;> (try constructor)
  <;> assumption

-- all_goals applies tactic `t` to all unsoleved goals
example (p q r: Prop) (hp: p) (hq: q) (hr: r): p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

-- any_goals passes if it successfully applies `t` to at least one goal
example (p q r: Prop) (hp: p) (hq: q) (hr: r): p ∧ q ∧ r := by
  constructor
  any_goals constructor
  all_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

-- one line
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))

-- Rewriting

example (f: Nat → Nat) (k: Nat)
  (h₁: f 0 = 0)
  (h₂: k = 0):
  f k = 0 := by
  rw [h₂] -- ⊢ f 0 = 0
  rw [h₁] -- ⊢ 0 = 0 which closes the goal

example (f: Nat → Nat) (k: Nat)
  (h₁: f 0 = 0)
  (h₂: k = 0):
  f k = 0 := by
  rw [h₂, h₁]

example (x y: Nat) (p: Nat → Prop) (q: Prop)
  (h: q → x = y)
  (h': p y)
  (hq: q):
  p x := by
  have : x = y := h hq
  rw [this]
  assumption -- or `exact h'`

example (f : Nat → Nat) (a b : Nat)
  (h₁ : a = b)
  (h₂ : f a = 0):
  f b = 0 := by
  rw [←h₁, h₂]

example (a b c : Nat) : a + b + c = a + c + b := by
  show (a + b) + c = (a + c) + b
  rw [Nat.add_assoc] -- ⊢ a + (b + c) = a + c + b
  rw [Nat.add_assoc] -- ⊢ a + (b + c) = a + (c + b)
  rw [Nat.add_comm c] -- ⊢ a + (b + c) = a + (b + c)

example (f : Nat → Nat) (a : Nat)
  (h : a + 0 = 0):
  f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]
