
import Mathlib.Tactic.Ring

-- 中学数学の整数の証明問題を形式証明してみる

/-- `a` is even -/
def is_even (a: Int): Prop :=
  ∃b: Int, a = 2 * b

/-- `a` is odd -/
def is_odd (a: Int): Prop :=
  ∃b: Int, a = 2 * b + 1

/-- ２つの整数が奇数のとき、その和は偶数になる -/
theorem odd_plus_even
  {a b: Int}
  (h₁: is_odd a)
  (h₂: is_odd b):
  is_even (a + b) :=
    let ⟨k, ak⟩ := h₁
    let ⟨l, bl⟩ := h₂
    have h₃: a + b = 2 * (k + l + 1) :=
      calc a + b
        _ = 2 * k + 1 + (2 * l + 1) := by rw [ak, bl]
        _ = 2 * (k + l + 1) := by ring
    show is_even (a + b) from Exists.intro (k + l + 1) h₃

/-- odd_plus_even proven with tactics -/
theorem t_odd_plus_even {a b : Int} (h₁ : is_odd a) (h₂ : is_odd b) : is_even (a + b) := by
  obtain ⟨k, rfl⟩ := h₁
  obtain ⟨l, rfl⟩ := h₂
  use k + l + 1
  ring
