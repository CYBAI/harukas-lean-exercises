
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

/-- 連続する奇数の積に1を加えると4の倍数になる -/
theorem odd_mul_four {a : Int} (h: is_odd a) : ∃b: Int, a * (a + 2) + 1 = 4 * b := by
  obtain ⟨k, rfl⟩ := h
  use k * k + 2 * k + 1
  ring

/-- 奇数の平方は奇数である -/
lemma odd_square_of_odd {a : Int} (h : is_odd a) : is_odd (a * a) := by
  let ⟨k, hk⟩ := h
  have : a * a = 2 * (2 * k * (k + 1)) + 1 := by
    calc
      a * a = (2 * k + 1) * (2 * k + 1) := by rw [hk]
      _ = 2 * (2 * k * (k + 1)) + 1 := by ring
  use 2 * k * (k + 1)

/-- 任意の整数は偶数か奇数のどちらかである -/
lemma even_or_odd (a : Int) : is_even a ∨ is_odd a := by
  let hc := fun d: Int =>
    calc d
      _ = d - 2 * (d / 2) + 2 * (d / 2) := by ring
      _ = d % 2 + 2 * (d / 2) := by rw [Int.emod_def]
  cases Int.emod_two_eq a with
  | inl h0 =>
    apply Or.inl
    show is_even a
    use a / 2
    calc a
      _ = a % 2 + 2 * (a / 2) := by rw [←hc]
      _ = 0 + 2 * (a / 2) := by rw [←h0]
      _ = 2 * (a / 2) := by ring
  | inr h1 =>
    apply Or.inr
    show is_odd a
    use a / 2
    calc a
      _ = a % 2 + 2 * (a / 2) := by rw [←hc]
      _ = 1 + 2 * (a / 2) := by rw [←h1]
      _ = 2 * (a / 2) + 1 := by ring

lemma one_ediv_two : (1 : Int) / 2 = 0 := by
  exact @Int.tdiv_eq_zero_of_lt 1 2 (by decide) (by decide)

lemma int_div_two_of_odd {a: Int} : (2 * a + 1) / 2 = a := calc (2 * a + 1) / 2
  _ = (1 + 2 * a) / 2 := by rw [Int.add_comm]
  _ = 1 / 2 + 2 * a / 2 := Int.add_ediv_of_dvd_right (by use a)
  _ = 0 + 2 * a / 2 := by rw [one_ediv_two]
  _ = a * 2 / 2 := by ring_nf
  _ = a := Int.mul_ediv_cancel a (by decide)

/-- 偶数でないことと奇数であることは同値 -/
lemma neg_odd_iff_even {a : Int} : ¬ is_odd a ↔ is_even a := by
  apply Iff.intro
  . have ha : is_odd a ∨ is_even a := by
      apply Or.comm.mp
      exact even_or_odd a
    exact or_iff_not_imp_left.mp ha
  . intro ha_even ha_odd
    let ⟨b, hb⟩ := ha_even
    have hzero: a % 2 = 0 := calc a % 2
      _ = a - 2 * (a / 2) := by rw [Int.emod_def]
      _ = 2 * b - 2 * (2 * b / 2) := by rw [hb]
      _ = 2 * b - 2 * (b * 2 / 2) := by ring_nf
      _ = 2 * b - 2 * b := by rw [Int.mul_ediv_cancel b (by decide)]
      _ = 0 := by ring
    let ⟨c, hc⟩ := ha_odd
    have hone: a % 2 = 1 := calc a % 2
      _ = a - 2 * (a / 2) := by rw [Int.emod_def]
      _ = (2 * c + 1) - 2 * ((2 * c + 1) / 2) := by rw [hc]
      _ = (2 * c + 1) - 2 * c := by rw [int_div_two_of_odd]
      _ = 1 := by ring
    rw [hone] at hzero
    contradiction

/-- 奇数でないことと偶数であることは同値 -/
lemma neg_even_iff_odd {a : Int} : ¬ is_even a ↔ is_odd a := by
  exact neg_odd_iff_even.not_right.symm

/-- 平方数が偶数ならもとの整数も偶数である -/
theorem even_of_even_square {a : Int} (h : is_even (a * a)) : is_even a := by
  contrapose! h
  apply neg_even_iff_odd.mp at h
  apply neg_even_iff_odd.mpr
  exact odd_square_of_odd h
