import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

def g (a b x: Int) : Int :=
  x ^ 3 + a * x ^ 2 + b * x

def gr (a b x :Int) : Int :=
  x ^ 2 + a * x + b

def g' (a b x: Int) : Int :=
  x * (x ^ 2 + a * x + b)

lemma g_eq_g'_val (a b x: Int) : g a b x = g' a b x := by
  rw [g, g']
  ring

lemma g_eq_g' : g = g' := by
  funext
  apply g_eq_g'_val

lemma sign_neg_zero_pos (n : Int) : n.sign = 0 ∨ n.sign = 1 ∨ n.sign = -1 := by
  if h: 0 < n then
    have : n.sign = 1 := Int.sign_eq_one_of_pos h
    apply Or.inr
    apply Or.inl
    exact this
  else if h: n = 0 then
    have : n.sign = 0 := Int.sign_eq_zero_iff_zero.mpr h
    apply Or.inl
    exact this
  else
    have : n < 0 := by
      apply lt_of_not_ge
      intro h'
      have : 0 = n ∨ 0 < n := Int.le_iff_eq_or_lt.mp h'
      cases this
      case inl hn =>
        symm at hn
        contradiction
      case inr =>
        contradiction
    have : n.sign = -1 := Int.sign_eq_neg_one_of_neg this
    apply Or.inr
    apply Or.inr
    exact this

lemma abs_ne_one {n : Int} (hpos : n ≠ 1) (hneg : n ≠ -1) : n.natAbs ≠ 1 := by
  cases n with
  | ofNat n =>
    have : Int.ofNat n = (n : Int) := by rfl
    rw [this, Int.natAbs_ofNat n]
    intro n_eq_1
    rw [n_eq_1] at hpos
    contradiction
  | negSucc k =>
    rw [Int.natAbs_negSucc k]
    intro k_succ
    have k_eq_zero: k = 0 := by
      rw [Nat.succ_eq_add_one] at k_succ
      apply Nat.add_right_cancel
      exact k_succ
    rw [k_eq_zero] at hneg
    contradiction

lemma mul_of_succ_neg_succ (n : Nat) (m : Nat) : ∃ k: Nat, Int.ofNat (m + 1) * Int.negSucc n = Int.negSucc k := by
  use m * n + m + n
  calc Int.ofNat (m + 1) * Int.negSucc n
    _ = -((↑m + 1) * (↑n + 1)) := by rfl
    _ = -((↑m * ↑n + ↑m + ↑n) + 1) := by ring

lemma toNat_mul {a : Int} {b : Int} (ha : a ≥ 0) : (a * b).toNat = a.toNat * b.toNat := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      simp
      rfl
    | negSucc n =>
      match m with
      | 0 =>
        simp
      | Nat.succ m' =>
        let ⟨k, hk⟩ := mul_of_succ_neg_succ n m'
        rw [hk]
        simp
  | negSucc m =>
    match b with
    | 0 =>
      simp
    | Nat.succ b' =>
      let ⟨k, hk⟩ := mul_of_succ_neg_succ m b'
      have : Int.negSucc m * ↑b'.succ = Int.negSucc k := by
        rw [mul_comm]
        exact hk
      rw [this]
      simp
    | Int.negSucc n =>
      contradiction

lemma four_conditions_of_prime_g (a b n : Int) : Nat.Prime (g a b n).toNat →
    n = 1 ∨ n = -1 ∨ gr a b n = 1 ∨ gr a b n = -1 := by
  contrapose!
  intro h
  let ⟨hn, hn', hg, hg'⟩ := h
  have : g a b n = n * gr a b n := by
    rw [g_eq_g', g', gr]

  have h_n_abs_ne_one : n.natAbs ≠ 1 := abs_ne_one hn hn'
  have h_g_abs_ne_one : (gr a b n).natAbs ≠ 1 := abs_ne_one hg hg'

  have h_sign_abs: g a b n = n.sign * (gr a b n).sign * n.natAbs * (gr a b n).natAbs := by
    rw [this]
    nth_rewrite 1 [←Int.sign_mul_natAbs n]
    nth_rewrite 1 [←Int.sign_mul_natAbs (gr a b n)]
    ring

  match sign_neg_zero_pos n with
  | Or.inl hn_sign =>
    -- n.sign = 0
    have : g a b n = 0 := by
     rw [h_sign_abs, hn_sign]
     ring
    simp [this]
    exact Nat.not_prime_zero
  | Or.inr (Or.inl hn_sign) =>
    -- n.sign = 1
    match sign_neg_zero_pos (gr a b n) with
    | Or.inl hg_sign =>
      -- (gr a b n).sign = 0
      have : g a b n = 0 := by
        rw [h_sign_abs, hg_sign]
        ring
      simp [this]
      exact Nat.not_prime_zero
    | Or.inr (Or.inl hg_sign) =>
      -- (gr a b n).sign = 1
      have : g a b n = n.natAbs * (gr a b n).natAbs := by
        rw [h_sign_abs, hn_sign, hg_sign]
        simp
      have : (g a b n).toNat = n.natAbs * (gr a b n).natAbs := by
        rw [this, toNat_mul, Int.toNat_natCast, Int.toNat_natCast]
        exact Int.natCast_nonneg n.natAbs
      rw [this]
      exact Nat.not_prime_mul h_n_abs_ne_one h_g_abs_ne_one
    | Or.inr (Or.inr hg_sign) =>
      -- (gr a b n).sign = -1
      have : (g a b n).toNat = 0 := by
        rw [h_sign_abs, hn_sign, hg_sign]
        simp
        apply Int.mul_nonneg
        . exact abs_nonneg n
        . exact abs_nonneg (gr a b n)
      rw [this]
      exact Nat.not_prime_zero
  | Or.inr (Or.inr hn_sign) =>
    -- n.sign = -1
    match sign_neg_zero_pos (gr a b n) with
    | Or.inl hg_sign =>
      -- (gr a b n).sign = 0
      have : g a b n = 0 := by
        rw [h_sign_abs, hg_sign]
        ring
      simp [this]
      exact Nat.not_prime_zero
    | Or.inr (Or.inl hg_sign) =>
      -- (gr a b n).sign = 1
      have : (g a b n).toNat = 0 := by
        rw [h_sign_abs, hn_sign, hg_sign]
        simp
        apply Int.mul_nonneg
        . exact abs_nonneg n
        . exact abs_nonneg (gr a b n)
      rw [this]
      exact Nat.not_prime_zero
    | Or.inr (Or.inr hg_sign) =>
      -- (gr a b n).sign = -1
      have : g a b n = n.natAbs * (gr a b n).natAbs := by
        rw [h_sign_abs, hn_sign, hg_sign]
        simp
      have : (g a b n).toNat = n.natAbs * (gr a b n).natAbs := by
        rw [this, toNat_mul, Int.toNat_natCast, Int.toNat_natCast]
        exact Int.natCast_nonneg n.natAbs
      rw [this]
      exact Nat.not_prime_mul h_n_abs_ne_one h_g_abs_ne_one

-- 東大 2024 理系数学 第6問 (2)
-- a, b を整数の定数とし、g(x) = x^3 + a * x^2 + b x とする。
-- g(x) が素数となるような整数の個数は3個以下であることを示せ。
theorem todai_2024_6_2 (a b : Int) :
  ∀ S : Finset Int, (∀ x ∈ S, Prime (g a b x).toNat) → S.card ≤ 3 := by
  by_contra!
  let ⟨S, ⟨hS_prime, hS_card⟩⟩ := this
  sorry
