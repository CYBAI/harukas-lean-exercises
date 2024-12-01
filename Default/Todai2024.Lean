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

lemma four_conditions_of_prime_g (a b n : Int) : Nat.Prime (g a b n).toNat →
    n = 1 ∨ n = -1 ∨ gr a b n = 1 ∨ gr a b n = -1 := by
  contrapose!
  intro h
  let ⟨hn, hn', hl, hl'⟩ := h
  have : g a b n = n * gr a b n := by
    rw [g_eq_g', g', gr]

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
    | Or.inl hg_sign => sorry
    | Or.inr (Or.inl hg_sign) => sorry
    | Or.inr (Or.inr hg_sign) => sorry
  | Or.inr (Or.inr hn_sign) =>
    -- n.sign = -1
    match sign_neg_zero_pos (gr a b n) with
    | Or.inl hg_sign => sorry
    | Or.inr (Or.inl hg_sign) => sorry
    | Or.inr (Or.inr hg_sign) => sorry


-- 東大 2024 理系数学 第6問 (2)
-- a, b を整数の定数とし、g(x) = x^3 + a * x^2 + b x とする。
-- g(x) が素数となるような整数の個数は3個以下であることを示せ。
theorem todai_2024_6_2 (a b : Int) :
  ∀ S : Finset Int, (∀ x ∈ S, Prime (g a b x).toNat) → S.card ≤ 3 := by
  by_contra!
  let ⟨S, ⟨hS_prime, hS_card⟩⟩ := this
  sorry
