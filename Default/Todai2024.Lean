import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

def g (a b x: Int) : Int :=
  x ^ 3 + a * x ^ 2 + b * x

def g' (a b x: Int) : Int :=
  x * (x ^ 2 + a * x + b)

lemma g_eq_g'_val (a b x: Int) : g a b x = g' a b x := by
  rw [g, g']
  ring

lemma g_eq_g' : g = g' := by
  funext
  apply g_eq_g'_val

-- 東大 2024 理系数学 第6問 (2)
-- a, b を整数の定数とし、g(x) = x^3 + a * x^2 + b x とする。
-- g(x) が素数となるような整数の個数は3個以下であることを示せ。
theorem todai_2024_6_2 (a b : Int) :
  ∀ S : Finset Int, (∀ x ∈ S, Prime (g a b x).toNat) → S.card ≤ 3 := by
  sorry
