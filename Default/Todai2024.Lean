import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

def g (a b : Int) (x : Int) : Int :=
  x ^ 3 + a * x ^ 2 + b * x

-- 東大 2024 理系数学 第6問 (2)
-- a, b を整数の定数とし、g(x) = x^3 + a * x^2 + b x とする。
-- g(x) が素数となるような整数の個数は3個以下であることを示せ。
theorem todai_2024_6_2 (a b : Int) :
  ∀ S : Finset Int, (∀ x ∈ S, Prime (g a b x).toNat) → S.card ≤ 3 := by
  sorry
