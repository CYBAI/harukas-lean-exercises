import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.List

example : 3 ∣ 12 := by decide

example (n: Nat) (h1: 2 ∣ n) (h2: 3 ∣ n) : 6 ∣ n := by
  exact Nat.lcm_dvd h1 h2

example : (2: Int).natAbs = 2 := by
  rfl

example (a: Int) : a.sign * a.natAbs = a := Int.sign_mul_natAbs a

lemma mul2_mul3_to_mul6 {n: Int} (h1: 2 ∣ n) (h2: 3 ∣ n) : 6 ∣ n := by
  let m := n.natAbs
  have h1': 2 ∣ m := by
    let ⟨a, ha⟩ := h1
    use a.natAbs
    calc m
      _ = n.natAbs := by rfl
      _ = (2: Int).natAbs * a.natAbs := by rw [ha, Int.natAbs_mul]
      _ = 2 * a.natAbs := by rfl
  have h2': 3 ∣ m := by
    let ⟨b, hb⟩ := h2
    use b.natAbs
    calc m
      _ = n.natAbs := by rfl
      _ = (3: Int).natAbs * b.natAbs := by rw [hb, Int.natAbs_mul]
      _ = 3 * b.natAbs := by rfl
  let ⟨k, hk⟩: 6 ∣ n.natAbs := by
    exact Nat.lcm_dvd h1' h2'
  have hn : n = Int.sign n * n.natAbs := by
    symm
    exact Int.sign_mul_natAbs n
  rw [hk] at hn
  have : n = 6 * (n.sign * k) := calc
    n = n.sign * ↑(6 * k) := hn
    _ = n.sign * (6 * k) := rfl
    _ = 6 * (n.sign * k) := by ring
  use n.sign * k

lemma emod_three (x: Int) : 0 ≤ x % 3 ∧ x % 3 < 3 := by
  have h₁ : 0 ≤ x % 3 := Int.emod_nonneg x (by decide)
  have h₂ : x % 3 < 3 := Int.emod_lt_of_pos x (by decide)
  exact ⟨h₁, h₂⟩

lemma emod_add_ediv (a : Int) (b : Int) : a = b * (a / b) + a % b := by
  symm
  exact Int.ediv_add_emod a b

example {n: Int} : 6 ∣ 2 * n ^ 3 - 3 * n ^ 2 + n := by
  let m := 2 * n ^ 3 - 3 * n ^ 2 + n
  have hm : m = (n - 1) * n * (2 * n - 1) := by ring
  have h2 : 2 ∣ m := by
    let ⟨k, hk⟩ := Int.even_mul_succ_self (n - 1)
    simp at hk
    use k * (2 * n - 1)
    calc
      m = (n - 1) * n * (2 * n - 1) := hm
      _ = (k + k) * (2 * n - 1) := by rw [hk]
      _ = 2 * (k * (2 * n - 1)) := by ring
  have h3 : 3 ∣ m := by
    match hn_emod3: n % 3, (emod_three n).left, (emod_three n).right with
    | 0, _, _ =>
      let k := n / 3
      have : n = 3 * k := calc
        n = 3 * (n / 3) + n % 3 := emod_add_ediv n 3
        _ = 3 * k + 0 := by rw [hn_emod3]
        _ = 3 * k := by ring
      use (18 * k ^ 3 - 9 * k ^ 2 + k)
      calc
        m = 2 * n ^ 3 - 3 * n ^ 2 + n := by rfl
        _ = 2 * (3 * k) ^ 3 - 3 * (3 * k) ^ 2 + (3 * k) := by rw [this]
        _ = 3 * (18 * k ^ 3 - 9 * k ^ 2 + k) := by ring
    | 1, _, _ =>
      let k := n / 3
      have : n = 3 * k + 1 := calc
        n = 3 * (n / 3) + n % 3 := emod_add_ediv n 3
        _ = 3 * k + 1 := by rw [hn_emod3]
      use k * n * (2 * n - 1)
      calc
        m = (n - 1) * n * (2 * n - 1) := hm
        _ = (3 * k + 1 - 1) * n * (2 * n - 1) := by rw [this]
        _ = 3 * (k * n * (2 * n - 1)) := by ring
    | 2, _, _ =>
      let k := n / 3
      have : n = 3 * k + 2 := calc
        n = 3 * (n / 3) + n % 3 := emod_add_ediv n 3
        _ = 3 * k + 2 := by rw [hn_emod3]
      use (n - 1) * n * (2 * k + 1)
      calc
        m = (n - 1) * n * (2 * n - 1) := hm
        _ = (n - 1) * n * (2 * (3 * k + 2) - 1) := by rw [this]
        _ = 3 * ((n - 1) * n * (2 * k + 1)) := by ring
  exact mul2_mul3_to_mul6 h2 h3

def sig(a: Int) (b: Int) (n: Nat): Int :=
  (∑ i in Finset.range n, a ^ (n - i - 1) * b ^ i)

example (a: Int) (b: Int): sig a b 3 = (a ^ 2 + a * b + b ^ 2) := by
  calc sig a b 3
    _ = (∑ i in Finset.range 3, a ^ (2 - i) * b ^ i) := by rfl
    _ = a ^ 2 + a * b + b ^ 2 := by simp [Finset.sum_range_succ]

lemma mul_sum (s : Finset Nat) (a : Int) (f : Nat → Int) :
  a * ∑ i in s, f i = ∑ i in s, a * f i := by
  rw [← Finset.sum_to_list]
  rw [← List.sum_map_mul_left]
  rw [← Finset.sum_to_list s (fun i => a * f i)]

example (s : Finset Nat) (a : Int) :
  ∑ i in s, a * i = ∑ i in s, i * a := by
  apply Finset.sum_congr rfl
  intro i _
  exact Int.mul_comm a i

example (n: Int) : n ^ (1 + 1) = n ^ 2 := by rfl
example (n: Nat) (a: Int): a ^ (n + 1 - 1) = a ^ n := by rfl
example (n: Nat) : n ≤ 3 → 3 ≥ n := Iff.rfl.mp
example (n : Nat) : n - 1 ≤ 2 → n ≤ 3 := by
  intro h
  have h2 := Nat.add_le_add_right h 1
  simp at h2
  exact h2

lemma sub_add_cancel_one {n: Nat} (h: n > 0) : n - 1 + 1 = n := by
  have h2: 0 < n := by exact h
  apply Nat.pos_iff_ne_zero.mp at h2
  have h3: 1 ≤ n := Nat.succ_le_of_lt h
  exact Nat.sub_add_cancel h3

-- i ≤ 0 - 1 → 1 ≤ 0 - i
-- i ≤ 0 → 1 → 1 ≤ 0

lemma lemma1 {n : Nat} {i : Nat} (h0 : n > 0) : i ≤ n - 1 → 1 ≤ n - i := by
  intro h
  have : i + 1 ≤ n - 1 + 1 :=
    Nat.add_le_add_right h 1
  have : i + 1 ≤ n := by
    rw [sub_add_cancel_one h0] at this
    exact this
  have : i + 1 - i ≤ n - i :=
    Nat.sub_le_sub_right this i
  have : 1 ≤ n - i := by
    simp at this
    exact this
  exact this

lemma gt_zero_p_to_p_succ (P: Nat → Prop): (∀ n, n > 0 → P n) → (∀ n, P (n + 1)) := by
  intro h n
  apply h
  exact Nat.succ_pos n

lemma lemma2 {a: Int} {b: Int} {n: Nat}
  : a ^ n - b ^ n = (a - b) * (∑ i in Finset.range n, a ^ (n - i - 1) * b ^ i) := by
  symm
  let s := Finset.range n
  calc (a - b) * sig a b n
    _ = a * (sig a b n) - b * (sig a b n) := by
      ring
    _ = a * (∑ i in s, a ^ (n - i - 1) * b ^ i) - b * (∑ i in s, a ^ (n - i - 1) * b ^ i) := by
      rfl
    _ = ∑ i in s, (a * (a ^ (n - i - 1) * b ^ i) - b * (a ^ (n - i - 1) * b ^ i)) := by
      rw [Finset.sum_sub_distrib, mul_sum, mul_sum]
    _ = ∑ i in s, (a ^ (n - i) * b ^ i - a ^ (n - i - 1) * b ^ (i + 1)) := by
      match hn: n with
      | 0 =>
        simp
        have hl : ∑ x ∈ s, a * b ^ x - ∑ x ∈ s, b * b ^ x = 0 := by
          have : s = ∅ := by calc
            s = Finset.range n := by rfl
            _ = Finset.range 0 := by rw [hn]
            _ = ∅ := by rfl
          rw [this, Finset.sum_empty, Finset.sum_empty]
          rfl
        have hr : ∑ x ∈ s, b ^ x - ∑ x ∈ s, b ^ (x + 1) = 0 := by sorry
        rw [hl, hr]
      | k + 1 =>
        rw [Nat.succ_eq_add_one] at hn
        rw [← hn]
        have h: n > 0 := by
          rw [hn]
          exact Nat.succ_pos k
        apply Finset.sum_congr rfl
        intro i si
        have: a * (a ^ (n - i - 1) * b ^ i) = a ^ (n - i) * b ^ i := by
          rw [← mul_assoc, mul_comm a, ← pow_succ]
          have : i ≤ n - 1 := by
            exact Nat.le_pred_of_lt (Finset.mem_range.1 si)
          have : 1 ≤ n - i := by
            exact lemma1 h this -- (h: n > 0) was removed
          rw [Nat.sub_add_cancel this]
        rw [this]
        have: b * (a ^ (n - i - 1) * b ^ i) = a ^ (n - i - 1) * b ^ (i + 1) := by
          calc b * (a ^ (n - i - 1) * b ^ i)
            _ = a ^ (n - i - 1) * (b ^ i * b) := by ring
            _ = a ^ (n - i - 1) * b ^ (i + 1) := by rw [← pow_succ]
        rw [this]
    _ = a ^ n - b ^ n := by
      induction n with
      | zero =>
        have hl: ∑ i ∈ s, (a ^ (0 - i) * b ^ i - a ^ (0 - i - 1) * b ^ (i + 1)) = 0 := by
          have : s = ∅ := by rfl
          rw [this, Finset.sum_empty]
        have hr: a ^ 0 - b ^ 0 = 0 := by simp
        rw [hl, hr]
      | succ n hi =>
        calc ∑ i ∈ s, (a ^ (n + 1 - i) * b ^ i - a ^ (n + 1 - i - 1) * b ^ (i + 1))
        _ = ∑ i ∈ Finset.range (n + 1), (a ^ (n + 1 - i) * b ^ i - a ^ (n - i) * b ^ (i + 1)) := by
          congr
          funext i
          have : n + 1 - i - 1 = n - i := by
            calc n + 1 - i - 1
            _ = n - i + 1 - 1 := by sorry
            _ = n - i := by rw [Nat.add_sub_cancel]
          rw [this]
        _ = ∑ i ∈ Finset.range n, (a ^ (n + 1 - i) * b ^ i - a ^ (n - i) * b ^ (i + 1)) + a ^ (n + 1 - n) * b ^ n - a ^ (n - n) * b ^ (n + 1) := by sorry
        _ = ∑ i ∈ Finset.range n, (a ^ (n + 1 - i) * b ^ i - a ^ (n - i) * b ^ (i + 1)) + a ^ 1 * b ^ n - a ^ 0 * b ^ (n + 1) := by sorry
        _ = ∑ i ∈ Finset.range n, (a ^ (n + 1 - i) * b ^ i - a ^ (n - i) * b ^ (i + 1)) + a * b ^ n - b ^ (n + 1) := by sorry
        _ = ∑ i ∈ Finset.range n, a * (a ^ (n - i) * b ^ i - a ^ (n - i - 1) * b ^ (i + 1)) + a * b ^ n - b ^ (n + 1) := by sorry
        _ = a * ∑ i ∈ Finset.range n, (a ^ (n - i) * b ^ i - a ^ (n - i - 1) * b ^ (i + 1)) + a * b ^ n - b ^ (n + 1) := by sorry
        _ = a * (a ^ n - b ^ n) + a * b ^ n - b ^ (n + 1) := by rw [hi]
        _ = a ^ (n + 1) - b ^ (n + 1) := by ring

example {n: ℕ} : Nat.Prime (2 ^ n - 1) → Nat.Prime n := by
  contrapose!
  intro hnp
  match hn: n with
  | 0 =>
    simp
    intro h
    have : 0 ≠ 0 := Nat.Prime.ne_zero h
    contradiction
  | 1 =>
    simp
    intro h
    have : 1 ≠ 1 := Nat.Prime.ne_one h
    contradiction
  | k + 2 =>
    sorry

    -- obtain ⟨m, mdvdn, m_ne_1, m_ne_n⟩ := Nat.exists_dvd_of_not_prime n_ge_2 n_not_prime
    -- have m_ge_2 : 2 ≤ m := by
    --   apply Nat.le_of_lt
    --   have m_gt_1 : 1 < m := Nat.lt_of_le_of_ne (Nat.le_of_dvd n_ge_2 mdvdn) m_ne_1.symm
    --   exact m_gt_1
    -- have m_lt_n : m < n := Nat.lt_of_le_of_ne (Nat.le_of_dvd n_ge_2 mdvdn) m_ne_n.symm
    -- let k := n / m
    -- have k_ge_2 : 2 ≤ k := by
    --   have n_eq_mk : n = m * k := Nat.mul_div_cancel' mdvdn
    --   rw [n_eq_mk] at n_ge_2
    --   have : 2 ≤ m * k := n_ge_2
    --   have m_ge_1 : 1 ≤ m := Nat.le_of_lt m_ge_2
    --   exact Nat.le_of_mul_le_mul_left this m_ge_1
    -- Now, factor 2^n - 1
    -- have h_factor : 2 ^ n - 1 = (2 ^ m - 1) * (∑ i in Finset.range k, 2 ^ (m * (k - i - 1))) := by
    --   have geom_sum : ∑ i in Finset.range k, 2 ^ (m * i) = (2 ^ (m * k) - 1) / (2 ^ m - 1) := by
    --     rw [←Nat.geom_sum_mul]
    --     rw [Nat.sub_add_cancel (Nat.one_le_pow' _ _ m_ge_2)]
    --   have : 2 ^ n - 1 = (2 ^ m - 1) * ∑ i in Finset.range k, 2 ^ (m * (k - i - 1)) := by
    --     rw [←Nat.pow_mul, Nat.mul_comm m k, ←Nat.geom_sum_mul, ←geom_sum]
    --     ring
    --   exact this
    -- -- Show that both factors are greater than 1
    -- have h2m1_gt1 : 1 < 2 ^ m - 1 := by
    --   have h2m_ge4 : 4 ≤ 2 ^ m := Nat.pow_le_pow_of_le_right (by decide) m_ge_2
    --   exact Nat.lt_sub_left_of_add_lt (by norm_num) h2m_ge4
    -- have sum_gt1 : 1 < ∑ i in Finset.range k, 2 ^ (m * (k - i - 1)) := by
    --   have : 2 ^ (m * 0) ≤ ∑ i in Finset.range k, 2 ^ (m * (k - i - 1)) := Finset.single_le_sum (λ _ _ => Nat.zero_le _) (Finset.mem_range.mpr k_ge_2)
    --   have h_pow : 1 < 2 ^ (m * 0) := by
    --     rw [Nat.mul_zero, Nat.pow_zero]; norm_num
    --   exact Nat.lt_of_lt_of_le h_pow this
    -- -- Conclude that 2^n - 1 is not prime
    -- have : ¬Nat.Prime (2 ^ n - 1) := Nat.not_prime_mul' h2m1_gt1 sum_gt1
    -- exact this
