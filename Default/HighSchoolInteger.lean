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

lemma add_one_of_le_lt {n : Nat} {m : Nat} : n < m + 1 → n ≤ m := by
  intro h
  apply Nat.le_iff_lt_or_eq.mpr
  cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with
  | inl h' => exact Or.inl h'
  | inr h' => exact Or.inr h'

example (n : Nat) : n > 0 → n ≥ 1 := by
  intro h
  exact Nat.succ_le_of_lt h

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
        have hs : s = ∅ := by calc
          s = Finset.range n := by rfl
          _ = Finset.range 0 := by rw [hn]
          _ = ∅ := by rfl
        rw [hs, Finset.sum_empty, Finset.sum_empty, Finset.sum_empty, Finset.sum_empty]
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
        -- n + 1 - i - 1 = n - i
        _ = ∑ i ∈ Finset.range (n + 1), (a ^ (n + 1 - i) * b ^ i - a ^ (n - i) * b ^ (i + 1)) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxn : x ≤ n := by
            let hx' : x < n + 1 := Finset.mem_range.mp hx
            exact add_one_of_le_lt hx'
          have : n + 1 - x - 1 = n - x := by
            calc n + 1 - x - 1
            _ = n - x + 1 - 1 := by
              rw [Nat.sub_add_comm]
              exact hxn
            _ = n - x := by rw [Nat.add_sub_cancel]
          rw [this]
        -- Finset.range (n + 1) to Finset.range n
        _ = ∑ i ∈ Finset.range n, (a ^ (n + 1 - i) * b ^ i - a ^ (n - i) * b ^ (i + 1))
            + a ^ (n + 1 - n) * b ^ n - a ^ (n - n) * b ^ (n + 1) := by
          rw [Finset.sum_range_succ]
          ring
        _ = ∑ i ∈ Finset.range n, (a ^ (n + 1 - i) * b ^ i - a ^ (n - i) * b ^ (i + 1))
            + a ^ 1 * b ^ n - a ^ 0 * b ^ (n + 1) := by simp
        _ = ∑ i ∈ Finset.range n, (a ^ (n + 1 - i) * b ^ i - a ^ (n - i) * b ^ (i + 1))
            + a * b ^ n - b ^ (n + 1) := by simp
        _ = ∑ i ∈ Finset.range n, a * (a ^ (n - i) * b ^ i - a ^ (n - i - 1) * b ^ (i + 1))
            + a * b ^ n - b ^ (n + 1) := by
          rw [Int.add_sub_assoc, Int.add_sub_assoc]
          apply (Int.add_right_inj (a * b ^ n - b ^ (n + 1))).mpr
          apply Finset.sum_congr rfl
          intro x hx
          let hx' : x < n := Finset.mem_range.mp hx
          have h1 : a ^ (n + 1 - x) = a * (a ^ (n - x)) := by
            rw [Nat.sub_add_comm]
            . rw [← Nat.succ_eq_add_one, pow_succ, mul_comm]
            . apply Nat.le_iff_lt_or_eq.mpr
              left
              exact hx'
          have h2 : a ^ (n - x) = a * a ^ (n - x - 1) := by
            have hx'' : 1 ≤ n - x := by
              have : n - x > 0 := by
                exact Nat.sub_pos_of_lt hx'
              have : n - x ≥ 1 := by
                exact Nat.succ_le_of_lt this
              exact this
            calc a ^ (n - x)
              _ = a ^ (n - x + 0) := by rfl
              _ = a ^ (n - x + (1 - 1)) := by rfl
              _ = a ^ (n - x + 1 - 1) := by rfl
              _ = a ^ (n - x - 1 + 1) := by
                rw [Nat.sub_add_comm]
                exact hx''
              _ = a ^ (n - x - 1) * a := by rw [pow_succ]
              _ = a * a ^ (n - x - 1) := by rw [mul_comm]
          rw [h1, h2]
          ring
        _ = a * ∑ i ∈ Finset.range n, (a ^ (n - i) * b ^ i - a ^ (n - i - 1) * b ^ (i + 1)) + a * b ^ n - b ^ (n + 1) := by rw [mul_sum]
        _ = a * (a ^ n - b ^ n) + a * b ^ n - b ^ (n + 1) := by rw [hi]
        _ = a ^ (n + 1) - b ^ (n + 1) := by ring

lemma toNat_eq_toNat {a : Int} {b : Int}: a = b → a.toNat = b.toNat := by
  intro h
  rw [h]

lemma mul_of_succ_neg_succ (n : Nat) (m : Nat) : ∃ k: Nat, Int.ofNat (m + 1) * Int.negSucc n = Int.negSucc k := by
  use m * n + m + n
  calc Int.ofNat (m + 1) * Int.negSucc n
    _ = -((↑m + 1) * (↑n + 1)) := by rfl
    _ = -((↑m * ↑n + ↑m + ↑n) + 1) := by ring

lemma toNat_mul_dist {a : Int} {b : Int} (ha : a ≥ 0) : (a * b).toNat = a.toNat * b.toNat := by
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

lemma Int_ofNat_pow {a : Nat} {b : Nat} : Int.ofNat a ^ b = Int.ofNat (a ^ b) := by calc
    Int.ofNat a ^ b = ↑(a: Nat) ^ b := by rfl
    _ = Int.ofNat (a ^ b) := Eq.symm (Lean.Omega.Int.ofNat_pow a b)

lemma int_pow_pos {n : Nat} {a : Int}: 0 < a → 0 < a ^ n := by
  intro ha
  have ha' : 0 ≤ a := le_of_lt ha
  have ha_nat : 0 < a.toNat := by
    have h1: 0 ≤ a.toNat := Int.toNat_le_toNat ha'
    have h2: 0 ≠ a.toNat := by
      intro h
      have : a.toNat = 0 ↔ a ≤ 0 := Int.toNat_eq_zero
      have : a ≤ 0 := this.mp h.symm
      have : a = 0 := (LE.le.le_iff_eq ha').mp this
      rw [this] at ha
      contradiction
    exact lt_of_le_of_ne h1 h2
  have : 0 < a.toNat ^ n := by
    exact pow_pos ha_nat n
  have : Int.ofNat 0 < Int.ofNat (a.toNat ^ n) := by
    exact Int.ofNat_le.mpr this
  have : Int.ofNat 0 < (Int.ofNat a.toNat) ^ n := by
    rw [Int_ofNat_pow]
    exact this
  simp at this
  have max_a: max a 0 = a := by
    exact max_eq_left ha'
  rw [max_a] at this
  exact this

lemma lemma3 {d₁ d₂: Nat} (hd₁ : d₁ > 1) (hd₂ : d₂ > 1)
  : let e₂': Int := ∑ i ∈ Finset.range d₂, (2 ^ d₁) ^ (d₂ - i - 1) * 1 ^ i;
    1 < e₂' := by
  simp
  induction d₂ with
  | zero =>
    contradiction
  | succ k ih =>
    match hk: k with
    | 0 =>
      contradiction
    | 1 =>
      -- When k = 1 (d₂ = 2), compute e₂' directly
      let e₂': Int := ∑ x ∈ Finset.range (1 + 1), (2 ^ d₁) ^ (1 + 1 - x - 1)
      have he₂': e₂' = ∑ x ∈ Finset.range (1 + 1), (2 ^ d₁) ^ (1 + 1 - x - 1) := by rfl
      have : e₂' = (2 ^ d₁) + 1 := by
        rw [he₂', Finset.sum_range_succ, Finset.sum_range_succ]
        simp
      rw [he₂'] at this
      rw [this]
      simp
      have :(0: Int) < 2 ^ d₁ := by
        exact int_pow_pos (by decide)
      exact this
    | l + 2 =>
      simp at ih
      rw [Finset.sum_range_succ]
      simp
      have : ∀x ∈ Finset.range (l + 2),
        ((2: Int) ^ d₁) ^ (l + 2 + 1 - x - 1) = (2 ^ d₁) ^ (l + 2 - x - 1) * 2 ^ d₁ := by
        sorry
      have : ∑ x ∈ Finset.range (l + 2), ((2: Int) ^ d₁) ^ (l + 2 + 1 - x - 1) = ∑ x ∈ Finset.range (l + 2), (2 ^ d₁) ^ (l + 2 - x - 1) * 2 ^ d₁ := by
        apply Finset.sum_congr rfl
        exact this
      rw [this]
      have : ∑ x ∈ Finset.range (l + 2), ((2: Int) ^ d₁) ^ (l + 2 - x - 1) * 2 ^ d₁ = 2 ^ d₁ * ∑ x ∈ Finset.range (l + 2), (2 ^ d₁) ^ (l + 2 - x - 1) := by
        sorry
      rw [this]
      calc (0: Int)
        _ < 2 ^ d₁ := by sorry
        _ = 2 ^ d₁ * 1 := by simp
        _ < 2 ^ d₁ * ∑ x ∈ Finset.range (l + 2), (2 ^ d₁) ^ (l + 2 - x - 1) := by
          apply Int.mul_lt_mul_of_pos_left
          . exact ih
          . exact int_pow_pos (by decide)

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
    let hn : n = k + 2 := by exact hn
    let hnp : ¬Nat.Prime n := by rw [hn]; exact hnp
    let m := 2 ^ n - 1

    have n_mul_of_nat : ∃d₁ : Nat, ∃d₂ : Nat, d₁ > 1 ∧ d₂ > 1 ∧ n = d₁ * d₂ := by
      have n2 : 2 ≤ n := by
        rw [hn]
        simp
      let ⟨d₁, ⟨d₂, h⟩ , h2, h3⟩ := Nat.exists_dvd_of_not_prime n2 hnp
      use d₁, d₂
      constructor
      . show d₁ > 1
        change 1 < d₁
        by_contra hd₁
        have := Nat.not_lt.mp hd₁
        match hd: d₁ with
        | 0 =>
          simp at h
          rw [h] at n2
          contradiction
        | 1 =>
          contradiction
        | 2 =>
          contradiction
      . constructor
        . show d₂ > 1
          by_contra hd₂
          have := Nat.not_lt.mp hd₂
          match hd: d₂ with
          | 0 =>
            simp at h
            rw [h] at n2
            contradiction
          | 1 =>
            simp at h
            symm at h
            contradiction
          | 2 =>
            contradiction
        . show n = d₁ * d₂
          exact h

    have m_mul_of_nat : ∃e₁ : Nat, ∃e₂ : Nat, e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ m = e₁ * e₂ := by
      let ⟨d₁, d₂, hd₁, hd₂, hd⟩ := n_mul_of_nat

      -- lemma2 が整数に関する定理なので整数にキャストする
      let e₁': Int := 2 ^ d₁ - 1
      let e₂': Int := ∑ i in Finset.range d₂, (2 ^ d₁) ^ (d₂ - i - 1) * 1 ^ i
      have hm: m = e₁' * e₂' := by calc Int.ofNat (2 ^ n - 1)
        _ = 2 ^ n - 1 := by simp
        _ = 2 ^ (d₁ * d₂) - 1 := by rw [hd]
        _ = (2 ^ d₁) ^ d₂ - 1 := by rw [pow_mul]
        _ = (2 ^ d₁) ^ d₂ - 1 ^ d₂ := by simp
        _ = (2 ^ d₁ - 1) * (∑ i in Finset.range d₂, (2 ^ d₁) ^ (d₂ - i - 1) * 1 ^ i) := by exact @lemma2 (2 ^ d₁) 1 d₂
        _ = e₁' * e₂' := by rfl

      let e₁ := e₁'.toNat
      let e₂ := e₂'.toNat
      have he₁ : e₁' ≥ 0 := by calc e₁'
        _ = 2 ^ d₁ - 1 := by rfl
        _ ≥ 2 ^ 0 - 1 := by
          apply Int.sub_le_sub_right
          simp
          have : (@OfNat.ofNat ℤ 2 instOfNat) ^ d₁ = ↑((2 : Nat) ^ d₁) := by calc
              (@OfNat.ofNat ℤ 2 instOfNat) ^ d₁ = ↑(2: Nat) ^ d₁ := by rfl
              _ = ↑((2: Nat) ^ d₁) := Eq.symm (Lean.Omega.Int.ofNat_pow 2 d₁)
          rw [this]
          have : 1 ≤ 2 ^ d₁ := by
            apply Nat.one_le_pow
            decide
          have : Int.ofNat 1 ≤ Int.ofNat (2 ^ d₁) := by
            exact Int.ofNat_le.mpr this
          exact this
        _ ≥ 0 := by simp

      have : m = e₁ * e₂ := by
        calc m
          _ = Int.toNat ↑m := by exact Int.toNat_natCast m
          _ = (e₁' * e₂').toNat := by rw [hm]
          _ = e₁'.toNat * e₂'.toNat := by
            rw [toNat_mul_dist]
            exact he₁
          _ = e₁ * e₂ := by rfl

      have : e₁ ≠ 1 := by
        intro he₁_eq_1
        have : (0: Int) ≤ 2 ^ d₁ - 1 := by
          have : 1 ≤ 2 ^ d₁ := by
            apply Nat.one_le_pow
            decide
          have : Int.ofNat 1 ≤ Int.ofNat (2 ^ d₁) := by
            exact Int.ofNat_le.mpr this
          have : Int.ofNat 1 ≤ Int.ofNat 2 ^ d₁ := by
            rw [Int_ofNat_pow]
            exact this
          have : Int.ofNat 0 ≤ Int.ofNat 2 ^ d₁ - Int.ofNat 1 := by
            exact Int.sub_le_sub_right this 1
          exact this
        have hd₁_cast: ↑(2 ^ d₁ - (1: Int)).toNat = 2 ^ d₁ - (1: Int) := by
          exact Int.toNat_of_nonneg this
        have : e₁ = e₁'.toNat := by rfl
        have : (2 ^ d₁ - (1: Int)).toNat = 1 := by
          rw [he₁_eq_1] at this
          symm at this
          exact this
        have : (2 ^ d₁ - (1: Int)).toNat = (1: Int) := by
          rw [this]
          rfl
        have : 2 ^ d₁ - (1: Int) = 1 := by
          rw [←hd₁_cast]
          exact this
        have : 2 ^ d₁ = (2: Int) := by calc
          (2: Int) ^ d₁ = 2 ^ d₁ - 1 + 1 := by simp
          _ = 1 + 1 := by rw [this]
          _ = 2 := by rfl
        have : 2 ^ d₁ = 2 := by calc
          2 ^ d₁ = ((2 ^ d₁: Int)).toNat := by
            have h2 := Int.toNat_ofNat (2 ^ d₁)
            rw [←h2]
            simp
          _ = (2: Int).toNat := by rw [this]
          _ = 2 := by simp
        have : d₁ = 1 := by
          apply @Nat.pow_right_injective 2
          . rfl
          . simp
            exact this
        rw [this] at hd₁
        contradiction

      have : 1 < e₂' := by
        exact lemma3 hd₁ hd₂
      have : 1 < e₂ := by
        have hb : 0 < e₂' := by
          exact Int.lt_trans (by decide) this
        exact (Int.toNat_lt_toNat hb).mpr this
      have : e₂ ≠ 1 := by
        intro he₂_eq_1
        rw [he₂_eq_1] at this
        contradiction

      use e₁, e₂

    have : ¬Nat.Prime (2 ^ (k + 2) - 1) := by
      rw [← hn]
      let ⟨e₁, e₂, he₁, he₂, he⟩ := m_mul_of_nat
      have : ¬Nat.Prime m := by
        rw [he]
        exact Nat.not_prime_mul he₁ he₂
      exact this
    exact this
