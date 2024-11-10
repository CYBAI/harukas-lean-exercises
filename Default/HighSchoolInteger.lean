import Mathlib.Tactic.Ring

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
