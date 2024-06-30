example
  (α: Type)
  (p q: α → Prop) :
  (∀x: α, p x ∧ q x) → ∀y: α, p y :=
    fun h: ∀x: α, p x ∧ q x =>
    fun y: α =>
    show p y from (h y).left

-- 推移的関係
namespace Trans_r
variable
  (α: Type)
  (r: α → α → Prop)
  (trans_r : ∀{x y z}, r x y → r y z → r x z)
  (a b c: α)
  (hab : r a b)
  (hbc : r b c)

#check trans_r hab hbc

end Trans_r

namespace Equiv_r
variable
  (α: Type)
  (r: α → α → Prop)

  (refl_r : ∀ x, r x x)
  (symm_r : ∀ {x y}, r x y → r y x)
  (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example
  (a b c d: α)
  (hab: r a b)
  (hcb: r c b)
  (hcd: r c d):
  r a d :=
    have hbc: r b c := symm_r hcb
    have hac: r a c := trans_r hab hbc
    show r a d from trans_r hac hcd

end Equiv_r

namespace For_all_excercises

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  have right: (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) :=
    fun (h: ∀x, p x ∧ q x) =>
      have hpx: ∀x, p x :=
        fun (x: α) => (h x).left
      have hqx: ∀x, q x :=
        fun (x: α) => (h x).right
      show (∀ x, p x) ∧ (∀ x, q x) from ⟨hpx, hqx⟩
  have left: (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x) :=
    fun (h: (∀ x, p x) ∧ (∀ x, q x)) =>
      have hpx: ∀ x, p x := h.left
      have hqx: ∀ x, q x := h.right
      show ∀ x, p x ∧ q x from
        fun (x: α) => ⟨hpx x, hqx x⟩
  Iff.intro right left

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun (h1: ∀ x, p x → q x) =>
  fun (h2: ∀ x, p x) =>
  show ∀ x, q x from
    fun x: α =>
      have hpx: p x := h2 x
      h1 x hpx

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h: (∀x, p x) ∨ (∀x, q x) =>
    fun x: α =>
      have left_to_con: (∀x, p x) → p x ∨ q x :=
        fun (hpx: ∀x, p x) =>
          Or.intro_left (q x) (hpx x)
      have right_to_con: (∀x, q x) → p x ∨ q x :=
        fun (hqx: ∀x, q x) =>
          Or.intro_right (p x) (hqx x)
      show p x ∨ q x from Or.elim h left_to_con right_to_con

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop) -- independent from α

example : α → ((∀ x : α, r) ↔ r) :=
  fun (a: α) =>
    have right: (∀ x : α, r) → r :=
      fun (h: ∀ x : α, r) => h a
    have left: r → (∀ x : α, r) :=
      fun hr: r =>
        fun (x: α) =>
          hr
    Iff.intro right left

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  have right: (∀ x, p x ∨ r) → (∀ x, p x) ∨ r :=
    fun h: ∀ x, p x ∨ r => byCases
      (fun hr: r => Or.intro_right (∀ x, p x) hr)
      (fun nr: ¬r =>
        have px: ∀x, p x :=
          fun x: α =>
            have px_or_r: p x ∨ r := h x
            show p x from Or.resolve_right px_or_r nr
        Or.intro_left r px)
  have left: (∀ x, p x) ∨ r → (∀ x, p x ∨ r) :=
    fun h: (∀ x, p x) ∨ r =>
      have left_to_con: (∀ x, p x) → (∀ x, p x ∨ r) :=
        fun apx: ∀ x, p x =>
        fun x: α =>
          have hpx: p x := apx x
          show p x ∨ r from Or.intro_left r hpx
      have right_to_con: r → (∀ x, p x ∨ r) :=
        fun hr: r =>
        fun x: α =>
          show p x ∨ r from Or.intro_right (p x) hr
      Or.elim h left_to_con right_to_con
  Iff.intro right left

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  ⟨
    (fun (h: ∀ x, r → p x) =>
      show r → ∀ x, p x from
        fun hr: r =>
        fun x: α =>
          h x hr
    ),
    (fun (h: r → ∀ x, p x) =>
      show ∀ x, r → p x from
        fun x: α =>
        fun hr: r =>
          h hr x
    )
  ⟩

-- 理髪師のパラドックス
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

theorem not_iff_not_self {p: Prop}: (p ↔ ¬p) → False :=
  fun (h: p ↔ ¬p) =>
    have p_to_np: p → ¬p := h.mp
    have np_to_p: ¬p → p := h.mpr
    have p_to_f: p → False :=
      fun (hp: p) => absurd hp (p_to_np hp)
    have np: ¬p := p_to_f
    have hp : p := np_to_p np
    show False from np hp

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have barber_barber: shaves barber barber ↔ ¬ shaves barber barber := h barber
  show False from not_iff_not_self barber_barber

end For_all_excercises

namespace Equality

#check Eq.refl
#check Eq.symm
#check Eq.trans

variable (α β: Type)

example (f: α → β) (a: α): (fun x => f x) a = f a :=
  rfl -- Eq.refl _

example (a: α) (b: β): (a, b).1 = a :=
  rfl -- Eq.refl _

example : 2 + 3 = 5 :=
  rfl -- Eq.rfl _

example (a b: α) (p: α → Prop)
  (h₁: a = b) (h₂: p a): p b :=
    Eq.subst h₁ h₂

example (a b: α) (p: α → Prop)
  (h₁: a = b) (h₂: p a): p b :=
    h₁ ▸ h₂ -- h₁ を使って h₂ を書き換える

variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

example (x y: Nat): (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1: (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2: (x + y) * (x + y) = x * x + y * x + (x + y) * y :=
    (Nat.add_mul x y x) ▸ h1
  have h3: (x + y) * (x + y) = (x * x + y * x) + (x * y + y * y) :=
    (Nat.add_mul x y y) ▸ h2
  have h4: (x + y) * (x + y) = ((x * x + y * x) + x * y) + y * y :=
    (Nat.add_assoc (x * x + y * x) (x * y) (y * y)) ▸ h3
  show _ from h4

-- proof by calc
example (x y: Nat): (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul, Nat.add_mul]
    _ =(x * x + y * x) + x * y + y * y  := by rw [←Nat.add_assoc]

example
  (a b c d: Nat)
  (h1: a = b)
  (h2: b = c + 1)
  (h3: c = d + 1):
  a = d + 2 :=
    calc
      a = b           := h1
      _ = c + 1       := h2
      _ = (d + 1) + 1 := congrArg Nat.succ h3
      _ = d + (1 + 1) := Nat.add_assoc d 1 1
      _ = d + 2       := rfl

-- Using rw
example
  (a b c d: Nat)
  (h1: a = b)
  (h2: b = c + 1)
  (h3: c = d + 1):
  a = d + 2 :=
    calc
      a = b           := by rw [h1]
      _ = c + 1       := by rw [h2]
      _ = d + 2       := by rw [h3]

example
  (a b c d: Nat)
  (h1: a = b)
  (h2: b ≤ c)
  (h3: c + 1 < d):
  a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

end Equality

namespace Divides

/--
  x は y を割り切る
-/
def divides (x y: Nat): Prop :=
  ∃k, k * x = y

def divides_trans (h₁: divides x y) (h₂: divides y z): divides x z :=
  let ⟨(k₁: Nat), (d₁: k₁ * x = y)⟩ := h₁
  let ⟨(k₂: Nat), (d₂: k₂ * y = z)⟩ := h₂
  have h1: k₂ * (k₁ * x) = z
    := d₁ ▸ d₂
  have h2: (k₂ * k₁) * x = z
    := Nat.mul_assoc k₂ k₁ x ▸ h1
  show divides x z from Exists.intro (k₂ * k₁) h2

theorem divides_trans2 (h₁: divides x y) (h₂: divides y z): divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  have h: (k₂ * k₁) * x = z :=
    Eq.symm (
      calc
        z = k₂ * y        := by rw [d₂]
        _ = k₂ * (k₁ * x) := by rw [d₁]
        _ = (k₂ * k₁) * x := by rw [Nat.mul_assoc]
    )
  show divides x z from ⟨k₂ * k₁, h⟩

theorem divides_mul (x: Nat) (k: Nat): divides x (k * x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁: divides x y) (h₂: y = z): divides x (2 * z) :=
  calc
    divides x y       := h₁
    _ = z             := h₂
    divides _ (2 * z) := divides_mul ..

end Divides

namespace Existence

example : ∃x: Nat, x > 0 :=
  have h: 1 > 0 := Nat.zero_lt_one
  show ∃x: Nat, x > 0 from Exists.intro 1 h

example (x: Nat) (h: x > 0): ∃y, y < x :=
  have x_non_zero: x ≠ 0 := Nat.not_eq_zero_of_lt h
  have h: 0 < x := Nat.zero_lt_of_ne_zero x_non_zero
  show ∃y, y < x from Exists.intro 0 h

example (x y z: Nat) (hxy: x < y) (hyz: y < z)
  : ∃w, x < w ∧ w < z :=
    have hxyz: x < y ∧ y < z := ⟨hxy, hyz⟩
    show ∃w, x < w ∧ w < z from Exists.intro y hxyz

example : ∃x: Nat, x > 0 :=
  have h: 1 > 0 := Nat.zero_lt_one
  ⟨1, h⟩

example (x y z: Nat) (hxy: x < y) (hyz: y < z)
  : ∃w, x < w ∧ w < z :=
    have hxyz: x < y ∧ y < z := ⟨hxy, hyz⟩
    show ∃w, x < w ∧ w < z from ⟨y, hxyz⟩

-- Exists.elim は任意の値 w : α に対して p w ならば q が成立することを示すことで、
-- ∃ x : α, p x から命題 q を証明することを可能にする。
-- ∀w: α, p w → q
-- (∃x: α, p w)
-- q

example (a: Type) (p q: α → Prop)
  (h: ∃x, p x ∧ q x):
  ∃x, q x ∧ p x :=
  have h₀: ∀w: α, p w ∧ q w → ∃x, q x ∧ p x :=
    fun w =>
    fun hw =>
    -- ⟨w, hw.right, hw.left⟩
    Exists.intro w ⟨hw.right, hw.left⟩
  show ∃x, q x ∧ p x from Exists.elim h h₀

-- いろいろなパターンマッチ

example (a: Type) (p q: α → Prop)
  (h: ∃x, p x ∧ q x):
  ∃x, q x ∧ p x :=
  match h with
  -- match 式で分解する
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

example (a: Type) (p q: α → Prop)
  (h: ∃x, p x ∧ q x):
  ∃x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

example (a: Type) (p q: α → Prop):
  (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

-- 偶数 + 偶数 = 偶数

def is_even (a: Nat): Prop :=
  ∃b: Nat, a = 2 * b

theorem even_plus_even
  {a b: Nat}
  (h₁: is_even a)
  (h₂: is_even b):
  is_even (a + b) :=
    let ⟨c, a_is_2_c⟩ := h₁
    let ⟨d, b_is_2_d⟩ := h₂
    have h₃: a + b = 2 * (c + d) :=
      calc a + b
        _ = 2 * c + 2 * d := by rw [a_is_2_c, b_is_2_d]
        _ = 2 * (c + d)   := by rw [Nat.mul_add]
    show is_even (a + b) from Exists.intro (c + d) h₃

theorem even_plus_even2:
  ∀a b: Nat, is_even a → is_even b → is_even (a + b) :=
    fun a: Nat =>
    fun b: Nat =>
    fun ⟨(c: Nat), (hc: a = 2 * c)⟩ =>
    fun ⟨(d: Nat), (hd: b = 2 * d)⟩ =>
      have h₃: a + b = 2 * (c + d) :=
      calc a + b
        _ = 2 * c + 2 * d := by rw [hc, hd]
        _ = 2 * (c + d)   := by rw [Nat.mul_add]
    show is_even (a + b) from Exists.intro (c + d) h₃

open Classical
universe u
variable (α: Sort u) (p: α → Prop)

example (h: ¬ ∀x, ¬ p x): ∃x, p x :=
  byContradiction (
    fun h1: ¬ ∃x, p x =>
      have h2: ∀x, ¬ p x :=
        fun x =>
        fun h3: p x =>
        have h4: ∃ x, p x := Exists.intro x h3
        absurd h4 h1
      absurd h2 h
  )

end Existence

namespace Ex_exercises

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun (⟨(_: α), (h: r)⟩) => h

example (a : α) : r → (∃ x : α, r) :=
  fun (hr: r) =>
  Exists.intro a hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  have right: (∃ x, p x ∧ r) → (∃ x, p x) ∧ r :=
    fun ⟨(w: α), (h: p w ∧ r)⟩ =>
    ⟨⟨w, h.left⟩, h.right⟩
  have left: (∃ x, p x) ∧ r → (∃ x, p x ∧ r) :=
    fun ⟨⟨(w: α), (h: p w)⟩, (hr: r)⟩ =>
    ⟨w, h, hr⟩
  Iff.intro right left

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  have l_to_r: (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x) :=
    fun ⟨(w: α), (h: p w ∨ q w)⟩ =>
    have h1: p w → (∃ x, p x) ∨ (∃ x, q x) :=
      fun hpw: p w =>
      have ex: ∃x, p x := ⟨w, hpw⟩
      Or.inl ex
    have h2: q w → (∃ x, p x) ∨ (∃ x, q x) :=
      fun hqw: q w =>
      have ex: ∃x, q x := ⟨w, hqw⟩
      Or.inr ex
    show (∃ x, p x) ∨ (∃ x, q x) from Or.by_cases h h1 h2
  have r_to_l: (∃ x, p x) ∨ (∃ x, q x) → (∃ x, p x ∨ q x) :=
    fun h: (∃ x, p x) ∨ (∃ x, q x) =>
    have h1: (∃ x, p x) → (∃ x, p x ∨ q x) :=
      fun ⟨w, h⟩ =>
      have pw_or_qw: p w ∨ q w := Or.inl h
      show ∃ x, p x ∨ q x from ⟨w, pw_or_qw⟩
    have h2: (∃ x, q x) → (∃ x, p x ∨ q x) :=
      fun ⟨w, h⟩ =>
      have pw_or_qw: p w ∨ q w := Or.inr h
      show ∃ x, p x ∨ q x from ⟨w, pw_or_qw⟩
    show (∃ x, p x ∨ q x) from Or.elim h h1 h2
  Iff.intro l_to_r r_to_l

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  have l_to_r: (∀ x, p x) → ¬ (∃ x, ¬ p x) :=
    fun h1: ∀x, p x =>
    fun h2: ∃x, ¬p x =>
    let ⟨(w: α), (npw: ¬ p w)⟩ := h2
    have hpw: p w := h1 w
    absurd hpw npw
  have r_to_l: ¬ (∃ x, ¬ p x) → (∀ x, p x) :=
    fun h1: ¬ (∃ x, ¬ p x) =>
    fun x: α =>
    have nnpx: ¬ ¬ p x :=
      fun npx: ¬ p x =>
      have h2: ∃x, ¬ p x := ⟨x, npx⟩
      absurd h2 h1
    show p x from not_not.mp nnpx
  Iff.intro l_to_r r_to_l

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  have l_to_r: (∃ x, p x) → ¬ (∀ x, ¬ p x) :=
    fun h1: ∃ x, p x =>
    let ⟨w, (hpw: p w)⟩ := h1
    fun h2: ∀ x, ¬ p x =>
    have npw: ¬ p w := h2 w
    absurd hpw npw
  have r_to_l: ¬ (∀ x, ¬ p x) → (∃ x, p x) :=
    fun h1: ¬ (∀ x, ¬ p x) =>
    have nn_con: ¬ ¬ ∃ x, p x :=
      fun n_con: ¬ ∃ x, p x =>
      have h2: ∀ x, ¬ p x :=
        fun x =>
        fun hpx: p x =>
        have h3: ∃ x, p x := ⟨x, hpx⟩
        absurd h3 n_con
      absurd h2 h1
    show ∃ x, p x from not_not.mp nn_con
  Iff.intro l_to_r r_to_l

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  have l_to_r: (¬ ∃ x, p x) → (∀ x, ¬ p x) :=
    fun h: ¬ ∃ x, p x =>
    fun x: α =>
    show ¬ p x from
      fun hpx: p x =>
      have ex: ∃x, p x := ⟨x, hpx⟩
      absurd ex h
  have r_to_l: (∀ x, ¬ p x) → (¬ ∃ x, p x) :=
    fun h1: ∀ x, ¬ p x =>
    fun h2: ∃ x, p x =>
    let ⟨w, (hpw: p w)⟩ := h2
    have npw: ¬ p w := h1 w
    absurd hpw npw
  Iff.intro l_to_r r_to_l

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  let l := ¬ ∀ x, p x
  let r := ∃ x, ¬ p x
  have l_to_r: l → r :=
    fun (h1: ¬ ∀ x, p x) =>
    have nnr: ¬ ¬ r :=
      fun nr: ¬ r =>
      have h2: ∀ x, p x :=
        fun x =>
        have nnpx: ¬ ¬ p x :=
          fun npx: ¬ p x =>
          have h3: ∃ x, ¬ p x := ⟨x, npx⟩
          absurd h3 nr
        not_not.mp nnpx
      absurd h2 h1
    show r from not_not.mp nnr
  have r_to_l: r → l :=
    fun ⟨w, (npw: ¬ p w)⟩ =>
    fun h: ∀ x, p x =>
    absurd (h w) npw
  Iff.intro l_to_r r_to_l

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  have l_to_r: (∀ x, p x → r) → (∃ x, p x) → r :=
    fun h1: ∀ x, p x → r =>
    fun h2: ∃ x, p x =>
    show r from
      let ⟨w, (hpw: p w)⟩ := h2
      h1 w hpw
  have r_to_l: ((∃ x, p x) → r) → (∀ x, p x → r) :=
    fun h1: (∃ x, p x) → r =>
    fun x =>
    fun hpx: p x =>
    show r from
      have : ∃ x, p x := ⟨x, hpx⟩
      h1 this
  Iff.intro l_to_r r_to_l

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  have l_to_r: (∃ x, p x → r) → ((∀ x, p x) → r) :=
    fun h1: ∃ x, p x → r =>
    fun h2: ∀ x, p x =>
    let ⟨w, (hw: p w → r)⟩ := h1
    let hpw: p w := h2 w
    show r from hw hpw
  have r_to_l: ((∀ x, p x) → r) → (∃ x, p x → r) :=
    fun h: (∀ x, p x) → r =>
    have h_case1: (∀ x, p x) → (∃ x, p x → r) :=
      fun (h1: ∀ x, p x) =>
      have : r := h h1
      have : p a → r :=
        fun _ => this
      ⟨a, this⟩
    have h_case2: ¬ (∀ x, p x) → (∃ x, p x → r) :=
      fun h1: ¬ (∀ x, p x) =>
      have : ∃ x, ¬ p x :=
        Classical.or_iff_not_imp_left.mp (forall_or_exists_not p) h1
      let ⟨w, (npw: ¬ p w)⟩ := this
      have : p w → r :=
        fun hpw: p w =>
        absurd hpw npw
      ⟨w, this⟩
    show ∃ x, p x → r from byCases h_case1 h_case2
  Iff.intro l_to_r r_to_l

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  have l_to_r: (∃ x, r → p x) → (r → ∃ x, p x) :=
    fun h: ∃ x, r → p x =>
    fun hr: r =>
    let ⟨w, (hw: r → p w)⟩ := h
    have : p w := hw hr
    show ∃ x, p x from ⟨w, this⟩
  have r_to_l: (r → ∃ x, p x) → (∃ x, r → p x) :=
    fun h: r → ∃ x, p x =>
    have case_r: r → (∃ x, r → p x) :=
      fun hr: r =>
      have : ∃ x, p x := h hr
      let ⟨w, (hpw: p w)⟩ := this
      have : r → p w :=
        fun _ => hpw
      ⟨w, this⟩
    have case_nr: ¬ r → (∃ x, r → p x) :=
      fun nr: ¬ r =>
      have : r → p a :=
        fun hr: r =>
        absurd hr nr
      ⟨a, this⟩
    show (∃ x, r → p x) from byCases case_r case_nr
  Iff.intro l_to_r r_to_l

end Ex_exercises
