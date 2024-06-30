namespace Exercises

example : p ∧ q → q ∧ p :=
  fun (h : p ∧ q) => ⟨h.right, h.left⟩

-- ∧ と ∨ の可換性
example : p ∧ q ↔ q ∧ p :=
  have hr : p ∧ q → q ∧ p :=
    fun h => ⟨h.right, h.left⟩
  have hl : q ∧ p → p ∧ q :=
    fun  h => ⟨h.right, h.left⟩
  Iff.intro hr hl

  example : p → q ∨ p :=
    fun (h : p) => Or.intro_right q h

example : p ∨ q ↔ q ∨ p :=
  have hp : p → q ∨ p :=
    fun h => Or.inr h
  have hq : q → q ∨ p :=
    fun h => Or.inl h
  have r : p ∨ q → q ∨ p :=
    fun h => Or.elim h hp hq
  have kp : p → p ∨ q :=
    fun h => Or.inl h
  have kq : q → p ∨ q :=
    fun h => Or.inr h
  have l : q ∨ p → p ∨ q :=
    fun h => Or.elim h kq kp
  show p ∨ q ↔ q ∨ p from Iff.intro r l

-- ∧ と ∨ の結合性
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  have hright: (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
    fun (h: (p ∧ q) ∧ r) =>
      have hp: p := h.left.left
      have hq: q := h.left.right
      have hr: r := h.right
      have hqr: q ∧ r := And.intro hq hr
      show p ∧ (q ∧ r) from And.intro hp hqr
  have hleft: p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
    fun (h: p ∧ (q ∧ r)) =>
      have hp: p := h.left
      have hq: q := h.right.left
      have hr: r := h.right.right
      have hpq: p ∧ q := And.intro hp hq
      show (p ∧ q) ∧ r from And.intro hpq hr
  show (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) from Iff.intro hright hleft

example : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
  have hp: p → p ∨ (q ∨ r) :=
    fun (h: p) =>
      Or.intro_left (q ∨ r) h
  have hq: q → p ∨ (q ∨ r) :=
    fun (h: q) =>
      have hqr: (q ∨ r) := Or.intro_left r h
      Or.intro_right p hqr
  have hr: r → p ∨ (q ∨ r) :=
    fun (h: r) =>
      have hqr: (q ∨ r) := Or.intro_right q h
      Or.intro_right p hqr
  have hpq: p ∨ q → p ∨ (q ∨ r) :=
    fun (h: p ∨ q) =>
      Or.elim h hp hq
  have hright: (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
    fun (h: (p ∨ q) ∨ r) =>
      Or.elim h hpq hr
  show (p ∨ q) ∨ r → p ∨ (q ∨ r) from hright

-- 分配性
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  have hright: p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
    fun (h: p ∧ (q ∨ r)) =>
      have hp: p := h.left
      have hqr: q ∨ r := h.right
      have hq: q → (p ∧ q) ∨ (p ∧ r) :=
        fun (h: q) =>
          have hpq: p ∧ q := ⟨hp, h⟩
          show (p ∧ q) ∨ (p ∧ r) from Or.intro_left (p ∧ r) hpq
      have hr: r → (p ∧ q) ∨ (p ∧ r) :=
        fun (h: r) =>
          have hpr: p ∧ r := ⟨hp, h⟩
          show (p ∧ q) ∨ (p ∧ r) from Or.intro_right (p ∧ q) hpr
      show (p ∧ q) ∨ (p ∧ r) from Or.elim hqr hq hr
  have hleft: (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) :=
    fun (h: (p ∧ q) ∨ (p ∧ r)) =>
      have hq: (p ∧ q) → p ∧ (q ∨ r) :=
        fun (hpq: p ∧ q) =>
          have hp: p := hpq.left
          have hq: q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.intro_left r hq⟩
      have hr: (p ∧ r) → p ∧ (q ∨ r) :=
        fun (hpr: p ∧ r) =>
          have hp: p := hpr.left
          have hr: r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.intro_right q hr⟩
      show p ∧ (q ∨ r) from Or.elim h hq hr
  show p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) from Iff.intro hright hleft

-- example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- 他の性質
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  have hright: (p → (q → r)) → (p ∧ q → r) :=
    fun (h: (p → (q → r))) =>
      fun (hpq: p ∧ q) =>
        show r from h hpq.left hpq.right
  have hleft: (p ∧ q → r) → (p → (q → r)) :=
    fun (h: (p ∧ q → r)) =>
      fun (hp: p) =>
        fun (hq: q) =>
          show r from h ⟨hp, hq⟩
  show (p → (q → r)) ↔ (p ∧ q → r) from Iff.intro hright hleft

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  have hright: ((p ∨ q) → r) → (p → r) ∧ (q → r) :=
    fun (h: ((p ∨ q) → r)) =>
      have hp_to_r: p → r := fun (hp: p) => h (Or.intro_left q hp)
      have hq_to_r: q → r := fun (hq: q) => h (Or.intro_right p hq)
      show (p → r) ∧ (q → r) from ⟨hp_to_r, hq_to_r⟩
  have hleft: (p → r) ∧ (q → r) → ((p ∨ q) → r) :=
    fun (h: (p → r) ∧ (q → r)) =>
      fun (hp_or_q: p ∨ q) =>
        show r from Or.elim hp_or_q h.left h.right
  show ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) from Iff.intro hright hleft

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  have hright: ¬(p ∨ q) → ¬p ∧ ¬q :=
    fun (hnpq: ¬(p ∨ q)) =>
      have hnp: ¬p := fun (hp: p) => absurd (Or.intro_left q hp) hnpq
      have hnq: ¬q := fun (hq: q) => absurd (Or.intro_right p hq) hnpq
      show ¬p ∧ ¬q from ⟨hnp, hnq⟩
  have hleft: ¬p ∧ ¬q → ¬(p ∨ q) :=
    fun (hnpnq: ¬p ∧ ¬q) =>
      fun (hp_or_q: p ∨ q) =>
        have hp_to_con: p → ¬(p ∨ q) :=
          fun (hp: p) => absurd hp hnpnq.left
        have hq_to_con: q → ¬(p ∨ q) :=
          fun (hq: q) => absurd hq hnpnq.right
        absurd hp_or_q (Or.elim hp_or_q hp_to_con hq_to_con)
  show ¬(p ∨ q) ↔ ¬p ∧ ¬q from Iff.intro hright hleft

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun (hnp_or_nq: ¬p ∨ ¬q) =>
    fun (hpq: p ∧ q) =>
      have hnp_to_false: ¬p → False :=
        fun (hnp: ¬p) => absurd hpq.left hnp
      have hnq_to_false: ¬q → False :=
        fun (hnq: ¬q) => absurd hpq.right hnq
      show False from hnp_or_nq.elim hnp_to_false hnq_to_false

example : ¬(p ∧ ¬p) :=
  fun (h: p ∧ ¬p) =>
    show False from absurd h.left h.right

example : p ∧ ¬q → ¬(p → q) :=
  fun (hpnq: p ∧ ¬q) =>
    fun (hp_to_q: p → q) =>
      have hq: q := hp_to_q hpnq.left
      have hnq: ¬q := hpnq.right
      absurd hq hnq

example : ¬p → (p → q) :=
  fun (hnp: ¬p) =>
    fun (hp: p) =>
      show q from absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
  fun (hnp_or_q: ¬p ∨ q) =>
    fun (hp: p) =>
      have left: ¬p → q := fun (hnp: ¬p) => show q from absurd hp hnp
      have right: q → q := fun (hq: q) => hq
      show q from Or.elim hnp_or_q left right

example : p ∨ False ↔ p :=
  have right: p ∨ False → p :=
    fun (hp_or_f: p ∨ False) =>
      have hp_to_p: p → p := fun (hp: p) => hp
      have hf_to_p: False → p := False.elim
      show p from hp_or_f.elim hp_to_p hf_to_p
  have left: p → p ∨ False :=
    fun (hp: p) => Or.intro_left False hp
  Iff.intro right left

example : False → p := False.elim

example : p ∧ False ↔ False :=
  suffices h: (p ∧ False → False) ∧ (False → p ∧ False) from Iff.intro h.left h.right
  have right: p ∧ False → False := fun (h: p ∧ False) => h.right
  have left: False → p ∧ False := False.elim
  show (p ∧ False → False) ∧ (False → p ∧ False) from ⟨right, left⟩

theorem contraposition : (p → q) → (¬q → ¬p) :=
  fun (p_to_q: p → q) =>
    fun (not_q: ¬q) =>
      fun (hp: p) => absurd (p_to_q hp) not_q

example : ¬(p ↔ ¬p) :=
  fun (h: p ↔ ¬p) =>
    have p_to_np: p → ¬p := h.mp
    have np_to_p: ¬p → p := h.mpr
    have p_to_f: p → False :=
      fun (hp: p) => absurd hp (p_to_np hp)
    have np: ¬p := p_to_f
    have hp : p := np_to_p np
    show False from np hp

end Exercises

namespace Exercises2
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun (h: p → q ∨ r) =>
    byCases
      (fun hp: p =>
        have q_or_r: q ∨ r := h hp
        have q_to_con: q → (p → q) ∨ (p → r) :=
          fun hq: q =>
            have p_to_q: p → q := fun (_: p) => hq
            show (p → q) ∨ (p → r) from Or.intro_left (p → r) p_to_q
        have r_to_con: r → (p → q) ∨ (p → r) :=
          fun hr: r =>
            have p_to_r: p → r := fun (_: p) => hr
            show (p → q) ∨ (p → r) from Or.intro_right (p → q) p_to_r
        show (p → q) ∨ (p → r) from Or.elim q_or_r q_to_con r_to_con
      )
      (fun hnp: ¬p =>
        have p_to_q: p → q :=
          fun (hp: p) => absurd hp hnp
        show (p → q) ∨ (p → r) from Or.intro_left (p → r) p_to_q
      )

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h: ¬(p ∧ q) =>
   byCases
     (fun hp: p =>
        have hnq: ¬q :=
          fun (hq: q) => absurd ⟨hp, hq⟩ h
        show ¬p ∨ ¬q from Or.intro_right _ hnq
     )
     (fun nhp: ¬p =>
        show ¬p ∨ ¬q from Or.intro_left _ nhp
     )

example : ¬(p → q) → p ∧ ¬q :=
  fun (h: ¬(p → q)) =>
    byCases
      (fun hp: p =>
        have nq: ¬q :=
          fun hq: q =>
            have p_to_q: p → q :=
              fun _: p => hq
            absurd p_to_q h
        show p ∧ ¬q from ⟨hp, nq⟩
      )
      (fun np: ¬p =>
        have p_to_q: p → q :=
          fun hp: p => absurd hp np
        absurd p_to_q h
      )

example : (p → q) → (¬p ∨ q) :=
  fun p_to_q: p → q =>
    show (¬p ∨ q) from byCases
      (fun hp: p =>
        have hq: q := p_to_q hp
        show (¬p ∨ q) from Or.intro_right _ hq
      )
      (fun np: ¬p =>
        show (¬p ∨ q) from Or.intro_left _ np
      )

example : (¬q → ¬p) → (p → q) :=
  fun nq_to_np: ¬q → ¬p =>
    fun hp: p =>
      show q from byCases
        (fun hq: q => hq)
        (fun nq: ¬q =>
          have np: ¬p := nq_to_np nq
          absurd hp np
        )

example : p ∨ ¬p := em p

example : ¬p → (p → q) :=
  fun np: ¬p =>
    fun hp: p =>
      absurd hp np

example : (((p → q) → p) → p) :=
  fun h : ((p → q) → p) =>
    show p from byContradiction
      (fun np : ¬p =>
        byCases
          (fun p_to_q: p → q =>
            absurd (h p_to_q) np)
          (fun not_p_to_q: ¬(p → q) =>
            have p_to_q: p → q :=
              fun hp: p => absurd hp np
            absurd p_to_q not_p_to_q)
      )

end Exercises2
