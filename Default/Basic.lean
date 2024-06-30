namespace Prop1
  variable (p q : Prop)

  theorem t1 : p → q → p :=
    fun hp : p =>
    fun _hq : q =>
    show p from hp

  variable (r s : Prop)
  variable (hr : r)
  #check t1        -- (p q : Prop) (a✝ : p) (a✝¹ : q) : p
  #check t1 r s    -- t1 r s : r → s → r
  #check t1 r s hr -- t1 r s hr : s → r
end Prop1

namespace Prop2
  variable (p q : Prop)
  theorem t1 (hp : p) (hq : q) : p := hp

  #print t1
  -- t1 : ∀ (p q : Prop), p → q → p :=
  --   fun p q hp hq => hp
end Prop2

namespace Prop3
  theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp
end Prop3

namespace Prop4
  theorem t1 : ∀ {p q : Prop}, p → q → p :=
    fun {p q : Prop} (hp : p) (hq : q) => hp
end Prop4

namespace Falsy
  -- Check the definition of False
  theorem pos_neg {p : Prop} : (p ∧ ¬p) → False :=
    fun h : p ∧ ¬p =>
    show False from h.right h.left

end Falsy

namespace Prop5
  theorem taiguu : ∀ {p q : Prop}, (p → q) → ¬q → ¬p :=
    fun {p q : Prop} (h : p → q) =>
    fun hng : ¬q =>
    fun hp : p =>
    show False from hng (h hp)

end Prop5

namespace And_intro
  variable (p q : Prop)

  -- `example` is an anonymous theorem
  example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
  -- theorem and_intro (hp : p) (hq : q) : p ∧ q := And.intro hp hq

  #check fun (hp : p) (hq : q) => And.intro hp hq

  example (h : p ∧ q) : p := And.left h
  example (h : p ∧ q) : q := And.right h

  example (h : p ∧ q) : q ∧ p :=
    And.intro (And.right h) (And.left h)
end And_intro

namespace Anonymouse_constructor
  variable (p q : Prop)
  variable (hp : p) (hq : q)

  -- The following two lines are equivalent
  #check (And.intro hp hq: p ∧ q)
  -- Anonymouse constructor for And.intro, which is a structure
  #check (⟨hp, hq⟩: p ∧ q)
end Anonymouse_constructor

namespace List_length
  variable (xs : List Nat)

  -- The following two lines are equivalent
  #check List.length xs
  #check xs.length
end List_length

namespace And_lr
  variable (p q : Prop)

  example (h : p ∧ q) : q ∧ p :=
    -- This is equivalent to `And.intro (And.right h) (And.left h)`
    ⟨h.right, h.left⟩
end And_lr

namespace And_nested_constructor
  variable (p q : Prop)
  variable (h : p ∧ q)

  -- The following two lines are equivalent
  example : q ∧ p ∧ q := ⟨h.right, ⟨h.left, h.right⟩⟩
  example : q ∧ p ∧ q := ⟨h.right, h.left, h.right⟩
end And_nested_constructor

namespace Or_intro
  variable (p q : Prop)
  example (hp : p) : p ∨ q := Or.intro_left q hp
  example (hq : q) : p ∨ q := Or.intro_right p hq
end Or_intro

namespace Or_elim
  variable (p q r : Prop)

  example (h : p ∨ q) : q ∨ p :=
    Or.elim h
      (fun hp : p =>
        show q ∨ p from Or.intro_right q hp)
      (fun hq : q =>
        show q ∨ p from Or.intro_left p hq)

  -- simplified example
  example (h : p ∨ q) : q ∨ p :=
    h.elim
      (fun hp : p => Or.inr hp)
      (fun hq : q => Or.inl hq)
end Or_elim

namespace Negation_and_Falsity
  variable (p q : Prop)

  example (hpq : p → q) (hnq : ¬q) : ¬p :=
    fun hp : p =>
    show False from hnq (hpq hp)

  example (hp : p) (hnp : ¬p) : q :=
    show q from False.elim (hnp hp)

  example (hp : p) (hnp : ¬p) : q :=
    absurd hp hnp

  example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
    absurd (hqp hq) hnp
end Negation_and_Falsity

namespace Logical_equivalence
  variable (p q : Prop)

  theorem and_swap : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (fun h : p ∧ q =>
        show q ∧ p from ⟨h.right, h.left⟩)
      (fun h : q ∧ p =>
        show p ∧ q from ⟨h.right, h.left⟩)

  #check and_swap p q

  -- using anonymous constructor
  example : p ∧ q ↔ q ∧ p :=
    ⟨fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩⟩

  variable (h : p ∧ q)
  example : q ∧ p :=
    -- Iff.mp (and_swap p q) h
  (and_swap p q).mp h

end Logical_equivalence

namespace Intorducing_auxiliarry_subgoals
  variable (p q : Prop)

  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    have hq : q := h.right
    show q ∧ p from ⟨hq, hp⟩

  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    suffices hq : q from ⟨hq, hp⟩
    show q from h.right

end Intorducing_auxiliarry_subgoals

namespace Classical_logic
  open Classical

  variable (p : Prop)
  #check em p

  theorem dne {p : Prop} (h : ¬¬p) : p :=
    Or.elim (em p)
      (fun hp : p => hp)
      (fun hnp : ¬p => absurd hnp h)

  example (h : ¬¬p) : p :=
    byCases
     (fun h1 : p => h1)
     (fun h1 : ¬p => absurd h1 h)

  example (h : ¬¬p) : p :=
    byContradiction
      (fun h1 : ¬p =>
        show False from h h1)

end Classical_logic
