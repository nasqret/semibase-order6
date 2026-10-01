import SemigroupBasis.CoRoots.Order6Day15.B16.B16PositiveEvaluation

namespace SemigroupBasis.CoRoots.Order6Day15.B16

/-- Equality of support and the globally simple initial-letter marker. -/
def SamePKey (u v : Word Nat) : Prop :=
  (∀ z, z ∈ u.toList ↔ z ∈ v.toList) ∧
  (∀ z, (u.head = z ∧ z ∉ u.tail) ↔ (v.head = z ∧ z ∉ v.tail))

/-- A proof-friendly presentation of exactly the same observation. -/
def SameTailKey (u v : Word Nat) : Prop :=
  (∀ z, z ∈ u.tail ↔ z ∈ v.tail) ∧
  (∀ z, (u.head = z ∧ z ∉ u.tail) ↔ (v.head = z ∧ z ∉ v.tail))

theorem word_membership (w : Word Nat) (z : Nat) :
    z ∈ w.toList ↔ z = w.head ∨ z ∈ w.tail := by
  exact List.mem_cons

theorem samePKey_symm {u v : Word Nat} (h : SamePKey u v) : SamePKey v u :=
  ⟨fun z => (h.1 z).symm, fun z => (h.2 z).symm⟩

theorem sameTailKey_symm {u v : Word Nat} (h : SameTailKey u v) : SameTailKey v u :=
  ⟨fun z => (h.1 z).symm, fun z => (h.2 z).symm⟩

theorem key_tail_forward {u v : Word Nat} (h : SamePKey u v)
    (z : Nat) (hz : z ∈ u.tail) : z ∈ v.tail := by
  by_cases hv : z ∈ v.tail
  · exact hv
  · have huword : z ∈ u.toList := (word_membership u z).mpr (Or.inr hz)
    have hvword : z ∈ v.toList := (h.1 z).mp huword
    have hhead : v.head = z := ((word_membership v z).mp hvword |>.resolve_right hv).symm
    have impossible : u.head = z ∧ z ∉ u.tail := (h.2 z).mpr ⟨hhead, hv⟩
    exact False.elim (impossible.2 hz)

theorem samePKey_tail {u v : Word Nat} (h : SamePKey u v) : SameTailKey u v :=
  ⟨fun z => ⟨key_tail_forward h z, key_tail_forward (samePKey_symm h) z⟩, h.2⟩

theorem tail_key_support_forward {u v : Word Nat} (h : SameTailKey u v)
    (z : Nat) (hz : z ∈ u.toList) : z ∈ v.toList := by
  by_cases ht : z ∈ u.tail
  · exact (word_membership v z).mpr (Or.inr ((h.1 z).mp ht))
  · have hh : u.head = z := ((word_membership u z).mp hz |>.resolve_right ht).symm
    have target : v.head = z ∧ z ∉ v.tail := (h.2 z).mp ⟨hh, ht⟩
    exact (word_membership v z).mpr (Or.inl target.1.symm)

theorem sameTailKey_support {u v : Word Nat} (h : SameTailKey u v) : SamePKey u v :=
  ⟨fun z => ⟨tail_key_support_forward h z,
    tail_key_support_forward (sameTailKey_symm h) z⟩, h.2⟩

theorem samePKey_iff_tail (u v : Word Nat) : SamePKey u v ↔ SameTailKey u v :=
  ⟨samePKey_tail, sameTailKey_support⟩

theorem positive_eval_eq_of_tail_key {u v : Word Nat} (h : SameTailKey u v)
    (rho : Nat → Fin 3) : positive.eval rho u = positive.eval rho v := by
  have allIff : (∀ x ∈ u.tail, rho x = 2) ↔ (∀ x ∈ v.tail, rho x = 2) := by
    constructor
    · intro hu x hx
      exact hu x ((h.1 x).mpr hx)
    · intro hv x hx
      exact hv x ((h.1 x).mp hx)
  rw [positive_eval, positive_eval]
  by_cases hu : ∀ x ∈ u.tail, rho x = 2
  · have hv := allIff.mp hu
    rw [if_pos hu, if_pos hv]
    by_cases hhead : u.head ∈ u.tail
    · have vhead : v.head ∈ v.tail := by
        by_cases hvhead : v.head ∈ v.tail
        · exact hvhead
        · have impossible : u.head = v.head ∧ v.head ∉ u.tail :=
            (h.2 v.head).mpr ⟨rfl, hvhead⟩
          exact False.elim (impossible.2 (impossible.1 ▸ hhead))
      exact (hu u.head hhead).trans (hv v.head vhead).symm
    · have heads : v.head = u.head := ((h.2 u.head).mp ⟨rfl, hhead⟩).1
      exact congrArg rho heads.symm
  · have hv : ¬ ∀ x ∈ v.tail, rho x = 2 := fun hv => hu (allIff.mpr hv)
    rw [if_neg hu, if_neg hv]

theorem positive_eval_eq_of_key {u v : Word Nat} (h : SamePKey u v)
    (rho : Nat → Fin 3) : positive.eval rho u = positive.eval rho v :=
  positive_eval_eq_of_tail_key (samePKey_tail h) rho

theorem positive_valid_iff_key (u v : Word Nat) :
    (∀ rho : Nat → Fin 3, positive.eval rho u = positive.eval rho v) ↔ SamePKey u v := by
  constructor
  · intro valid
    have tailKey : SameTailKey u v := ⟨valid_tail_support valid, valid_simple_head valid⟩
    exact sameTailKey_support tailKey
  · intro h rho
    exact positive_eval_eq_of_key h rho

theorem positive_identity_iff_key (e : Identity Nat) :
    e.SatisfiedBy positive ↔ SamePKey e.lhs e.rhs := positive_valid_iff_key e.lhs e.rhs

end SemigroupBasis.CoRoots.Order6Day15.B16
