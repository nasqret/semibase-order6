import SemigroupBasis.CoRoots.Order6D2D4SuffixTraceV2M5Endpoint
import SemigroupBasis.CoRoots.Order6Day15.B16.B16ObservationOne

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Necessity

open Literal
open SemigroupBasis.CoRoots.Order6D2D4SuffixTrace

private theorem mem_eraseDups (x : Nat) : ∀ xs : List Nat,
    x ∈ xs.eraseDups ↔ x ∈ xs
  | [] => by simp
  | a :: xs => by
      rw [List.eraseDups_cons]
      simp only [List.mem_cons]
      rw [mem_eraseDups x (xs.filter fun b => !b == a)]
      by_cases h : x = a
      · subst x; simp
      · simp [h]
termination_by xs => xs.length
decreasing_by
  have h : (xs.filter fun b => !b == a).length ≤ xs.length := List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le h

theorem sortedSupport_member (xs : List Nat) (x : Nat) :
    x ∈ sortedSupport xs ↔ x ∈ xs := by
  simp only [sortedSupport,List.mem_mergeSort]
  exact mem_eraseDups x xs

theorem support_of_sorted_eq {xs ys : List Nat} (h : sortedSupport xs = sortedSupport ys) :
    ∀ x, x ∈ xs ↔ x ∈ ys := by
  intro x
  rw [← sortedSupport_member xs x,← sortedSupport_member ys x,h]

theorem simpleLetters_member (xs : List Nat) (x : Nat) :
    x ∈ simpleLetters xs ↔ Single x xs := by
  simp only [simpleLetters,List.mem_filter,decide_eq_true_eq,sortedSupport_member]
  constructor
  · exact fun h => h.2
  · intro h
    have pos : 0 < xs.count x := by change xs.count x = 1 at h; omega
    exact ⟨List.count_pos_iff.mp pos,h⟩

theorem firstSimple_pin (a z : Nat) (xs : List Nat) :
    firstSimple (a :: xs) = some z ↔ a = z ∧ z ∉ xs := by
  by_cases absent : a ∉ xs
  · have count : (a :: xs).count a = 1 := by
      rw [List.count_cons_self,List.count_eq_zero.mpr absent]
    rw [firstSimple,if_pos count]
    constructor
    · intro h
      have eq : a = z := Option.some.inj h
      exact ⟨eq,eq ▸ absent⟩
    · exact fun h => congrArg some h.1
  · have count : (a :: xs).count a ≠ 1 := by
      intro h
      rw [List.count_cons_self] at h
      have zero : xs.count a = 0 := by omega
      exact absent (List.count_eq_zero.mp zero)
    rw [firstSimple,if_neg count]
    constructor
    · intro h; cases h
    · intro h
      exact False.elim (absent (h.1.symm ▸ h.2))

theorem pkey_of_fields (u v : Word Nat)
    (content : sortedSupport u.toList = sortedSupport v.toList)
    (pin : firstSimple u.toList = firstSimple v.toList) : SamePKey u v := by
  refine ⟨support_of_sorted_eq content,?_⟩
  intro z
  cases u with
  | mk a xs =>
      cases v with
      | mk b ys =>
          change (a = z ∧ z ∉ xs) ↔ (b = z ∧ z ∉ ys)
          rw [← firstSimple_pin a z xs,← firstSimple_pin b z ys]
          exact congrArg (fun o => o = some z) pin |>.to_iff

theorem optionalKey_of_fields (xs ys : List Nat)
    (content : sortedSupport xs = sortedSupport ys)
    (pin : firstSimple xs = firstSimple ys) : SameOptionalKey xs ys := by
  have mem := support_of_sorted_eq content
  cases xs with
  | nil =>
      cases ys with
      | nil => exact True.intro
      | cons b ys => exact False.elim (List.not_mem_nil ((mem b).mpr (List.Mem.head _)))
  | cons a xs =>
      cases ys with
      | nil => exact False.elim (List.not_mem_nil ((mem a).mp (List.Mem.head _)))
      | cons b ys => exact pkey_of_fields ⟨a,xs⟩ ⟨b,ys⟩ content pin

theorem suffixAfter_eq_afterLetter (xs : List Nat) (x : Nat) :
    suffixAfter xs x = afterLetter x xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : a = x
      · subst a; simp [suffixAfter,afterLetter]
      · simpa [suffixAfter,afterLetter,h] using ih

theorem descriptor_simples {u v : Word Nat} (eq : descriptor u = descriptor v) :
    ∀ x, Single x u.toList ↔ Single x v.toList := by
  have traces := congrArg Descriptor.simpleLetterSuffixTraces eq
  have letters := congrArg (List.map SimpleLetterSuffixTrace.letter) traces
  have same : simpleLetters u.toList = simpleLetters v.toList := by
    have normalized : (simpleLetters u.toList).map (fun x : Nat => x) =
        (simpleLetters v.toList).map (fun x : Nat => x) := by
      simpa only [descriptor,List.map_map,suffixTrace,Function.comp_def] using letters
    rw [List.map_id',List.map_id'] at normalized
    exact normalized
  intro x
  rw [← simpleLetters_member u.toList x,← simpleLetters_member v.toList x,same]

theorem descriptor_trace {u v : Word Nat} (eq : descriptor u = descriptor v)
    (x : Nat) (one : Single x u.toList) : suffixTrace u.toList x = suffixTrace v.toList x := by
  have traces : (simpleLetters u.toList).map (suffixTrace u.toList) =
      (simpleLetters v.toList).map (suffixTrace v.toList) :=
    congrArg Descriptor.simpleLetterSuffixTraces eq
  have member : suffixTrace u.toList x ∈ (simpleLetters u.toList).map (suffixTrace u.toList) :=
    List.mem_map.mpr ⟨x,(simpleLetters_member u.toList x).mpr one,rfl⟩
  rw [traces] at member
  rcases List.mem_map.mp member with ⟨y,_,same⟩
  have letters : y = x := congrArg SimpleLetterSuffixTrace.letter same
  subst y
  exact same.symm

/-- The historical descriptor gives precisely the observations consumed by B16 reach. -/
theorem descriptor_sameObservation {u v : Word Nat} (eq : descriptor u = descriptor v) :
    SameObservation u v := by
  refine ⟨pkey_of_fields u v (congrArg Descriptor.content eq)
    (congrArg Descriptor.firstSimple eq),descriptor_simples eq,?_⟩
  intro x one
  have trace := descriptor_trace eq x one
  have content : sortedSupport (suffixAfter u.toList x) = sortedSupport (suffixAfter v.toList x) :=
    congrArg SimpleLetterSuffixTrace.suffixContent trace
  have pin : firstSimple (suffixAfter u.toList x) = firstSimple (suffixAfter v.toList x) :=
    congrArg SimpleLetterSuffixTrace.suffixFirstSimple trace
  rw [suffixAfter_eq_afterLetter,suffixAfter_eq_afterLetter] at content pin
  exact optionalKey_of_fields _ _ content pin

private theorem semigroup_eq_of_mul {S : Type} (A B : Semigroup S) (h : A.mul = B.mul) : A = B := by
  cases A; cases B; cases h; rfl

theorem d2_literal : V2.d2G = s6432 := by
  have checked : ∀ a b : Fin 6, V2.d2G.mul a b = s6432.mul a b := by decide
  exact semigroup_eq_of_mul _ _ (funext fun a => funext fun b => checked a b)

theorem d4_literal : V2.d4G = s6439 := by
  have checked : ∀ a b : Fin 6, V2.d4G.mul a b = s6439.mul a b := by decide
  exact semigroup_eq_of_mul _ _ (funext fun a => funext fun b => checked a b)

theorem valid_observation6432 (e : Identity Nat) (valid : e.SatisfiedBy s6432) :
    SameObservation e.lhs e.rhs := by
  have old : e.SatisfiedBy V2.d2G := by rw [d2_literal]; exact valid
  exact descriptor_sameObservation (V2.d2_valid_frozenDescriptor_eq e old)

theorem valid_observation6439 (e : Identity Nat) (valid : e.SatisfiedBy s6439) :
    SameObservation e.lhs e.rhs := by
  have old : e.SatisfiedBy V2.d4G := by rw [d4_literal]; exact valid
  exact descriptor_sameObservation (V2.d4_valid_frozenDescriptor_eq e old)

end SemigroupBasis.CoRoots.Order6Day15.B16.Necessity
