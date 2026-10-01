import SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808CanonicalAssembly

/-! Reconstruct singleton-separated runs from actual prefix-cut permutations.
The structural theorem is unrestricted in list length. Its semantic input is
explicit: this module does not assert that JointSignature supplies the cuts. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808BarrierCuts

open SemigroupBasis
open Msg0524Parity808Gather (basis)
open Msg0524Parity808RunSort
open Msg0524Parity808RunUnique
open Msg0524Parity808RunMultiplicity
open Msg0524Parity808LastNecessary
open Msg0534Parity808CanonicalSpine
open Msg0534Parity808CanonicalAssembly

def beforeBlock (marker : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | head :: tail => if head = marker then [] else head :: beforeBlock marker tail

def SameBarrierCuts (left right : List (Nat × Nat)) : Prop :=
  ∀ marker, marker.2 = 0 → marker ∈ left →
    (beforeBlock marker left).Perm (beforeBlock marker right)

theorem beforeBlock_append (marker : Nat × Nat) (front tail : List (Nat × Nat))
    (absent : marker ∉ front) : beforeBlock marker (front ++ tail) = front ++ beforeBlock marker tail := by
  induction front with
  | nil => rfl
  | cons head rest ih =>
    have different : head ≠ marker := by
      intro same
      apply absent
      rw [← same]
      exact List.mem_cons_self
    have restAbsent : marker ∉ rest := fun member => absent (List.mem_cons_of_mem head member)
    simp only [List.cons_append,beforeBlock,if_neg different,ih restAbsent]

theorem beforeBlock_self (marker : Nat × Nat) (tail : List (Nat × Nat)) :
    beforeBlock marker (marker :: tail) = [] := by simp [beforeBlock]

theorem singleton_not_in_pure (front : List (Nat × Nat)) (pure : AllRepeated front)
    (marker : Nat × Nat) (single : marker.2 = 0) : marker ∉ front :=
  fun member => pure marker member single

theorem pure_or_first_single (blocks : List (Nat × Nat)) :
    AllRepeated blocks ∨ ∃ front marker tail, blocks = front ++ marker :: tail ∧
      AllRepeated front ∧ marker.2 = 0 := by
  induction blocks with
  | nil => exact Or.inl (fun block member => by cases member)
  | cons head rest ih =>
    by_cases single : head.2 = 0
    · exact Or.inr ⟨[],head,rest,rfl,(fun block member => by cases member),single⟩
    · rcases ih with pure | ⟨front,marker,tail,represented,pure,markerSingle⟩
      · apply Or.inl
        intro block member
        rcases List.mem_cons.mp member with same | member
        · subst block; exact single
        · exact pure block member
      · apply Or.inr
        refine ⟨head :: front,marker,tail,?_,?_,markerSingle⟩
        · simp only [represented,List.cons_append]
        · intro block member
          rcases List.mem_cons.mp member with same | member
          · subst block; exact single
          · exact pure block member

theorem key_parts (front : List (Nat × Nat)) (marker : Nat × Nat) (tail : List (Nat × Nat))
    (distinct : ((front ++ marker :: tail).map Prod.fst).Nodup) :
    (front.map Prod.fst).Nodup ∧ (tail.map Prod.fst).Nodup := by
  have split : (front.map Prod.fst ++ marker.1 :: tail.map Prod.fst).Nodup := by
    simpa only [List.map_append,List.map_cons] using distinct
  have parts := List.nodup_append.mp split
  exact ⟨parts.1,(List.nodup_cons.mp parts.2.1).2⟩

theorem marker_absent_parts (front : List (Nat × Nat)) (marker : Nat × Nat) (tail : List (Nat × Nat))
    (distinct : ((front ++ marker :: tail).map Prod.fst).Nodup) :
    marker ∉ front ∧ marker ∉ tail := by
  have unique := blocks_nodup_of_keys (front ++ marker :: tail) distinct
  have parts := List.nodup_append.mp unique
  constructor
  · intro member
    exact parts.2.2 marker member marker (List.mem_cons_self) rfl
  · exact (List.nodup_cons.mp parts.2.1).1

theorem perm_suffix (leftFront rightFront leftTail rightTail : List (Nat × Nat))
    (fronts : leftFront.Perm rightFront)
    (whole : (leftFront ++ leftTail).Perm (rightFront ++ rightTail)) : leftTail.Perm rightTail := by
  rw [List.perm_iff_count]
  intro block
  have counts := whole.count_eq block
  have frontCounts := fronts.count_eq block
  rw [List.count_append,List.count_append] at counts
  omega

theorem reconstruct_with_fuel (fuel : Nat) (left right : List (Nat × Nat))
    (enough : left.length ≤ fuel)
    (leftDistinct : (left.map Prod.fst).Nodup) (rightDistinct : (right.map Prod.fst).Nodup)
    (whole : left.Perm right) (cuts : SameBarrierCuts left right) : SameRunCounts left right := by
  induction fuel generalizing left right with
  | zero =>
    have empty : left = [] := by
      cases left with
      | nil => rfl
      | cons head tail => simp at enough
    subst left
    have otherEmpty := whole.nil_eq
    subst right
    exact SameRunCounts.last [] [] leftDistinct rightDistinct
      (fun block member => by cases member) (fun _ => rfl)
  | succ fuel ih =>
    rcases pure_or_first_single left with pure | ⟨leftFront,marker,leftTail,leftForm,leftPure,single⟩
    · exact SameRunCounts.last left right leftDistinct rightDistinct pure
        (render_counts_of_perm left right whole)
    · subst left
      have markerRight : marker ∈ right := whole.mem_iff.mp (by simp)
      obtain ⟨rightFront,rightTail,rightForm⟩ := List.append_of_mem markerRight
      subst right
      have leftParts := key_parts leftFront marker leftTail leftDistinct
      have rightParts := key_parts rightFront marker rightTail rightDistinct
      have leftAbsent := marker_absent_parts leftFront marker leftTail leftDistinct
      have rightAbsent := marker_absent_parts rightFront marker rightTail rightDistinct
      have frontPerm := cuts marker single (by simp)
      rw [beforeBlock_append marker leftFront _ leftAbsent.1,
        beforeBlock_append marker rightFront _ rightAbsent.1] at frontPerm
      simp only [beforeBlock_self,List.append_nil] at frontPerm
      have rightPure := allRepeated_perm leftFront rightFront frontPerm leftPure
      have tailPerm : leftTail.Perm rightTail :=
        (perm_suffix leftFront rightFront (marker :: leftTail) (marker :: rightTail)
          frontPerm whole).cons_inv
      have tailCuts : SameBarrierCuts leftTail rightTail := by
        intro tested testedSingle testedMember
        have leftFrontAbsent := singleton_not_in_pure leftFront leftPure tested testedSingle
        have rightFrontAbsent := singleton_not_in_pure rightFront rightPure tested testedSingle
        have different : marker ≠ tested := by
          intro same
          exact leftAbsent.2 (same.symm ▸ testedMember)
        have observed := cuts tested testedSingle
          (List.mem_append_right leftFront (List.mem_cons_of_mem marker testedMember))
        rw [beforeBlock_append tested leftFront _ leftFrontAbsent,
          beforeBlock_append tested rightFront _ rightFrontAbsent] at observed
        simp only [beforeBlock,if_neg different] at observed
        exact (perm_suffix leftFront rightFront _ _ frontPerm observed).cons_inv
      have smaller : leftTail.length ≤ fuel := by
        simp only [List.length_append,List.length_cons] at enough
        omega
      exact SameRunCounts.split leftFront rightFront marker leftTail rightTail
        leftParts.1 rightParts.1 leftPure (render_counts_of_perm leftFront rightFront frontPerm)
        single (ih leftTail rightTail smaller leftParts.2 rightParts.2 tailPerm tailCuts)

theorem sameRunCounts_of_barrierCuts (left right : List (Nat × Nat))
    (leftDistinct : (left.map Prod.fst).Nodup) (rightDistinct : (right.map Prod.fst).Nodup)
    (whole : left.Perm right) (cuts : SameBarrierCuts left right) : SameRunCounts left right :=
  reconstruct_with_fuel left.length left right (Nat.le_refl _) leftDistinct rightDistinct whole cuts

theorem canonical_runs_of_barrierCuts {left right : Word Nat} (same : JointSignature left right)
    (cuts : SameBarrierCuts (canonicalPrefix left) (canonicalPrefix right)) :
    SameRunCounts (canonicalPrefix left) (canonicalPrefix right) :=
  sameRunCounts_of_barrierCuts _ _ (canonicalPrefix_distinct left) (canonicalPrefix_distinct right)
    (canonicalPrefix_perm same) cuts

theorem derives_of_barrierCuts {left right : Word Nat} (same : JointSignature left right)
    (cuts : SameBarrierCuts (canonicalPrefix left) (canonicalPrefix right)) : Derives basis left right :=
  derives_of_runCounts same (canonical_runs_of_barrierCuts same cuts)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808BarrierCuts
