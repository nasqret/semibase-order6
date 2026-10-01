import SemigroupBasis.CoRoots.Order6Day14.S3950.S3950GuardedReplay
import SemigroupBasis.CoRoots.Order6Day14.S3950.S3950Factors

/-! Unrestricted fixed-head completeness. Repeated heads supply a guard
by duplication. Unique heads delete semantically in the lower factor;
empty tails use singleton rigidity, never empty word substitutions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day14.S3950

open SemigroupBasis
open SemigroupBasis.CoRoots

abbrev LowerSignature := S5_110Syntax.SameCappedSingletonSignature

private theorem foldlEvalCongr {S : Type}
    (G : Semigroup S) (phi psi : Nat → S) :
    ∀ (letters : List Nat) (initial : S),
      (∀ c, c ∈ letters → phi c = psi c) →
      letters.foldl (fun value c => G.mul value (phi c)) initial =
        letters.foldl (fun value c => G.mul value (psi c)) initial
  | [], _, _ => rfl
  | c :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree c (List.Mem.head rest)]
      apply foldlEvalCongr G phi psi
      intro tested member
      exact agree tested (List.Mem.tail c member)

private theorem evalCongrOnLetters {S : Type}
    (G : Semigroup S) (word : Word Nat) (phi psi : Nat → S)
    (agree : ∀ c ∈ word.toList, phi c = psi c) :
    G.eval phi word = G.eval psi word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [agree head (by simp [Word.toList])]
      apply foldlEvalCongr G phi psi
      intro c member
      exact agree c (List.Mem.tail head member)

theorem tailValidOfUniqueHeadValid (head : Nat) (left right : Word Nat)
    (leftAbsent : head ∉ left.toList) (rightAbsent : head ∉ right.toList)
    (valid : (Identity.mk (Word.singleton head ++ left)
      (Word.singleton head ++ right)).SatisfiedBy rightTable.semigroup) :
    (Identity.mk left right).SatisfiedBy rightTable.semigroup := by
  intro valuation
  let changed : Nat → Fin 5 := fun letter => if letter = head then 4 else valuation letter
  have evaluated := valid changed
  have deleted (word : Word Nat) (absent : head ∉ word.toList) :
      rightTable.semigroup.eval changed (Word.singleton head ++ word) =
        rightTable.semigroup.eval valuation word := by
    rw [Semigroup.eval_append, Semigroup.eval_singleton]
    rw [show changed head = (4 : Fin 5) by simp [changed], lowerLeftUnit]
    apply evalCongrOnLetters rightTable.semigroup word changed valuation
    intro letter member
    have different : letter ≠ head := fun equal => absent (equal ▸ member)
    simp only [changed, if_neg different]
  exact (deleted left leftAbsent).symm.trans (evaluated.trans (deleted right rightAbsent))

theorem singletonRigid (letter : Nat) (word : Word Nat)
    (same : LowerSignature (Word.singleton letter) word) :
    Word.singleton letter = word := by
  cases word with
  | mk head tail =>
      have headEq : head = letter := by
        have member := (same.support head).mpr (List.Mem.head tail)
        simpa only [Word.toList_singleton, List.mem_singleton] using member
      subst head
      cases tail with
      | nil => rfl
      | cons next rest =>
          have nextEq : next = letter := by
            have member := (same.support next).mpr (List.Mem.tail letter (List.Mem.head rest))
            simpa only [Word.toList_singleton, List.mem_singleton] using member
          subst next
          have one := (same.simple letter).mp (by simp [Word.toList, Word.singleton])
          simp only [Word.toList, List.count_cons_self] at one
          omega

theorem derivesOfHeadAndLowerValid (left right : Word Nat)
    (heads : left.head = right.head)
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup) :
    Derives basis left right := by
  have same := S5_110Family.S5_110.valid_sameSignature (Identity.mk left right) valid
  cases left with
  | mk head leftTail =>
      cases right with
      | mk rightHead rightTail =>
          change head = rightHead at heads
          subst rightHead
          by_cases repeated : head ∈ leftTail
          · have leftMany : 2 ≤ (Word.mk head leftTail).toList.count head := by
              have positive := List.count_pos_iff.mpr repeated
              simp only [Word.toList, List.count_cons_self]
              omega
            have rightMany := (same.multiple head).mp leftMany
            have rightRepeated : head ∈ rightTail := by
              apply List.count_pos_iff.mp
              simp only [Word.toList, List.count_cons_self] at rightMany
              omega
            have duplicateLeft := duplicateRepeatedHead head leftTail repeated
            have duplicateRight := duplicateRepeatedHead head rightTail rightRepeated
            have middle := derivesSamePrefixOfLowerValid (Word.mk head leftTail)
              (Word.mk head rightTail) (Word.singleton head) valid
            exact duplicateLeft.trans (middle.trans duplicateRight.symm)
          · have leftOne : (Word.mk head leftTail).toList.count head = 1 := by
              simp [Word.toList, List.count_eq_zero.mpr repeated]
            have rightOne := (same.simple head).mp leftOne
            have rightAbsent : head ∉ rightTail := by
              apply List.count_eq_zero.mp
              simp only [Word.toList, List.count_cons_self] at rightOne
              omega
            cases leftTail with
            | nil =>
                have equal := singletonRigid head (Word.mk head rightTail) same
                change Derives basis (Word.singleton head) (Word.mk head rightTail)
                rw [equal]
                exact Derives.refl _
            | cons leftFirst leftRest =>
                cases rightTail with
                | nil =>
                    have equal := singletonRigid head (Word.mk head (leftFirst :: leftRest)) same.symm
                    change Derives basis (Word.mk head (leftFirst :: leftRest)) (Word.singleton head)
                    rw [equal]
                    exact Derives.refl _
                | cons rightFirst rightRest =>
                    have tailValid := tailValidOfUniqueHeadValid head
                      (Word.mk leftFirst leftRest) (Word.mk rightFirst rightRest)
                      repeated rightAbsent valid
                    exact derivesSamePrefixOfLowerValid (Word.mk leftFirst leftRest)
                      (Word.mk rightFirst rightRest) (Word.singleton head) tailValid

theorem complete (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfHeadAndLowerValid identity.lhs identity.rhs
    (Examples.leftNormalBandFifteenValid_head_eq identity leftValid) rightValid

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := complete

namespace S6_3950

theorem basisFor : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor pair

theorem oppositeBasisFor : BasisFor table.semigroup.opposite dualBasis :=
  basisFor.oppositeReversed

theorem valid_iff_derives (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ Derives basis identity.lhs identity.rhs := by
  constructor
  · exact basisFor.2 identity
  · intro derivation valuation
    exact derivation.sound basisFor.1 valuation

theorem opposite_valid_iff_derives (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup.opposite ↔ Derives dualBasis identity.lhs identity.rhs := by
  constructor
  · exact oppositeBasisFor.2 identity
  · intro derivation valuation
    exact derivation.sound oppositeBasisFor.1 valuation

end S6_3950
end SemigroupBasis.CoRoots.Order6Day14.S3950
