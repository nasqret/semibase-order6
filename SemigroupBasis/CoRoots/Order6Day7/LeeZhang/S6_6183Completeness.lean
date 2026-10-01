import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183NormalForms
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-! Unrestricted completeness of the unchanged S6_6183 raw7. Stabilized words
are glued through commuting square suffixes; observable terminals are reduced
to their unique adjacent simple anchor. Only after those proofs close do we
instantiate the existing C1 quotient and reviewed normalizer interface. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183

open SemigroupBasis
open S4_71Suffix

theorem stable_not_active (front : List Nat) (last simple : Nat)
    (stable : StableTerminal front last) (active : ActiveCut front last simple) : False := by
  have one := (activeProbe_eq_one_iff front last last simple active.1).mpr ⟨rfl, active⟩
  have observation := Derives.sound models_raw stable (activeProbe last simple)
  rw [Semigroup.eval_append, Semigroup.eval_singleton, one] at observation
  change (1 : Fin 6) = mul 1 (activeProbe last simple last) at observation
  have zero := (by decide : ∀ value : Fin 6, mul 1 value = 0) (activeProbe last simple last)
  rw [zero] at observation
  exact (by decide : (1 : Fin 6) ≠ 0) observation

theorem stable_terminals_complete (left right : List Nat) (leftLast rightLast : Nat)
    (same : EndEquivalent left leftLast right rightLast)
    (leftStable : StableTerminal left leftLast) (rightStable : StableTerminal right rightLast) :
    Derives basis (endWord left leftLast) (endWord right rightLast) := by
  let leftWord := endWord left leftLast
  let rightWord := endWord right rightLast
  let x := Word.singleton leftLast
  let y := Word.singleton rightLast
  have leftPad : Derives basis leftWord (leftWord ++ (x ++ x)) := by
    simpa only [leftWord, x, Word.append_assoc] using
      leftStable.trans (Derives.appendRight leftStable (Word.singleton leftLast))
  have rightPad : Derives basis rightWord (rightWord ++ (y ++ y)) := by
    simpa only [rightWord, y, Word.append_assoc] using
      rightStable.trans (Derives.appendRight rightStable (Word.singleton rightLast))
  have lowerTheory : ListTheory leftWord.toList rightWord.toList := by
    simpa only [leftWord, rightWord, endWord, put_toList, Word.toList_singleton] using same.lower
  have leftReplay : Derives basis (leftWord ++ (x ++ x)) (rightWord ++ (x ++ x)) := by
    simpa only [put_word] using prefix_lower_replay leftWord.toList rightWord.toList (x ++ x) lowerTheory
  have rightReplay : Derives basis (leftWord ++ (y ++ y)) (rightWord ++ (y ++ y)) := by
    simpa only [put_word] using prefix_lower_replay leftWord.toList rightWord.toList (y ++ y) lowerTheory
  have switch : Derives basis ((rightWord ++ (y ++ y)) ++ (x ++ x))
      ((rightWord ++ (x ++ x)) ++ (y ++ y)) := by
    simpa only [Word.append_assoc] using Derives.prepend rightWord (derivesSquareCommutation y x)
  exact leftPad.trans (leftReplay.trans ((Derives.appendRight rightPad (x ++ x)).trans
    (switch.trans ((Derives.appendRight leftReplay.symm (y ++ y)).trans
      ((Derives.appendRight leftPad.symm (y ++ y)).trans (rightReplay.trans rightPad.symm))))))

theorem end_complete (left right : List Nat) (leftLast rightLast : Nat)
    (same : EndEquivalent left leftLast right rightLast) :
    Derives basis (endWord left leftLast) (endWord right rightLast) := by
  rcases terminal_cases left leftLast with leftSimple | leftStable | leftAnchored
  · exact simple_terminal_complete left right leftLast rightLast same leftSimple
  · rcases terminal_cases right rightLast with rightSimple | rightStable | rightAnchored
    · exact (simple_terminal_complete right left rightLast leftLast same.symm rightSimple).symm
    · exact stable_terminals_complete left right leftLast rightLast same leftStable rightStable
    · obtain ⟨rightBefore, rightAfter, rightAnchor, rightReduction, rightShape⟩ := rightAnchored
      have normalizedSame : EndEquivalent left leftLast (rightBefore ++ rightLast :: rightAnchor :: rightAfter) rightLast :=
        fun valuation => (same valuation).trans (Derives.sound models_raw rightReduction valuation)
      have rightActive := anchored_active rightBefore rightAfter rightLast rightAnchor rightShape
      obtain ⟨equal, leftActive⟩ := active_terminal_preserved _ _ rightLast leftLast rightAnchor normalizedSame.symm rightActive
      subst leftLast
      exact False.elim (stable_not_active left rightLast rightAnchor leftStable leftActive)
  · obtain ⟨leftBefore, leftAfter, leftAnchor, leftReduction, leftShape⟩ := leftAnchored
    rcases terminal_cases right rightLast with rightSimple | rightStable | rightAnchored
    · exact (simple_terminal_complete right left rightLast leftLast same.symm rightSimple).symm
    · have normalizedSame : EndEquivalent (leftBefore ++ leftLast :: leftAnchor :: leftAfter) leftLast right rightLast :=
        fun valuation => (Derives.sound models_raw leftReduction valuation).symm.trans (same valuation)
      have leftActive := anchored_active leftBefore leftAfter leftLast leftAnchor leftShape
      obtain ⟨equal, rightActive⟩ := active_terminal_preserved _ _ leftLast rightLast leftAnchor normalizedSame leftActive
      subst rightLast
      exact False.elim (stable_not_active right leftLast leftAnchor rightStable rightActive)
    · obtain ⟨rightBefore, rightAfter, rightAnchor, rightReduction, rightShape⟩ := rightAnchored
      have normalizedSame : EndEquivalent (leftBefore ++ leftLast :: leftAnchor :: leftAfter) leftLast
          (rightBefore ++ rightLast :: rightAnchor :: rightAfter) rightLast := by
        intro valuation
        exact (Derives.sound models_raw leftReduction valuation).symm.trans
          ((same valuation).trans (Derives.sound models_raw rightReduction valuation))
      have leftActive := anchored_active leftBefore leftAfter leftLast leftAnchor leftShape
      have equal := (active_terminal_preserved _ _ leftLast rightLast leftAnchor normalizedSame leftActive).1
      subst rightLast
      have anchorEqual := anchored_anchor_preserved leftBefore leftAfter rightBefore rightAfter
        leftLast leftAnchor rightAnchor leftShape rightShape normalizedSame
      subst rightAnchor
      have normalizedDerivation := anchored_terminal_complete leftBefore leftAfter rightBefore rightAfter
        leftLast leftAnchor normalizedSame leftShape.1 leftShape.2.1 rightShape.2.1 leftShape.2.2 rightShape.2.2
      exact leftReduction.trans (normalizedDerivation.trans rightReduction.symm)

theorem derives_of_valid_words (left right : Word Nat)
    (same : ∀ valuation, table.semigroup.eval valuation left = table.semigroup.eval valuation right) :
    Derives basis left right := by
  obtain ⟨leftFront, leftLast, leftShape⟩ := existsEndWord left
  obtain ⟨rightFront, rightLast, rightShape⟩ := existsEndWord right
  subst left
  subst right
  exact end_complete leftFront rightFront leftLast rightLast same

theorem raw_complete : Raw7Completeness :=
  fun identity valid => derives_of_valid_words identity.lhs identity.rhs valid

theorem raw_representative_basis : BasisFor table.semigroup basis := ⟨models_raw, raw_complete⟩

def provedIntersection : IntersectionBasis table.semigroup table.semigroup basis where
  leftModels := models_raw
  rightModels := models_raw
  complete := fun identity valid _ => raw_complete identity valid

noncomputable def quotientNormalizer : IntersectionNormalizer table.semigroup table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer provedIntersection

/-- The shared transport interface is identity-on-basis here, not a claimed
new core, amended basis, or factorization. All completeness is already proved. -/
noncomputable def normalizer : IntersectionNormalizer table.semigroup table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer quotientNormalizer
    (fun _ member => Derives.fromBasis member) (fun _ valid => valid) (fun _ valid => valid)

def diagonalIntersection : IntersectionBasis table.semigroup table.semigroup basis :=
  normalizer.toIntersectionBasis models_raw models_raw

theorem complete (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs := diagonalIntersection.complete identity valid valid

theorem representative_basis : BasisFor table.semigroup basis := ⟨models_raw, complete⟩

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

theorem both_orientations_complete : Raw7BothOrientations := ⟨complete, opposite_basis.2⟩

def oppositeIntersection : IntersectionBasis table.semigroup.opposite table.semigroup.opposite (reversedBasis basis) where
  leftModels := models_opposite_raw
  rightModels := models_opposite_raw
  complete := fun identity valid _ => opposite_basis.2 identity valid

noncomputable def oppositeNormalizer :
    IntersectionNormalizer table.semigroup.opposite table.semigroup.opposite (reversedBasis basis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer oppositeIntersection

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183
