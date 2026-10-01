import SemigroupBasis.CoRoots.Order6SporadicSection16CanonicalCounts
import SemigroupBasis.CoRoots.Order6SporadicSection16Invariants

/-! Nonempty-word and semantic boundaries for the Section16 completeness
argument. The simple-word case is proved outright. Nonsimple words obtain
actual canonical data and a Derives proof; no completeness field is assumed. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis SemigroupBasis.Examples

def canonicalWord (data : CanonicalData) : Word Nat :=
  match data.initial with
  | [] => ⟨data.anchor, data.anchor :: renderBlocks data.anchor data.blocks⟩
  | first :: rest => ⟨first, rest ++ [data.anchor,data.anchor] ++ renderBlocks data.anchor data.blocks⟩

theorem canonicalWord_toList (data : CanonicalData) : (canonicalWord data).toList = renderCanonical data := by
  cases initial : data.initial <;> simp [canonicalWord, renderCanonical, initial, Word.toList]

theorem listDerives_toWord {left right : Word Nat}
    (derivation : ListDerives left.toList right.toList) : Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail => exact derivation.toWord

theorem existsCanonicalWord (word : Word Nat) (nonsimple : ¬ word.toList.Nodup) :
    ∃ data : CanonicalData, CanonicalWellFormed data ∧ Derives basis word (canonicalWord data) := by
  obtain ⟨data,wellFormed,derivation,_⟩ := existsCanonicalForm word.toList nonsimple
  refine ⟨data,wellFormed,listDerives_toWord ?_⟩
  rw [canonicalWord_toList]
  exact derivation

theorem canonicalWord_ini (data : CanonicalData) (wellFormed : CanonicalWellFormed data) :
    firstOccurrenceSequence (canonicalWord data).toList = canonicalLabels data := by
  rw [canonicalWord_toList]
  exact CanonicalIni.ini_renderCanonical data wellFormed

theorem canonicalized_identity_valid {S : Type u} (G : Semigroup S)
    (models : Models G basis) (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (left right : CanonicalData)
    (leftDerives : Derives basis identity.lhs (canonicalWord left))
    (rightDerives : Derives basis identity.rhs (canonicalWord right)) :
    (Identity.mk (canonicalWord left) (canonicalWord right)).SatisfiedBy G := by
  intro valuation
  exact (leftDerives.sound models valuation).symm.trans ((valid valuation).trans (rightDerives.sound models valuation))

theorem nodup_of_count_le_one : ∀ letters : List Nat,
    (∀ x, letters.count x ≤ 1) → letters.Nodup
  | [], _ => by simp
  | first :: rest, bound => by
      have headBound := bound first
      rw [List.count_cons_self] at headBound
      have zero : rest.count first = 0 := by omega
      refine List.nodup_cons.mpr ⟨List.count_eq_zero.mp zero, nodup_of_count_le_one rest ?_⟩
      intro x
      have wholeBound := bound x
      by_cases same : first = x
      · subst x
        rw [List.count_cons_self] at wholeBound
        omega
      · rw [List.count_cons_of_ne same] at wholeBound
        exact wholeBound

theorem ini_of_nodup (letters : List Nat) (distinct : letters.Nodup) :
    firstOccurrenceSequence letters = letters := by
  have result := CanonicalIni.ini_prefix [] letters distinct (fun _ _ => by simp)
  simpa [firstOccurrenceSequence] using result

theorem simple_left_identity_trivial (identity : Identity Nat)
    (same : FactorInvariants identity.lhs identity.rhs) (simple : identity.lhs.toList.Nodup) :
    identity.lhs = identity.rhs := by
  have rightSimple : identity.rhs.toList.Nodup := by
    apply nodup_of_count_le_one
    intro letter
    have leftBound : identity.lhs.toList.count letter ≤ 1 := by
      rw [simple.count]
      split <;> decide
    have capped := same.capped letter
    omega
  apply Word.toList_injective
  have equal := same.ini
  rw [ini_of_nodup identity.lhs.toList simple, ini_of_nodup identity.rhs.toList rightSimple] at equal
  exact equal

#print axioms existsCanonicalWord
#print axioms canonicalWord_ini
#print axioms canonicalized_identity_valid
#print axioms simple_left_identity_trivial

end SemigroupBasis.CoRoots.Order6SporadicSection16
