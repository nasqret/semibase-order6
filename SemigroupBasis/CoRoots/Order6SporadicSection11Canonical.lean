import SemigroupBasis.CoRoots.Order6SporadicSection11Pivot
import SemigroupBasis.CoRoots.Order6SporadicSection11Semantics
import SemigroupBasis.CoRoots.S5_530Normalization

namespace SemigroupBasis.CoRoots.Order6SporadicSection11

open SemigroupBasis
open SemigroupBasis.Examples

set_option maxRecDepth 100000 in
theorem section11Basis_models_leftRegularBandThree :
    Models leftRegularBandThree.semigroup basis :=
  models_of_finite_checks leftRegularBandThree (by decide)

set_option maxRecDepth 100000 in
theorem section11Basis_models_commutativeExponentFour :
    Models commutativeExponentFour.semigroup basis :=
  models_of_finite_checks commutativeExponentFour (by decide)

set_option maxRecDepth 100000 in
theorem section11Basis_models_finalMarkerThree :
    Models finalMarkerThree.semigroup basis :=
  models_of_finite_checks finalMarkerThree (by decide)

/-- Derivability from the seven Section 11 laws preserves all three fields of
the signature because the three separating factors model those laws. -/
theorem signature_eq_of_derives
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    signature left = signature right :=
  signature_eq_of_factor_semantics ⟨left, right⟩
    (Derives.sound
      section11Basis_models_leftRegularBandThree derivation)
    (Derives.sound
      section11Basis_models_commutativeExponentFour derivation)
    (Derives.sound
      section11Basis_models_finalMarkerThree derivation)

theorem signature_gatheredWord_eq (word : Word Nat) :
    signature word = signature (gatheredWord word) :=
  signature_eq_of_derives (derivesGatheredWord word)

theorem canonicalWord_gatheredWord_eq (word : Word Nat) :
    canonicalWord word = canonicalWord (gatheredWord word) :=
  canonicalWord_eq_of_signature_eq (signature_gatheredWord_eq word)

private theorem section11_count_replicate_of_ne
    {x z : Nat} (different : z ≠ x) :
    ∀ count : Nat, (List.replicate count x).count z = 0
  | 0 => rfl
  | count + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm different),
        section11_count_replicate_of_ne different count]

private theorem section11_count_filter_ne_self
    (x : Nat) (letters : List Nat) :
    (letters.filter (fun value => decide (value ≠ x))).count x = 0 := by
  apply List.count_eq_zero.mpr
  simp

private theorem normal_filter_ne
    {letters : List Nat}
    (normal : S5_530.S5_530Normal letters) (selected : Nat) :
    S5_530.S5_530Normal
      (letters.filter (fun letter => decide (letter ≠ selected))) := by
  induction normal with
  | nil =>
      exact .nil
  | single letter rest _ notMem induction =>
      by_cases equal : letter = selected
      · subst letter
        have filtered :
            rest.filter (fun value => decide (value ≠ selected)) = rest := by
          apply List.filter_eq_self.mpr
          intro value member
          simp only [decide_eq_true_eq]
          intro valueEqual
          subst value
          exact notMem member
        simpa [filtered] using induction
      · have notMemFiltered :
            letter ∉ rest.filter
              (fun value => decide (value ≠ selected)) := by
          exact fun member => notMem (List.mem_filter.mp member).1
        simpa [equal] using
          S5_530.S5_530Normal.single
            letter _ induction notMemFiltered
  | double letter rest _ notMem induction =>
      by_cases equal : letter = selected
      · subst letter
        have filtered :
            rest.filter (fun value => decide (value ≠ selected)) = rest := by
          apply List.filter_eq_self.mpr
          intro value member
          simp only [decide_eq_true_eq]
          intro valueEqual
          subst value
          exact notMem member
        simpa [filtered] using induction
      · have notMemFiltered :
            letter ∉ rest.filter
              (fun value => decide (value ≠ selected)) := by
          exact fun member => notMem (List.mem_filter.mp member).1
        simpa [equal] using
          S5_530.S5_530Normal.double
            letter _ induction notMemFiltered
  | triple letter rest _ notMem induction =>
      by_cases equal : letter = selected
      · subst letter
        have filtered :
            rest.filter (fun value => decide (value ≠ selected)) = rest := by
          apply List.filter_eq_self.mpr
          intro value member
          simp only [decide_eq_true_eq]
          intro valueEqual
          subst value
          exact notMem member
        simpa [filtered] using induction
      · have notMemFiltered :
            letter ∉ rest.filter
              (fun value => decide (value ≠ selected)) := by
          exact fun member => notMem (List.mem_filter.mp member).1
        simpa [equal] using
          S5_530.S5_530Normal.triple
            letter _ induction notMemFiltered

/-- The unrestricted gather scan produces one capped block per variable. -/
theorem gatheredPrefix_normal :
    ∀ (stem : List Nat) (final : Nat),
      S5_530.S5_530Normal (gatheredPrefix final stem)
  | [], _ => .nil
  | letter :: rest, final => by
      have tailNormal := gatheredPrefix_normal rest final
      have filteredNormal := normal_filter_ne tailNormal letter
      have letterNotMem :
          letter ∉
            (gatheredPrefix final rest).filter
              (fun value => decide (value ≠ letter)) := by
        simp
      have positive :
          0 < prefixExponent final letter
            ((gatheredPrefix final rest).count letter + 1) := by
        unfold prefixExponent
        split
        · simp only [Nat.min_def]
          split <;> omega
        · simp only [Nat.min_def]
          split <;> omega
      have bound :
          prefixExponent final letter
              ((gatheredPrefix final rest).count letter + 1) ≤ 3 := by
        unfold prefixExponent
        split
        · exact Nat.le_trans (Nat.min_le_right _ _) (by omega)
        · exact Nat.min_le_right _ _
      have cases :
          prefixExponent final letter
                ((gatheredPrefix final rest).count letter + 1) = 1 ∨
            prefixExponent final letter
                ((gatheredPrefix final rest).count letter + 1) = 2 ∨
              prefixExponent final letter
                ((gatheredPrefix final rest).count letter + 1) = 3 := by
        omega
      change S5_530.S5_530Normal
        (List.replicate
            (prefixExponent final letter
              ((gatheredPrefix final rest).count letter + 1))
            letter ++
          (gatheredPrefix final rest).filter
            (fun value => decide (value ≠ letter)))
      rcases cases with exponent | exponent | exponent
      · rw [exponent]
        simpa using
          S5_530.S5_530Normal.single
            letter _ filteredNormal letterNotMem
      · rw [exponent]
        simpa using
          S5_530.S5_530Normal.double
            letter _ filteredNormal letterNotMem
      · rw [exponent]
        simpa using
          S5_530.S5_530Normal.triple
            letter _ filteredNormal letterNotMem

/-- The protected final occurrence supplies the possible third copy, so its
prefix block never contains more than two copies. -/
theorem gatheredPrefix_count_final_le_two :
    ∀ (stem : List Nat) (final : Nat),
      (gatheredPrefix final stem).count final ≤ 2
  | [], _ => by
      simp [gatheredPrefix]
  | letter :: rest, final => by
      have induction := gatheredPrefix_count_final_le_two rest final
      by_cases equal : letter = final
      · subst letter
        have filteredCount :
            ((gatheredPrefix final rest).filter
              (fun value => decide (value ≠ final))).count final = 0 :=
          section11_count_filter_ne_self final (gatheredPrefix final rest)
        change
          (List.replicate
              (prefixExponent final final
                ((gatheredPrefix final rest).count final + 1))
              final ++
            (gatheredPrefix final rest).filter
              (fun value => decide (value ≠ final))).count final ≤ 2
        rw [List.count_append, List.count_replicate_self,
          filteredCount, Nat.add_zero]
        simpa [prefixExponent] using
          (Nat.min_le_right
            ((gatheredPrefix final rest).count final + 1) 2)
      · simpa [gatheredPrefix, prefixExponent, equal,
          Ne.symm equal,
          section11_count_replicate_of_ne (Ne.symm equal)] using induction

/-- A list-level block normal form with one separately protected final
occurrence. -/
structure ProtectedBlockNormal (letters : List Nat) : Type where
  stem : List Nat
  final : Nat
  list_eq : letters = stem ++ [final]
  prefix_normal : S5_530.S5_530Normal stem
  final_count_le_two : stem.count final ≤ 2

def gatheredWord_protectedBlockNormal (word : Word Nat) :
    ProtectedBlockNormal (gatheredWord word).toList := by
  let split := splitPrefixFinal word
  refine
    ⟨gatheredPrefix split.2 split.1, split.2, ?_,
      gatheredPrefix_normal split.1 split.2,
      gatheredPrefix_count_final_le_two split.1 split.2⟩
  simp [gatheredWord, split, toList_wordOfPrefixFinal]

end SemigroupBasis.CoRoots.Order6SporadicSection11
