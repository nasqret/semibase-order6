import SemigroupBasis.CoRoots.Order6SporadicSection22E7Canonical
import SemigroupBasis.CoRoots.Order6SporadicSection22Models
import SemigroupBasis.CoRoots.S5_345Factors

/-! The first-occurrence invariant and its exact canonical-label boundary.
The subsemigroup {1,3,5} on paper p98 is the three-element left regular band.
No uniqueness or completeness field is assumed. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E7
open SemigroupBasis SemigroupBasis.Examples

def iniEmbedding : Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (2 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

theorem valid_ini (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList = firstOccurrenceSequence identity.rhs.toList :=
  S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq identity
    (iniEmbedding.pullback_identity identity valid)

def iniFrom (seen letters : List Nat) : List Nat :=
  (firstOccurrenceSequence letters).filter (fun x => decide (x ∉ seen))

theorem iniFrom_cons (seen : List Nat) (x : Nat) (xs : List Nat) :
    iniFrom seen (x :: xs) =
      if x ∈ seen then iniFrom seen xs else x :: iniFrom (x :: seen) xs := by
  by_cases known : x ∈ seen
  · simp [iniFrom,firstOccurrenceSequence,known,List.filter_filter]
    apply congrArg (fun predicate : Nat → Bool => (firstOccurrenceSequence xs).filter predicate)
    funext a
    by_cases same : a = x
    · subst a; simp [known]
    · simp [same]
  · simp [iniFrom,firstOccurrenceSequence,known,List.filter_filter,Bool.and_comm]

theorem iniFrom_known_prefix (seen suffix : List Nat) : ∀ stem : List Nat,
    (∀ x ∈ stem, x ∈ seen) → iniFrom seen (stem ++ suffix) = iniFrom seen suffix
  | [], _ => rfl
  | x :: xs, known => by
      rw [List.cons_append,iniFrom_cons,if_pos (known x (by simp))]
      exact iniFrom_known_prefix seen suffix xs
        (fun y member => known y (List.mem_cons_of_mem x member))

theorem iniFrom_render (seen : List Nat) : ∀ blocks : List CanonicalBlock,
    WellFormed seen blocks → iniFrom seen (renderBlocks blocks) = blocks.map CanonicalBlock.letter
  | [], _ => rfl
  | first :: rest, good => by
      rw [renderBlocks,iniFrom_cons,if_neg good.1,
        iniFrom_known_prefix (first.letter :: seen) (renderBlocks rest) first.extra good.2.2.1,
        iniFrom_render (first.letter :: seen) rest good.2.2.2]
      rfl

theorem ini_render (blocks : List CanonicalBlock) (good : WellFormed [] blocks) :
    firstOccurrenceSequence (renderBlocks blocks) = blocks.map CanonicalBlock.letter := by
  have erase : ∀ xs : List Nat, xs.filter (fun _ => true) = xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => exact congrArg (List.cons x) ih
  simpa [iniFrom,erase] using iniFrom_render [] blocks good

#print axioms valid_ini
#print axioms iniFrom_cons
#print axioms iniFrom_known_prefix
#print axioms iniFrom_render
#print axioms ini_render

end SemigroupBasis.CoRoots.Order6SporadicSection22.E7
