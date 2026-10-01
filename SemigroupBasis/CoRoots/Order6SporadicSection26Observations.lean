import SemigroupBasis.CoRoots.Order6SporadicSection26Predecessor
import SemigroupBasis.CoRoots.Order6SporadicSection26Derivations
import SemigroupBasis.CoRoots.S5_345Factors

/-! Unrestricted observations of literal F7 identities: first occurrence,
capped counts, final letter, and predecessor of each first occurrence.
The factor maps and right-zero probe use the actual six-element table. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection26.F7
open SemigroupBasis SemigroupBasis.Examples

def iniEmbedding : Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun x : Fin 3 => if x = 0 then (0 : Fin 6) else if x = 1 then (4 : Fin 6) else (3 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def countEmbedding : Embedding commutativeExponentThree.semigroup table.semigroup where
  toFun := fun x : Fin 3 => if x = 0 then (0 : Fin 6) else if x = 1 then (1 : Fin 6) else (4 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

theorem valid_ini (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList = firstOccurrenceSequence identity.rhs.toList :=
  S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq identity
    (iniEmbedding.pullback_identity identity valid)

theorem valid_capped (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup)
    (letter : Nat) : min (identity.lhs.toList.count letter) 2 = min (identity.rhs.toList.count letter) 2 :=
  exponentValid_capped_count_eq identity (countEmbedding.pullback_identity identity valid) letter

def lastLetter : List Nat → Option Nat
  | [] => none
  | head :: tail => some (tail.foldl (fun _ x => x) head)

def finalProbe (selected letter : Nat) : Fin 6 := if letter = selected then 5 else 4

private theorem finalProbe_mul (selected a b : Nat) :
    tableMul (finalProbe selected a) (finalProbe selected b) = finalProbe selected b := by
  by_cases ha : a = selected <;> by_cases hb : b = selected <;>
    simp only [finalProbe, ha, hb, ite_true, ite_false] <;> decide

theorem finalProbe_fold (selected previous : Nat) (letters : List Nat) :
    letters.foldl (fun state x => tableMul state (finalProbe selected x)) (finalProbe selected previous) =
      finalProbe selected (letters.foldl (fun _ x => x) previous) := by
  induction letters generalizing previous with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, finalProbe_mul]
      exact ih x

theorem eval_finalProbe (selected : Nat) (word : Word Nat) :
    table.semigroup.eval (finalProbe selected) word =
      finalProbe selected (word.tail.foldl (fun _ x => x) word.head) :=
  finalProbe_fold selected word.head word.tail

theorem valid_lastLetter (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    lastLetter identity.lhs.toList = lastLetter identity.rhs.toList := by
  let left := identity.lhs.tail.foldl (fun _ x => x) identity.lhs.head
  let right := identity.rhs.tail.foldl (fun _ x => x) identity.rhs.head
  by_cases same : left = right
  · exact congrArg some same
  · have observation := valid (finalProbe left)
    rw [eval_finalProbe, eval_finalProbe] at observation
    change finalProbe left left = finalProbe left right at observation
    have leftValue : finalProbe left left = (5 : Fin 6) := by simp [finalProbe]
    have rightValue : finalProbe left right = (4 : Fin 6) := by simp [finalProbe, Ne.symm same]
    rw [leftValue, rightValue] at observation
    exact False.elim ((by decide : (5 : Fin 6) ≠ 4) observation)

def predecessorList (separator : Nat) : List Nat → Option Nat
  | [] => none
  | head :: tail => if head = separator then none else some (predecessorScan separator head tail)

structure Observations (left right : List Nat) : Prop where
  ini : firstOccurrenceSequence left = firstOccurrenceSequence right
  capped : ∀ letter, min (left.count letter) 2 = min (right.count letter) 2
  last : lastLetter left = lastLetter right
  predecessor : ∀ separator, predecessorList separator left = predecessorList separator right

namespace Observations

theorem refl (letters : List Nat) : Observations letters letters :=
  ⟨rfl, fun _ => rfl, rfl, fun _ => rfl⟩

theorem symm {left right : List Nat} (same : Observations left right) : Observations right left :=
  ⟨same.ini.symm, fun x => (same.capped x).symm, same.last.symm,
    fun x => (same.predecessor x).symm⟩

theorem trans {left middle right : List Nat} (first : Observations left middle)
    (second : Observations middle right) : Observations left right :=
  ⟨first.ini.trans second.ini, fun x => (first.capped x).trans (second.capped x),
    first.last.trans second.last, fun x => (first.predecessor x).trans (second.predecessor x)⟩

end Observations

theorem valid_observations (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Observations identity.lhs.toList identity.rhs.toList :=
  ⟨valid_ini identity valid, valid_capped identity valid, valid_lastLetter identity valid,
    valid_predecessorOrLast identity valid⟩

theorem observations_of_listDerives {left right : List Nat} (derivation : ListDerives left right) :
    Observations left right := by
  cases derivation with
  | empty => exact Observations.refl []
  | @words leftHead rightHead leftTail rightTail proof =>
      exact valid_observations
        ⟨S5_107.listWordOfCons leftHead leftTail, S5_107.listWordOfCons rightHead rightTail⟩
        (proof.sound models)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.iniEmbedding
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.countEmbedding
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.valid_ini
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.valid_capped
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.finalProbe_fold
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.eval_finalProbe
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.valid_lastLetter
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.Observations.refl
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.Observations.symm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.Observations.trans
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.valid_observations
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.observations_of_listDerives
end SemigroupBasis.CoRoots.Order6SporadicSection26.F7
