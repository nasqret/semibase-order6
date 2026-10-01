import SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776Guarded
import SemigroupBasis.CoRoots.S5_520Family
import SemigroupBasis.Generated.CatalogueOrder2
import SemigroupBasis.HomomorphicImage

/-!
# S6_9776: unrestricted exact-key completeness and both raw8 endpoints

The actual S2_4-opposite quotient detects the final letter. The proved
S5_534-direct theory detects the head, support and length capped at three.
Long-word derivations are replayed after their common final letter, with
that letter inserted and removed by the proved raw8 padding theorem.
Singletons and doubletons are handled literally, not by a false x²=x³ law.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776

open SemigroupBasis

abbrev leftSemigroup := Generated.Catalogue.S2_4.table.semigroup.opposite
abbrev rightSemigroup := Generated.Catalogue.S5_534.table.semigroup

def leftProjection (a : Fin 6) : Fin 2 := if a = 5 then 1 else 0

def rightProjection (a : Fin 6) : Fin 5 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2
  else if a = 3 then 3 else 4

def leftSection (a : Fin 2) : Fin 6 := if a = 0 then 0 else 5

def rightSection (a : Fin 5) : Fin 6 := ⟨a.val, by omega⟩

theorem left_section : ∀ a, leftProjection (leftSection a) = a := by decide
theorem right_section : ∀ a, rightProjection (rightSection a) = a := by decide

def leftHom : Hom table.semigroup leftSemigroup where
  toFun := leftProjection
  map_mul := by decide

def rightHom : Hom table.semigroup rightSemigroup where
  toFun := rightProjection
  map_mul := by decide

theorem left_surjective : Function.Surjective leftHom.toFun := by
  intro a
  exact ⟨leftSection a, left_section a⟩

theorem right_surjective : Function.Surjective rightHom.toFun := by
  intro a
  exact ⟨rightSection a, right_section a⟩

theorem jointly_injective : ∀ a b : Fin 6,
    leftProjection a = leftProjection b → rightProjection a = rightProjection b → a = b := by decide

theorem left_models : Models leftSemigroup basis :=
  models_raw.homomorphicImage leftHom left_surjective

theorem right_models : Models rightSemigroup basis :=
  models_raw.homomorphicImage rightHom right_surjective

private theorem right_zero_mul : ∀ a b : Fin 2, leftSemigroup.mul a b = b := by decide

theorem eval_left (valuation : Nat → Fin 2) (word : Word Nat) :
    leftSemigroup.eval valuation word = valuation word.reverse.head := by
  rcases word with ⟨head, tail⟩
  induction tail generalizing head with
  | nil => rfl
  | cons next rest ih =>
      simpa only [Semigroup.eval, List.foldl_cons, right_zero_mul,
        Word.reverse, Word.reverseAux, Word.append_head] using ih next

theorem valid_last (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftSemigroup) :
    identity.lhs.reverse.head = identity.rhs.reverse.head := by
  by_cases same : identity.lhs.reverse.head = identity.rhs.reverse.head
  · exact same
  · let valuation : Nat → Fin 2 := fun letter =>
      if letter = identity.lhs.reverse.head then 0 else 1
    have values := valid valuation
    rw [eval_left, eval_left] at values
    have unequal : identity.rhs.reverse.head ≠ identity.lhs.reverse.head := Ne.symm same
    have impossible : (0 : Fin 2) = 1 := by
      simpa only [valuation, if_pos rfl, if_neg unequal] using values
    exact False.elim ((by decide : (0 : Fin 2) ≠ 1) impossible)

structure SameKey (left right : Word Nat) : Prop where
  head_eq : left.head = right.head
  last_eq : left.reverse.head = right.reverse.head
  support : ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList
  capped_length : min left.toList.length 3 = min right.toList.length 3

theorem key_of_factors (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftSemigroup)
    (rightValid : identity.SatisfiedBy rightSemigroup) :
    SameKey identity.lhs identity.rhs :=
  ⟨SemigroupBasis.CoRoots.S5_520Family.S5_534.valid_head identity rightValid,
    valid_last identity leftValid,
    SemigroupBasis.CoRoots.S5_520Family.S5_534.valid_support identity rightValid,
    SemigroupBasis.CoRoots.S5_520Family.S5_534.valid_capped_length identity rightValid⟩

private theorem short_eq {left right : Word Nat} (key : SameKey left right)
    (short : left.toList.length < 3) : left = right := by
  rcases key with ⟨heads, lasts, support, lengths⟩
  rcases left with ⟨a, leftTail⟩
  rcases right with ⟨b, rightTail⟩
  change a = b at heads
  subst b
  cases leftTail with
  | nil =>
      cases rightTail with
      | nil => rfl
      | cons d ds =>
          simp only [Word.toList, List.length_cons, List.length_nil] at lengths
          omega
  | cons c cs =>
      cases cs with
      | cons d ds =>
          simp only [Word.toList, List.length_cons] at short
          omega
      | nil =>
          cases rightTail with
          | nil =>
              simp only [Word.toList, List.length_cons, List.length_nil] at lengths
              omega
          | cons d ds =>
              cases ds with
              | nil =>
                  change c = d at lasts
                  subst d
                  rfl
              | cons e es =>
                  simp only [Word.toList, List.length_cons, List.length_nil] at lengths
                  omega

/-- The screened key is now sufficient for arbitrary words, by a derivation. -/
theorem derives_of_key {left right : Word Nat} (key : SameKey left right) :
    Derives basis left right := by
  by_cases longLeft : 3 ≤ left.toList.length
  · have longRight : 3 ≤ right.toList.length := by
      have lengths := key.capped_length
      omega
    have lower : Derives SemigroupBasis.CoRoots.S5_520.basis left right :=
      SemigroupBasis.CoRoots.S5_520.derivesLongOfHeadSupportEq left right
        longLeft longRight key.head_eq key.support
    have lifted := lowerDerivationAfterLast lower (Word.singleton left.reverse.head)
    have aligned : Derives basis (left ++ Word.singleton left.reverse.head)
        (right ++ Word.singleton right.reverse.head) := by
      simpa only [key.last_eq] using lifted
    exact (appendLast left longLeft).trans
      (aligned.trans (appendLast right longRight).symm)
  · have words : left = right := short_eq key (by omega)
    rw [words]
    exact Derives.refl _

theorem key_of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) : SameKey identity.lhs identity.rhs :=
  key_of_factors identity
    (identity.satisfiedBy_homomorphicImage valid leftHom left_surjective)
    (identity.satisfiedBy_homomorphicImage valid rightHom right_surjective)

theorem valid_iff_key (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔ SameKey identity.lhs identity.rhs := by
  constructor
  · exact key_of_valid identity
  · intro key valuation
    exact (derives_of_key key).sound models_raw valuation

theorem factor_complete (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftSemigroup)
    (rightValid : identity.SatisfiedBy rightSemigroup) :
    Derives basis identity.lhs identity.rhs :=
  derives_of_key (key_of_factors identity leftValid rightValid)

theorem complete (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derives_of_key (key_of_valid identity valid)

theorem representative_basis : BasisFor table.semigroup basis := ⟨models_raw, complete⟩

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.left_section
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.right_section
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.leftHom
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.rightHom
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.left_surjective
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.right_surjective
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.jointly_injective
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.left_models
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.right_models
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.eval_left
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.valid_last
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.key_of_factors
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.derives_of_key
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.key_of_valid
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.valid_iff_key
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.factor_complete
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.complete
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.representative_basis
#print axioms SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776.opposite_basis

end SemigroupBasis.CoRoots.Order6Sunday.HeadLast.S9776
