import SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071SigmaPlusReplay
import SemigroupBasis.CoRoots.S5_381Invariant
import SemigroupBasis.CoRoots.Order6Day10.S3_15.Rank048Intersection

/-!
# Rank071: actual initial-marker semantics and product-only head stripping

The two Rank048 lemmas reused here concern ONLY the complete S5_240
signature. No B10 derivation or raw-head-equality premise is retargeted.
Element3 is a left identity on products, not on arbitrary values.
-/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071SigmaPlusSemantics

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071SigmaPlusReplay

theorem simpleInitial_iff (word : Word Nat) (letter : Nat) :
    SemigroupBasis.CoRoots.S5_107.SimpleInitial word letter ↔
      word.head = letter ∧ letter ∉ word.tail := by
  cases word with
  | mk head tail =>
      by_cases equal : head = letter
      · subst head
        simp [SemigroupBasis.CoRoots.S5_107.SimpleInitial,
          SemigroupBasis.CoRoots.S5_107.SimpleIn, Word.toList, List.count_eq_zero]
      · simp [SemigroupBasis.CoRoots.S5_107.SimpleInitial, equal]

theorem initialMarkerValid (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) (letter : Nat) :
    (identity.lhs.head = letter ∧ letter ∉ identity.lhs.tail) ↔
      (identity.rhs.head = letter ∧ letter ∉ identity.rhs.tail) := by
  have actual : identity.SatisfiedBy finalMarkerThree.semigroup.opposite := valid
  have same := SemigroupBasis.CoRoots.S5_381Invariant.oppositeFinalMarkerValid_simpleInitial_iff
    identity actual letter
  simpa only [simpleInitial_iff] using same

theorem sameHeadOfSimple (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup)
    (fresh : identity.lhs.head ∉ identity.lhs.tail) :
    identity.rhs.head = identity.lhs.head ∧ identity.lhs.head ∉ identity.rhs.tail :=
  (initialMarkerValid identity valid identity.lhs.head).mp ⟨rfl, fresh⟩

theorem repeatedRight (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup)
    (repeated : identity.lhs.head ∈ identity.lhs.tail) :
    identity.rhs.head ∈ identity.rhs.tail := by
  apply Decidable.byContradiction
  intro missing
  have leftSimple := (initialMarkerValid identity valid identity.rhs.head).mpr ⟨rfl, missing⟩
  exact leftSimple.2 (by simpa only [← leftSimple.1] using repeated)

theorem singletonRigid (letter : Nat) (word : Word Nat)
    (same : LowerSignature (Word.singleton letter) word) :
    Word.singleton letter = word :=
  SemigroupBasis.CoRoots.Order6Day10.S3_15.Rank048Intersection.singletonRigid letter word same

theorem distinctPairRigid (first second : Nat) (different : first ≠ second)
    (word : Word Nat) (same : LowerSignature (Word.mk first [second]) word) :
    Word.mk first [second] = word :=
  SemigroupBasis.CoRoots.Order6Day10.S3_15.Rank048Intersection.distinctPairRigid first second different word same

theorem leftUnitOnProducts (first second : Fin 5) :
    rightTable.semigroup.mul (3 : Fin 5) (rightTable.semigroup.mul first second) =
      rightTable.semigroup.mul first second := by
  revert first second
  decide

theorem leftUnitOnLongEval (valuation : Nat → Fin 5) (word : Word Nat)
    (long : word.tail ≠ []) :
    rightTable.semigroup.mul (3 : Fin 5) (rightTable.semigroup.eval valuation word) =
      rightTable.semigroup.eval valuation word := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => exact False.elim (long rfl)
      | cons first rest =>
          change rightTable.semigroup.mul (3 : Fin 5)
            (rightTable.semigroup.eval valuation (Word.singleton head ++ Word.mk first rest)) =
              rightTable.semigroup.eval valuation (Word.singleton head ++ Word.mk first rest)
          rw [Semigroup.eval_append, Semigroup.eval_singleton]
          exact leftUnitOnProducts _ _

private theorem foldlCongrOn (first second : Nat → Fin 5) (letters : List Nat) :
    ∀ value : Fin 5, (∀ letter, letter ∈ letters → first letter = second letter) →
      letters.foldl (fun value letter => rightTable.semigroup.mul value (first letter)) value =
        letters.foldl (fun value letter => rightTable.semigroup.mul value (second letter)) value := by
  induction letters with
  | nil => intro value _; rfl
  | cons letter rest induction =>
      intro value agree
      simp only [List.foldl_cons]
      rw [agree letter (by simp)]
      exact induction _ (fun next member => agree next (by simp [member]))

theorem evalCongrOnSupport (first second : Nat → Fin 5) (word : Word Nat)
    (agree : ∀ letter, letter ∈ word.toList → first letter = second letter) :
    rightTable.semigroup.eval first word = rightTable.semigroup.eval second word := by
  cases word with
  | mk head tail =>
      change tail.foldl (fun value letter => rightTable.semigroup.mul value (first letter)) (first head) =
        tail.foldl (fun value letter => rightTable.semigroup.mul value (second letter)) (second head)
      rw [agree head (by simp [Word.toList])]
      exact foldlCongrOn first second tail _ (fun letter member => agree letter (by simp [Word.toList, member]))

/-- Strip the fresh head only from semantic validity, and only for product tails. -/
theorem freshHeadTailValid (head : Nat) (left right : Word Nat)
    (leftFresh : head ∉ left.toList) (rightFresh : head ∉ right.toList)
    (leftLong : left.tail ≠ []) (rightLong : right.tail ≠ [])
    (whole : (Identity.mk (Word.singleton head ++ left) (Word.singleton head ++ right)).SatisfiedBy
      rightTable.semigroup) :
    (Identity.mk left right).SatisfiedBy rightTable.semigroup := by
  intro valuation
  let lifted : Nat → Fin 5 := fun letter => if letter = head then 3 else valuation letter
  have leftAgree : rightTable.semigroup.eval valuation left = rightTable.semigroup.eval lifted left := by
    apply evalCongrOnSupport
    intro letter member
    have different : letter ≠ head := by
      intro equal
      subst letter
      exact leftFresh member
    simp [lifted, different]
  have rightAgree : rightTable.semigroup.eval valuation right = rightTable.semigroup.eval lifted right := by
    apply evalCongrOnSupport
    intro letter member
    have different : letter ≠ head := by
      intro equal
      subst letter
      exact rightFresh member
    simp [lifted, different]
  have evaluated := whole lifted
  simp only [Semigroup.eval_append, Semigroup.eval_singleton] at evaluated
  have liftedHead : lifted head = (3 : Fin 5) := by simp [lifted]
  rw [liftedHead, leftUnitOnLongEval lifted left leftLong, leftUnitOnLongEval lifted right rightLong] at evaluated
  exact leftAgree.trans (evaluated.trans rightAgree.symm)

end SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071SigmaPlusSemantics
