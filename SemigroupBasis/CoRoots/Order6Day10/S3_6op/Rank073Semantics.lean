import SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Replay
import SemigroupBasis.CoRoots.S5_381Invariant

/-!
# Rank073: actual initial-marker semantics and product-only head stripping

The short-word arguments use the actual S5_303 content/endpoint signature.
Two-letter rigidity additionally requires freshness from the initial marker.
Element3 is a left identity on products, not on arbitrary values.
-/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Semantics

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83
open SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Replay

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
    Word.singleton letter = word := by
  have singletonRight := same.singleton.mp (show IsSingletonWord (Word.singleton letter) from trivial)
  cases splitEq : terminalSplit word with
  | singleton final =>
      have tested := (same.finalLetter letter).mp
        (show SemigroupBasis.CoRoots.S5_303.FinalLetter (Word.singleton letter) letter from rfl)
      have finals : final = letter := by
        simpa [SemigroupBasis.CoRoots.S5_303.FinalLetter, splitEq] using tested
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      simpa [TerminalSplit.renderWord, finals] using reconstruct
  | pair stem penultimate final =>
      simp [IsSingletonWord, splitEq] at singletonRight

/-- The lower factor alone is NOT enough: the first letter must stay fresh. -/
theorem simplePairRigid (first second : Nat) (different : first ≠ second)
    (word : Word Nat) (firstFresh : first ∉ word.tail)
    (same : LowerSignature (Word.mk first [second]) word) :
    Word.mk first [second] = word := by
  have leftPair : SemigroupBasis.CoRoots.S5_303.UniqueFinalPair
      (Word.mk first [second]) first second := by
    change first = first ∧ second = second ∧ second ≠ first ∧ second ∉ ([] : List Nat)
    simp [Ne.symm different]
  have rightPair := (same.uniqueFinalPair first second).mp leftPair
  cases splitEq : terminalSplit word with
  | singleton final =>
      simp [SemigroupBasis.CoRoots.S5_303.UniqueFinalPair, splitEq] at rightPair
  | pair stem penultimate final =>
      have parts : penultimate = first ∧ final = second ∧ final ≠ penultimate ∧ final ∉ stem := by
        simpa [SemigroupBasis.CoRoots.S5_303.UniqueFinalPair, splitEq] using rightPair
      have stemNil : stem = [] := by
        cases stem with
        | nil => rfl
        | cons head tail =>
            have wordShape : word = Word.mk head (tail ++ [penultimate, final]) := by
              apply Word.toList_injective
              rw [← terminalSplit_renderList word, splitEq]
              simp [TerminalSplit.renderList, Word.toList]
            have repeated : first ∈ word.tail := by
              rw [wordShape]
              simp [parts.1]
            exact False.elim (firstFresh repeated)
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq, stemNil] at reconstruct
      simpa [TerminalSplit.renderWord, parts.1, parts.2.1, wordOfPrefixFinal,
        Word.append, Word.singleton] using reconstruct

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

end SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Semantics
