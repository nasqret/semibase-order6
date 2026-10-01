import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.Generated.S4_77
import SemigroupBasis.CoRoots.S5_83Invariant
import SemigroupBasis.Subdirect

/-!
# Rank068: S3_15 direct / S4_77 opposite, exact six-law completeness

The actual factor-invariant pair and six-law countermodel screens were
checked before authoring. The full converse replays the complete left-normal
band calculus behind a two-block suffix, whose literal key is forced by the
already complete opposite S4_77 theory. No bounded result is used as a proof.
-/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_15.Rank068Intersection

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 1], Word.mk 0 [1]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [1], Word.mk 0 [1, 0, 1]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 2], Word.mk 0 [1, 2, 2]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [1, 2], Word.mk 0 [2, 1, 2]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [1, 2, 0, 0], Word.mk 0 [2, 1, 0, 0]⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05]
abbrev displayedBasisSHA256 : String :=
  "fe48e76f52c98be09df4a45ecfd78731600654ee6323d59dea9efad4a4fc3820"
abbrev leftTable : FiniteTable := Generated.S3_15.table
abbrev rightBaseTable : FiniteTable := Generated.S4_77.table
def rightTable : FiniteTable where
  order := 4
  mul first second := rightBaseTable.mul second first
  assoc := by decide
abbrev lowerBasis : List (Identity Nat) := leftNormalBandThreeBasis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_length : basis.length = 6 := by decide
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

/-- An unbounded alphabet, retaining exactly the last one or two letters. -/
inductive TailForm where
  | single (letter : Nat)
  | pair (penultimate final : Nat)
deriving DecidableEq, Repr

def TailForm.last : TailForm → Nat
  | .single letter => letter
  | .pair _ final => final

def TailForm.mul (first second : TailForm) : TailForm :=
  match second with
  | .single final => .pair first.last final
  | .pair penultimate final => .pair penultimate final

def suffixSemigroup : Semigroup TailForm where
  mul := TailForm.mul
  assoc first second third := by
    cases first <;> cases second <;> cases third <;> rfl

theorem suffixModels : Models suffixSemigroup (reversedBasis twoLetterPrefixBasis) := by
  have literal : reversedBasis twoLetterPrefixBasis =
      [(⟨Word.mk 2 [1, 0], Word.mk 1 [0]⟩ : Identity Nat)] := by decide
  intro identity member
  rw [literal] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  intro valuation
  change TailForm.mul (TailForm.mul (valuation 2) (valuation 1)) (valuation 0) =
    TailForm.mul (valuation 1) (valuation 0)
  cases valuation 2 <;> cases valuation 1 <;> cases valuation 0 <;> rfl

def suffixKey (word : Word Nat) : TailForm :=
  match terminalSplit word with
  | .singleton letter => .single letter
  | .pair _ penultimate final => .pair penultimate final

private theorem terminalPair_cons (letter : Nat) (stem : List Nat) (penultimate final : Nat) :
    (TerminalSplit.pair (letter :: stem) penultimate final).renderWord =
      Word.singleton letter ++ (TerminalSplit.pair stem penultimate final).renderWord := rfl

theorem evalTerminalPair (stem : List Nat) (penultimate final : Nat) :
    suffixSemigroup.eval TailForm.single (TerminalSplit.pair stem penultimate final).renderWord =
      TailForm.pair penultimate final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [terminalPair_cons, Semigroup.eval_append, Semigroup.eval_singleton, induction]
      rfl

theorem evalSuffixKey (word : Word Nat) :
    suffixSemigroup.eval TailForm.single word = suffixKey word := by
  have reconstruct := terminalSplit_renderWord word
  cases splitEq : terminalSplit word with
  | singleton letter =>
      rw [splitEq] at reconstruct
      have shape : Word.singleton letter = word := reconstruct
      rw [← shape]
      rfl
  | pair stem penultimate final =>
      rw [splitEq] at reconstruct
      have evaluated := evalTerminalPair stem penultimate final
      rw [reconstruct] at evaluated
      simpa only [suffixKey, splitEq] using evaluated

/-- The true opposite factor forces the unrestricted terminal key. -/
theorem suffixKeyOfValid (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    suffixKey identity.lhs = suffixKey identity.rhs := by
  have lower := Generated.S4_77.opposite_basis.2 identity valid
  have evaluated := lower.sound suffixModels TailForm.single
  simpa only [evalSuffixKey] using evaluated

private def threeWords (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | _ => third

theorem derivesPrefixIdempotence (block guard : Word Nat) :
    Derives basis (block ++ guard) ((block ++ block) ++ guard) := by
  have primitive : Derives basis law01.lhs law01.rhs :=
    Derives.fromBasis (e := law01) (by decide)
  have mapped := (Derives.subst primitive (threeWords block guard guard)).symm
  simpa [law01, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem derivesProductDouble (first second : Word Nat) :
    Derives basis (first ++ second) ((first ++ second) ++ (first ++ second)) := by
  have primitive : Derives basis law02.lhs law02.rhs :=
    Derives.fromBasis (e := law02) (by decide)
  have mapped := Derives.subst primitive (threeWords first second second)
  simpa [law02, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem derivesReturnBeforeSquare (head gap guard : Word Nat) :
    Derives basis ((head ++ gap) ++ (guard ++ guard))
      (((head ++ gap) ++ head) ++ (guard ++ guard)) := by
  have primitive : Derives basis law03.lhs law03.rhs :=
    Derives.fromBasis (e := law03) (by decide)
  have mapped := (Derives.subst primitive (threeWords head gap guard)).symm
  simpa [law03, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem derivesSwapBeforeOwnSquare (head first second : Word Nat) :
    Derives basis (((head ++ first) ++ second) ++ (head ++ head))
      (((head ++ second) ++ first) ++ (head ++ head)) := by
  have primitive : Derives basis law05.lhs law05.rhs :=
    Derives.fromBasis (e := law05) (by decide)
  have mapped := Derives.subst primitive (threeWords head first second)
  simpa [law05, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

/-- Seven typed edges preserve the two-block guard throughout the lower swap. -/
theorem derivesGuardedLeftNormal (head first second tailFirst tailSecond : Word Nat) :
    Derives basis (((head ++ first) ++ second) ++ (tailFirst ++ tailSecond))
      (((head ++ second) ++ first) ++ (tailFirst ++ tailSecond)) := by
  let guard := tailFirst ++ tailSecond
  have step0 : Derives basis (((head ++ first) ++ second) ++ guard)
      (((head ++ first) ++ second) ++ (guard ++ guard)) :=
    Derives.prepend ((head ++ first) ++ second) (derivesProductDouble tailFirst tailSecond)
  have step1 : Derives basis (((head ++ first) ++ second) ++ (guard ++ guard))
      ((((head ++ first) ++ second) ++ head) ++ (guard ++ guard)) := by
    simpa [Word.append_assoc] using derivesReturnBeforeSquare head (first ++ second) guard
  have step2 : Derives basis ((((head ++ first) ++ second) ++ head) ++ (guard ++ guard))
      ((((head ++ first) ++ second) ++ (head ++ head)) ++ (guard ++ guard)) := by
    simpa [Word.append_assoc] using derivesReturnBeforeSquare head ((first ++ second) ++ head) guard
  have step3 : Derives basis ((((head ++ first) ++ second) ++ (head ++ head)) ++ (guard ++ guard))
      ((((head ++ second) ++ first) ++ (head ++ head)) ++ (guard ++ guard)) :=
    Derives.appendRight (derivesSwapBeforeOwnSquare head first second) (guard ++ guard)
  have step4 : Derives basis ((((head ++ second) ++ first) ++ (head ++ head)) ++ (guard ++ guard))
      ((((head ++ second) ++ first) ++ head) ++ (guard ++ guard)) := by
    simpa [Word.append_assoc] using (derivesReturnBeforeSquare head ((second ++ first) ++ head) guard).symm
  have step5 : Derives basis ((((head ++ second) ++ first) ++ head) ++ (guard ++ guard))
      (((head ++ second) ++ first) ++ (guard ++ guard)) := by
    simpa [Word.append_assoc] using (derivesReturnBeforeSquare head (second ++ first) guard).symm
  have step6 : Derives basis (((head ++ second) ++ first) ++ (guard ++ guard))
      (((head ++ second) ++ first) ++ guard) :=
    Derives.prepend ((head ++ second) ++ first) (derivesProductDouble tailFirst tailSecond).symm
  exact step0.trans (step1.trans (step2.trans (step3.trans (step4.trans (step5.trans step6)))))

theorem guardedLowerAxiom (identity : Identity Nat) (member : identity ∈ lowerBasis)
    (substitution : Nat → Word Nat) (tailFirst tailSecond : Word Nat) :
    Derives basis (identity.lhs.bind substitution ++ (tailFirst ++ tailSecond))
      (identity.rhs.bind substitution ++ (tailFirst ++ tailSecond)) := by
  have literal : lowerBasis =
      [(⟨Word.mk 0 [], Word.mk 0 [0]⟩ : Identity Nat),
       (⟨Word.mk 0 [1, 2], Word.mk 0 [2, 1]⟩ : Identity Nat)] := by decide
  rw [literal] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      derivesPrefixIdempotence (substitution 0) (tailFirst ++ tailSecond)
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      derivesGuardedLeftNormal (substitution 0) (substitution 1) (substitution 2) tailFirst tailSecond

private theorem bind_append (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution = left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second = word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) : word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

theorem liftLowerWithSuffix {left right : Word Nat} (derivation : Derives lowerBasis left right)
    (tailFirst tailSecond : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (left.bind substitution ++ (tailFirst ++ tailSecond))
      (right.bind substitution ++ (tailFirst ++ tailSecond)) := by
  induction derivation generalizing tailFirst tailSecond substitution with
  | fromBasis member => exact guardedLowerAxiom _ member substitution tailFirst tailSecond
  | refl => exact Derives.refl _
  | symm _ induction => exact (induction tailFirst tailSecond substitution).symm
  | trans _ _ first second =>
      exact (first tailFirst tailSecond substitution).trans (second tailFirst tailSecond substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind substitution) (induction tailFirst tailSecond substitution)
  | appendRight _ final induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (final.bind substitution ++ tailFirst) tailSecond substitution
  | subst _ next induction =>
      simpa [bind_bind] using
        induction tailFirst tailSecond (fun letter => (next letter).bind substitution)

theorem derivesDuplicateTerminalPair (stem : List Nat) (penultimate final : Nat) :
    Derives basis (TerminalSplit.pair stem penultimate final).renderWord
      ((TerminalSplit.pair stem penultimate final).renderWord ++
        (Word.singleton penultimate ++ Word.singleton final)) := by
  induction stem with
  | nil =>
      exact derivesProductDouble (Word.singleton penultimate) (Word.singleton final)
  | cons letter rest induction =>
      simpa only [terminalPair_cons, Word.append_assoc] using
        Derives.prepend (Word.singleton letter) induction

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

/-- The full exact six-law converse, with singleton and pair strata separated. -/
theorem complete : Complete := by
  intro identity leftValid rightValid
  have keys := suffixKeyOfValid identity rightValid
  have leftReconstruct := terminalSplit_renderWord identity.lhs
  have rightReconstruct := terminalSplit_renderWord identity.rhs
  cases leftSplit : terminalSplit identity.lhs with
  | singleton leftLetter =>
      cases rightSplit : terminalSplit identity.rhs with
      | singleton rightLetter =>
          have letters : leftLetter = rightLetter := by
            simpa [suffixKey, leftSplit, rightSplit] using keys
          rw [leftSplit] at leftReconstruct
          rw [rightSplit] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct, letters]
          exact Derives.refl _
      | pair rightStem rightPenultimate rightFinal =>
          simp [suffixKey, leftSplit, rightSplit] at keys
  | pair leftStem leftPenultimate leftFinal =>
      cases rightSplit : terminalSplit identity.rhs with
      | singleton rightLetter =>
          simp [suffixKey, leftSplit, rightSplit] at keys
      | pair rightStem rightPenultimate rightFinal =>
          have ends : leftPenultimate = rightPenultimate ∧ leftFinal = rightFinal := by
            simpa [suffixKey, leftSplit, rightSplit] using keys
          have penultimateEq : rightPenultimate = leftPenultimate := ends.1.symm
          have finalEq : rightFinal = leftFinal := ends.2.symm
          subst rightPenultimate
          subst rightFinal
          rw [leftSplit] at leftReconstruct
          rw [rightSplit] at rightReconstruct
          have leftDuplicate : Derives basis identity.lhs
              (identity.lhs ++ (Word.singleton leftPenultimate ++ Word.singleton leftFinal)) := by
            simpa only [leftReconstruct] using
              derivesDuplicateTerminalPair leftStem leftPenultimate leftFinal
          have rightDuplicate : Derives basis identity.rhs
              (identity.rhs ++ (Word.singleton leftPenultimate ++ Word.singleton leftFinal)) := by
            simpa only [rightReconstruct] using
              derivesDuplicateTerminalPair rightStem leftPenultimate leftFinal
          have lower := Generated.S3_15.representative_basis.2 identity leftValid
          have middle : Derives basis
              (identity.lhs ++ (Word.singleton leftPenultimate ++ Word.singleton leftFinal))
              (identity.rhs ++ (Word.singleton leftPenultimate ++ Word.singleton leftFinal)) := by
            simpa only [bind_singleton] using
              liftLowerWithSuffix lower (Word.singleton leftPenultimate) (Word.singleton leftFinal) Word.singleton
          exact leftDuplicate.trans (middle.trans rightDuplicate.symm)

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := complete

abbrev FinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup

theorem basisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup basis := intersectionBasis.basisFor pair

theorem oppositeBasisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup.opposite (reversedBasis basis) :=
  (basisForOfFinitePair target pair).oppositeReversed

end SemigroupBasis.CoRoots.Order6Day10.S3_15.Rank068Intersection
