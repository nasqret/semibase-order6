import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.CoRoots.S5_240Completeness
import SemigroupBasis.Subdirect

/-!
# Rank048: the exact S3_15 / S5_240 ten-law intersection

This is S6_6167's direct contract, not the older S2_4/Rank048 class6165.
The source-bound factor-pair key and bounded countermodel screens passed
before authoring. Lee--Zhang2015 Condition17 is an intake fact, not this proof.
The complete lower S5_240 calculus is replayed behind a nonempty guard.
Rigid short words are handled separately; every other word duplicates its
own head, supplying the same guard on both sides of every joint identity.
-/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_15.Rank048Intersection

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [1, 0]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 1]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [0, 1, 2], Word.mk 0 [1, 2]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [1, 0, 0], Word.mk 0 [1, 1]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [1, 0, 2], Word.mk 0 [1, 1, 2]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [1, 2, 0, 1], Word.mk 0 [1, 2, 2]⟩
def law07 : Identity Nat := ⟨Word.mk 0 [1, 2, 0, 2], Word.mk 0 [1, 2, 2]⟩
def law08 : Identity Nat := ⟨Word.mk 0 [1, 2, 1, 0], Word.mk 0 [1, 2, 2]⟩
def law09 : Identity Nat := ⟨Word.mk 0 [1, 2, 2], Word.mk 0 [2, 1, 1]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09]

abbrev displayedBasisSHA256 : String :=
  "f7448164beb2dde4c6e47fd5abc05894bc007d9be5409e30d9c23da35c512c22"
abbrev leftTable : FiniteTable := Generated.S3_15.table
abbrev rightTable : FiniteTable := Generated.Catalogue.S5_240.table
abbrev lowerBasis : List (Identity Nat) := SemigroupBasis.CoRoots.S5_240.basis
abbrev LowerSignature := SemigroupBasis.CoRoots.S5_240.SameEndpointSuffixSignature

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_length : basis.length = 10 := by decide

theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)

theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

private def threeWords (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | _ => third

theorem derivesPower (block : Word Nat) :
    Derives basis (block ++ block) ((block ++ block) ++ block) := by
  have primitive : Derives basis law00.lhs law00.rhs :=
    Derives.fromBasis (e := law00) (by decide)
  have mapped := Derives.subst primitive (threeWords block block block)
  simpa [law00, threeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using mapped

theorem derivesLongInsertion (first second third : Word Nat) :
    Derives basis ((first ++ second) ++ third) (((first ++ first) ++ second) ++ third) := by
  have primitive : Derives basis law03.lhs law03.rhs :=
    Derives.fromBasis (e := law03) (by decide)
  have mapped := (Derives.subst primitive (threeWords first second third)).symm
  simpa [law03, threeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using mapped

/-- The lower marker switch is legal only behind the retained nonempty guard. -/
theorem derivesGuardedMarkerSwitch (guard first second : Word Nat) :
    Derives basis (guard ++ ((first ++ second) ++ second))
      (guard ++ ((second ++ first) ++ first)) := by
  have primitive : Derives basis law09.lhs law09.rhs :=
    Derives.fromBasis (e := law09) (by decide)
  have mapped := Derives.subst primitive (threeWords guard first second)
  simpa [law09, threeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using mapped

theorem guardedLowerAxiom (identity : Identity Nat) (member : identity ∈ lowerBasis)
    (substitution : Nat → Word Nat) (guard : Word Nat) :
    Derives basis (guard ++ identity.lhs.bind substitution)
      (guard ++ identity.rhs.bind substitution) := by
  simp only [lowerBasis, SemigroupBasis.CoRoots.S5_240.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · have literal : SemigroupBasis.CoRoots.S5_240.powerLaw =
        (⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.prepend guard (derivesPower (substitution 0))
  · have literal : SemigroupBasis.CoRoots.S5_240.markerSwitchLaw =
        (⟨Word.mk 0 [1, 1], Word.mk 1 [0, 0]⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      derivesGuardedMarkerSwitch guard (substitution 0) (substitution 1)
  · have literal : SemigroupBasis.CoRoots.S5_240.longInsertionLaw =
        (⟨Word.mk 0 [1, 2], Word.mk 0 [0, 1, 2]⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using Derives.prepend guard
        (derivesLongInsertion (substitution 0) (substitution 1) (substitution 2))

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

/-- Every lower derivation replays with an arbitrary nonempty leading guard. -/
theorem liftLowerWithPrefix {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (guard : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (guard ++ left.bind substitution) (guard ++ right.bind substitution) := by
  induction derivation generalizing guard substitution with
  | fromBasis member => exact guardedLowerAxiom _ member substitution guard
  | refl => exact Derives.refl _
  | symm _ induction => exact (induction guard substitution).symm
  | trans _ _ first second => exact (first guard substitution).trans (second guard substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (guard ++ stem.bind substitution) substitution
  | appendRight _ final induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (induction guard substitution) (final.bind substitution)
  | subst _ next induction =>
      simpa [bind_bind] using
        induction guard (fun letter => (next letter).bind substitution)

theorem derivesSamePrefixOfLowerValid (left right guard : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup) :
    Derives basis (guard ++ left) (guard ++ right) := by
  have lower := SemigroupBasis.CoRoots.S5_240.basis_complete.2 (Identity.mk left right) valid
  simpa [bind_singleton] using liftLowerWithPrefix lower guard Word.singleton

/-- A singleton's exact lower signature cannot equal that of another word. -/
theorem singletonRigid (letter : Nat) (word : Word Nat)
    (same : LowerSignature (Word.singleton letter) word) :
    Word.singleton letter = word := by
  have singletonRight := same.singleton.mp (show IsSingletonWord (Word.singleton letter) from trivial)
  cases splitEq : terminalSplit word with
  | singleton final =>
      have tested := (same.uniqueFinal letter).mp (show UniqueFinal (Word.singleton letter) letter from rfl)
      have finals : final = letter := by simpa [UniqueFinal, splitEq] using tested
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq] at reconstruct
      simpa [TerminalSplit.renderWord, finals] using reconstruct
  | pair stem penultimate final =>
      simp [IsSingletonWord, splitEq] at singletonRight

/-- Two distinct letters are rigid, even against arbitrarily long words. -/
theorem distinctPairRigid (first second : Nat) (different : first ≠ second)
    (word : Word Nat) (same : LowerSignature (Word.mk first [second]) word) :
    Word.mk first [second] = word := by
  have leftPair : SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
      (Word.mk first [second]) first second := by
    change first = first ∧ second = second ∧ first ∉ ([] : List Nat) ∧ second ≠ first
    simp [Ne.symm different]
  have leftFinal : UniqueFinal (Word.mk first [second]) second := by
    change second = second ∧ second ≠ first ∧ second ∉ ([] : List Nat)
    simp [Ne.symm different]
  have rightPair := (same.simplePenultimatePair first second).mp leftPair
  have rightFinal := (same.uniqueFinal second).mp leftFinal
  cases splitEq : terminalSplit word with
  | singleton final =>
      simp [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair, splitEq] at rightPair
  | pair stem penultimate final =>
      have parts : penultimate = first ∧ final = second ∧ first ∉ stem ∧ second ≠ first := by
        simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair, splitEq] using rightPair
      have finals : final = second ∧ final ≠ penultimate ∧ final ∉ stem := by
        simpa [UniqueFinal, splitEq] using rightFinal
      have stemNil : stem = [] := by
        cases stem with
        | nil => rfl
        | cons letter rest =>
            have member : letter ∈ word.toList := by
              rw [← terminalSplit_renderList word, splitEq]
              simp [TerminalSplit.renderList]
            have oldMember := (same.support letter).mpr member
            have either : letter = first ∨ letter = second := by
              simpa [Word.toList] using oldMember
            rcases either with equal | equal
            · exact False.elim (parts.2.2.1 (by simp [equal]))
            · exact False.elim (finals.2.2 (by simp [equal, finals.1]))
      have reconstruct := terminalSplit_renderWord word
      rw [splitEq, stemNil] at reconstruct
      simpa [TerminalSplit.renderWord, parts.1, parts.2.1, wordOfPrefixFinal,
        Word.append, Word.singleton] using reconstruct

/-- Exactly the potentially non-rigid strata admit a duplicate of their own head. -/
theorem headDuplicateOrRigid (word : Word Nat) :
    (∀ other, LowerSignature word other → word = other) ∨
      Derives basis word (Word.singleton word.head ++ word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          exact Or.inl (singletonRigid head)
      | cons second rest =>
          cases rest with
          | nil =>
              by_cases equal : head = second
              · subst second
                right
                simpa [Word.append, Word.singleton] using derivesPower (Word.singleton head)
              · exact Or.inl (distinctPairRigid head second equal)
          | cons third tail =>
              right
              simpa [Word.append, Word.singleton] using
                derivesLongInsertion (Word.singleton head) (Word.singleton second) (Word.mk third tail)

/-- Equal actual heads and lower validity suffice, at unrestricted rank/length. -/
theorem derivesOfHeadAndLowerValid (left right : Word Nat) (heads : left.head = right.head)
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup) :
    Derives basis left right := by
  have same := SemigroupBasis.CoRoots.S5_240.valid_signature (Identity.mk left right) valid
  rcases headDuplicateOrRigid left with rigid | duplicateLeft
  · rw [rigid right same]
    exact Derives.refl _
  · rcases headDuplicateOrRigid right with rigid | duplicateRight
    · rw [rigid left same.symm]
      exact Derives.refl _
    · have middle := derivesSamePrefixOfLowerValid left right (Word.singleton left.head) valid
      have duplicateRightSame : Derives basis right (Word.singleton left.head ++ right) := by
        simpa only [heads] using duplicateRight
      exact duplicateLeft.trans (middle.trans duplicateRightSame.symm)

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

/-- Full converse for the frozen ten-law basis, with no remaining owner hypothesis. -/
theorem complete : Complete := by
  intro identity leftValid rightValid
  have heads : identity.lhs.head = identity.rhs.head :=
    leftNormalBandFifteenValid_head_eq identity leftValid
  exact derivesOfHeadAndLowerValid identity.lhs identity.rhs heads rightValid

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := complete

abbrev FinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup

theorem basisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup basis :=
  intersectionBasis.basisFor pair

theorem oppositeBasisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup.opposite (reversedBasis basis) :=
  (basisForOfFinitePair target pair).oppositeReversed

end SemigroupBasis.CoRoots.Order6Day10.S3_15.Rank048Intersection
