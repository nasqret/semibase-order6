import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.Generated.S4_77
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.CoRoots.S5_830
import SemigroupBasis.Generated.SquareFreeDoubledHeadFiveTransfersLayer1

/-! Exact B6 and the full S5_830 derivation grammar before one nonempty
suffix. Every displayed law is retained and explicitly instantiated.
The final letter is duplicated, never erased or cancelled. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section05.Section05Replay

open SemigroupBasis

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 1, 2], Word.mk 0 [0, 2, 1, 2]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 0], Word.mk 0 [0, 2, 1, 0]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [1], Word.mk 0 [1, 0, 1]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [1], Word.mk 0 [1, 1]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [1, 0, 2], Word.mk 0 [1, 2]⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05]
abbrev displayedBasisSHA256 : String := "deaac1ae4fce1036d3b26fdc8fce660957e91a690182b97c99ed03dec95b1c51"

def leftTable : FiniteTable where
  order := 3
  mul first second := Generated.S3_15.table.mul second first
  assoc := by decide
abbrev rightTable : FiniteTable := Generated.S4_77.table
def alternateLeftTable : FiniteTable where
  order := 2
  mul first second := Generated.S2_4.table.mul second first
  assoc := by decide
abbrev alternateRightTable : FiniteTable := Generated.Catalogue.S5_904.table
abbrev replayBasis := CoRoots.S5_830.basis

theorem leftTable_is_actual_opposite :
    leftTable.semigroup = Generated.S3_15.table.semigroup.opposite := rfl
theorem alternateLeftTable_is_actual_opposite :
    alternateLeftTable.semigroup = Generated.S2_4.table.semigroup.opposite := rfl

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_length : basis.length = 6 := by decide
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)
theorem modelsAlternateLeft : Models alternateLeftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound alternateLeftTable basis toFinThree (by decide)
theorem modelsAlternateRight : Models alternateRightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound alternateRightTable basis toFinThree (by decide)
theorem leftBasis_complete :
    BasisFor leftTable.semigroup (reversedBasis Examples.leftNormalBandThreeBasis) :=
  Generated.S3_15.opposite_basis
theorem rightBasis_complete : BasisFor rightTable.semigroup Examples.twoLetterPrefixBasis :=
  Generated.S4_77.representative_basis
theorem alternateLeftBasis_complete : BasisFor alternateLeftTable.semigroup Examples.rightZeroBasis :=
  Generated.S2_4.opposite_basis
theorem alternateRightBasis_complete : BasisFor alternateRightTable.semigroup replayBasis :=
  Generated.SquareFreeDoubledHeadFiveTransfers.S5_904.representative_basis

theorem rawLaw00 (u : Word Nat) : Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by decide)
  have mapped := primitive.subst (fun _ => u)
  simpa [law00, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw01 (u v w : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ w) ((((u ++ u) ++ w) ++ v) ++ w) := by
  have primitive : Derives basis law01.lhs law01.rhs := Derives.fromBasis (e := law01) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw02 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ w) ++ u) ((((u ++ u) ++ w) ++ v) ++ u) := by
  have primitive : Derives basis law02.lhs law02.rhs := Derives.fromBasis (e := law02) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw03 (u v : Word Nat) :
    Derives basis (u ++ v) (((u ++ v) ++ u) ++ v) := by
  have primitive : Derives basis law03.lhs law03.rhs := Derives.fromBasis (e := law03) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw04 (u v : Word Nat) : Derives basis (u ++ v) ((u ++ v) ++ v) := by
  have primitive : Derives basis law04.lhs law04.rhs := Derives.fromBasis (e := law04) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law04, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw05 (u v w : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ w) ((u ++ v) ++ w) := by
  have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem guardedSquare (u guard : Word Nat) :
    Derives basis ((u ++ u) ++ guard) (((u ++ u) ++ u) ++ guard) :=
  (rawLaw00 u).appendRight guard

theorem guardedReturn (u v guard : Word Nat) :
    Derives basis ((u ++ v) ++ guard) (((u ++ v) ++ u) ++ guard) :=
  (rawLaw05 u v guard).symm

theorem guardedSwapInsert (u v w guard : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ w) ++ guard)
      (((((u ++ u) ++ w) ++ v) ++ w) ++ guard) :=
  (rawLaw01 u v w).appendRight guard

theorem guardedSwapDelete (u v w guard : Word Nat) :
    Derives basis (((((u ++ u) ++ w) ++ v) ++ w) ++ guard)
      ((((u ++ u) ++ w) ++ v) ++ guard) := by
  simpa only [Word.append_assoc] using Derives.prepend (u ++ u) (rawLaw05 w v guard)

theorem guardedDoubledPrefixSwap (u v w guard : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ w) ++ guard)
      ((((u ++ u) ++ w) ++ v) ++ guard) :=
  (guardedSwapInsert u v w guard).trans (guardedSwapDelete u v w guard)

theorem replayBasis_literal : replayBasis =
    [⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩,
     ⟨Word.mk 0 [1], Word.mk 0 [1, 0]⟩,
     ⟨Word.mk 0 [0, 1, 2], Word.mk 0 [0, 2, 1]⟩] := by decide

theorem guardedReplayAxiom (identity : Identity Nat) (member : identity ∈ replayBasis)
    (substitution : Nat → Word Nat) (guard : Word Nat) :
    Derives basis (identity.lhs.bind substitution ++ guard) (identity.rhs.bind substitution ++ guard) := by
  rw [replayBasis_literal] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using guardedSquare (substitution 0) guard
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      guardedReturn (substitution 0) (substitution 1) guard
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      guardedDoubledPrefixSwap (substitution 0) (substitution 1) (substitution 2) guard

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

theorem liftReplay {left right : Word Nat} (derivation : Derives replayBasis left right)
    (guard : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (left.bind substitution ++ guard) (right.bind substitution ++ guard) := by
  induction derivation generalizing guard substitution with
  | fromBasis member => exact guardedReplayAxiom _ member substitution guard
  | refl => exact Derives.refl _
  | symm _ ih => exact (ih guard substitution).symm
  | trans _ _ first second => exact (first guard substitution).trans (second guard substitution)
  | prepend pre _ ih =>
      simpa [bind_append, Word.append_assoc] using Derives.prepend (pre.bind substitution) (ih guard substitution)
  | appendRight _ final ih =>
      simpa [bind_append, Word.append_assoc] using ih (final.bind substitution ++ guard) substitution
  | subst _ next ih =>
      simpa [bind_bind] using ih guard (fun letter => (next letter).bind substitution)

theorem liftReplayIdentity {left right : Word Nat} (derivation : Derives replayBasis left right)
    (guard : Word Nat) : Derives basis (left ++ guard) (right ++ guard) := by
  simpa [bind_singleton] using liftReplay derivation guard Word.singleton

def Last (word : Word Nat) : Nat := word.reverse.head

theorem last_cons (first second : Nat) (rest : List Nat) :
    Last (Word.mk first (second :: rest)) = Last (Word.mk second rest) := rfl

theorem derivesAppendLastAux (first second : Nat) (rest : List Nat) :
    Derives basis (Word.mk first (second :: rest))
      (Word.mk first (second :: rest) ++ Word.singleton (Last (Word.mk first (second :: rest)))) := by
  induction rest generalizing first second with
  | nil =>
      simpa [Last, Word.reverse, Word.reverseAux, Word.singleton, Word.append] using
        rawLaw04 (Word.singleton first) (Word.singleton second)
  | cons third more ih =>
      simpa [Word.singleton, Word.append, List.append_assoc, last_cons] using
        Derives.prepend (Word.singleton first) (ih second third)

theorem derivesAppendLast (word : Word Nat) (long : 2 ≤ word.toList.length) :
    Derives basis word (word ++ Word.singleton (Last word)) := by
  rcases word with ⟨first, tail⟩
  cases tail with
  | nil => simp [Word.toList] at long
  | cons second rest => exact derivesAppendLastAux first second rest

theorem derivesOfLongData (left right : Word Nat)
    (leftLong : 2 ≤ left.toList.length) (rightLong : 2 ≤ right.toList.length)
    (prefixEq : CoRoots.S5_830.FirstTwo left = CoRoots.S5_830.FirstTwo right)
    (support : CoRoots.S5_830.SameSupport left right) (lastEq : Last left = Last right) :
    Derives basis left right := by
  have replay := CoRoots.S5_830.derivesOfFirstTwoSupportEq left right leftLong rightLong prefixEq support
  have middle := liftReplayIdentity replay (Word.singleton (Last left))
  have first := derivesAppendLast left leftLong
  have finalStep := derivesAppendLast right rightLong
  rw [← lastEq] at finalStep
  exact first.trans (middle.trans finalStep.symm)

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section05.Section05Replay
