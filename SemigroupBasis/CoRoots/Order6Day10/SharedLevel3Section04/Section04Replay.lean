import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S2_3
import SemigroupBasis.Generated.S3_4
import SemigroupBasis.CoRoots.S5_526
import SemigroupBasis.CoRoots.S5_830
import SemigroupBasis.Generated.SquareFreeDoubledHeadFiveTransfersLayer1

/-! Exact B8, full S5_830 Derives replay BEFORE a nonempty suffix, and
explicit terminal-head padding for all words of length at least three.
Preproof gates: 2465 models, 549 B8 models, fresh broad and linear-four clean.
No actual factor converse or class endpoint is asserted by this module. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section04.Section04Replay

open SemigroupBasis

def law00 : Identity Nat := ⟨Word.mk 0 [0, 0], Word.mk 0 [0, 0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 0, 1], Word.mk 0 [0, 1]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [0, 1], Word.mk 0 [0, 1, 0]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [0, 1], Word.mk 0 [0, 1, 1]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [0, 1, 2], Word.mk 0 [0, 2, 1]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 0]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 1]⟩
def law07 : Identity Nat := ⟨Word.mk 0 [1, 0, 2], Word.mk 0 [1, 2]⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06, law07]
abbrev displayedBasisSHA256 : String := "97669b62097df325d3729fa64a1c68612db50398ef95416373328f469a1a2dbb"
abbrev leftTable : FiniteTable := Generated.S2_3.table
abbrev rightTable : FiniteTable := CoRoots.S5_526.table
abbrev alternateLeftTable : FiniteTable := Generated.S3_4.table
abbrev alternateRightTable : FiniteTable := Generated.Catalogue.S5_904.table
abbrev replayBasis := CoRoots.S5_830.basis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_length : basis.length = 8 := by decide
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)
theorem modelsAlternateLeft : Models alternateLeftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound alternateLeftTable basis toFinThree (by decide)
theorem modelsAlternateRight : Models alternateRightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound alternateRightTable basis toFinThree (by decide)
theorem leftBasis_complete : BasisFor leftTable.semigroup Examples.semilatticeBasis :=
  Generated.S2_3.representative_basis
theorem rightBasis_complete : BasisFor rightTable.semigroup CoRoots.S5_526.basis :=
  CoRoots.S5_526.representative_basis
theorem alternateLeftBasis_complete :
    BasisFor alternateLeftTable.semigroup Examples.projectionQuadraticThreeBasis :=
  Generated.S3_4.representative_basis
theorem alternateRightBasis_complete : BasisFor alternateRightTable.semigroup replayBasis :=
  Generated.SquareFreeDoubledHeadFiveTransfers.S5_904.representative_basis

theorem guardedSquare (u guard : Word Nat) :
    Derives basis ((u ++ u) ++ guard) (((u ++ u) ++ u) ++ guard) := by
  have primitive : Derives basis law01.lhs law01.rhs := Derives.fromBasis (e := law01) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => guard | _ => Word.singleton 0)
  simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped.symm

theorem guardedReturn (u v guard : Word Nat) :
    Derives basis ((u ++ v) ++ guard) (((u ++ v) ++ u) ++ guard) := by
  have primitive : Derives basis law07.lhs law07.rhs := Derives.fromBasis (e := law07) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => guard | _ => Word.singleton 0)
  simpa [law07, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped.symm

theorem rawDoubledPrefixSwap (u v w : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ w) (((u ++ u) ++ w) ++ v) := by
  have primitive : Derives basis law04.lhs law04.rhs := Derives.fromBasis (e := law04) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law04, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

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
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      guardedSquare (substitution 0) guard
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      guardedReturn (substitution 0) (substitution 1) guard
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.appendRight (rawDoubledPrefixSwap (substitution 0) (substitution 1) (substitution 2)) guard

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

theorem guardedBlockSquare (p q guard : Word Nat) :
    Derives basis (((p ++ q) ++ (p ++ q)) ++ guard) ((p ++ q) ++ guard) :=
  liftReplayIdentity (CoRoots.S5_830.derivesBlockSquareContraction p q) guard

theorem tailSwap (p q u v : Word Nat) :
    Derives basis (((p ++ q) ++ u) ++ v) (((p ++ q) ++ v) ++ u) := by
  have first : Derives basis (((p ++ q) ++ u) ++ v)
      ((((p ++ q) ++ (p ++ q)) ++ u) ++ v) := by
    simpa only [Word.append_assoc] using (guardedBlockSquare p q (u ++ v)).symm
  have second : Derives basis ((((p ++ q) ++ (p ++ q)) ++ u) ++ v)
      ((((p ++ q) ++ (p ++ q)) ++ v) ++ u) := rawDoubledPrefixSwap (p ++ q) u v
  have third : Derives basis ((((p ++ q) ++ (p ++ q)) ++ v) ++ u)
      (((p ++ q) ++ v) ++ u) := by
    simpa only [Word.append_assoc] using guardedBlockSquare p q (v ++ u)
  exact first.trans (second.trans third)

theorem appendFirstToThreeBlocks (p q r : Word Nat) :
    Derives basis ((p ++ q) ++ r) (((p ++ q) ++ r) ++ p) := by
  have first : Derives basis ((p ++ q) ++ r) (((p ++ q) ++ p) ++ r) := guardedReturn p q r
  have second : Derives basis (((p ++ q) ++ p) ++ r) (((p ++ q) ++ r) ++ p) := tailSwap p q p r
  exact first.trans second

theorem derivesAppendHead (word : Word Nat) (long : 3 ≤ word.toList.length) :
    Derives basis word (word ++ Word.singleton word.head) := by
  rcases word with ⟨first, tail⟩
  cases tail with
  | nil => simp [Word.toList] at long
  | cons second rest =>
      cases rest with
      | nil => simp [Word.toList] at long
      | cons third more =>
          simpa [Word.singleton, Word.append, List.append_assoc] using
            appendFirstToThreeBlocks (Word.singleton first) (Word.singleton second) (Word.mk third more)

theorem derivesOfLongData (left right : Word Nat)
    (leftLong : 3 ≤ left.toList.length) (rightLong : 3 ≤ right.toList.length)
    (prefixEq : CoRoots.S5_830.FirstTwo left = CoRoots.S5_830.FirstTwo right)
    (support : CoRoots.S5_830.SameSupport left right) : Derives basis left right := by
  have heads : left.head = right.head := by
    have same := congrArg List.head? prefixEq
    simpa [CoRoots.S5_830.FirstTwo, Word.toList] using same
  have replay := CoRoots.S5_830.derivesOfFirstTwoSupportEq left right (by omega) (by omega) prefixEq support
  have middle := liftReplayIdentity replay (Word.singleton left.head)
  have first := derivesAppendHead left leftLong
  have last := derivesAppendHead right rightLong
  rw [← heads] at last
  exact first.trans (middle.trans last.symm)

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section04.Section04Replay
