import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.Generated.S4_96
import SemigroupBasis.Generated.S4_96TransfersLayer1

/-! Exact B6 and unrestricted affine derivation replay AFTER a nonempty
prefix. A double copy of the common first letter is inserted and removed
using the displayed power law. No cancellation or extra bridge is used. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section06.Section06Replay

open SemigroupBasis

def law00 : Identity Nat := ⟨Word.mk 0 [], Word.mk 0 [0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 1], Word.mk 0 [1, 1, 0, 1]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [0, 1, 0, 1], Word.mk 0 [1, 0, 0, 1]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [0, 1, 1, 0], Word.mk 0 [1, 0, 1, 0]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [1, 2], Word.mk 0 [2, 2, 1, 2]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [1, 2, 1, 2], Word.mk 0 [2, 1, 1, 2]⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05]
abbrev displayedBasisSHA256 : String := "5d7e4876c5ebae2f77124bea8dff165b3e007ce7fe569c9bc0fc4f9fcd36df41"
abbrev leftTable : FiniteTable := Generated.S2_4.table
abbrev rightTable : FiniteTable := Generated.S4_96.table
abbrev alternateLeftTable : FiniteTable := Generated.S2_4.table
abbrev alternateRightTable : FiniteTable := Generated.Catalogue.S5_997.table
abbrev replayBasis := Examples.affineParityFourBasis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_length : basis.length = 6 := by decide
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)
theorem modelsAlternateLeft : Models alternateLeftTable.semigroup basis := modelsLeft
theorem modelsAlternateRight : Models alternateRightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound alternateRightTable basis toFinThree (by decide)
theorem leftBasis_complete : BasisFor leftTable.semigroup Examples.leftZeroBasis :=
  Generated.S2_4.representative_basis
theorem rightBasis_complete : BasisFor rightTable.semigroup replayBasis :=
  Generated.S4_96.representative_basis
theorem alternateLeftBasis_complete : BasisFor alternateLeftTable.semigroup Examples.leftZeroBasis :=
  Generated.S2_4.representative_basis
theorem alternateRightBasis_complete : BasisFor alternateRightTable.semigroup replayBasis :=
  Generated.S4_96Transfers.S5_997.representative_basis

theorem rawLaw00 (u : Word Nat) : Derives basis u ((u ++ u) ++ u) := by
  have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by decide)
  have mapped := primitive.subst (fun _ => u)
  simpa [law00, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw01 (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v) ((((u ++ v) ++ v) ++ u) ++ v) := by
  have primitive : Derives basis law01.lhs law01.rhs := Derives.fromBasis (e := law01) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw02 (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ u) ++ v) ((((u ++ v) ++ u) ++ u) ++ v) := by
  have primitive : Derives basis law02.lhs law02.rhs := Derives.fromBasis (e := law02) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw03 (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ v) ++ u) ((((u ++ v) ++ u) ++ v) ++ u) := by
  have primitive : Derives basis law03.lhs law03.rhs := Derives.fromBasis (e := law03) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw04 (u v w : Word Nat) :
    Derives basis ((u ++ v) ++ w) ((((u ++ w) ++ w) ++ v) ++ w) := by
  have primitive : Derives basis law04.lhs law04.rhs := Derives.fromBasis (e := law04) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law04, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw05 (u v w : Word Nat) :
    Derives basis ((((u ++ v) ++ w) ++ v) ++ w) ((((u ++ w) ++ v) ++ v) ++ w) := by
  have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem guardedPower (initial u : Word Nat) :
    Derives basis (initial ++ u) (initial ++ ((u ++ u) ++ u)) :=
  Derives.prepend initial (rawLaw00 u)

theorem guardedSquareReturn (initial u v : Word Nat) :
    Derives basis (initial ++ (((u ++ u) ++ v) ++ u)) (initial ++ (v ++ u)) := by
  simpa only [Word.append_assoc] using (rawLaw04 initial v u).symm

theorem guardedMiddleSquare (initial u v : Word Nat) :
    Derives basis (initial ++ (((u ++ v) ++ v) ++ u)) (initial ++ (((v ++ u) ++ v) ++ u)) := by
  simpa only [Word.append_assoc] using (rawLaw05 initial v u).symm

theorem replayBasis_literal : replayBasis =
    [⟨Word.mk 0 [], Word.mk 0 [0, 0]⟩,
     ⟨Word.mk 0 [0, 1, 0], Word.mk 1 [0]⟩,
     ⟨Word.mk 0 [1, 1, 0], Word.mk 1 [0, 1, 0]⟩] := by decide

theorem guardedReplayAxiom (identity : Identity Nat) (member : identity ∈ replayBasis)
    (substitution : Nat → Word Nat) (initial : Word Nat) :
    Derives basis (initial ++ identity.lhs.bind substitution) (initial ++ identity.rhs.bind substitution) := by
  rw [replayBasis_literal] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using guardedPower initial (substitution 0)
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      guardedSquareReturn initial (substitution 0) (substitution 1)
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      guardedMiddleSquare initial (substitution 0) (substitution 1)

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
    (initial : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (initial ++ left.bind substitution) (initial ++ right.bind substitution) := by
  induction derivation generalizing initial substitution with
  | fromBasis member => exact guardedReplayAxiom _ member substitution initial
  | refl => exact Derives.refl _
  | symm _ ih => exact (ih initial substitution).symm
  | trans _ _ first second => exact (first initial substitution).trans (second initial substitution)
  | prepend pre _ ih =>
      simpa [bind_append, Word.append_assoc] using ih (initial ++ pre.bind substitution) substitution
  | appendRight _ final ih =>
      simpa [bind_append, Word.append_assoc] using Derives.appendRight (ih initial substitution) (final.bind substitution)
  | subst _ next ih =>
      simpa [bind_bind] using ih initial (fun letter => (next letter).bind substitution)

theorem liftReplayIdentity {left right : Word Nat} (derivation : Derives replayBasis left right)
    (initial : Word Nat) : Derives basis (initial ++ left) (initial ++ right) := by
  simpa [bind_singleton] using liftReplay derivation initial Word.singleton

theorem derivesHeadDoubleExpansion (word : Word Nat) :
    Derives basis word ((Word.singleton word.head ++ Word.singleton word.head) ++ word) := by
  rcases word with ⟨first, tail⟩
  cases tail with
  | nil => simpa [Word.singleton, Word.append] using rawLaw00 (Word.singleton first)
  | cons second rest =>
      simpa [Word.singleton, Word.append, Word.append_assoc] using
        Derives.appendRight (rawLaw00 (Word.singleton first)) (Word.mk second rest)

theorem derivesOfHeadAndAffine (left right : Word Nat)
    (heads : left.head = right.head) (affine : Derives replayBasis left right) :
    Derives basis left right := by
  let initial := Word.singleton left.head ++ Word.singleton left.head
  have first : Derives basis left (initial ++ left) := derivesHeadDoubleExpansion left
  have finalStep : Derives basis right (initial ++ right) := by
    simpa [initial, heads] using derivesHeadDoubleExpansion right
  exact first.trans ((liftReplayIdentity affine initial).trans finalStep.symm)

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section06.Section06Replay
