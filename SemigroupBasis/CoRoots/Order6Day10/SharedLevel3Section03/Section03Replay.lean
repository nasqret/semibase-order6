import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.CoRoots.S5_831Family
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Exact direct B13 for S3_6 opposite with S5_831/S5_832 direct.
The entire lower two-law calculus replays only AFTER a nonempty prefix. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Replay

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [0, 1, 1]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 0], Word.mk 0 [0, 1, 2, 1]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 0]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 1]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 1, 0]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 0], Word.mk 0 [1, 0, 2, 1]⟩
def law07 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 0], Word.mk 0 [1, 1, 2, 0]⟩
def law08 : Identity Nat := ⟨Word.mk 0 [1, 2, 0], Word.mk 0 [1, 2, 0, 1]⟩
def law09 : Identity Nat := ⟨Word.mk 0 [1, 2, 0], Word.mk 0 [1, 2, 0, 2]⟩
def law10 : Identity Nat := ⟨Word.mk 0 [1, 2, 0], Word.mk 0 [1, 2, 1, 0]⟩
def law11 : Identity Nat := ⟨Word.mk 0 [1, 2, 0], Word.mk 0 [1, 2, 2, 0]⟩
def law12 : Identity Nat := ⟨Word.mk 0 [1, 2, 1], Word.mk 0 [1, 2, 2]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11, law12]
abbrev displayedBasisSHA256 : String := "e203d7a157f8204d27e25ea10aa85bdcb661a380fd31b239ce50065cb7d2e5b0"

def leftTable : FiniteTable where
  order := 3
  mul first second := Generated.S3_6.table.mul second first
  assoc := by decide
abbrev rightTable : FiniteTable := Generated.Catalogue.S5_831.table
abbrev alternateRightTable : FiniteTable := Generated.Catalogue.S5_832.table
abbrev lowerBasis := CoRoots.S5_831.basis
abbrev D := ListDerives basis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_length : basis.length = 13 := by decide
theorem leftTable_is_actual_opposite :
    leftTable.semigroup = Generated.S3_6.table.semigroup.opposite := rfl
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)
theorem modelsAlternateRight : Models alternateRightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound alternateRightTable basis toFinThree (by decide)
theorem lowerBasis_complete : BasisFor rightTable.semigroup lowerBasis :=
  CoRoots.S5_831Family.S5_831.basisFor
theorem alternateLowerBasis_complete : BasisFor alternateRightTable.semigroup lowerBasis :=
  CoRoots.S5_831Family.S5_832.basisFor

theorem rawPower (u : Word Nat) : Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by decide)
  have mapped := primitive.subst (fun _ => u)
  simpa [law00, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawReturnDuplicate (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have primitive : Derives basis law03.lhs law03.rhs := Derives.fromBasis (e := law03) (by decide)
  have mapped := primitive.subst (fun | 0 => u | _ => v)
  simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawReturnMiddleDuplicate (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ v) ++ u) := by
  have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by decide)
  have mapped := primitive.subst (fun | 0 => u | _ => v)
  simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawMarkerTransfer (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      ((((u ++ v) ++ v) ++ z) ++ u) := by
  have primitive : Derives basis law07.lhs law07.rhs := Derives.fromBasis (e := law07) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => z)
  simpa [law07, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem guardedCopy (guard u v : Word Nat) :
    Derives basis (guard ++ ((u ++ v) ++ u)) (guard ++ ((u ++ v) ++ v)) := by
  have primitive : Derives basis law12.lhs law12.rhs := Derives.fromBasis (e := law12) (by decide)
  have mapped := primitive.subst (fun | 0 => guard | 1 => u | _ => v)
  simpa [law12, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem lowerBasis_literal : lowerBasis =
    [⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩,
     ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 1]⟩] := by decide

theorem guardedLowerAxiom (identity : Identity Nat) (member : identity ∈ lowerBasis)
    (substitution : Nat → Word Nat) (guard : Word Nat) :
    Derives basis (guard ++ identity.lhs.bind substitution) (guard ++ identity.rhs.bind substitution) := by
  rw [lowerBasis_literal] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.prepend guard (rawPower (substitution 0))
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      guardedCopy guard (substitution 0) (substitution 1)

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

theorem liftLower {left right : Word Nat} (derivation : Derives lowerBasis left right)
    (guard : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (guard ++ left.bind substitution) (guard ++ right.bind substitution) := by
  induction derivation generalizing guard substitution with
  | fromBasis member => exact guardedLowerAxiom _ member substitution guard
  | refl => exact Derives.refl _
  | symm _ ih => exact (ih guard substitution).symm
  | trans _ _ first second => exact (first guard substitution).trans (second guard substitution)
  | prepend pre _ ih =>
      simpa [bind_append, Word.append_assoc] using ih (guard ++ pre.bind substitution) substitution
  | appendRight _ final ih =>
      simpa [bind_append, Word.append_assoc] using Derives.appendRight (ih guard substitution) (final.bind substitution)
  | subst _ next ih =>
      simpa [bind_bind] using ih guard (fun letter => (next letter).bind substitution)

theorem replayLower {left right : Word Nat} (derivation : Derives lowerBasis left right)
    (guard : Word Nat) : Derives basis (guard ++ left) (guard ++ right) := by
  simpa only [bind_singleton] using liftLower derivation guard Word.singleton

theorem replayLowerList {left right : List Nat}
    (derivation : ListDerives lowerBasis left right) (guard : Word Nat) :
    D (guard.toList ++ left) (guard.toList ++ right) := by
  cases derivation with
  | empty => simpa using (ListDerives.refl (basis := basis) guard.toList)
  | words derivation =>
      simpa [Word.toList_append, listWordOfCons, Word.toList] using
        ListDerives.ofWord (replayLower derivation guard)

theorem appendOldTail (head letter : Nat) (tail : List Nat) (member : letter ∈ tail) :
    D ((head :: tail) ++ [letter]) ((head :: tail) ++ [tail.getLastD letter]) := by
  simpa [Word.toList, Word.singleton] using
    replayLowerList (CoRoots.S5_831.listDerivesAppendOld tail letter member) (Word.singleton head)

theorem derivesSamePrefixOfLowerValid (left right guard : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup) :
    Derives basis (guard ++ left) (guard ++ right) :=
  replayLower (lowerBasis_complete.2 (Identity.mk left right) valid) guard

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section03.Section03Replay
