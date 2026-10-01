import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.CoRoots.S5_869Family
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Exact direct B13. Every lower-basis derivation is replayed BEFORE ONE
nonempty suffix block, with explicit displayed-law edges. The lower calculus
is not silently retargeted without that suffix. -/

namespace SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section02.Section02Replay

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [0, 1, 1]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 0], Word.mk 0 [0, 1, 2, 1]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 0], Word.mk 0 [0, 1, 2, 2]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 0]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 1]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 1, 0]⟩
def law07 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 0], Word.mk 0 [1, 0, 2, 1]⟩
def law08 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 0], Word.mk 0 [1, 0, 2, 2]⟩
def law09 : Identity Nat := ⟨Word.mk 0 [1, 1, 2], Word.mk 0 [1, 2]⟩
def law10 : Identity Nat := ⟨Word.mk 0 [1, 2, 0], Word.mk 0 [1, 2, 0, 1]⟩
def law11 : Identity Nat := ⟨Word.mk 0 [1, 2, 0], Word.mk 0 [1, 2, 0, 2]⟩
def law12 : Identity Nat := ⟨Word.mk 0 [1, 2, 0], Word.mk 0 [1, 2, 1, 0]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11, law12]
abbrev displayedBasisSHA256 : String := "c1dd96ab480c62c4655efc0c141eafa7169d379fb5d5e77bab593433c5809687"
abbrev leftTable : FiniteTable := Generated.S3_6.table
abbrev rightTable : FiniteTable := Generated.Catalogue.S5_869.table
abbrev alternateRightTable : FiniteTable := Generated.Catalogue.S5_871.table
abbrev lowerBasis := CoRoots.S5_869.basis
abbrev D := ListDerives basis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_length : basis.length = 13 := by decide
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)
theorem modelsAlternateRight : Models alternateRightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound alternateRightTable basis toFinThree (by decide)
theorem leftBasis_complete : BasisFor leftTable.semigroup finalMarkerThreeBasis :=
  Generated.S3_6.representative_basis
theorem lowerBasis_complete : BasisFor rightTable.semigroup lowerBasis :=
  CoRoots.S5_869Family.S5_869.basis_complete
theorem alternateLowerBasis_complete : BasisFor alternateRightTable.semigroup lowerBasis :=
  CoRoots.S5_869Family.S5_871.basis_complete

theorem rawPower (u : Word Nat) : Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by decide)
  have mapped := primitive.subst (fun _ => u)
  simpa [law00, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem guardedPower (u guard : Word Nat) :
    Derives basis ((u ++ u) ++ guard) (((u ++ u) ++ u) ++ guard) :=
  Derives.appendRight (rawPower u) guard

theorem guardedDuplication (u v guard : Word Nat) :
    Derives basis ((u ++ v) ++ guard) (((u ++ v) ++ v) ++ guard) := by
  have primitive : Derives basis law09.lhs law09.rhs := Derives.fromBasis (e := law09) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => guard | _ => Word.singleton 0)
  simpa [law09, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped.symm

theorem guardedSquaredPrefix (u v guard : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ guard) ((((u ++ u) ++ v) ++ u) ++ guard) := by
  have first : Derives basis (((u ++ u) ++ v) ++ guard)
      ((((u ++ u) ++ v) ++ v) ++ guard) := guardedDuplication (u ++ u) v guard
  have second : Derives basis ((((u ++ u) ++ v) ++ v) ++ guard)
      ((((u ++ u) ++ v) ++ u) ++ guard) := by
    have primitive : Derives basis law01.lhs law01.rhs := Derives.fromBasis (e := law01) (by decide)
    have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
    simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.appendRight mapped.symm guard
  exact first.trans second

theorem guardedInitialGap (u v z guard : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ guard)
      (((((u ++ v) ++ u) ++ z) ++ u) ++ guard) := by
  have first : Derives basis ((((u ++ v) ++ u) ++ z) ++ guard)
      (((((u ++ v) ++ u) ++ z) ++ z) ++ guard) := guardedDuplication ((u ++ v) ++ u) z guard
  have second : Derives basis (((((u ++ v) ++ u) ++ z) ++ z) ++ guard)
      (((((u ++ v) ++ u) ++ z) ++ u) ++ guard) := by
    have primitive : Derives basis law08.lhs law08.rhs := Derives.fromBasis (e := law08) (by decide)
    have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => z | _ => Word.singleton 0)
    simpa [law08, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.appendRight mapped.symm guard
  exact first.trans second

theorem lowerBasis_literal : lowerBasis =
    [⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩,
     ⟨Word.mk 0 [1], Word.mk 0 [1, 1]⟩,
     ⟨Word.mk 0 [0, 1], Word.mk 0 [0, 1, 0]⟩,
     ⟨Word.mk 0 [1, 0, 2], Word.mk 0 [1, 0, 2, 0]⟩] := by decide

theorem guardedLowerAxiom (identity : Identity Nat) (member : identity ∈ lowerBasis)
    (substitution : Nat → Word Nat) (guard : Word Nat) :
    Derives basis (identity.lhs.bind substitution ++ guard) (identity.rhs.bind substitution ++ guard) := by
  rw [lowerBasis_literal] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using guardedPower (substitution 0) guard
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using guardedDuplication (substitution 0) (substitution 1) guard
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using guardedSquaredPrefix (substitution 0) (substitution 1) guard
  · simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using guardedInitialGap (substitution 0) (substitution 1) (substitution 2) guard

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
    Derives basis (left.bind substitution ++ guard) (right.bind substitution ++ guard) := by
  induction derivation generalizing guard substitution with
  | fromBasis member => exact guardedLowerAxiom _ member substitution guard
  | refl => exact Derives.refl _
  | symm _ ih => exact (ih guard substitution).symm
  | trans _ _ first second => exact (first guard substitution).trans (second guard substitution)
  | prepend pre _ ih =>
      simpa [bind_append, Word.append_assoc] using Derives.prepend (pre.bind substitution) (ih guard substitution)
  | appendRight _ final ih =>
      simpa [bind_append, Word.append_assoc] using ih (final.bind substitution ++ guard) substitution
  | subst _ next ih =>
      simpa [bind_bind] using ih guard (fun letter => (next letter).bind substitution)

theorem derivesSameSuffixOfLowerValid (left right guard : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup) :
    Derives basis (left ++ guard) (right ++ guard) := by
  have derived := lowerBasis_complete.2 (Identity.mk left right) valid
  simpa [bind_singleton] using liftLower derived guard Word.singleton

/-- Absorption is first proved in the actual lower calculus; a B13 consumer
must retain the suffix supplied by liftLower. A noninitial occurrence is used. -/
theorem lowerAbsorbTailMember (word : Word Nat) (m : Nat) (member : m ∈ word.tail) :
    Derives lowerBasis (word ++ Word.singleton m) word := by
  cases word with
  | mk head tail =>
      obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp member
      cases post with
      | nil =>
          simpa [Word.singleton, Word.append, List.append_assoc] using
            CoRoots.S5_869.derivesTailContraction (Word.mk head pre) (Word.singleton m)
      | cons q qs =>
          have shape : (Word.mk head pre ++ Word.singleton m) ++ Word.mk q qs =
              Word.mk head (pre ++ m :: q :: qs) := by
            apply Word.toList_injective
            simp [Word.toList, List.append_assoc]
          simpa only [shape] using CoRoots.S5_869.derivesNoninitialRepeatDeletion
            (Word.mk head pre) (Word.singleton m) (Word.mk q qs)

theorem rawReturnDuplicate (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have primitive : Derives basis law04.lhs law04.rhs := Derives.fromBasis (e := law04) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law04, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawReturnRepeat (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ v) := by
  have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawReturnPrefixExtension (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u) ((((u ++ v) ++ z) ++ u) ++ v) := by
  have primitive : Derives basis law10.lhs law10.rhs := Derives.fromBasis (e := law10) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => z | _ => Word.singleton 0)
  simpa [law10, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawSquareFinalSwitch (m t : Word Nat) :
    Derives basis (((m ++ m) ++ t) ++ t) (((m ++ m) ++ t) ++ m) := by
  have primitive : Derives basis law01.lhs law01.rhs := Derives.fromBasis (e := law01) (by decide)
  have mapped := primitive.subst (fun | 0 => m | 1 => t | _ => Word.singleton 0)
  simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped.symm

end SemigroupBasis.CoRoots.Order6Day10.SharedLevel3Section02.Section02Replay
