import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.CoRoots.S5_523

/-! Exact B7 guarded replay for S3_15 direct / S5_539 opposite.
The 2465-table screen passed over 801 basis models before this source.
Five complete-lower axioms replay behind an arbitrary nonempty guard;
all ten concrete displayed-law edges use typed intermediates and decide membership.
This module alone does not assert the joint converse. -/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_15.Rank104Replay

open SemigroupBasis

def law00 : Identity Nat := ⟨Word.mk 0 [0, 0], Word.mk 0 [0, 0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 0, 1], Word.mk 0 [0, 1]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [0, 1], Word.mk 0 [1, 0, 1]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [0, 1], Word.mk 0 [1, 1]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [1, 0]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [0, 1, 2], Word.mk 0 [1, 2]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [1, 2], Word.mk 0 [2, 1, 2]⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06]

abbrev displayedBasisSHA256 : String := "947d9ea41e9770e5bcbd53753cbc4131b9661e3615e2202b934146f88df9a79b"
abbrev leftTable : FiniteTable := Generated.S3_15.table
def rightTable : FiniteTable where
  order := 5
  mul first second := Generated.Catalogue.S5_539.table.mul second first
  assoc := by decide

theorem rightTable_is_actual_opposite :
    rightTable.semigroup = Generated.Catalogue.S5_539.table.semigroup.opposite := rfl

abbrev lowerBasis : List (Identity Nat) := SemigroupBasis.CoRoots.S5_523.expectedOppositeBasis

theorem lowerBasis_complete : BasisFor rightTable.semigroup lowerBasis :=
  SemigroupBasis.CoRoots.S5_523.sibling_opposite_basis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_length : basis.length = 7 := by decide
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

theorem guarded_00 : Derives basis (Word.mk 3 [0, 0, 0]) (Word.mk 3 [0, 0, 0, 0]) := by
  have step0 : Derives basis (Word.mk 3 [0, 0, 0]) (Word.mk 3 [0, 0, 0, 0]) := by
    have primitive : Derives basis law00.lhs law00.rhs :=
      Derives.fromBasis (e := law00) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law00, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.prepend (Word.mk 3 []) mapped)
  exact step0

theorem guarded_01 : Derives basis (Word.mk 3 [1, 0, 0]) (Word.mk 3 [0, 1, 0]) := by
  have step0 : Derives basis (Word.mk 3 [1, 0, 0]) (Word.mk 3 [1, 1, 0]) := by
    have primitive : Derives basis law03.lhs law03.rhs :=
      Derives.fromBasis (e := law03) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 1 [])
        | 1 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.prepend (Word.mk 3 []) mapped.symm)
  have step1 : Derives basis (Word.mk 3 [1, 1, 0]) (Word.mk 3 [3, 1, 0]) := by
    have primitive : Derives basis law03.lhs law03.rhs :=
      Derives.fromBasis (e := law03) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 3 [])
        | 1 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 0 []))
  have step2 : Derives basis (Word.mk 3 [3, 1, 0]) (Word.mk 3 [1, 0]) := by
    have primitive : Derives basis law05.lhs law05.rhs :=
      Derives.fromBasis (e := law05) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 3 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  have step3 : Derives basis (Word.mk 3 [1, 0]) (Word.mk 3 [0, 1, 0]) := by
    have primitive : Derives basis law06.lhs law06.rhs :=
      Derives.fromBasis (e := law06) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 3 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law06, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  exact step0.trans (step1.trans (step2.trans (step3)))

theorem guarded_02 : Derives basis (Word.mk 3 [1, 0, 0]) (Word.mk 3 [1, 1, 0]) := by
  have step0 : Derives basis (Word.mk 3 [1, 0, 0]) (Word.mk 3 [1, 1, 0]) := by
    have primitive : Derives basis law03.lhs law03.rhs :=
      Derives.fromBasis (e := law03) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 1 [])
        | 1 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.prepend (Word.mk 3 []) mapped.symm)
  exact step0

theorem guarded_03 : Derives basis (Word.mk 3 [1, 0, 0]) (Word.mk 3 [1, 0, 0, 0]) := by
  have step0 : Derives basis (Word.mk 3 [1, 0, 0]) (Word.mk 3 [1, 0, 0, 0]) := by
    have primitive : Derives basis law06.lhs law06.rhs :=
      Derives.fromBasis (e := law06) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 3 [1])
        | 1 => (Word.mk 0 [])
        | 2 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law06, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  exact step0

theorem guarded_04 : Derives basis (Word.mk 3 [2, 1, 0]) (Word.mk 3 [2, 1, 0, 0]) := by
  have step0 : Derives basis (Word.mk 3 [2, 1, 0]) (Word.mk 3 [2, 2, 1, 0]) := by
    have primitive : Derives basis law05.lhs law05.rhs :=
      Derives.fromBasis (e := law05) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 2 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.prepend (Word.mk 3 []) mapped.symm)
  have step1 : Derives basis (Word.mk 3 [2, 2, 1, 0]) (Word.mk 3 [2, 1, 1, 0]) := by
    have primitive : Derives basis law03.lhs law03.rhs :=
      Derives.fromBasis (e := law03) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 2 [])
        | 1 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight (Derives.prepend (Word.mk 3 []) mapped) (Word.mk 0 []))
  have step2 : Derives basis (Word.mk 3 [2, 1, 1, 0]) (Word.mk 3 [2, 1, 0, 0]) := by
    have primitive : Derives basis law03.lhs law03.rhs :=
      Derives.fromBasis (e := law03) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 1 [])
        | 1 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.prepend (Word.mk 3 [2]) mapped)
  exact step0.trans (step1.trans (step2))

theorem lowerBasis_literal : lowerBasis =
  [⟨Word.mk 0 [0, 0], Word.mk 0 [0, 0, 0]⟩,
    ⟨Word.mk 1 [0, 0], Word.mk 0 [1, 0]⟩,
    ⟨Word.mk 1 [0, 0], Word.mk 1 [1, 0]⟩,
    ⟨Word.mk 1 [0, 0], Word.mk 1 [0, 0, 0]⟩,
    ⟨Word.mk 2 [1, 0], Word.mk 2 [1, 0, 0]⟩] := by decide

private def fourWords (first second third guard : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | _ => guard

theorem guardedLowerAxiom (identity : Identity Nat) (member : identity ∈ lowerBasis)
    (substitution : Nat → Word Nat) (guard : Word Nat) :
    Derives basis (guard ++ identity.lhs.bind substitution)
      (guard ++ identity.rhs.bind substitution) := by
  rw [lowerBasis_literal] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · have mapped := Derives.subst guarded_00
      (fourWords (substitution 0) (substitution 1) (substitution 2) guard)
    simpa [fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  · have mapped := Derives.subst guarded_01
      (fourWords (substitution 0) (substitution 1) (substitution 2) guard)
    simpa [fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  · have mapped := Derives.subst guarded_02
      (fourWords (substitution 0) (substitution 1) (substitution 2) guard)
    simpa [fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  · have mapped := Derives.subst guarded_03
      (fourWords (substitution 0) (substitution 1) (substitution 2) guard)
    simpa [fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  · have mapped := Derives.subst guarded_04
      (fourWords (substitution 0) (substitution 1) (substitution 2) guard)
    simpa [fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

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
  have lower := lowerBasis_complete.2 (Identity.mk left right) valid
  simpa [bind_singleton] using liftLowerWithPrefix lower guard Word.singleton

theorem derivesLongInsertion (first second third : Word Nat) :
    Derives basis ((first ++ second) ++ third) (((first ++ first) ++ second) ++ third) := by
  have primitive : Derives basis law05.lhs law05.rhs :=
    Derives.fromBasis (e := law05) (by decide)
  have mapped := (Derives.subst primitive (fourWords first second third first)).symm
  simpa [law05, fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

end SemigroupBasis.CoRoots.Order6Day10.S3_15.Rank104Replay
