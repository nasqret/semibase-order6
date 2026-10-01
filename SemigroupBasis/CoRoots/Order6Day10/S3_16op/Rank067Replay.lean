import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.Generated.SquareFreeDoubledHeadFiveTransfersLayer1

/-! Exact B7 replay for S3_16 opposite / S5_904 direct.
Before authoring: 2465 models, 435 B7 models, clean in (2,8),(3,5),(4,5).
All four guarded displayed-law edges have typed endpoints and decide membership.
An arbitrary prefix is decomposed into TWO nonempty words; it is never erased.
This module alone does not assert the joint converse. -/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_16op.Rank067Replay

open SemigroupBasis

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 1, 2], Word.mk 0 [0, 2, 1, 2]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [1], Word.mk 0 [1, 0, 1]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [1], Word.mk 0 [1, 1]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [1, 0, 2], Word.mk 0 [1, 2, 0, 2]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 0], Word.mk 0 [1, 2, 0]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 1], Word.mk 0 [1, 2, 1]⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06]

abbrev displayedBasisSHA256 : String := "bf866951b671207b90abeda737606c2afe3618e9a45b2ef827570f3ca976a053"
def leftTable : FiniteTable where
  order := 3
  mul first second := Generated.S3_16.table.mul second first
  assoc := by decide
abbrev rightTable : FiniteTable := Generated.Catalogue.S5_904.table

theorem leftTable_is_actual_opposite :
    leftTable.semigroup = Generated.S3_16.table.semigroup.opposite := rfl

abbrev upperBasis : List (Identity Nat) := Examples.leftRegularBandThreeOppositeBasis
abbrev lowerBasis : List (Identity Nat) := CoRoots.S5_830.basis

theorem upperBasis_complete : BasisFor leftTable.semigroup upperBasis :=
  Generated.S3_16.opposite_basis

theorem lowerBasis_complete : BasisFor rightTable.semigroup lowerBasis :=
  Generated.SquareFreeDoubledHeadFiveTransfers.S5_904.representative_basis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_length : basis.length = 7 := by decide
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

theorem guarded_band_idempotence : Derives basis (Word.mk 3 [4, 0]) (Word.mk 3 [4, 0, 0]) := by
  have step0 : Derives basis (Word.mk 3 [4, 0]) (Word.mk 3 [4, 0, 0]) := by
    have primitive : Derives basis law03.lhs law03.rhs :=
      Derives.fromBasis (e := law03) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 3 [4])
        | 1 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  exact step0

theorem guarded_band_return : Derives basis (Word.mk 3 [4, 1, 0]) (Word.mk 3 [4, 0, 1, 0]) := by
  have step0 : Derives basis (Word.mk 3 [4, 1, 0]) (Word.mk 3 [4, 3, 4, 1, 0]) := by
    have primitive : Derives basis law02.lhs law02.rhs :=
      Derives.fromBasis (e := law02) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 3 [])
        | 1 => (Word.mk 4 [])
        | _ => Word.singleton 0)
    simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped (Word.mk 1 [0]))
  have step1 : Derives basis (Word.mk 3 [4, 3, 4, 1, 0]) (Word.mk 3 [4, 3, 4, 0, 1, 0]) := by
    have primitive : Derives basis law01.lhs law01.rhs :=
      Derives.fromBasis (e := law01) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 3 [4])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  have step2 : Derives basis (Word.mk 3 [4, 3, 4, 0, 1, 0]) (Word.mk 3 [4, 0, 1, 0]) := by
    have primitive : Derives basis law02.lhs law02.rhs :=
      Derives.fromBasis (e := law02) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 3 [])
        | 1 => (Word.mk 4 [])
        | _ => Word.singleton 0)
    simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped.symm (Word.mk 0 [1, 0]))
  exact step0.trans (step1.trans (step2))

theorem upperBasis_literal : upperBasis =
  [⟨Word.mk 0 [], Word.mk 0 [0]⟩,
    ⟨Word.mk 1 [0], Word.mk 0 [1, 0]⟩] := by decide


private def fourWords (first second guardFirst guardSecond : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 3 => guardFirst
  | 4 => guardSecond
  | _ => Word.singleton 0

theorem guardedUpperAxiom (identity : Identity Nat) (member : identity ∈ upperBasis)
    (substitution : Nat → Word Nat) (first second : Word Nat) :
    Derives basis ((first ++ second) ++ identity.lhs.bind substitution)
      ((first ++ second) ++ identity.rhs.bind substitution) := by
  rw [upperBasis_literal] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · have mapped := Derives.subst guarded_band_idempotence
      (fourWords (substitution 0) (substitution 1) first second)
    simpa [fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  · have mapped := Derives.subst guarded_band_return
      (fourWords (substitution 0) (substitution 1) first second)
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

/-- Every band derivation lifts behind two nonempty prefix blocks. -/
theorem liftUpperWithTwoPrefix {left right : Word Nat}
    (derivation : Derives upperBasis left right)
    (first second : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis ((first ++ second) ++ left.bind substitution)
      ((first ++ second) ++ right.bind substitution) := by
  induction derivation generalizing first second substitution with
  | fromBasis member => exact guardedUpperAxiom _ member substitution first second
  | refl => exact Derives.refl _
  | symm _ induction => exact (induction first second substitution).symm
  | trans _ _ leftIH rightIH =>
      exact (leftIH first second substitution).trans (rightIH first second substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction first (second ++ stem.bind substitution) substitution
  | appendRight _ final induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (induction first second substitution) (final.bind substitution)
  | subst _ next induction =>
      simpa [bind_bind] using
        induction first second (fun letter => (next letter).bind substitution)

theorem derivesSameTwoPrefixOfUpperValid (left right first second : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy leftTable.semigroup) :
    Derives basis ((first ++ second) ++ left) ((first ++ second) ++ right) := by
  have upper : Derives upperBasis left right :=
    upperBasis_complete.2 (Identity.mk left right) valid
  simpa [bind_singleton] using liftUpperWithTwoPrefix upper first second Word.singleton

theorem derivesProductSquare (first second : Word Nat) :
    Derives basis (first ++ second) ((first ++ second) ++ (first ++ second)) := by
  have primitive : Derives basis law02.lhs law02.rhs :=
    Derives.fromBasis (e := law02) (by decide)
  have mapped := Derives.subst primitive (fourWords first second first second)
  simpa [law02, fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

/-- Actual lower validity supplies the literal first-two prefix, not an assumed key. -/
theorem lowerValid_firstTwo (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    CoRoots.S5_830.FirstTwo identity.lhs = CoRoots.S5_830.FirstTwo identity.rhs := by
  have derived : Derives lowerBasis identity.lhs identity.rhs :=
    lowerBasis_complete.2 identity valid
  have valid830 : identity.SatisfiedBy Generated.Catalogue.S5_830.table.semigroup :=
    fun valuation => derived.sound CoRoots.S5_830.models valuation
  exact CoRoots.S5_830.valid_firstTwo identity valid830

end SemigroupBasis.CoRoots.Order6Day10.S3_16op.Rank067Replay
