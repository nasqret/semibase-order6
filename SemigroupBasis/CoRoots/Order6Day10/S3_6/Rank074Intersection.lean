import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Intersection

/-! Exact B13 converse: reuse the already proved opposite Rank073 theory.
Every one of the twelve reversed B12 axioms is transported by typed displayed-law paths.
All seventeen concrete transport edges are kernel checked; no new bridge is assumed.
The enhanced four-letter countermodel screen ran before this new source. -/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank074Intersection

open SemigroupBasis

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [1, 0]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 0]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [0, 1, 2], Word.mk 0 [1, 0, 1, 2]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 1], Word.mk 0 [1, 2, 0]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 2], Word.mk 0 [1, 2, 0]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 0]⟩
def law07 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 1, 0]⟩
def law08 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 1], Word.mk 0 [1, 2, 0]⟩
def law09 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 2], Word.mk 0 [1, 2, 0]⟩
def law10 : Identity Nat := ⟨Word.mk 0 [1, 1, 2], Word.mk 0 [1, 2]⟩
def law11 : Identity Nat := ⟨Word.mk 0 [1, 2, 0], Word.mk 0 [2, 1, 0]⟩
def law12 : Identity Nat := ⟨Word.mk 0 [1, 2, 1], Word.mk 0 [1, 2, 1, 2]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11, law12]

abbrev displayedBasisSHA256 : String := "699898150b01acc06e5d00a6cd5c696f8789fa1ff5e2e1615f4b2437bb95b76a"
abbrev leftTable : FiniteTable := Generated.S3_6.table
def rightTable : FiniteTable where
  order := 5
  mul first second := Generated.Catalogue.S5_303.table.mul second first
  assoc := by decide
abbrev oldBasis : List (Identity Nat) := reversedBasis SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Replay.basis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_length : basis.length = 13 := by decide
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

theorem old_00 : Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) := by
  have step0 : Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) := by
    have primitive : Derives basis law00.lhs law00.rhs :=
      Derives.fromBasis (e := law00) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law00, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  exact step0

theorem old_01 : Derives basis (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0]) := by
  have step0 : Derives basis (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0]) := by
    have primitive : Derives basis law01.lhs law01.rhs :=
      Derives.fromBasis (e := law01) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  exact step0

theorem old_02 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 0]) := by
  have step0 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 0]) := by
    have primitive : Derives basis law02.lhs law02.rhs :=
      Derives.fromBasis (e := law02) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  exact step0

theorem old_03 : Derives basis (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [2, 1, 0]) := by
  have step0 : Derives basis (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [1, 2, 0]) := by
    have primitive : Derives basis law04.lhs law04.rhs :=
      Derives.fromBasis (e := law04) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 2 [])
        | _ => Word.singleton 0)
    simpa [law04, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  have step1 : Derives basis (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) := by
    have primitive : Derives basis law11.lhs law11.rhs :=
      Derives.fromBasis (e := law11) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 2 [])
        | _ => Word.singleton 0)
    simpa [law11, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  exact step0.trans (step1)

theorem old_04 : Derives basis (Word.mk 0 [0, 2, 1, 1]) (Word.mk 0 [2, 1, 0]) := by
  have step0 : Derives basis (Word.mk 0 [0, 2, 1, 1]) (Word.mk 0 [2, 1, 0]) := by
    have primitive : Derives basis law05.lhs law05.rhs :=
      Derives.fromBasis (e := law05) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 2 [])
        | 2 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  exact step0

theorem old_05 : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 0, 0]) := by
  have step0 : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 0, 0]) := by
    have primitive : Derives basis law06.lhs law06.rhs :=
      Derives.fromBasis (e := law06) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law06, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  exact step0

theorem old_06 : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 0, 1]) := by
  have step0 : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 0, 1, 0]) := by
    have primitive : Derives basis law07.lhs law07.rhs :=
      Derives.fromBasis (e := law07) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law07, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  have step1 : Derives basis (Word.mk 0 [1, 0, 1, 0]) (Word.mk 0 [1, 0, 1]) := by
    have primitive : Derives basis law12.lhs law12.rhs :=
      Derives.fromBasis (e := law12) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law12, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped.symm
  exact step0.trans (step1)

theorem old_07 : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 1, 0]) := by
  have step0 : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 1, 0]) := by
    have primitive : Derives basis law10.lhs law10.rhs :=
      Derives.fromBasis (e := law10) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law10, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped.symm
  exact step0

theorem old_08 : Derives basis (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) := by
  have step0 : Derives basis (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) := by
    have primitive : Derives basis law11.lhs law11.rhs :=
      Derives.fromBasis (e := law11) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 2 [])
        | _ => Word.singleton 0)
    simpa [law11, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  exact step0

theorem old_09 : Derives basis (Word.mk 0 [2, 0, 1, 1]) (Word.mk 0 [2, 1, 0]) := by
  have step0 : Derives basis (Word.mk 0 [2, 0, 1, 1]) (Word.mk 0 [2, 1, 0]) := by
    have primitive : Derives basis law09.lhs law09.rhs :=
      Derives.fromBasis (e := law09) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 2 [])
        | 2 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law09, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  exact step0

theorem old_10 : Derives basis (Word.mk 0 [2, 1, 0]) (Word.mk 0 [2, 1, 0, 1]) := by
  have step0 : Derives basis (Word.mk 0 [2, 1, 0]) (Word.mk 0 [1, 2, 0]) := by
    have primitive : Derives basis law11.lhs law11.rhs :=
      Derives.fromBasis (e := law11) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 2 [])
        | 2 => (Word.mk 1 [])
        | _ => Word.singleton 0)
    simpa [law11, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  have step1 : Derives basis (Word.mk 0 [1, 2, 0]) (Word.mk 0 [1, 0, 2, 1]) := by
    have primitive : Derives basis law08.lhs law08.rhs :=
      Derives.fromBasis (e := law08) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 2 [])
        | _ => Word.singleton 0)
    simpa [law08, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped.symm
  have step2 : Derives basis (Word.mk 0 [1, 0, 2, 1]) (Word.mk 0 [1, 2, 0, 1]) := by
    have primitive : Derives basis law11.lhs law11.rhs :=
      Derives.fromBasis (e := law11) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 1 [])
        | 1 => (Word.mk 0 [])
        | 2 => (Word.mk 2 [])
        | _ => Word.singleton 0)
    simpa [law11, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.prepend (Word.mk 0 []) mapped)
  have step3 : Derives basis (Word.mk 0 [1, 2, 0, 1]) (Word.mk 0 [2, 1, 0, 1]) := by
    have primitive : Derives basis law11.lhs law11.rhs :=
      Derives.fromBasis (e := law11) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 0 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 2 [])
        | _ => Word.singleton 0)
    simpa [law11, Word.bind, Word.append, Word.singleton, Word.append_assoc] using (Derives.appendRight mapped (Word.mk 1 []))
  exact step0.trans (step1.trans (step2.trans (step3)))

theorem old_11 : Derives basis (Word.mk 2 [1, 0]) (Word.mk 2 [1, 1, 0]) := by
  have step0 : Derives basis (Word.mk 2 [1, 0]) (Word.mk 2 [1, 1, 0]) := by
    have primitive : Derives basis law10.lhs law10.rhs :=
      Derives.fromBasis (e := law10) (by decide)
    have mapped := Derives.subst primitive (fun
        | 0 => (Word.mk 2 [])
        | 1 => (Word.mk 1 [])
        | 2 => (Word.mk 0 [])
        | _ => Word.singleton 0)
    simpa [law10, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped.symm
  exact step0

theorem oldBasis_literal : oldBasis =
  [⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩,
    ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [1, 0]⟩,
    ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 0]⟩,
    ⟨Word.mk 0 [0, 1, 2, 1], Word.mk 0 [2, 1, 0]⟩,
    ⟨Word.mk 0 [0, 2, 1, 1], Word.mk 0 [2, 1, 0]⟩,
    ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 0]⟩,
    ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 1]⟩,
    ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 1, 0]⟩,
    ⟨Word.mk 0 [1, 2, 0], Word.mk 0 [2, 1, 0]⟩,
    ⟨Word.mk 0 [2, 0, 1, 1], Word.mk 0 [2, 1, 0]⟩,
    ⟨Word.mk 0 [2, 1, 0], Word.mk 0 [2, 1, 0, 1]⟩,
    ⟨Word.mk 2 [1, 0], Word.mk 2 [1, 1, 0]⟩] := by decide

theorem derivesOldAxiom (identity : Identity Nat) (member : identity ∈ oldBasis) :
    Derives basis identity.lhs identity.rhs := by
  rw [oldBasis_literal] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact old_00
  · exact old_01
  · exact old_02
  · exact old_03
  · exact old_04
  · exact old_05
  · exact old_06
  · exact old_07
  · exact old_08
  · exact old_09
  · exact old_10
  · exact old_11

theorem replayOld {left right : Word Nat} (derivation : Derives oldBasis left right) :
    Derives basis left right := by
  induction derivation with
  | fromBasis member => exact derivesOldAxiom _ member
  | refl => exact Derives.refl _
  | symm _ induction => exact induction.symm
  | trans _ _ first second => exact first.trans second
  | prepend stem _ induction => exact Derives.prepend stem induction
  | appendRight _ tail induction => exact Derives.appendRight induction tail
  | subst _ substitution induction => exact Derives.subst induction substitution

/-- The whole actual-factor theorem is dualized, not an unproved descriptor premise. -/
def inheritedIntersection : IntersectionBasis leftTable.semigroup rightTable.semigroup oldBasis :=
  SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Intersection.intersectionBasis.oppositeReversed

def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives basis identity.lhs identity.rhs

theorem complete : Complete := by
  intro identity leftValid rightValid
  exact replayOld (inheritedIntersection.complete identity leftValid rightValid)

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := complete

abbrev FinitePair (target : FiniteTable) :=
  SubdirectPair target.semigroup leftTable.semigroup rightTable.semigroup

theorem basisForOfFinitePair (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup basis := intersectionBasis.basisFor pair

theorem basisForOppositeOfFinitePair (target : FiniteTable)
    (pair : SubdirectPair target.semigroup.opposite leftTable.semigroup.opposite rightTable.semigroup.opposite) :
    BasisFor target.semigroup.opposite (reversedBasis basis) :=
  intersectionBasis.oppositeReversed.basisFor pair

end SemigroupBasis.CoRoots.Order6Day10.S3_6.Rank074Intersection
