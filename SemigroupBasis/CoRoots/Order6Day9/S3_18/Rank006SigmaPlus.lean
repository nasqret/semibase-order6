import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Raw12Obstruction

/-!
# Rank006: the positively reviewed thirteen-law successor

Fable msg-0367 approves precisely the raw twelve laws plus aba = aaaaba.
The original raw12 constant and its incompleteness theorem are unchanged.
The required two-sided, two-generator period-absorption screen completed
before authoring this module. Its CLEAN result is bounded evidence only.

This file proves soundness and records the exact unrestricted obligation;
it does not assert completeness or construct any class-specific witness.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus

open SemigroupBasis

abbrev leftTable : FiniteTable := Rank006Shape.leftTable
abbrev rightTable : FiniteTable := Rank006Shape.rightTable

def sigmaPlus : List (Identity Nat) :=
  Rank006Shape.basis ++ [Rank006Raw12Obstruction.missingLaw]

def displayedBasisSHA256 : String :=
  "13522974f29a1e29a7948fd276ff5c0926ec27d1224b8dd154dc9f6cecb9a9d2"

theorem sigmaPlus_length : sigmaPlus.length = 13 := by decide

theorem raw_member {identity : Identity Nat}
    (member : identity ∈ Rank006Shape.basis) : identity ∈ sigmaPlus :=
  List.mem_append_left _ member

theorem bridge_member : Rank006Raw12Obstruction.missingLaw ∈ sigmaPlus := by
  decide

theorem raw_derives {left right : Word Nat}
    (derivation : Derives Rank006Shape.basis left right) :
    Derives sigmaPlus left right :=
  derivation.transport (fun _ member => Derives.fromBasis (raw_member member))

theorem modelsLeft : Models leftTable.semigroup sigmaPlus := by
  intro identity member
  rcases List.mem_append.mp member with raw | bridge
  · exact Rank006Shape.modelsLeft identity raw
  · have same : identity = Rank006Raw12Obstruction.missingLaw := by simpa using bridge
    subst identity
    exact Rank006Raw12Obstruction.missingLaw_leftValid

theorem modelsRight : Models rightTable.semigroup sigmaPlus := by
  intro identity member
  rcases List.mem_append.mp member with raw | bridge
  · exact Rank006Shape.modelsRight identity raw
  · have same : identity = Rank006Raw12Obstruction.missingLaw := by simpa using bridge
    subst identity
    exact Rank006Raw12Obstruction.missingLaw_rightValid

theorem derives_factor_valid {left right : Word Nat}
    (derivation : Derives sigmaPlus left right) :
    (Identity.mk left right).SatisfiedBy leftTable.semigroup ∧
      (Identity.mk left right).SatisfiedBy rightTable.semigroup :=
  ⟨derivation.sound modelsLeft, derivation.sound modelsRight⟩

/-- Exactly fable's approved statement: no alphabet, rank, length, or
multiplicity restriction. This definition is an obligation, not its proof. -/
def Complete : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
    identity.SatisfiedBy rightTable.semigroup →
    Derives sigmaPlus identity.lhs identity.rhs

abbrev FinitePair (target : FiniteTable) := Rank006Shape.FinitePair target
abbrev FinitePairOpposite (target : FiniteTable) := Rank006Shape.FinitePairOpposite target

/-- Conditional assembly only; S3's finite interface is basis-independent. -/
def intersectionBasisOfComplete (complete : Complete) :
    IntersectionBasis leftTable.semigroup rightTable.semigroup sigmaPlus where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := complete

theorem basisForOfComplete (complete : Complete)
    (target : FiniteTable) (pair : FinitePair target) :
    BasisFor target.semigroup sigmaPlus :=
  (intersectionBasisOfComplete complete).basisFor pair

theorem basisForOppositeOfComplete (complete : Complete)
    (target : FiniteTable) (pair : FinitePairOpposite target) :
    BasisFor target.semigroup.opposite (reversedBasis sigmaPlus) :=
  (intersectionBasisOfComplete complete).oppositeReversed.basisFor pair

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus
