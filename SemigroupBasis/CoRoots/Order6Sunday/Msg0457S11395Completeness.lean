import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SelectorAssembly

/-! Unrestricted exact-B12 completeness for S11395. The original actual
sectorWord is a signature-canonical, idempotent normalizer. No sampled
bound, semantic reach field or caller-supplied renderer is assumed. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Completeness

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395Observations Msg0457S11395Signature
open Msg0457S11395ResolveLetter Msg0457S11395ProfileComparison
open Msg0457S11395IntroductionOrder Msg0457S11395SelectorAssembly

theorem sectorWord_eq_of_signature (left right : Word Nat) (same : SameSignature left right) :
    sectorWord left = sectorWord right := by
  have order := same.firstOrder
  rw [factor_firstOrder left, factor_firstOrder right] at order
  have parts := List.cons.inj order
  exact sectorWord_eq_of_profiles left right parts.1 parts.2 (signature_placed_profiles left right same)

theorem derivesOfSameSignature {left right : Word Nat} (same : SameSignature left right) :
    Derives basis left right := by
  have normalEqual := sectorWord_eq_of_signature left right same
  have back : Derives basis (sectorWord left) right := by
    rw [normalEqual]
    exact (sectorWord_derives right).symm
  exact (sectorWord_derives left).trans back

theorem signatureReach : SignatureReach := fun _ _ same => derivesOfSameSignature same

theorem complete (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameSignature (sameSignature_of_valid identity valid)

theorem representative_basis : BasisFor table.semigroup basis :=
  basisFor_iff_signatureReach.mpr signatureReach

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

theorem derives_iff_signature (left right : Word Nat) :
    Derives basis left right ↔ SameSignature left right :=
  ⟨derives_preserve_signature, derivesOfSameSignature⟩

theorem sectorWord_idempotent (word : Word Nat) : sectorWord (sectorWord word) = sectorWord word :=
  (sectorWord_eq_of_signature word (sectorWord word) (sectorWord_signature word)).symm

theorem sectorWord_eq_iff_signature (left right : Word Nat) :
    sectorWord left = sectorWord right ↔ SameSignature left right := by
  constructor
  · intro equal
    have back : Derives basis (sectorWord left) right := by
      rw [equal]
      exact (sectorWord_derives right).symm
    exact derives_preserve_signature ((sectorWord_derives left).trans back)
  · exact sectorWord_eq_of_signature left right

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Completeness
