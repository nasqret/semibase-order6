import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SuffixFlags

/-! Literal SameSignature now supplies both observations required by the
actual scalar resolver comparison. Selector-fold/final-word assembly is
not assumed and remains separate. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SignatureResolver

open SemigroupBasis
open Msg0457S11395WordGaps Msg0457S11395WordReduction Msg0457S11395ResolveLetter
open Msg0457S11395Observations Msg0457S11395CoordinateSectors Msg0457S11395SectorSignature
open Msg0457S11395GapParity Msg0457S11395SuffixFlags Msg0457S11395ScalarBridge

theorem signature_sector_observations (leftHead rightHead tested : Nat) (left right : Chain)
    (leftGood : WellFormed [leftHead] left) (rightGood : WellFormed [rightHead] right)
    (same : SameSignature ⟨leftHead,flatten left⟩ ⟨rightHead,flatten right⟩) :
    (sectorCounts (leftHead :: flatten left) tested left).map bits =
      (sectorCounts (rightHead :: flatten right) tested right).map bits ∧
    suffixFlags (sectorCounts (leftHead :: flatten left) tested left) =
      suffixFlags (sectorCounts (rightHead :: flatten right) tested right) :=
  ⟨signature_sectorBits leftHead rightHead tested left right leftGood rightGood same,
    signature_suffixFlags leftHead rightHead tested left right leftGood rightGood same⟩

theorem signature_canonicalBlocks (leftHead rightHead tested : Nat) (left right : Chain)
    (leftGood : WellFormed [leftHead] left) (rightGood : WellFormed [rightHead] right)
    (leftRed : Reduced left) (rightRed : Reduced right)
    (same : SameSignature ⟨leftHead,flatten left⟩ ⟨rightHead,flatten right⟩) :
    canonicalBlocks (sectorCounts (leftHead :: flatten left) tested left) =
      canonicalBlocks (sectorCounts (rightHead :: flatten right) tested right) := by
  have observations := signature_sector_observations leftHead rightHead tested left right leftGood rightGood same
  exact actual_sector_canonical_comparison _ _ tested left right leftRed rightRed observations.1 observations.2

theorem signature_resolver_profile (leftHead rightHead tested : Nat) (left right : Chain)
    (leftGood : WellFormed [leftHead] left) (rightGood : WellFormed [rightHead] right)
    (leftRed : Reduced left) (rightRed : Reduced right)
    (same : SameSignature ⟨leftHead,flatten left⟩ ⟨rightHead,flatten right⟩) :
    gapProfile tested (resolveLetter [leftHead] tested left) =
      gapProfile tested (resolveLetter [rightHead] tested right) := by
  have observations := signature_sector_observations leftHead rightHead tested left right leftGood rightGood same
  exact singleton_resolver_eq_of_observations leftHead rightHead tested left right leftGood rightGood
    leftRed rightRed observations.1 observations.2

theorem signature_factor_suffixFlags (left right : Word Nat) (same : SameSignature left right) (tested : Nat) :
    suffixFlags (sectorCounts left.toList tested (factor [left.head] left.tail)) =
      suffixFlags (sectorCounts right.toList tested (factor [right.head] right.tail)) := by
  have represented : SameSignature
      ⟨left.head,flatten (factor [left.head] left.tail)⟩
      ⟨right.head,flatten (factor [right.head] right.tail)⟩ := by
    simpa only [factor_flatten] using same
  simpa only [factor_flatten] using signature_suffixFlags left.head right.head tested
    (factor [left.head] left.tail) (factor [right.head] right.tail)
    (factor_wellFormed [left.head] left.tail) (factor_wellFormed [right.head] right.tail) represented

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SignatureResolver
