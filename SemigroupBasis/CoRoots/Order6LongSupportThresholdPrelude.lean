import SemigroupBasis.CoRoots.S5_55
import SemigroupBasis.CoRoots.S5_215Normalization

namespace SemigroupBasis.CoRoots.Order6LongSupportThreshold

open SemigroupBasis

def xyztx : Word Nat :=
  ⟨0, [1, 2, 3, 0]⟩

def longSupportLaw : Identity Nat :=
  ⟨S5_55.xyzt, xyztx⟩

/-- The exact six-law long-support-threshold intersection basis. -/
def longSupportThresholdBasis : List (Identity Nat) :=
  [S5_55.firstSwapLaw,
    S5_55.multiplicityTransferLaw,
    S5_55.prefixSwapLaw,
    S5_55.suffixCommutationLaw,
    S5_55.prefixCommutationLaw,
    longSupportLaw]

end SemigroupBasis.CoRoots.Order6LongSupportThreshold
