import SemigroupBasis.ChainReplay
import SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank043
import SemigroupBasis.Opposite

/-!
# Exact D043 adapter from the reversed C2/S5_196 ten-law root

The source list duplicates the existing unrestricted
`Order6FactorPairS2S5196Intersection.basis` literally.  Every one of its ten
reversed axioms is replayed from the immutable rank-043 displayed basis.
Seven axioms take one checked edge and three axioms take three separately
typed, association-fixed checked edges, for sixteen independent checks total.
No finite search implies unrestricted completeness here.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_516DualAdapter

open SemigroupBasis

private def word (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

def sourceLaw00 : Identity Nat := ⟨word 0 [0, 0], word 0 [0, 0, 0, 0]⟩
def sourceLaw01 : Identity Nat := ⟨word 0 [0, 0, 0, 1], word 0 [0, 1]⟩
def sourceLaw02 : Identity Nat := ⟨word 0 [0, 0, 1, 0], word 0 [1, 0]⟩
def sourceLaw03 : Identity Nat := ⟨word 0 [0, 0, 1, 2], word 0 [1, 2]⟩
def sourceLaw04 : Identity Nat := ⟨word 0 [0, 1, 0], word 0 [1, 1, 1]⟩
def sourceLaw05 : Identity Nat := ⟨word 0 [0, 1, 1], word 0 [1, 1, 0]⟩
def sourceLaw06 : Identity Nat := ⟨word 0 [0, 1, 1, 1], word 0 [1, 0]⟩
def sourceLaw07 : Identity Nat := ⟨word 0 [1, 0], word 0 [1, 1, 1, 0]⟩
def sourceLaw08 : Identity Nat := ⟨word 0 [1, 0], word 1 [0, 0]⟩
def sourceLaw09 : Identity Nat := ⟨word 0 [1, 2], word 1 [0, 2]⟩

def sourceBasis : List (Identity Nat) :=
  [sourceLaw00, sourceLaw01, sourceLaw02, sourceLaw03, sourceLaw04,
   sourceLaw05, sourceLaw06, sourceLaw07, sourceLaw08, sourceLaw09]

theorem sourceBasis_length : sourceBasis.length = 10 := by
  decide

private def fixedStep
    (lawIndex : Nat) (direction : ChainReplay.Direction)
    (leftContext rightContext : List Nat)
    (substitution : List (List Nat)) : ChainReplay.Chain Nat :=
  [{lawIndex, direction, leftContext, rightContext, substitution}]

private def unchanged : List (List Nat) := [[0], [1], [2]]

theorem reversedSourceLaw00 :
    Derives Rank043.basis sourceLaw00.reversed.lhs sourceLaw00.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 0 .forward [] [] unchanged) (by decide)

theorem reversedSourceLaw01 :
    Derives Rank043.basis sourceLaw01.reversed.lhs sourceLaw01.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 7 .backward [] [] [[1], [0], [2]]) (by decide)

/-- `xyxxx -> xxyxx`, using the frozen gather law under protected `xx`. -/
theorem prefixParityEdge00 :
    Derives Rank043.basis (word 0 [1, 0, 0, 0]) (word 0 [0, 1, 0, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 4 .backward [] [0, 0] unchanged) (by decide)

/-- `xxyxx -> xyyyx`, using the initial-switch law under protected `x`. -/
theorem prefixParityEdge01 :
    Derives Rank043.basis (word 0 [0, 1, 0, 0]) (word 0 [1, 1, 1, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 2 .backward [0] [] [[1], [0], [2]]) (by decide)

/-- `xyyyx -> xyx`, using the exact middle-pair contraction. -/
theorem prefixParityEdge02 :
    Derives Rank043.basis (word 0 [1, 1, 1, 0]) (word 0 [1, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 8 .forward [] [] [[0], [1], [0]]) (by decide)

theorem reversedSourceLaw02 :
    Derives Rank043.basis sourceLaw02.reversed.lhs sourceLaw02.reversed.rhs := by
  exact prefixParityEdge00.trans
    (prefixParityEdge01.trans prefixParityEdge02)

/-- `zyxxx -> zyyyxxx`, with the original trailing `xx` retained. -/
theorem guardedContractionEdge00 :
    Derives Rank043.basis (word 2 [1, 0, 0, 0])
      (word 2 [1, 1, 1, 0, 0, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 8 .backward [] [0, 0] [[2], [1], [0]]) (by decide)

/-- `zyyyxxx -> zyyyx`, preserving the literal `zy` prefix. -/
theorem guardedContractionEdge01 :
    Derives Rank043.basis (word 2 [1, 1, 1, 0, 0, 0])
      (word 2 [1, 1, 1, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 3 .backward [2, 1] [] [[1], [0], [2]]) (by decide)

/-- `zyyyx -> zyx`, independently checking the exact final contraction. -/
theorem guardedContractionEdge02 :
    Derives Rank043.basis (word 2 [1, 1, 1, 0]) (word 2 [1, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 8 .forward [] [] [[2], [1], [0]]) (by decide)

theorem reversedSourceLaw03 :
    Derives Rank043.basis sourceLaw03.reversed.lhs sourceLaw03.reversed.rhs := by
  exact guardedContractionEdge00.trans
    (guardedContractionEdge01.trans guardedContractionEdge02)

theorem reversedSourceLaw04 :
    Derives Rank043.basis sourceLaw04.reversed.lhs sourceLaw04.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 2 .backward [] [] [[1], [0], [2]]) (by decide)

theorem reversedSourceLaw05 :
    Derives Rank043.basis sourceLaw05.reversed.lhs sourceLaw05.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 6 .forward [] [] [[1], [0], [2]]) (by decide)

/-- `yyyxx -> yxxyy`, with genuine composite substitutions `yy` and `xx`. -/
theorem compositeSwapEdge00 :
    Derives Rank043.basis (word 1 [1, 1, 0, 0]) (word 1 [0, 0, 1, 1]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 9 .forward [] [] [[1], [1, 1], [0, 0]]) (by decide)

/-- `yxxyy -> xxy`, the exact displayed initial-head contraction. -/
theorem compositeSwapEdge01 :
    Derives Rank043.basis (word 1 [0, 0, 1, 1]) (word 0 [0, 1]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 5 .backward [] [] unchanged) (by decide)

/-- `xxy -> xyx`, the exact displayed gather law. -/
theorem compositeSwapEdge02 :
    Derives Rank043.basis (word 0 [0, 1]) (word 0 [1, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 4 .forward [] [] unchanged) (by decide)

theorem reversedSourceLaw06 :
    Derives Rank043.basis sourceLaw06.reversed.lhs sourceLaw06.reversed.rhs := by
  exact compositeSwapEdge00.trans
    (compositeSwapEdge01.trans compositeSwapEdge02)

theorem reversedSourceLaw07 :
    Derives Rank043.basis sourceLaw07.reversed.lhs sourceLaw07.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 8 .backward [] [] [[0], [1], [0]]) (by decide)

theorem reversedSourceLaw08 :
    Derives Rank043.basis sourceLaw08.reversed.lhs sourceLaw08.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 4 .backward [] [] unchanged) (by decide)

theorem reversedSourceLaw09 :
    Derives Rank043.basis sourceLaw09.reversed.lhs sourceLaw09.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 9 .forward [] [] [[2], [1], [0]]) (by decide)

/-- Every literal reversed source axiom is backed by its checked frozen edges. -/
theorem reversedSourceAxiomsDeriveFrozen
    (identity : Identity Nat)
    (member : identity ∈ reversedBasis sourceBasis) :
    Derives Rank043.basis identity.lhs identity.rhs := by
  simp only [sourceBasis, reversedBasis, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact reversedSourceLaw00
  · exact reversedSourceLaw01
  · exact reversedSourceLaw02
  · exact reversedSourceLaw03
  · exact reversedSourceLaw04
  · exact reversedSourceLaw05
  · exact reversedSourceLaw06
  · exact reversedSourceLaw07
  · exact reversedSourceLaw08
  · exact reversedSourceLaw09

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_516DualAdapter
