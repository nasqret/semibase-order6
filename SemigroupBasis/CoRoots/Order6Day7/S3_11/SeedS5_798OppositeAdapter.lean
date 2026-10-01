import SemigroupBasis.ChainReplay
import SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank020
import SemigroupBasis.Opposite

/-!
# Exact D020 adapter from reversed e2c to frozen B13

The thirteen source laws below duplicate the existing unrestricted
`Order6Level2TierBHashE2c5e460.basis` literally.  Twelve reversed source
laws have individually checked one-edge certificates over the immutable
rank-020 displayed basis.  The remaining attachment law has four separately
typed, independently checked edges with association-fixed intermediate
words.  No semantic completeness or factor-theory equality is inferred here.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_798OppositeAdapter

open SemigroupBasis

private def word (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

def sourceLaw00 : Identity Nat := ⟨word 0 [0], word 0 [0, 0, 0]⟩
def sourceLaw01 : Identity Nat := ⟨word 0 [0, 0, 1, 0], word 0 [1, 0]⟩
def sourceLaw02 : Identity Nat := ⟨word 0 [0, 1, 0], word 0 [1, 0, 0]⟩
def sourceLaw03 : Identity Nat := ⟨word 0 [0, 1, 0, 0], word 0 [1, 0]⟩
def sourceLaw04 : Identity Nat := ⟨word 0 [1, 0], word 0 [1, 0, 0, 0]⟩
def sourceLaw05 : Identity Nat := ⟨word 0 [1, 0], word 0 [1, 0, 1, 1]⟩
def sourceLaw06 : Identity Nat := ⟨word 0 [1, 0], word 0 [1, 1, 0, 1]⟩
def sourceLaw07 : Identity Nat := ⟨word 0 [1, 0], word 0 [1, 1, 1, 0]⟩
def sourceLaw08 : Identity Nat := ⟨word 0 [1, 0, 1], word 0 [1, 1, 0]⟩
def sourceLaw09 : Identity Nat := ⟨word 0 [1, 0, 2, 1], word 0 [1, 1, 2, 0]⟩
def sourceLaw10 : Identity Nat := ⟨word 0 [1, 1, 2, 1], word 0 [2, 1, 2, 2]⟩
def sourceLaw11 : Identity Nat := ⟨word 0 [1, 2, 0], word 0 [2, 1, 0]⟩
def sourceLaw12 : Identity Nat := ⟨word 0 [1, 2, 1, 2], word 0 [2, 1, 1, 2]⟩

/-- Independently materialized literal source list; equality with the
historical unrestricted root is checked in the downstream owner module. -/
def sourceBasis : List (Identity Nat) :=
  [sourceLaw00, sourceLaw01, sourceLaw02, sourceLaw03, sourceLaw04,
   sourceLaw05, sourceLaw06, sourceLaw07, sourceLaw08, sourceLaw09,
   sourceLaw10, sourceLaw11, sourceLaw12]

theorem sourceBasis_length : sourceBasis.length = 13 := by
  decide

private def fixedStep
    (lawIndex : Nat) (direction : ChainReplay.Direction)
    (leftContext rightContext : List Nat)
    (substitution : List (List Nat)) : ChainReplay.Chain Nat :=
  [{lawIndex, direction, leftContext, rightContext, substitution}]

private def unchanged : List (List Nat) := [[0], [1], [2]]

theorem reversedSourceLaw00 :
    Derives Rank020.basis sourceLaw00.reversed.lhs sourceLaw00.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 0 .forward [] [] unchanged) (by decide)

theorem reversedSourceLaw01 :
    Derives Rank020.basis sourceLaw01.reversed.lhs sourceLaw01.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 5 .backward [] [] unchanged) (by decide)

theorem reversedSourceLaw02 :
    Derives Rank020.basis sourceLaw02.reversed.lhs sourceLaw02.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 2 .backward [] [] unchanged) (by decide)

theorem reversedSourceLaw03 :
    Derives Rank020.basis sourceLaw03.reversed.lhs sourceLaw03.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 3 .forward [] [] unchanged) (by decide)

theorem reversedSourceLaw04 :
    Derives Rank020.basis sourceLaw04.reversed.lhs sourceLaw04.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 1 .backward [] [] unchanged) (by decide)

theorem reversedSourceLaw05 :
    Derives Rank020.basis sourceLaw05.reversed.lhs sourceLaw05.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 8 .forward [] [] unchanged) (by decide)

theorem reversedSourceLaw06 :
    Derives Rank020.basis sourceLaw06.reversed.lhs sourceLaw06.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 7 .forward [] [] unchanged) (by decide)

theorem reversedSourceLaw07 :
    Derives Rank020.basis sourceLaw07.reversed.lhs sourceLaw07.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 6 .forward [] [] unchanged) (by decide)

theorem reversedSourceLaw08 :
    Derives Rank020.basis sourceLaw08.reversed.lhs sourceLaw08.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 9 .forward [] [] [[1], [0], [2]]) (by decide)

/-- `yzxyx -> yxzyx`, using frozen law 12 with a protected final `x`. -/
theorem attachmentEdge00 :
    Derives Rank020.basis (word 1 [2, 0, 1, 0]) (word 1 [0, 2, 1, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 12 .forward [] [0] [[1], [2], [0]]) (by decide)

/-- `yxzyx -> yxyzx`, using frozen law 12 behind a protected first `y`. -/
theorem attachmentEdge01 :
    Derives Rank020.basis (word 1 [0, 2, 1, 0]) (word 1 [0, 1, 2, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 12 .forward [1] [] [[0], [2], [1]]) (by decide)

/-- `yxyzx -> xyyzx`, using frozen law 11 with its literal variable swap. -/
theorem attachmentEdge02 :
    Derives Rank020.basis (word 1 [0, 1, 2, 0]) (word 0 [1, 1, 2, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 11 .forward [] [] [[1], [0], [2]]) (by decide)

/-- `xyyzx -> xzyyx`, using frozen law 12 and the genuine composite `yy`. -/
theorem attachmentEdge03 :
    Derives Rank020.basis (word 0 [1, 1, 2, 0]) (word 0 [2, 1, 1, 0]) :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 12 .forward [] [] [[0], [1, 1], [2]]) (by decide)

/-- The only nontrivial source adapter, with all three intermediate words
fixed by separately checked Lean declarations. -/
theorem reversedSourceLaw09 :
    Derives Rank020.basis sourceLaw09.reversed.lhs sourceLaw09.reversed.rhs := by
  exact attachmentEdge00.trans
    (attachmentEdge01.trans (attachmentEdge02.trans attachmentEdge03))

theorem reversedSourceLaw10 :
    Derives Rank020.basis sourceLaw10.reversed.lhs sourceLaw10.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 4 .backward [] [] [[2], [1], [0]]) (by decide)

theorem reversedSourceLaw11 :
    Derives Rank020.basis sourceLaw11.reversed.lhs sourceLaw11.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 12 .forward [] [] [[0], [2], [1]]) (by decide)

theorem reversedSourceLaw12 :
    Derives Rank020.basis sourceLaw12.reversed.lhs sourceLaw12.reversed.rhs :=
  ChainReplay.check_sound
    (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 10 .forward [] [] [[2], [1], [0]]) (by decide)

/-- Every axiom of the LITERAL reversed source basis derives under the
authenticated target basis; this is not a bare basis retarget. -/
theorem reversedSourceAxiomsDeriveFrozen
    (identity : Identity Nat)
    (member : identity ∈ reversedBasis sourceBasis) :
    Derives Rank020.basis identity.lhs identity.rhs := by
  simp only [sourceBasis, reversedBasis, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact reversedSourceLaw10
  · exact reversedSourceLaw11
  · exact reversedSourceLaw12

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_798OppositeAdapter
