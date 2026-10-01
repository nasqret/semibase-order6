import SemigroupBasis.CoRoots.Order6Day13.S1193.S1193Presentation
import SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110Prelude

/-! Five typed edges rebase the four reversed laws of the pinned complete
S3_6/S5_110 intersection onto the approved S6_1193 presentation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day13.S1193

open SemigroupBasis

abbrev sourceBasis : List (Identity Nat) :=
  reversedBasis Order6FactorPairS3_6S5_110.basis

def sourceLaw00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩
def sourceLaw01 : Identity Nat := ⟨Word.mk 1 [1, 0, 0], Word.mk 0 [1, 1, 0]⟩
def sourceLaw02 : Identity Nat := ⟨Word.mk 2 [1, 0, 0], Word.mk 2 [0, 1, 0]⟩
def sourceLaw03 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [0, 1]⟩

theorem sourceBasis_exact :
    sourceBasis = [sourceLaw00, sourceLaw01, sourceLaw02, sourceLaw03] := by decide

theorem bridgeLaw00 : Derives basis sourceLaw00.lhs sourceLaw00.rhs :=
  rawLaw00 (Word.singleton 0)

theorem bridgeLaw01 : Derives basis sourceLaw01.lhs sourceLaw01.rhs :=
  rawLaw02 (Word.singleton 1) (Word.singleton 0)

/-- The intermediate is w u u v. All three endpoints use left association. -/
theorem rawDoubledInteriorMove (u v w : Word Nat) :
    Derives basis (((w ++ v) ++ u) ++ u) (((w ++ u) ++ v) ++ u) := by
  have first : Derives basis (((w ++ v) ++ u) ++ u) (((w ++ u) ++ u) ++ v) :=
    (rawLaw03 w u v).symm
  have second : Derives basis (((w ++ u) ++ u) ++ v) (((w ++ u) ++ v) ++ u) := by
    simpa only [Word.append_assoc] using Derives.prepend w (rawLaw01 u v)
  exact first.trans second

theorem bridgeLaw02 : Derives basis sourceLaw02.lhs sourceLaw02.rhs :=
  rawDoubledInteriorMove (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)

theorem bridgeLaw03 : Derives basis sourceLaw03.lhs sourceLaw03.rhs :=
  (rawLaw01 (Word.singleton 0) (Word.singleton 1)).symm

theorem sourceLawDerives (identity : Identity Nat) (member : identity ∈ sourceBasis) :
    Derives basis identity.lhs identity.rhs := by
  rw [sourceBasis_exact] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact bridgeLaw00
  · exact bridgeLaw01
  · exact bridgeLaw02
  · exact bridgeLaw03

theorem transportSource {left right : Word Nat}
    (derivation : Derives sourceBasis left right) : Derives basis left right :=
  derivation.transport sourceLawDerives

end SemigroupBasis.CoRoots.Order6Day13.S1193
