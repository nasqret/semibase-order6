import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiProposition8A

open SemigroupBasis

/-- The nonempty word with the displayed head and tail. -/
def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-!
## Lee--Li Proposition 8.1, published monoid A

Variables use the shared Lee--Li encoding
`x = 0`, `h = 1`, `y = 2`, and `t = 3`.
-/

def htxxx : Word Nat := w 1 [3, 0, 0, 0]
def xhxtx : Word Nat := w 0 [1, 0, 3, 0]
def hxxx : Word Nat := w 1 [0, 0, 0]
def xhxx : Word Nat := w 0 [1, 0, 0]
def txxx : Word Nat := w 3 [0, 0, 0]
def xxtx : Word Nat := w 0 [0, 3, 0]
def xhxyyy : Word Nat := w 0 [1, 0, 2, 2, 2]
def xhyyyx : Word Nat := w 0 [1, 2, 2, 2, 0]
def xhytxy : Word Nat := w 0 [1, 2, 3, 0, 2]
def xhytyx : Word Nat := w 0 [1, 2, 3, 2, 0]
def xhyxy : Word Nat := w 0 [1, 2, 0, 2]
def xhyyx : Word Nat := w 0 [1, 2, 2, 0]
def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxxyyy : Word Nat := w 0 [0, 0, 2, 2, 2]
def yyyxxx : Word Nat := w 2 [2, 2, 0, 0, 0]
def xxyyy : Word Nat := w 0 [0, 2, 2, 2]
def xyyyx : Word Nat := w 0 [2, 2, 2, 0]
def xyhxty : Word Nat := w 0 [2, 1, 0, 3, 2]
def yxhxty : Word Nat := w 2 [0, 1, 0, 3, 2]
def xyhxy : Word Nat := w 0 [2, 1, 0, 2]
def yxhxy : Word Nat := w 2 [0, 1, 0, 2]
def xytxy : Word Nat := w 0 [2, 3, 0, 2]
def xytyx : Word Nat := w 0 [2, 3, 2, 0]
def xyxty : Word Nat := w 0 [2, 0, 3, 2]
def yxxty : Word Nat := w 2 [0, 0, 3, 2]
def xyxy : Word Nat := w 0 [2, 0, 2]
def xyyx : Word Nat := w 0 [2, 2, 0]
def yxxy : Word Nat := w 2 [0, 0, 2]

/-- Accepted law 1: `htxxx = xhxtx`. -/
def tripleGatherGeneralLaw : Identity Nat := ⟨htxxx, xhxtx⟩

/-- Accepted law 2: `hxxx = xhxx`. -/
def tripleGatherFinalGapEmptyLaw : Identity Nat := ⟨hxxx, xhxx⟩

/-- Accepted law 3: `txxx = xxtx`. -/
def tripleGatherInitialGapEmptyLaw : Identity Nat := ⟨txxx, xxtx⟩

/-- Accepted law 4: `xhxyyy = xhyyyx`. -/
def cubeMoveGeneralLaw : Identity Nat := ⟨xhxyyy, xhyyyx⟩

/-- Accepted law 5: `xhytxy = xhytyx`. -/
def sortGeneralRightLaw : Identity Nat := ⟨xhytxy, xhytyx⟩

/-- Accepted law 6: `xhyxy = xhyyx`. -/
def sortFinalGapRightLaw : Identity Nat := ⟨xhyxy, xhyyx⟩

/-- Accepted law 7: `xxx = xxxx`. -/
def powerLaw : Identity Nat := ⟨xxx, xxxx⟩

/-- Accepted law 8: `xxxyyy = yyyxxx`. -/
def cubeInterchangeLaw : Identity Nat := ⟨xxxyyy, yyyxxx⟩

/-- Accepted law 9: `xxyyy = xyyyx`. -/
def cubeMoveFinalGapEmptyLaw : Identity Nat := ⟨xxyyy, xyyyx⟩

/-- Accepted law 10: `xyhxty = yxhxty`. -/
def sortGeneralLeftLaw : Identity Nat := ⟨xyhxty, yxhxty⟩

/-- Accepted law 11: `xyhxy = yxhxy`. -/
def sortFinalGapLeftLaw : Identity Nat := ⟨xyhxy, yxhxy⟩

/-- Accepted law 12: `xytxy = xytyx`. -/
def sortInitialGapRightLaw : Identity Nat := ⟨xytxy, xytyx⟩

/-- Accepted law 13: `xyxty = yxxty`. -/
def sortInitialGapLeftLaw : Identity Nat := ⟨xyxty, yxxty⟩

/-- Accepted law 14: `xyxy = xyyx`. -/
def sortBothEmptyRightLaw : Identity Nat := ⟨xyxy, xyyx⟩

/-- Accepted law 15: `xyxy = yxxy`. -/
def sortBothEmptyLeftLaw : Identity Nat := ⟨xyxy, yxxy⟩

/-- The exact direct Proposition 8.1/A basis accepted for `S6_5647`, in
literal packet order and orientation. -/
def basis : List (Identity Nat) :=
  [tripleGatherGeneralLaw, tripleGatherFinalGapEmptyLaw,
    tripleGatherInitialGapEmptyLaw, cubeMoveGeneralLaw,
    sortGeneralRightLaw, sortFinalGapRightLaw, powerLaw,
    cubeInterchangeLaw, cubeMoveFinalGapEmptyLaw,
    sortGeneralLeftLaw, sortFinalGapLeftLaw, sortInitialGapRightLaw,
    sortInitialGapLeftLaw, sortBothEmptyRightLaw,
    sortBothEmptyLeftLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

/-- The eight Proposition 8.1 laws that only permute the two displayed later
occurrences.  This is exactly accepted laws 5, 6, and 10--15, in packet
order. -/
def sortBasis : List (Identity Nat) :=
  [sortGeneralRightLaw, sortFinalGapRightLaw,
    sortGeneralLeftLaw, sortFinalGapLeftLaw,
    sortInitialGapRightLaw, sortInitialGapLeftLaw,
    sortBothEmptyRightLaw, sortBothEmptyLeftLaw]

/-! ## Four-variable finite reflection -/

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Exhaustive checking of the four displayed variables proves soundness of
the literal 15-law system for an exact finite table. -/
theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

private theorem satisfied_of_fused_check
    (candidate : FiniteTable) (identity : Identity Nat)
    (member : identity ∈ basis)
    (checked :
      candidate.checkIdentityFused (identity.map toFinFour) = true) :
    identity.SatisfiedBy candidate.semigroup := by
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound
      (identity.map toFinFour) checked
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

/-- Memory-bounded target soundness interface.  The 15 fused certificates
remain separate so the kernel need not materialize a single large decision
term for the complete basis. -/
theorem models_of_individual_fused_checks
    (candidate : FiniteTable)
    (checkTripleGatherGeneral :
      candidate.checkIdentityFused
        (tripleGatherGeneralLaw.map toFinFour) = true)
    (checkTripleGatherFinalGapEmpty :
      candidate.checkIdentityFused
        (tripleGatherFinalGapEmptyLaw.map toFinFour) = true)
    (checkTripleGatherInitialGapEmpty :
      candidate.checkIdentityFused
        (tripleGatherInitialGapEmptyLaw.map toFinFour) = true)
    (checkCubeMoveGeneral :
      candidate.checkIdentityFused
        (cubeMoveGeneralLaw.map toFinFour) = true)
    (checkSortGeneralRight :
      candidate.checkIdentityFused
        (sortGeneralRightLaw.map toFinFour) = true)
    (checkSortFinalGapRight :
      candidate.checkIdentityFused
        (sortFinalGapRightLaw.map toFinFour) = true)
    (checkPower :
      candidate.checkIdentityFused (powerLaw.map toFinFour) = true)
    (checkCubeInterchange :
      candidate.checkIdentityFused
        (cubeInterchangeLaw.map toFinFour) = true)
    (checkCubeMoveFinalGapEmpty :
      candidate.checkIdentityFused
        (cubeMoveFinalGapEmptyLaw.map toFinFour) = true)
    (checkSortGeneralLeft :
      candidate.checkIdentityFused
        (sortGeneralLeftLaw.map toFinFour) = true)
    (checkSortFinalGapLeft :
      candidate.checkIdentityFused
        (sortFinalGapLeftLaw.map toFinFour) = true)
    (checkSortInitialGapRight :
      candidate.checkIdentityFused
        (sortInitialGapRightLaw.map toFinFour) = true)
    (checkSortInitialGapLeft :
      candidate.checkIdentityFused
        (sortInitialGapLeftLaw.map toFinFour) = true)
    (checkSortBothEmptyRight :
      candidate.checkIdentityFused
        (sortBothEmptyRightLaw.map toFinFour) = true)
    (checkSortBothEmptyLeft :
      candidate.checkIdentityFused
        (sortBothEmptyLeftLaw.map toFinFour) = true) :
    Models candidate.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact satisfied_of_fused_check candidate tripleGatherGeneralLaw
      (by simp [basis]) checkTripleGatherGeneral
  · exact satisfied_of_fused_check candidate tripleGatherFinalGapEmptyLaw
      (by simp [basis]) checkTripleGatherFinalGapEmpty
  · exact satisfied_of_fused_check candidate tripleGatherInitialGapEmptyLaw
      (by simp [basis]) checkTripleGatherInitialGapEmpty
  · exact satisfied_of_fused_check candidate cubeMoveGeneralLaw
      (by simp [basis]) checkCubeMoveGeneral
  · exact satisfied_of_fused_check candidate sortGeneralRightLaw
      (by simp [basis]) checkSortGeneralRight
  · exact satisfied_of_fused_check candidate sortFinalGapRightLaw
      (by simp [basis]) checkSortFinalGapRight
  · exact satisfied_of_fused_check candidate powerLaw
      (by simp [basis]) checkPower
  · exact satisfied_of_fused_check candidate cubeInterchangeLaw
      (by simp [basis]) checkCubeInterchange
  · exact satisfied_of_fused_check candidate cubeMoveFinalGapEmptyLaw
      (by simp [basis]) checkCubeMoveFinalGapEmpty
  · exact satisfied_of_fused_check candidate sortGeneralLeftLaw
      (by simp [basis]) checkSortGeneralLeft
  · exact satisfied_of_fused_check candidate sortFinalGapLeftLaw
      (by simp [basis]) checkSortFinalGapLeft
  · exact satisfied_of_fused_check candidate sortInitialGapRightLaw
      (by simp [basis]) checkSortInitialGapRight
  · exact satisfied_of_fused_check candidate sortInitialGapLeftLaw
      (by simp [basis]) checkSortInitialGapLeft
  · exact satisfied_of_fused_check candidate sortBothEmptyRightLaw
      (by simp [basis]) checkSortBothEmptyRight
  · exact satisfied_of_fused_check candidate sortBothEmptyLeftLaw
      (by simp [basis]) checkSortBothEmptyLeft

/-! ## Sorting-subbasis transport -/

/-- Every axiom of the reusable sorting subsystem occurs literally in the
full Proposition 8.1/A basis. -/
theorem sortBasis_subset_basis
    (identity : Identity Nat) (member : identity ∈ sortBasis) :
    identity ∈ basis := by
  simp only [sortBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [basis]

/-- Lift a word derivation from the sorting subsystem to the full basis. -/
theorem liftSortDerives
    {left right : Word Nat}
    (derivation : Derives sortBasis left right) :
    Derives basis left right :=
  derivation.transport fun identity member =>
    Derives.fromBasis (sortBasis_subset_basis identity member)

/-- Lift a list-level derivation from the sorting subsystem to the full
Proposition 8.1/A basis. -/
theorem liftSortListDerives
    {left right : List Nat}
    (derivation :
      SemigroupBasis.CoRoots.S5_107.ListDerives sortBasis left right) :
    SemigroupBasis.CoRoots.S5_107.ListDerives basis left right := by
  cases derivation with
  | empty =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.empty
  | words wordDerivation =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.words
        (liftSortDerives wordDerivation)

end SemigroupBasis.CoRoots.Order6LeeLiProposition8A
