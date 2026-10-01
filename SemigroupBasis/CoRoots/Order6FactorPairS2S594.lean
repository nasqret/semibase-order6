import SemigroupBasis.CoRoots.S5_94Family
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S594

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xxxyy : Word Nat := w 0 [0, 0, 1, 1]
def yxxxy : Word Nat := w 1 [0, 0, 0, 1]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyxx : Word Nat := w 0 [0, 1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyxz : Word Nat := w 0 [1, 0, 2]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def yxxzy : Word Nat := w 1 [0, 0, 2, 1]
def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyy : Word Nat := w 0 [2, 1, 1]
def xyzt : Word Nat := w 0 [1, 2, 3]
def xzyt : Word Nat := w 0 [2, 1, 3]

def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def tripleLeftContractionLaw : Identity Nat := ⟨xxxyx, xyx⟩
def tripleHeadSwitchLaw : Identity Nat := ⟨xxxyy, yxxxy⟩
def endpointTransferLaw : Identity Nat := ⟨xxyx, xyxx⟩
def splitEndpointContractionLaw : Identity Nat := ⟨xxyxx, xyx⟩
def squareInterleaveLaw : Identity Nat := ⟨xxyy, xyxy⟩
def squareFinalSwitchLaw : Identity Nat := ⟨xxyy, xyyx⟩
def squareInitialSwitchLaw : Identity Nat := ⟨xxyy, yxxy⟩
def doubledInitialMoveLaw : Identity Nat := ⟨xxyz, xyxz⟩
def attachmentXYYZXLaw : Identity Nat := ⟨xxyzy, xyyzx⟩
def attachmentYXXZYLaw : Identity Nat := ⟨xxyzy, yxxzy⟩
def rightTripleExpansionLaw : Identity Nat := ⟨xyx, xyxxx⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩
def repeatedFinalSwapLaw : Identity Nat := ⟨xyzy, xzyy⟩
def openInteriorSwapLaw : Identity Nat := ⟨xyzt, xzyt⟩

/-- The corrected fifteen-law basis for the `C2 x S5_94` factor-pair family.
The final squarefree law is necessary: none of the original fourteen laws can
rewrite a squarefree four-letter word. -/
def basis : List (Identity Nat) :=
  [powerLaw, tripleLeftContractionLaw, tripleHeadSwitchLaw,
    endpointTransferLaw, splitEndpointContractionLaw,
    squareInterleaveLaw, squareFinalSwitchLaw, squareInitialSwitchLaw,
    doubledInitialMoveLaw, attachmentXYYZXLaw, attachmentYXXZYLaw,
    rightTripleExpansionLaw, closedInteriorSwapLaw, repeatedFinalSwapLaw,
    openInteriorSwapLaw]

def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem basisRoundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basisRoundTripChecked) identity member

/-- Executable four-variable checking proves soundness of this fixed basis on
any finite table. -/
theorem modelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basisRoundTrip identity member] at finiteValid
  exact finiteValid

private theorem cyclicTwoChecked :
    finiteBasis.all cyclicTwo.checkIdentity = true := by
  decide

theorem modelsCyclicTwo : Models cyclicTwo.semigroup basis :=
  modelsOfFiniteChecks cyclicTwo cyclicTwoChecked

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem s5_94Checked :
    finiteBasis.all
      SemigroupBasis.Generated.Catalogue.S5_94.table.checkIdentity = true := by
  decide

theorem modelsS5_94 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_94.table.semigroup basis :=
  modelsOfFiniteChecks
    SemigroupBasis.Generated.Catalogue.S5_94.table s5_94Checked

theorem openInteriorSwapSatisfiedByCyclicTwo :
    openInteriorSwapLaw.SatisfiedBy cyclicTwo.semigroup :=
  modelsCyclicTwo openInteriorSwapLaw (by simp [basis])

theorem openInteriorSwapSatisfiedByS5_94 :
    openInteriorSwapLaw.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_94.table.semigroup :=
  modelsS5_94 openInteriorSwapLaw (by simp [basis])

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private def instantiateFourWords
    (u v z t : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

theorem derivesBasisSubstitution
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat → Word Nat) :
    Derives basis
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis member) substitution

/-- Contract four consecutive copies of a nonempty block to two. -/
theorem derivesFourToTwo (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have substituted :=
    derivesBasisSubstitution powerLaw (by simp [basis])
      (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

/-- Contract `u^3 v u` to `u v u`. -/
theorem derivesTripleLeftContraction (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ v) ++ u) ((u ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution tripleLeftContractionLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [tripleLeftContractionLaw, xxxyx, xyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Move a repeated initial block through a doubled final block. -/
theorem derivesTripleHeadSwitch (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ v) ++ v)
      ((((v ++ u) ++ u) ++ u) ++ v) := by
  have substituted :=
    derivesBasisSubstitution tripleHeadSwitchLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [tripleHeadSwitchLaw, xxxyy, yxxxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Move one copy of a repeated endpoint from the left to the right. -/
theorem derivesEndpointTransfer (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ u) ((u ++ v) ++ (u ++ u)) := by
  have substituted :=
    derivesBasisSubstitution endpointTransferLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [endpointTransferLaw, xxyx, xyxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Contract two separated endpoint pairs to one pair. -/
theorem derivesSplitEndpointContraction (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ u) ++ u) ((u ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution splitEndpointContractionLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [splitEndpointContractionLaw, xxyxx, xyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSquareInterleave (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v)) ((u ++ v) ++ (u ++ v)) := by
  have substituted :=
    derivesBasisSubstitution squareInterleaveLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [squareInterleaveLaw, xxyy, xyxy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareFinalSwitch (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v)) (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution squareFinalSwitchLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [squareFinalSwitchLaw, xxyy, xyyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareInitialSwitch (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v)) (((v ++ u) ++ u) ++ v) := by
  have substituted :=
    derivesBasisSubstitution squareInitialSwitchLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [squareInitialSwitchLaw, xxyy, yxxy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesDoubledInitialMove (u v z : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ z) (((u ++ v) ++ u) ++ z) := by
  have substituted :=
    derivesBasisSubstitution doubledInitialMoveLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [doubledInitialMoveLaw, xxyz, xyxz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesAttachmentXYYZX (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ v) ++ z) ++ u) := by
  have substituted :=
    derivesBasisSubstitution attachmentXYYZXLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [attachmentXYYZXLaw, xxyzy, xyyzx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesAttachmentYXXZY (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((v ++ u) ++ u) ++ z) ++ v) := by
  have substituted :=
    derivesBasisSubstitution attachmentYXXZYLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [attachmentYXXZYLaw, xxyzy, yxxzy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesRightTripleExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((((u ++ v) ++ u) ++ u) ++ u) := by
  have substituted :=
    derivesBasisSubstitution rightTripleExpansionLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [rightTripleExpansionLaw, xyx, xyxxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesClosedInteriorSwap (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u) (((u ++ z) ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution closedInteriorSwapLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [closedInteriorSwapLaw, xyzx, xzyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesRepeatedFinalSwap (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ v) (((u ++ z) ++ v) ++ v) := by
  have substituted :=
    derivesBasisSubstitution repeatedFinalSwapLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [repeatedFinalSwapLaw, xyzy, xzyy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Any basis containing `xyzt = xzyt` permits adjacent nonempty blocks to be
swapped strictly between fixed nonempty prefix and suffix contexts. -/
theorem derivesOpenInteriorSwapOfMember
    {candidateBasis : List (Identity Nat)}
    (member : openInteriorSwapLaw ∈ candidateBasis)
    (u v z t : Word Nat) :
    Derives candidateBasis
      (((u ++ v) ++ z) ++ t)
      (((u ++ z) ++ v) ++ t) := by
  have substituted :=
    Derives.subst (Derives.fromBasis member)
      (instantiateFourWords u v z t)
  simpa [openInteriorSwapLaw, xyzt, xzyt, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesOpenInteriorSwap (u v z t : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ t)
      (((u ++ z) ++ v) ++ t) :=
  derivesOpenInteriorSwapOfMember (by simp [basis]) u v z t

end SemigroupBasis.CoRoots.Order6FactorPairS2S594
