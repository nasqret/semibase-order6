import SemigroupBasis.CoRoots.Order6FactorPairS2S594
import SemigroupBasis.CoRoots.S5_344Family
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Subdirect

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S5356

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyxx : Word Nat := w 0 [0, 1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xxyyy : Word Nat := w 0 [0, 1, 1, 1]
def xyyyx : Word Nat := w 0 [1, 1, 1, 0]
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyxz : Word Nat := w 0 [1, 0, 2]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyy : Word Nat := w 0 [2, 1, 1]
def xyzt : Word Nat := w 0 [1, 2, 3]
def xzyt : Word Nat := w 0 [2, 1, 3]

def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def tripleLeftContractionLaw : Identity Nat := ⟨xxxyx, xyx⟩
def endpointTransferLaw : Identity Nat := ⟨xxyx, xyxx⟩
def splitEndpointContractionLaw : Identity Nat := ⟨xxyxx, xyx⟩
def squareInterleaveLaw : Identity Nat := ⟨xxyy, xyxy⟩
def squareFinalSwitchLaw : Identity Nat := ⟨xxyy, xyyx⟩
def tripleFinalSwitchLaw : Identity Nat := ⟨xxyyy, xyyyx⟩
def doubledInitialMoveLaw : Identity Nat := ⟨xxyz, xyxz⟩
def attachmentXYYZXLaw : Identity Nat := ⟨xxyzy, xyyzx⟩
def rightTripleExpansionLaw : Identity Nat := ⟨xyx, xyxxx⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩
def repeatedFinalSwapLaw : Identity Nat := ⟨xyzy, xzyy⟩
def openInteriorSwapLaw : Identity Nat := ⟨xyzt, xzyt⟩

/-- The corrected thirteen-law basis for the `C2 x S5_356` factor-pair
family. The squarefree open-interior law is essential: none of the twelve
pre-correction laws can rewrite a squarefree four-letter word. -/
def basis : List (Identity Nat) :=
  [powerLaw, tripleLeftContractionLaw, endpointTransferLaw,
    splitEndpointContractionLaw, squareInterleaveLaw, squareFinalSwitchLaw,
    tripleFinalSwitchLaw, doubledInitialMoveLaw, attachmentXYYZXLaw,
    rightTripleExpansionLaw, openInteriorSwapLaw, closedInteriorSwapLaw,
    repeatedFinalSwapLaw]

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem modelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinFour).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp basisRoundTripChecked) identity member
  rw [restored] at finiteValid
  exact finiteValid

theorem modelsS2_2 :
    Models SemigroupBasis.Generated.S2_2.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S2_2.table (by decide)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem modelsS5_356 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_356.table.semigroup basis :=
  modelsOfFiniteChecks
    SemigroupBasis.Generated.Catalogue.S5_356.table (by decide)

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

theorem derivesBasisSubstitution
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat → Word Nat) :
    Derives basis
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis member) substitution

theorem derivesFourToTwo (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have substituted :=
    derivesBasisSubstitution powerLaw (by simp [basis])
      (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

theorem derivesTripleLeftContraction (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ v) ++ u) ((u ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution tripleLeftContractionLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [tripleLeftContractionLaw, xxxyx, xyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesEndpointTransfer (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ u) ((u ++ v) ++ (u ++ u)) := by
  have substituted :=
    derivesBasisSubstitution endpointTransferLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [endpointTransferLaw, xxyx, xyxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

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

theorem derivesTripleFinalSwitch (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ (v ++ v))
      ((((u ++ v) ++ v) ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution tripleFinalSwitchLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [tripleFinalSwitchLaw, xxyyy, xyyyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

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

theorem derivesOpenInteriorSwap (u v z t : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ t)
      (((u ++ z) ++ v) ++ t) := by
  exact
    SemigroupBasis.CoRoots.Order6FactorPairS2S594.derivesOpenInteriorSwapOfMember
      (by
        change openInteriorSwapLaw ∈ basis
        simp [basis]) u v z t

end SemigroupBasis.CoRoots.Order6FactorPairS2S5356
