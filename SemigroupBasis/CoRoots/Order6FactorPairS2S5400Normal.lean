import SemigroupBasis.CoRoots.S5_400CanonicalSufficiency
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.Examples.UniqueSeparatorFourSortDerives
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Generated.S5_400PublishedRoots
import SemigroupBasis.Opposite
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S5400Normal

open SemigroupBasis
open SemigroupBasis.Examples

/-!
Unrestricted joint completeness for the direct factor pair
`S2_2 x S5_400` (WO-3 obligation
`OBL-JOINT-S2_2_direct-S5_400_direct`).  The corresponding order-six
roots are `S6_4089`, `S6_4199`, and `S6_4295`.

The right factor fixes the capped multiplicities, the ordered sequence of
globally simple variables, and the first/last simple-variable gaps of every
repeated variable.  The cyclic factor additionally fixes every occurrence
parity.  Multiplicities can therefore be reduced to `0,1,2,3`.  A variable
with three copies is put in first-pair position; repeated blocks can then be
sorted independently between the aligned simple separators.
-/

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxxyy : Word Nat := w 0 [0, 0, 1, 1]
def yxxxy : Word Nat := w 1 [0, 0, 0, 1]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyxx : Word Nat := w 0 [0, 1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xxyzx : Word Nat := w 0 [0, 1, 2, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
def yxxzy : Word Nat := w 1 [0, 0, 2, 1]
def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
def xyxzz : Word Nat := w 0 [1, 0, 2, 2]
def xyzxz : Word Nat := w 0 [1, 2, 0, 2]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]
def xyzxy : Word Nat := w 0 [1, 2, 0, 1]
def xyzyx : Word Nat := w 0 [1, 2, 1, 0]
def yxzxy : Word Nat := w 1 [0, 2, 0, 1]

def powerLaw : Identity Nat := Identity.mk xx xxxx
def tripleLeftContractionLaw : Identity Nat :=
  Identity.mk xxxyx xyx
def tripleHeadSwitchLaw : Identity Nat := Identity.mk xxxyy yxxxy
def endpointTransferLaw : Identity Nat := Identity.mk xxyx xyxx
def splitEndpointContractionLaw : Identity Nat :=
  Identity.mk xxyxx xyx
def squareInterleaveLaw : Identity Nat := Identity.mk xxyy xyxy
def squareFinalLaw : Identity Nat := Identity.mk xxyy xyyx
def squareInitialLaw : Identity Nat := Identity.mk xxyy yxxy
def gatherGeneralLaw : Identity Nat := Identity.mk xxyzx xyxzx
def attachmentXYXZYLaw : Identity Nat := Identity.mk xxyzy xyxzy
def attachmentYXXZYLaw : Identity Nat := Identity.mk xxyzy yxxzy
def rightTripleExpansionLaw : Identity Nat := Identity.mk xyx xyxxx
def doubledSuffixMoveLaw : Identity Nat := Identity.mk xyxzz xyzxz
def terminalSquareMoveLaw : Identity Nat := Identity.mk xyxzz xyzzx
def terminalRightSwitchLaw : Identity Nat := Identity.mk xyzxy xyzyx
def terminalLeftSwitchLaw : Identity Nat := Identity.mk xyzxy yxzxy

/-- The exact sixteen-law candidate recorded for the direct
`S2_2 x S5_400` factor-pair obligation. -/
def basis : List (Identity Nat) :=
  [powerLaw, tripleLeftContractionLaw, tripleHeadSwitchLaw,
    endpointTransferLaw, splitEndpointContractionLaw,
    squareInterleaveLaw, squareFinalLaw, squareInitialLaw,
    gatherGeneralLaw, attachmentXYXZYLaw, attachmentYXXZYLaw,
    rightTripleExpansionLaw, doubledSuffixMoveLaw,
    terminalSquareMoveLaw, terminalRightSwitchLaw,
    terminalLeftSwitchLaw]

theorem basis_length : basis.length = 16 := by
  decide

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem modelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinThree).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp basisRoundTripChecked) identity member
  rw [restored] at finiteValid
  exact finiteValid

/-- Every candidate law is valid in the cyclic factor. -/
theorem modelsS2_2 :
    Models SemigroupBasis.Generated.S2_2.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S2_2.table (by decide)

set_option maxHeartbeats 1000000 in
/-- Every candidate law is valid in the direct `S5_400` factor. -/
theorem modelsS5_400 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup basis :=
  modelsOfFiniteChecks
    SemigroupBasis.Generated.Catalogue.S5_400.table (by decide)

private theorem sameIdentityTheoryOverOfCommonBasis
    {A : Type u} {B : Type v} {X : Type w}
    {G : Semigroup A} {H : Semigroup B}
    {commonBasis : List (Identity X)}
    (basisForG : BasisFor G commonBasis)
    (basisForH : BasisFor H commonBasis) :
    SameIdentityTheoryOver G H X := by
  intro identity
  constructor
  · intro validInG valuation
    exact Derives.sound basisForH.1
      (basisForG.2 identity validInG) valuation
  · intro validInH valuation
    exact Derives.sound basisForG.1
      (basisForH.2 identity validInH) valuation

/-- The two published order-five representatives have the same identity
theory because the same sealed sixteen-law basis is complete for both. -/
theorem sameTheoryS5_400S5_840 :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.Generated.S5_400PublishedRoots.S5_400.representativeBasisFor
    SemigroupBasis.Generated.S5_400PublishedRoots.S5_840.representativeBasisFor

/-- Candidate soundness transports directly to `S5_840`. -/
theorem modelsS5_840 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup basis :=
  modelsS5_400.transportIdentityTheory sameTheoryS5_400S5_840

private abbrev ListDerives (left right : List Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis left right

private def instantiateThreeWords
    (first second third : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

theorem derivesBasisSubstitution
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat -> Word Nat) :
    Derives basis
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis member) substitution

theorem derivesFourToTwo (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have substituted :=
    derivesBasisSubstitution powerLaw (by simp [basis])
      (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted.symm

theorem derivesTripleLeftContraction (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ v) ++ u)
      ((u ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution tripleLeftContractionLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [tripleLeftContractionLaw, xxxyx, xyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesTripleHeadSwitch (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ v) ++ v)
      ((((v ++ u) ++ u) ++ u) ++ v) := by
  have substituted :=
    derivesBasisSubstitution tripleHeadSwitchLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [tripleHeadSwitchLaw, xxxyy, yxxxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesEndpointTransfer (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ u)
      ((u ++ v) ++ (u ++ u)) := by
  have substituted :=
    derivesBasisSubstitution endpointTransferLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [endpointTransferLaw, xxyx, xyxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSplitEndpointContraction (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ u) ++ u)
      ((u ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution splitEndpointContractionLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [splitEndpointContractionLaw, xxyxx, xyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSquareInterleave (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      ((u ++ v) ++ (u ++ v)) := by
  have substituted :=
    derivesBasisSubstitution squareInterleaveLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [squareInterleaveLaw, xxyy, xyxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSquareFinal (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution squareFinalLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [squareFinalLaw, xxyy, xyyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSquareInitial (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      (((v ++ u) ++ u) ++ v) := by
  have substituted :=
    derivesBasisSubstitution squareInitialLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [squareInitialLaw, xxyy, yxxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Gather an interior occurrence next to the first occurrence while
retaining the final occurrence. -/
theorem derivesGatherGeneral (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ u)
      ((((u ++ v) ++ u) ++ z) ++ u) := by
  have substituted :=
    derivesBasisSubstitution gatherGeneralLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [gatherGeneralLaw, xxyzx, xyxzx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesAttachmentXYXZY (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ u) ++ z) ++ v) := by
  have substituted :=
    derivesBasisSubstitution attachmentXYXZYLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [attachmentXYXZYLaw, xxyzy, xyxzy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesAttachmentYXXZY (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((v ++ u) ++ u) ++ z) ++ v) := by
  have substituted :=
    derivesBasisSubstitution attachmentYXXZYLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [attachmentYXXZYLaw, xxyzy, yxxzy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesRightTripleExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u)
      ((((u ++ v) ++ u) ++ u) ++ u) := by
  have substituted :=
    derivesBasisSubstitution rightTripleExpansionLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [rightTripleExpansionLaw, xyx, xyxxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesDoubledSuffixMove (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ z)
      ((((u ++ v) ++ z) ++ u) ++ z) := by
  have substituted :=
    derivesBasisSubstitution doubledSuffixMoveLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [doubledSuffixMoveLaw, xyxzz, xyzxz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesTerminalSquareMove (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ z)
      ((((u ++ v) ++ z) ++ z) ++ u) := by
  have substituted :=
    derivesBasisSubstitution terminalSquareMoveLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [terminalSquareMoveLaw, xyxzz, xyzzx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesTerminalRightSwitch (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ z) ++ u) ++ v)
      ((((u ++ v) ++ z) ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution terminalRightSwitchLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [terminalRightSwitchLaw, xyzxy, xyzyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesTerminalLeftSwitch (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ z) ++ u) ++ v)
      ((((v ++ u) ++ z) ++ u) ++ v) := by
  have substituted :=
    derivesBasisSubstitution terminalLeftSwitchLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [terminalLeftSwitchLaw, xyzxy, yxzxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The reversed form of the third candidate law. -/
private theorem derivesReverseTripleHead (u v : Word Nat) :
    Derives basis ((((v ++ v) ++ u) ++ u) ++ u)
      ((((v ++ u) ++ u) ++ u) ++ v) := by
  have first :
      Derives basis
        ((((v ++ v) ++ u) ++ u) ++ u)
        ((((v ++ u) ++ u) ++ v) ++ u) := by
    simpa [Word.append_assoc] using
      Derives.appendRight (derivesSquareFinal v u) u
  have second :
      Derives basis
        ((((v ++ u) ++ u) ++ v) ++ u)
        ((((v ++ u) ++ u) ++ u) ++ v) :=
    derivesTerminalRightSwitch v u u
  exact first.trans second

/-- The reversed form of the general gathering law. -/
private theorem derivesReverseGatherGeneral (u v z : Word Nat) :
    Derives basis ((((u ++ z) ++ v) ++ u) ++ u)
      ((((u ++ z) ++ u) ++ v) ++ u) := by
  have transfer :
      Derives basis
        ((((u ++ z) ++ v) ++ u) ++ u)
        ((((u ++ u) ++ z) ++ v) ++ u) := by
    simpa [Word.append_assoc] using
      (derivesEndpointTransfer u (z ++ v)).symm
  have gather :
      Derives basis
        ((((u ++ u) ++ z) ++ v) ++ u)
        ((((u ++ z) ++ u) ++ v) ++ u) :=
    derivesGatherGeneral u z v
  exact transfer.trans gather

/-! ## Reversal closure -/

private def expectedReversedBasis : List (Identity Nat) :=
  [Identity.mk xx xxxx,
    Identity.mk xyxxx xyx,
    Identity.mk (w 1 [1, 0, 0, 0]) yxxxy,
    Identity.mk xyxx xxyx,
    Identity.mk xxyxx xyx,
    Identity.mk (w 1 [1, 0, 0]) (w 1 [0, 1, 0]),
    Identity.mk (w 1 [1, 0, 0]) xyyx,
    Identity.mk (w 1 [1, 0, 0]) yxxy,
    Identity.mk (w 0 [2, 1, 0, 0]) (w 0 [2, 0, 1, 0]),
    Identity.mk (w 1 [2, 1, 0, 0]) (w 1 [2, 0, 1, 0]),
    Identity.mk (w 1 [2, 1, 0, 0]) (w 1 [2, 0, 0, 1]),
    Identity.mk xyx xxxyx,
    Identity.mk (w 2 [2, 0, 1, 0]) (w 2 [0, 2, 1, 0]),
    Identity.mk (w 2 [2, 0, 1, 0]) (w 0 [2, 2, 1, 0]),
    Identity.mk (w 1 [0, 2, 1, 0]) xyzyx,
    Identity.mk (w 1 [0, 2, 1, 0]) yxzxy]

private theorem reversedBasis_eq_expected :
    reversedBasis basis = expectedReversedBasis := by
  decide

private theorem reversedLawDerives
    (identity : Identity Nat) (member : identity ∈ reversedBasis basis) :
    Derives basis identity.lhs identity.rhs := by
  rw [reversedBasis_eq_expected] at member
  simp only [expectedReversedBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [powerLaw, xx, xxxx, w] using
      Derives.fromBasis (e := powerLaw) (by simp [basis])
  · simpa [tripleLeftContractionLaw, xxxyx, xyx,
      rightTripleExpansionLaw, xyxxx, w] using
        (Derives.fromBasis (e := rightTripleExpansionLaw)
          (by simp [basis])).symm
  · simpa [yxxxy, w] using
        derivesReverseTripleHead
          (Word.singleton 0) (Word.singleton 1)
  · simpa [endpointTransferLaw, xxyx, xyxx, w] using
      (Derives.fromBasis (e := endpointTransferLaw)
        (by simp [basis])).symm
  · simpa [splitEndpointContractionLaw, xxyxx, xyx, w] using
        Derives.fromBasis (e := splitEndpointContractionLaw)
          (by simp [basis])
  · simpa [squareInterleaveLaw, xxyy, xyxy, w] using
      derivesSquareInterleave (Word.singleton 1) (Word.singleton 0)
  · simpa [squareFinalLaw, xxyy, xyyx, w] using
      derivesSquareInitial (Word.singleton 1) (Word.singleton 0)
  · simpa [squareInitialLaw, xxyy, yxxy, w] using
      derivesSquareFinal (Word.singleton 1) (Word.singleton 0)
  · simpa [w] using
        derivesReverseGatherGeneral
          (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)
  · simpa [attachmentXYXZYLaw, xxyzy, xyxzy, w] using
      derivesDoubledSuffixMove
        (Word.singleton 1) (Word.singleton 2) (Word.singleton 0)
  · simpa [attachmentYXXZYLaw, xxyzy, yxxzy, w] using
      derivesTerminalSquareMove
        (Word.singleton 1) (Word.singleton 2) (Word.singleton 0)
  · simpa [rightTripleExpansionLaw, xyx, xyxxx,
      tripleLeftContractionLaw, xxxyx, w] using
        (Derives.fromBasis (e := tripleLeftContractionLaw)
          (by simp [basis])).symm
  · simpa [doubledSuffixMoveLaw, xyxzz, xyzxz, w] using
      derivesAttachmentXYXZY
        (Word.singleton 2) (Word.singleton 0) (Word.singleton 1)
  · simpa [terminalSquareMoveLaw, xyxzz, xyzzx, w] using
      derivesAttachmentYXXZY
        (Word.singleton 2) (Word.singleton 0) (Word.singleton 1)
  · simpa [terminalRightSwitchLaw, xyzxy, xyzyx, w] using
      derivesTerminalLeftSwitch
        (Word.singleton 1) (Word.singleton 0) (Word.singleton 2)
  · simpa [terminalLeftSwitchLaw, xyzxy, yxzxy, w] using
      derivesTerminalRightSwitch
        (Word.singleton 1) (Word.singleton 0) (Word.singleton 2)

/-- The candidate calculus is closed under reversing every word. -/
theorem derivesReverse
    {source target : Word Nat}
    (derivation : Derives basis source target) :
    Derives basis source.reverse target.reverse :=
  Derives.transport reversedLawDerives derivation.reverse

private theorem listDerivesReverse
    {source target : List Nat}
    (derivation : ListDerives source target) :
    ListDerives source.reverse target.reverse := by
  cases derivation with
  | empty => exact .empty
  | words wordDerivation =>
      simpa only [Word.toList_reverse] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesReverse wordDerivation)

/-! ## Repeated-letter interchange -/

/-- The four left-witness cases used to exchange an adjacent repeated pair. -/
theorem listDerivesL6
    (x y : Nat) (middle tail : List Nat) :
    ListDerives
      ([x, y] ++ middle ++ [x] ++ tail ++ [y])
      ([y, x] ++ middle ++ [x] ++ tail ++ [y]) := by
  cases middle with
  | nil =>
      cases tail with
      | nil =>
          have switched :=
            (derivesSquareInterleave
              (Word.singleton x) (Word.singleton y)).symm.trans
              (derivesSquareInitial
                (Word.singleton x) (Word.singleton y))
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord switched
      | cons tailHead tailRest =>
          let tailWord :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              tailHead tailRest
          have switched :=
            (derivesAttachmentXYXZY
              (Word.singleton x) (Word.singleton y) tailWord).symm.trans
              (derivesAttachmentYXXZY
                (Word.singleton x) (Word.singleton y) tailWord)
          simpa [tailWord,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord switched
  | cons middleHead middleRest =>
      let middleWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons
          middleHead middleRest
      cases tail with
      | nil =>
          have switched :=
            derivesTerminalLeftSwitch
              (Word.singleton x) (Word.singleton y) middleWord
          simpa [middleWord,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord switched
      | cons tailHead tailRest =>
          let tailWord :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              tailHead tailRest
          let xWord := Word.singleton x
          let yWord := Word.singleton y
          have expand :
              Derives basis
                (xWord ++ yWord ++ middleWord ++ xWord ++
                  tailWord ++ yWord)
                (xWord ++ yWord ++ middleWord ++ xWord ++ xWord ++
                  xWord ++ tailWord ++ yWord) := by
            simpa [Word.append_assoc] using Derives.appendRight
              (derivesRightTripleExpansion
                xWord (yWord ++ middleWord))
              (tailWord ++ yWord)
          have gather :
              Derives basis
                (xWord ++ yWord ++ middleWord ++ xWord ++ xWord ++
                  xWord ++ tailWord ++ yWord)
                (xWord ++ xWord ++ yWord ++ middleWord ++ xWord ++
                  xWord ++ tailWord ++ yWord) := by
            simpa [Word.append_assoc] using Derives.appendRight
              (derivesGatherGeneral
                xWord (yWord ++ middleWord) xWord).symm
              (tailWord ++ yWord)
          have switch :
              Derives basis
                (xWord ++ xWord ++ yWord ++ middleWord ++ xWord ++
                  xWord ++ tailWord ++ yWord)
                (yWord ++ xWord ++ xWord ++ middleWord ++ xWord ++
                  xWord ++ tailWord ++ yWord) := by
            simpa [Word.append_assoc] using
              derivesAttachmentYXXZY xWord yWord
                (middleWord ++ xWord ++ xWord ++ tailWord)
          have contract :
              Derives basis
                (yWord ++ xWord ++ xWord ++ middleWord ++ xWord ++
                  xWord ++ tailWord ++ yWord)
                (yWord ++ xWord ++ middleWord ++ xWord ++
                  tailWord ++ yWord) := by
            simpa [Word.append_assoc] using Derives.appendRight
              (Derives.prepend yWord
                (derivesSplitEndpointContraction xWord middleWord))
              (tailWord ++ yWord)
          have combined :=
            expand.trans <| gather.trans <| switch.trans contract
          simpa [middleWord, tailWord, xWord, yWord,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord combined

/-- The four straddling-witness cases. -/
theorem listDerivesL7
    (x y : Nat) (left right : List Nat) :
    ListDerives
      ([x] ++ left ++ [y, x] ++ right ++ [y])
      ([x] ++ left ++ [x, y] ++ right ++ [y]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          have switched :=
            (derivesSquareInterleave
              (Word.singleton x) (Word.singleton y)).symm
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord switched
      | cons rightHead rightRest =>
          let rightWord :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              rightHead rightRest
          have switched :=
            (derivesAttachmentXYXZY
              (Word.singleton x) (Word.singleton y) rightWord).symm
          simpa [rightWord,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord switched
  | cons leftHead leftRest =>
      let leftWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons leftHead leftRest
      cases right with
      | nil =>
          have switched :=
            (derivesDoubledSuffixMove
              (Word.singleton x) leftWord (Word.singleton y)).symm
          simpa [leftWord,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord switched
      | cons rightHead rightRest =>
          let rightWord :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              rightHead rightRest
          let xWord := Word.singleton x
          let yWord := Word.singleton y
          have expand :
              Derives basis
                (xWord ++ leftWord ++ yWord ++ xWord ++
                  rightWord ++ yWord)
                (xWord ++ leftWord ++ yWord ++ xWord ++ rightWord ++
                  yWord ++ yWord ++ yWord) := by
            simpa [Word.append_assoc] using
              Derives.prepend (xWord ++ leftWord)
              (derivesRightTripleExpansion
                yWord (xWord ++ rightWord))
          have gather :
              Derives basis
                (xWord ++ leftWord ++ yWord ++ xWord ++ rightWord ++
                  yWord ++ yWord ++ yWord)
                (xWord ++ leftWord ++ yWord ++ xWord ++ yWord ++
                  rightWord ++ yWord ++ yWord) := by
            simpa [Word.append_assoc] using Derives.appendRight
              (Derives.prepend (xWord ++ leftWord)
                (derivesReverseGatherGeneral
                  yWord rightWord xWord))
              yWord
          have expose :
              Derives basis
                (xWord ++ leftWord ++ yWord ++ xWord ++ yWord ++
                  rightWord ++ yWord ++ yWord)
                (xWord ++ leftWord ++ xWord ++ yWord ++ yWord ++
                  rightWord ++ yWord ++ yWord) := by
            simpa [Word.append_assoc] using Derives.appendRight
              (derivesDoubledSuffixMove xWord leftWord yWord).symm
              (rightWord ++ yWord ++ yWord)
          have contract :
              Derives basis
                (xWord ++ leftWord ++ xWord ++ yWord ++ yWord ++
                  rightWord ++ yWord ++ yWord)
                (xWord ++ leftWord ++ xWord ++ yWord ++
                  rightWord ++ yWord) := by
            simpa [Word.append_assoc] using
              Derives.prepend (xWord ++ leftWord ++ xWord)
              (derivesSplitEndpointContraction yWord rightWord)
          have combined :=
            expand.trans <| gather.trans <| expose.trans contract
          simpa [leftWord, rightWord, xWord, yWord,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord combined

/-- The right-witness cases follow by reversing `L6`; reversal closure is
why no separate starred laws are required. -/
theorem listDerivesL8
    (x y : Nat) (left middle : List Nat) :
    ListDerives
      ([x] ++ left ++ [y] ++ middle ++ [x, y])
      ([x] ++ left ++ [y] ++ middle ++ [y, x]) := by
  have reversed :=
    listDerivesReverse
      (listDerivesL6 y x middle.reverse left.reverse)
  simpa [List.reverse_append, List.append_assoc] using reversed

private theorem repeatedWitnesses
    {x y : Nat} {pre post : List Nat}
    (different : x ≠ y)
    (xRepeated : 2 ≤ (pre ++ x :: y :: post).count x)
    (yRepeated : 2 ≤ (pre ++ x :: y :: post).count y) :
    (x ∈ pre ∨ x ∈ post) ∧ (y ∈ pre ∨ y ∈ post) := by
  constructor
  · by_cases inPre : x ∈ pre
    · exact Or.inl inPre
    · right
      apply Decidable.byContradiction
      intro inPost
      have preZero := List.count_eq_zero.mpr inPre
      have postZero := List.count_eq_zero.mpr inPost
      simp [List.count_append, preZero, postZero, different,
        Ne.symm different] at xRepeated
  · by_cases inPre : y ∈ pre
    · exact Or.inl inPre
    · right
      apply Decidable.byContradiction
      intro inPost
      have preZero := List.count_eq_zero.mpr inPre
      have postZero := List.count_eq_zero.mpr inPost
      simp [List.count_append, preZero, postZero, different,
        Ne.symm different] at yRepeated

private theorem listDerivesAdjacentWithFutureWitnesses
    (x y : Nat) (pre post : List Nat)
    (different : x ≠ y) (xFuture : x ∈ post) (yFuture : y ∈ post) :
    ListDerives (pre ++ x :: y :: post) (pre ++ y :: x :: post) := by
  rcases uniqueSeparatorDistinctOccurrencesOrdered
      different xFuture yFuture with orderedXY | orderedYX
  · obtain ⟨before, middle, after, shape⟩ := orderedXY
    rw [shape]
    simpa [List.append_assoc] using
      (listDerivesL6 x y before middle).context pre after
  · obtain ⟨before, middle, after, shape⟩ := orderedYX
    rw [shape]
    simpa [List.append_assoc] using
      (listDerivesL6 y x before middle).symm.context pre after

private theorem listDerivesAdjacentWithPastWitnesses
    (x y : Nat) (pre post : List Nat)
    (different : x ≠ y) (xPast : x ∈ pre) (yPast : y ∈ pre) :
    ListDerives (pre ++ x :: y :: post) (pre ++ y :: x :: post) := by
  rcases uniqueSeparatorDistinctOccurrencesOrdered
      different xPast yPast with orderedXY | orderedYX
  · obtain ⟨before, middle, after, shape⟩ := orderedXY
    rw [shape]
    simpa [List.append_assoc] using
      (listDerivesL8 x y middle after).context before post
  · obtain ⟨before, middle, after, shape⟩ := orderedYX
    rw [shape]
    simpa [List.append_assoc] using
      (listDerivesL8 y x middle after).symm.context before post

private theorem listDerivesAdjacentStraddlePastFuture
    (x y : Nat) (pre post : List Nat)
    (xPast : x ∈ pre) (yFuture : y ∈ post) :
    ListDerives (pre ++ x :: y :: post) (pre ++ y :: x :: post) := by
  obtain ⟨before, left, preShape⟩ := List.mem_iff_append.mp xPast
  obtain ⟨right, after, postShape⟩ := List.mem_iff_append.mp yFuture
  rw [preShape, postShape]
  simpa [List.append_assoc] using
    (listDerivesL7 x y left right).symm.context before after

private theorem listDerivesAdjacentStraddleFuturePast
    (x y : Nat) (pre post : List Nat)
    (xFuture : x ∈ post) (yPast : y ∈ pre) :
    ListDerives (pre ++ x :: y :: post) (pre ++ y :: x :: post) := by
  obtain ⟨before, left, preShape⟩ := List.mem_iff_append.mp yPast
  obtain ⟨right, after, postShape⟩ := List.mem_iff_append.mp xFuture
  rw [preShape, postShape]
  simpa [List.append_assoc] using
    (listDerivesL7 y x left right).context before after

/-- Adjacent distinct letters can be exchanged whenever both are globally
repeated in the surrounding word. -/
theorem listDerivesAdjacentRepeatedSwap
    {x y : Nat} {pre post : List Nat}
    (different : x ≠ y)
    (xRepeated : 2 ≤ (pre ++ x :: y :: post).count x)
    (yRepeated : 2 ≤ (pre ++ x :: y :: post).count y) :
    ListDerives (pre ++ x :: y :: post) (pre ++ y :: x :: post) := by
  obtain ⟨xWitness, yWitness⟩ :=
    repeatedWitnesses different xRepeated yRepeated
  rcases xWitness with xPast | xFuture
  · rcases yWitness with yPast | yFuture
    · exact listDerivesAdjacentWithPastWitnesses
        x y pre post different xPast yPast
    · exact listDerivesAdjacentStraddlePastFuture
        x y pre post xPast yFuture
  · rcases yWitness with yPast | yFuture
    · exact listDerivesAdjacentStraddleFuturePast
        x y pre post xFuture yPast
    · exact listDerivesAdjacentWithFutureWitnesses
        x y pre post different xFuture yFuture

/-- Any permutation of a globally repeated block is derivable. -/
theorem listDerivesRepeatedPermutation
    {source target : List Nat}
    (permutation : source.Perm target) :
    ∀ (pre post : List Nat),
      (∀ letter, letter ∈ source ->
        2 ≤ (pre ++ source ++ post).count letter) ->
      ListDerives
        (pre ++ source ++ post)
        (pre ++ target ++ post) := by
  induction permutation with
  | nil =>
      intro pre post _
      simpa using
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (pre ++ post)
  | @cons letter source target permutation induction =>
      intro pre post repeated
      have tailRepeated :
          ∀ selected, selected ∈ source ->
            2 ≤ ((pre ++ [letter]) ++ source ++ post).count selected := by
        intro selected member
        have count :=
          repeated selected (List.mem_cons_of_mem letter member)
        simpa [List.append_assoc] using count
      simpa [List.append_assoc] using
        induction (pre ++ [letter]) post tailRepeated
  | swap x y rest =>
      intro pre post repeated
      by_cases equal : y = x
      · subst y
        simpa [List.append_assoc] using
          SemigroupBasis.CoRoots.S5_107.ListDerives.refl
            (basis := basis) (pre ++ x :: x :: rest ++ post)
      · have yRepeated :
            2 ≤ (pre ++ y :: x :: (rest ++ post)).count y := by
          simpa [List.append_assoc] using repeated y (by simp)
        have xRepeated :
            2 ≤ (pre ++ y :: x :: (rest ++ post)).count x := by
          simpa [List.append_assoc] using repeated x (by simp)
        simpa [List.append_assoc] using
          listDerivesAdjacentRepeatedSwap
            (pre := pre) (post := rest ++ post)
            equal yRepeated xRepeated
  | @trans source middle target first second
      firstInduction secondInduction =>
      intro pre post repeated
      have firstStep := firstInduction pre post repeated
      have middleRepeated :
          ∀ letter, letter ∈ middle ->
            2 ≤ (pre ++ middle ++ post).count letter := by
        intro letter member
        have sourceMember : letter ∈ source := first.mem_iff.mpr member
        have sourceCount := repeated letter sourceMember
        have countEquality :
            (pre ++ source ++ post).count letter =
              (pre ++ middle ++ post).count letter := by
          simp only [List.count_append]
          rw [first.count letter]
        rw [← countEquality]
        exact sourceCount
      exact firstStep.trans
        (secondInduction pre post middleRepeated)

/-! ## The joint semantic signature -/

/-- The exact invariant supplied jointly by `S5_400` and cyclic two. -/
structure SameFactorSignature (left right : Word Nat) : Prop where
  s5 :
    SemigroupBasis.CoRoots.S5_400.SameCanonicalSignature left right
  parity :
    ∀ letter,
      left.toList.count letter % 2 =
        right.toList.count letter % 2

namespace SameFactorSignature

theorem refl (word : Word Nat) : SameFactorSignature word word :=
  ⟨SemigroupBasis.CoRoots.S5_400.SameCanonicalSignature.refl word,
    fun _ => rfl⟩

theorem symm {left right : Word Nat}
    (same : SameFactorSignature left right) :
    SameFactorSignature right left :=
  ⟨same.s5.symm, fun letter => (same.parity letter).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameFactorSignature left middle)
    (second : SameFactorSignature middle right) :
    SameFactorSignature left right :=
  ⟨first.s5.trans second.s5,
    fun letter => (first.parity letter).trans (second.parity letter)⟩

/-- At multiplicities at most three, cap two and parity recover the exact
multiplicity. -/
theorem count_eq_of_le_three
    {left right : Word Nat}
    (same : SameFactorSignature left right) (letter : Nat)
    (leftBound : left.toList.count letter ≤ 3)
    (rightBound : right.toList.count letter ≤ 3) :
    left.toList.count letter = right.toList.count letter := by
  have capped := same.s5.capped letter
  have parity := same.parity letter
  unfold SemigroupBasis.CoRoots.S5_107.cappedMultiplicity at capped
  simp only [Nat.min_def] at capped
  split at capped <;> split at capped <;> omega

end SameFactorSignature

/-- Factor validity exposes the complete canonical right-factor signature
and the coordinatewise parity supplied by the cyclic factor. -/
theorem sameFactorSignatureOfFactorValid
    (identity : Identity Nat)
    (s2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup) :
    SameFactorSignature identity.lhs identity.rhs := by
  have cyclicValid : identity.SatisfiedBy cyclicTwo.semigroup := by
    rw [← SemigroupBasis.Generated.S2_2.table_eq_catalogue_model]
    exact s2Valid
  have s5Derivation :
      Derives SemigroupBasis.CoRoots.S5_400.basis
        identity.lhs identity.rhs :=
    SemigroupBasis.Generated.S5_400PublishedRoots.S5_400.representativeBasisFor.2
      identity s5Valid
  exact
    ⟨SemigroupBasis.CoRoots.S5_400.sameCanonicalSignature_of_derives
        s5Derivation,
      cyclicValid_parity_eq identity cyclicValid⟩

/-- The same signature constructor for the identity-equivalent `S5_840`
representative. -/
theorem sameFactorSignatureOfS5_840FactorValid
    (identity : Identity Nat)
    (s2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup) :
    SameFactorSignature identity.lhs identity.rhs :=
  sameFactorSignatureOfFactorValid identity s2Valid
    ((sameTheoryS5_400S5_840 identity).mpr s5Valid)

/-- Candidate derivations preserve both factors' complete joint signature. -/
theorem sameFactorSignatureOfDerives
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameFactorSignature left right := by
  have s2Valid :
      (Identity.mk left right).SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup := by
    intro valuation
    exact derivation.sound modelsS2_2 valuation
  have s5Valid :
      (Identity.mk left right).SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup := by
    intro valuation
    exact derivation.sound modelsS5_400 valuation
  exact sameFactorSignatureOfFactorValid
    (Identity.mk left right) s2Valid s5Valid

/-! ## Parity-preserving multiplicity reduction -/

private theorem listDerivesGatherMiddleToFirst
    (letter : Nat) (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
        [letter] ++ after)
      (before ++ [letter, letter] ++ firstGap ++ secondGap ++
        [letter] ++ after) := by
  cases firstGap with
  | nil =>
      simpa [List.append_assoc] using
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis)
          (before ++ [letter, letter] ++ secondGap ++
            [letter] ++ after)
  | cons firstHead firstTail =>
      let firstWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons
          firstHead firstTail
      cases secondGap with
      | nil =>
          have moved :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (derivesEndpointTransfer
                (Word.singleton letter) firstWord).symm
          simpa [firstWord,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              moved.context before after
      | cons secondHead secondTail =>
          let secondWord :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              secondHead secondTail
          have gathered :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (derivesGatherGeneral
                (Word.singleton letter) firstWord secondWord).symm
          simpa [firstWord, secondWord,
            SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              gathered.context before after

private theorem listDerivesContractFrontPair
    (letter : Nat) (before middle after : List Nat) :
    ListDerives
      (before ++ [letter, letter, letter] ++ middle ++
        [letter] ++ after)
      (before ++ [letter] ++ middle ++ [letter] ++ after) := by
  cases middle with
  | nil =>
      have contracted :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesFourToTwo (Word.singleton letter))
      simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.singleton, Word.append, Word.append_assoc,
        List.append_assoc] using
          contracted.context before after
  | cons middleHead middleTail =>
      let middleWord :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons
          middleHead middleTail
      have contracted :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesTripleLeftContraction
            (Word.singleton letter) middleWord)
      simpa [middleWord,
        SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.singleton, Word.append, Word.append_assoc,
        List.append_assoc] using
          contracted.context before after

/-- Delete the second and third of four displayed occurrences. -/
theorem listDerivesDeleteSecondAndThird
    (letter : Nat)
    (before firstGap secondGap thirdGap after : List Nat) :
    ListDerives
      (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
        [letter] ++ thirdGap ++ [letter] ++ after)
      (before ++ [letter] ++ firstGap ++ secondGap ++ thirdGap ++
        [letter] ++ after) := by
  have gatherSecond :=
    listDerivesGatherMiddleToFirst letter before firstGap secondGap
      (thirdGap ++ [letter] ++ after)
  have gatherThird :=
    listDerivesGatherMiddleToFirst letter (before ++ [letter])
      (firstGap ++ secondGap) thirdGap after
  have contract :=
    listDerivesContractFrontPair letter before
      (firstGap ++ secondGap ++ thirdGap) after
  have first :
      ListDerives
        (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
          [letter] ++ thirdGap ++ [letter] ++ after)
        (before ++ [letter, letter] ++ firstGap ++ secondGap ++
          [letter] ++ thirdGap ++ [letter] ++ after) := by
    simpa [List.append_assoc] using gatherSecond
  have second :
      ListDerives
        (before ++ [letter, letter] ++ firstGap ++ secondGap ++
          [letter] ++ thirdGap ++ [letter] ++ after)
        (before ++ [letter, letter, letter] ++ firstGap ++ secondGap ++
          thirdGap ++ [letter] ++ after) := by
    simpa [List.append_assoc] using gatherThird
  have third :
      ListDerives
        (before ++ [letter, letter, letter] ++ firstGap ++ secondGap ++
          thirdGap ++ [letter] ++ after)
        (before ++ [letter] ++ firstGap ++ secondGap ++ thirdGap ++
          [letter] ++ after) := by
    simpa [List.append_assoc] using contract
  exact first.trans (second.trans third)

private theorem existsTwoOccurrenceSplit
    (letter : Nat) :
    ∀ {letters : List Nat},
      2 ≤ letters.count letter ->
        ∃ before middle after,
          letters = before ++ letter :: middle ++ letter :: after
  | [], count => by
      simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        have restPositive : 0 < rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        obtain ⟨middle, after, split⟩ :=
          List.mem_iff_append.mp
            (List.count_pos_iff.mp restPositive)
        exact ⟨[], middle, after,
          by simp [split, List.append_assoc]⟩
      · have restCount : 2 ≤ rest.count letter := by
          simpa [equality] using count
        obtain ⟨before, middle, after, split⟩ :=
          existsTwoOccurrenceSplit letter restCount
        exact ⟨first :: before, middle, after,
          by simp [split, List.append_assoc]⟩

private theorem existsThreeOccurrenceSplit
    (letter : Nat) :
    ∀ {letters : List Nat},
      3 ≤ letters.count letter ->
        ∃ before firstGap secondGap after,
          letters = before ++ letter :: firstGap ++ letter ::
            secondGap ++ letter :: after
  | [], count => by
      simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        have restCount : 2 ≤ rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        obtain ⟨firstGap, secondGap, after, split⟩ :=
          existsTwoOccurrenceSplit letter restCount
        exact ⟨[], firstGap, secondGap, after,
          by simp [split, List.append_assoc]⟩
      · have restCount : 3 ≤ rest.count letter := by
          simpa [equality] using count
        obtain ⟨before, firstGap, secondGap, after, split⟩ :=
          existsThreeOccurrenceSplit letter restCount
        exact ⟨first :: before, firstGap, secondGap, after,
          by simp [split, List.append_assoc]⟩

/-- Every list derives to one in which each multiplicity is at most three. -/
private theorem existsThreeLimitedFrom :
    ∀ (remaining kept : List Nat),
      (∀ tested, kept.count tested ≤ 3) ->
        ∃ reduced : List Nat,
          (∀ tested, reduced.count tested ≤ 3) ∧
          ListDerives (kept ++ remaining) reduced
  | [], kept, keptBound =>
      ⟨kept, keptBound,
        by simpa using
          SemigroupBasis.CoRoots.S5_107.ListDerives.refl
            (basis := basis) kept⟩
  | letter :: rest, kept, keptBound => by
      by_cases room : kept.count letter < 3
      · have nextBound :
            ∀ tested, (kept ++ [letter]).count tested ≤ 3 := by
          intro tested
          rw [List.count_append]
          by_cases equality : letter = tested
          · subst letter
            simp only [List.count_cons_self, List.count_nil]
            omega
          · have singletonZero : [letter].count tested = 0 := by
              simp [equality]
            rw [singletonZero, Nat.add_zero]
            exact keptBound tested
        obtain ⟨reduced, reducedBound, derivation⟩ :=
          existsThreeLimitedFrom rest (kept ++ [letter]) nextBound
        exact ⟨reduced, reducedBound, by
          simpa [List.append_assoc] using derivation⟩
      · have full : kept.count letter = 3 := by
          have bound := keptBound letter
          omega
        obtain ⟨firstBefore, secondBefore, thirdBefore,
            thirdAfter, split⟩ :=
          existsThreeOccurrenceSplit letter (letters := kept) (by omega)
        let nextKept :=
          firstBefore ++ [letter] ++ secondBefore ++ thirdBefore ++
            thirdAfter ++ [letter]
        have nextBound :
            ∀ tested, nextKept.count tested ≤ 3 := by
          intro tested
          by_cases equality : tested = letter
          · subst tested
            simp only [nextKept, List.count_append,
              List.count_cons_self, List.count_nil]
            have splitCount := congrArg (List.count letter) split
            simp only [List.count_append, List.count_cons_self]
              at splitCount
            omega
          · have countEq :
                nextKept.count tested = kept.count tested := by
              rw [split]
              simp [nextKept, List.count_append, equality,
                Ne.symm equality]
            rw [countEq]
            exact keptBound tested
        obtain ⟨reduced, reducedBound, recurse⟩ :=
          existsThreeLimitedFrom rest nextKept nextBound
        have deletePair :
            ListDerives (kept ++ letter :: rest)
              (nextKept ++ rest) := by
          rw [split]
          simpa [nextKept, List.append_assoc] using
            listDerivesDeleteSecondAndThird letter firstBefore
              secondBefore thirdBefore thirdAfter rest
        exact ⟨reduced, reducedBound, deletePair.trans recurse⟩

private theorem existsThreeLimited (letters : List Nat) :
    ∃ reduced : List Nat,
      (∀ tested, reduced.count tested ≤ 3) ∧
      ListDerives letters reduced := by
  simpa using existsThreeLimitedFrom letters [] (by simp)

/-! ## First-pair placement -/

/-- In a first-pair canonical list, a variable with three copies begins
with an adjacent pair at its first occurrence. -/
inductive FirstPairCanonical : List Nat -> Prop
  | nil : FirstPairCanonical []
  | single (letter : Nat) (tail : List Nat) :
      FirstPairCanonical tail ->
      tail.count letter = 0 ->
      FirstPairCanonical (letter :: tail)
  | double (letter : Nat) (tail : List Nat) :
      FirstPairCanonical tail ->
      tail.count letter = 1 ->
      FirstPairCanonical (letter :: tail)
  | triple (letter : Nat) (tail : List Nat) :
      FirstPairCanonical tail ->
      tail.count letter = 1 ->
      FirstPairCanonical (letter :: letter :: tail)

private theorem existsFirstPairCanonical :
    ∀ letters : List Nat,
      (∀ tested, letters.count tested ≤ 3) ->
        ∃ normalized : List Nat,
          FirstPairCanonical normalized ∧
          (∀ tested,
            normalized.count tested = letters.count tested) ∧
          ListDerives letters normalized
  | [], _ =>
      ⟨[], .nil, by simp,
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl []⟩
  | letter :: rest, bounded => by
      have restBound : ∀ tested, rest.count tested ≤ 3 := by
        intro tested
        have wholeBound := bounded tested
        simp only [List.count_cons] at wholeBound
        omega
      by_cases twoLater : 2 ≤ rest.count letter
      · have restCount : rest.count letter = 2 := by
          have wholeBound := bounded letter
          simp only [List.count_cons_self] at wholeBound
          omega
        obtain ⟨firstGap, secondGap, after, split⟩ :=
          existsTwoOccurrenceSplit letter twoLater
        let remainder :=
          firstGap ++ secondGap ++ [letter] ++ after
        have exposedPermutation :
            (letter :: rest).Perm
              (letter :: letter :: remainder) := by
          rw [List.perm_iff_count]
          intro tested
          by_cases equality : tested = letter
          · subst tested
            simp [split, remainder, List.count_append, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm]
          · simp [split, remainder, List.count_append, equality,
              Ne.symm equality]
        have remainderBound :
            ∀ tested, remainder.count tested ≤ 3 := by
          intro tested
          have targetBound :
              (letter :: letter :: remainder).count tested ≤ 3 := by
            rw [← exposedPermutation.count tested]
            exact bounded tested
          simp only [List.count_cons] at targetBound
          omega
        have remainderShorter :
            remainder.length < (letter :: rest).length := by
          simp only [remainder, split, List.length_append,
            List.length_cons, List.length_nil]
          omega
        obtain ⟨normalizedTail, tailCanonical, tailCounts,
            tailDerivation⟩ :=
          existsFirstPairCanonical remainder remainderBound
        have remainderLetterCount : remainder.count letter = 1 := by
          rw [split] at restCount
          simp only [List.count_append, List.count_cons_self] at restCount
          simp only [remainder, List.count_append,
            List.count_cons_self, List.count_nil]
          omega
        have normalizedTailLetterCount :
            normalizedTail.count letter = 1 := by
          rw [tailCounts letter, remainderLetterCount]
        have gathered :=
          listDerivesGatherMiddleToFirst letter []
            firstGap secondGap after
        have normalizedRest :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.prepend
            [letter, letter] tailDerivation
        refine ⟨letter :: letter :: normalizedTail,
          .triple letter normalizedTail tailCanonical
            normalizedTailLetterCount, ?_, ?_⟩
        · intro tested
          calc
            (letter :: letter :: normalizedTail).count tested =
                (letter :: letter :: remainder).count tested := by
              simp only [List.count_cons]
              rw [tailCounts tested]
            _ = (letter :: rest).count tested :=
              (exposedPermutation.count tested).symm
        · simpa [split, remainder, List.append_assoc] using
            gathered.trans normalizedRest
      · obtain ⟨normalizedTail, tailCanonical, tailCounts,
            tailDerivation⟩ :=
          existsFirstPairCanonical rest restBound
        have restSmall : rest.count letter ≤ 1 := by omega
        have normalizedCounts :
            ∀ tested,
              (letter :: normalizedTail).count tested =
                (letter :: rest).count tested := by
          intro tested
          simp only [List.count_cons]
          rw [tailCounts tested]
        have prefixed :
            ListDerives (letter :: rest)
              (letter :: normalizedTail) := by
          simpa using
            SemigroupBasis.CoRoots.S5_107.ListDerives.prepend
              [letter] tailDerivation
        by_cases zero : rest.count letter = 0
        · have normalizedZero : normalizedTail.count letter = 0 := by
            rw [tailCounts letter, zero]
          exact ⟨letter :: normalizedTail,
            .single letter normalizedTail tailCanonical normalizedZero,
            normalizedCounts, prefixed⟩
        · have one : rest.count letter = 1 := by omega
          have normalizedOne : normalizedTail.count letter = 1 := by
            rw [tailCounts letter, one]
          exact ⟨letter :: normalizedTail,
            .double letter normalizedTail tailCanonical normalizedOne,
            normalizedCounts, prefixed⟩
termination_by letters => letters.length
decreasing_by
  · exact remainderShorter
  · simp

private theorem FirstPairCanonical.firstPairOfCountThree
    {letters : List Nat} (canonical : FirstPairCanonical letters)
    (tested : Nat) (count : letters.count tested = 3) :
    ∃ before after,
      letters = before ++ tested :: tested :: after ∧
        tested ∉ before := by
  induction canonical with
  | nil => simp at count
  | single letter tail tailCanonical letterZero induction =>
      by_cases equality : tested = letter
      · subst tested
        simp only [List.count_cons_self, letterZero] at count
        omega
      · have tailCount : tail.count tested = 3 := by
          simpa [equality, Ne.symm equality] using count
        obtain ⟨before, after, shape, absent⟩ :=
          induction tailCount
        exact ⟨letter :: before, after, by simp [shape], by
          simp [equality, Ne.symm equality, absent]⟩
  | double letter tail tailCanonical letterOne induction =>
      by_cases equality : tested = letter
      · subst tested
        simp only [List.count_cons_self, letterOne] at count
        omega
      · have tailCount : tail.count tested = 3 := by
          simpa [equality, Ne.symm equality] using count
        obtain ⟨before, after, shape, absent⟩ :=
          induction tailCount
        exact ⟨letter :: before, after, by simp [shape], by
          simp [equality, Ne.symm equality, absent]⟩
  | triple letter tail tailCanonical letterOne induction =>
      by_cases equality : tested = letter
      · subst tested
        exact ⟨[], tail, rfl, by simp⟩
      · have tailCount : tail.count tested = 3 := by
          simpa [equality, Ne.symm equality] using count
        obtain ⟨before, after, shape, absent⟩ :=
          induction tailCount
        exact ⟨letter :: letter :: before, after,
          by simp [shape], by
            simp [equality, Ne.symm equality, absent]⟩

private theorem prefixCount_ne_one_of_firstPairAux
    (tested separator : Nat) (pairAfter suffix : List Nat)
    (different : tested ≠ separator) :
    ∀ (pairBefore preWords : List Nat),
      tested ∉ pairBefore ->
      pairBefore ++ tested :: tested :: pairAfter =
        preWords ++ separator :: suffix ->
      preWords.count tested ≠ 1
  | [], [], _, _ => by simp
  | [], first :: rest, _, shape => by
      simp only [List.nil_append, List.cons_append] at shape
      injection shape with firstEq tailEq
      subst first
      intro countOne
      cases rest with
      | nil =>
          simp only [List.nil_append] at tailEq
          injection tailEq with equality
          exact different equality
      | cons next more =>
          simp only [List.cons_append] at tailEq
          injection tailEq with equality
          subst next
          simp only [List.count_cons_self] at countOne
          omega
  | first :: rest, [], _, _ => by simp
  | first :: rest, next :: preWords, absent, shape => by
      have firstDifferent : first ≠ tested := by
        intro equality
        subst first
        exact absent (List.Mem.head rest)
      have restAbsent : tested ∉ rest :=
        fun member => absent (List.Mem.tail first member)
      simp only [List.cons_append] at shape
      injection shape with headEq tailEq
      subst next
      have recurse :=
        prefixCount_ne_one_of_firstPairAux tested separator
          pairAfter suffix different rest preWords restAbsent tailEq
      simpa [firstDifferent] using recurse

private def SimpleSplitCanonical (whole : List Nat) : Prop :=
  ∀ tested separator before after,
    whole = before ++ separator :: after ->
    whole.count tested = 3 ->
    whole.count separator = 1 ->
    tested ≠ separator ->
    before.count tested ≠ 1

private theorem FirstPairCanonical.simpleSplitCanonical
    {letters : List Nat} (canonical : FirstPairCanonical letters) :
    SimpleSplitCanonical letters := by
  intro tested separator before after split testedThree
    _separatorSimple different
  obtain ⟨pairBefore, pairAfter, pairShape, pairBeforeAbsent⟩ :=
    canonical.firstPairOfCountThree tested testedThree
  exact prefixCount_ne_one_of_firstPairAux tested separator
    pairAfter after different pairBefore before pairBeforeAbsent
    (pairShape.symm.trans split)

/-! ## Reading the `S5_400` order-gap scanner -/

private abbrev OrderGapState :=
  SemigroupBasis.CoRoots.S5_793Invariant.OrderGapState

private def pairKeep (x y value : Nat) : Bool :=
  value == x || value == y

private def pairProjection
    (letters : List Nat) (x y : Nat) : List Nat :=
  letters.filter (pairKeep x y)

private def pairScan
    (letters : List Nat) (x y : Nat) : OrderGapState :=
  letters.foldl
    (fun state letter =>
      SemigroupBasis.CoRoots.S5_793Invariant.orderStep state
        (SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol
          x y letter))
    .empty

private theorem pairScan_eq_orderGapScan
    (word : Word Nat) (x y : Nat) :
    pairScan word.toList x y =
      SemigroupBasis.CoRoots.S5_793Invariant.orderGapScan word x y :=
  rfl

private theorem pairScan_filter
    (x y : Nat) :
    ∀ (letters : List Nat) (initial : OrderGapState),
      letters.foldl
          (fun state letter =>
            SemigroupBasis.CoRoots.S5_793Invariant.orderStep state
              (SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol
                x y letter))
          initial =
        (pairProjection letters x y).foldl
          (fun state letter =>
            SemigroupBasis.CoRoots.S5_793Invariant.orderStep state
              (SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol
                x y letter))
          initial
  | [], _ => rfl
  | letter :: rest, initial => by
      by_cases isX : letter = x
      · subst letter
        have induction :=
          pairScan_filter x y rest
            (SemigroupBasis.CoRoots.S5_793Invariant.orderStep initial
              (SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol x y x))
        simpa [pairProjection, pairKeep] using induction
      · by_cases isY : letter = y
        · subst letter
          have induction :=
            pairScan_filter x y rest
              (SemigroupBasis.CoRoots.S5_793Invariant.orderStep initial
                (SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol
                  x y y))
          simpa [pairProjection, pairKeep, isX] using induction
        · have induction := pairScan_filter x y rest initial
          simpa [pairProjection, pairKeep,
            SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol,
            isX, isY] using induction

private theorem pairScan_eq_pairProjection
    (letters : List Nat) (x y : Nat) :
    pairScan letters x y =
      pairScan (pairProjection letters x y) x y :=
  pairScan_filter x y letters .empty

private theorem pairProjection_of_y_absent
    {x y : Nat} (different : x ≠ y) :
    ∀ letters : List Nat,
      y ∉ letters ->
        pairProjection letters x y =
          List.replicate (letters.count x) x
  | [], _ => by simp [pairProjection]
  | letter :: rest, absent => by
      have restAbsent : y ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      by_cases isX : letter = x
      · subst letter
        simp [pairProjection, pairKeep]
        change
          x :: pairProjection rest x y =
            List.replicate (Nat.succ (rest.count x)) x
        rw [pairProjection_of_y_absent different rest restAbsent]
        rw [List.replicate_succ]
      · have isY : letter ≠ y := by
          intro equality
          subst letter
          exact absent (List.Mem.head rest)
        simp [pairProjection, pairKeep, isX, isY]
        exact pairProjection_of_y_absent different rest restAbsent

private theorem pairProjection_at_simple_split
    (word : Word Nat) {x y : Nat} {before rest : List Nat}
    (different : x ≠ y)
    (shape : word.toList = before ++ y :: rest)
    (yCount : word.toList.count y = 1) :
    pairProjection word.toList x y =
      List.replicate (before.count x) x ++
        y :: List.replicate (rest.count x) x := by
  have yAbsentPrefix : y ∉ before := by
    intro member
    have positive : 1 ≤ before.count y :=
      List.one_le_count_iff.mpr member
    rw [shape, List.count_append, List.count_cons_self] at yCount
    omega
  have yAbsentRest : y ∉ rest := by
    intro member
    have positive : 1 ≤ rest.count y :=
      List.one_le_count_iff.mpr member
    rw [shape, List.count_append, List.count_cons_self] at yCount
    omega
  rw [shape]
  simp only [pairProjection, List.filter_append, List.filter_cons]
  have yKept : pairKeep x y y = true := by
    simp [pairKeep]
  rw [if_pos yKept]
  change
    pairProjection before x y ++ y :: pairProjection rest x y = _
  rw [pairProjection_of_y_absent different before yAbsentPrefix,
    pairProjection_of_y_absent different rest yAbsentRest]

private theorem simplePrecedes_iff_prefixCount_one
    (word : Word Nat) {x y : Nat} {before rest : List Nat}
    (different : x ≠ y)
    (shape : word.toList = before ++ y :: rest)
    (xCount : word.toList.count x = 1)
    (yCount : word.toList.count y = 1) :
    SemigroupBasis.CoRoots.S5_793Invariant.SimplePrecedes word x y ↔
      before.count x = 1 := by
  rw [SemigroupBasis.CoRoots.S5_793Invariant.SimplePrecedes,
    ← pairScan_eq_orderGapScan]
  rw [pairScan_eq_pairProjection,
    pairProjection_at_simple_split word different shape yCount]
  have splitCount : before.count x + rest.count x = 1 := by
    rw [shape, List.count_append,
      List.count_cons_of_ne (Ne.symm different)] at xCount
    simpa using xCount
  have prefixCases : before.count x = 0 ∨ before.count x = 1 := by
    omega
  rcases prefixCases with prefixZero | prefixOne
  · have restOne : rest.count x = 1 := by omega
    simp [pairScan, prefixZero, restOne, different,
      Ne.symm different,
      SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol,
      SemigroupBasis.CoRoots.S5_793Invariant.orderStep]
  · have restZero : rest.count x = 0 := by omega
    simp [pairScan, prefixOne, restZero, different,
      Ne.symm different,
      SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol,
      SemigroupBasis.CoRoots.S5_793Invariant.orderStep]

private theorem multipleLastBeforeSimple_iff_prefixCount_total
    (word : Word Nat) {x y : Nat} {before rest : List Nat}
    (different : x ≠ y)
    (shape : word.toList = before ++ y :: rest)
    (xMultiple : 2 ≤ word.toList.count x)
    (xBound : word.toList.count x ≤ 3)
    (yCount : word.toList.count y = 1) :
    SemigroupBasis.CoRoots.S5_793Invariant.MultipleLastBeforeSimple
        word x y ↔
      before.count x = word.toList.count x := by
  rw [SemigroupBasis.CoRoots.S5_793Invariant.MultipleLastBeforeSimple,
    ← pairScan_eq_orderGapScan]
  rw [pairScan_eq_pairProjection,
    pairProjection_at_simple_split word different shape yCount]
  have splitCount :
      before.count x + rest.count x = word.toList.count x := by
    rw [shape, List.count_append,
      List.count_cons_of_ne (Ne.symm different)]
  have totalCases :
      word.toList.count x = 2 ∨ word.toList.count x = 3 := by
    omega
  have prefixBound : before.count x ≤ 3 := by omega
  have prefixCases :
      before.count x = 0 ∨ before.count x = 1 ∨
        before.count x = 2 ∨ before.count x = 3 := by
    omega
  rcases totalCases with totalTwo | totalThree
  · rw [totalTwo] at splitCount ⊢
    rcases prefixCases with prefixZero | prefixOne | prefixTwo | prefixThree
    · have restTwo : rest.count x = 2 := by omega
      simp [pairScan, prefixZero, restTwo, different,
        Ne.symm different,
        SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol,
        SemigroupBasis.CoRoots.S5_793Invariant.orderStep]
    · have restOne : rest.count x = 1 := by omega
      simp [pairScan, prefixOne, restOne, different,
        Ne.symm different,
        SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol,
        SemigroupBasis.CoRoots.S5_793Invariant.orderStep]
    · have restZero : rest.count x = 0 := by omega
      simp [pairScan, prefixTwo, restZero, different,
        Ne.symm different,
        SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol,
        SemigroupBasis.CoRoots.S5_793Invariant.orderStep]
    · omega
  · rw [totalThree] at splitCount ⊢
    rcases prefixCases with prefixZero | prefixOne | prefixTwo | prefixThree
    · have restThree : rest.count x = 3 := by omega
      simp [pairScan, prefixZero, restThree, different,
        Ne.symm different,
        SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol,
        SemigroupBasis.CoRoots.S5_793Invariant.orderStep]
    · have restTwo : rest.count x = 2 := by omega
      simp [pairScan, prefixOne, restTwo, different,
        Ne.symm different,
        SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol,
        SemigroupBasis.CoRoots.S5_793Invariant.orderStep]
    · have restOne : rest.count x = 1 := by omega
      simp [pairScan, prefixTwo, restOne, different,
        Ne.symm different,
        SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol,
        SemigroupBasis.CoRoots.S5_793Invariant.orderStep]
    · have restZero : rest.count x = 0 := by omega
      simp [pairScan, prefixThree, restZero, different,
        Ne.symm different,
        SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol,
        SemigroupBasis.CoRoots.S5_793Invariant.orderStep]

private theorem reverseMultipleLastBeforeSimple_iff_prefixCount_zero
    (word : Word Nat) {x y : Nat} {before rest : List Nat}
    (different : x ≠ y)
    (shape : word.toList = before ++ y :: rest)
    (xMultiple : 2 ≤ word.toList.count x)
    (xBound : word.toList.count x ≤ 3)
    (yCount : word.toList.count y = 1) :
    SemigroupBasis.CoRoots.S5_793Invariant.MultipleLastBeforeSimple
        word.reverse x y ↔
      before.count x = 0 := by
  have reverseShape :
      word.reverse.toList = rest.reverse ++ y :: before.reverse := by
    rw [Word.toList_reverse, shape, List.reverse_append]
    simp
  have reverseXCount :
      word.reverse.toList.count x = word.toList.count x := by
    simp [Word.toList_reverse, List.count_reverse]
  have reverseYCount : word.reverse.toList.count y = 1 := by
    simpa [Word.toList_reverse, List.count_reverse] using yCount
  rw [multipleLastBeforeSimple_iff_prefixCount_total
    word.reverse different reverseShape
      (by rw [reverseXCount]; exact xMultiple)
      (by rw [reverseXCount]; exact xBound)
      reverseYCount]
  rw [List.count_reverse, reverseXCount]
  have splitCount :
      before.count x + rest.count x = word.toList.count x := by
    rw [shape, List.count_append,
      List.count_cons_of_ne (Ne.symm different)]
  omega

/-- On first-pair canonical three-limited words, the joint signature fixes
the exact cumulative multiplicity before every simple separator. -/
private theorem prefixCount_eq
    {left right : Word Nat}
    (same : SameFactorSignature left right)
    (leftBound : ∀ letter, left.toList.count letter ≤ 3)
    (rightBound : ∀ letter, right.toList.count letter ≤ 3)
    (leftCanonical : SimpleSplitCanonical left.toList)
    (rightCanonical : SimpleSplitCanonical right.toList)
    {separator : Nat}
    {leftPrefix leftRest rightPrefix rightRest : List Nat}
    (leftShape : left.toList = leftPrefix ++ separator :: leftRest)
    (rightShape : right.toList = rightPrefix ++ separator :: rightRest)
    (leftSeparator : left.toList.count separator = 1)
    (rightSeparator : right.toList.count separator = 1) :
    ∀ letter, leftPrefix.count letter = rightPrefix.count letter := by
  intro letter
  have totalEqual :=
    same.count_eq_of_le_three letter
      (leftBound letter) (rightBound letter)
  by_cases selectedSeparator : letter = separator
  · subst letter
    have leftZero : leftPrefix.count separator = 0 := by
      rw [leftShape, List.count_append,
        List.count_cons_self] at leftSeparator
      omega
    have rightZero : rightPrefix.count separator = 0 := by
      rw [rightShape, List.count_append,
        List.count_cons_self] at rightSeparator
      omega
    rw [leftZero, rightZero]
  · have different : letter ≠ separator := selectedSeparator
    by_cases absent : left.toList.count letter = 0
    · have rightAbsent : right.toList.count letter = 0 := by omega
      rw [leftShape, List.count_append,
        List.count_cons_of_ne (Ne.symm different)] at absent
      rw [rightShape, List.count_append,
        List.count_cons_of_ne (Ne.symm different)] at rightAbsent
      omega
    · by_cases simple : left.toList.count letter = 1
      · have rightSimple : right.toList.count letter = 1 := by omega
        have order := same.s5.simpleSequence letter separator
        have leftOrder :=
          simplePrecedes_iff_prefixCount_one left different
            leftShape simple leftSeparator
        have rightOrder :=
          simplePrecedes_iff_prefixCount_one right different
            rightShape rightSimple rightSeparator
        have prefixIff :
            leftPrefix.count letter = 1 ↔
              rightPrefix.count letter = 1 := by
          rw [← leftOrder, ← rightOrder]
          exact order
        have leftPrefixBound : leftPrefix.count letter ≤ 1 := by
          rw [leftShape, List.count_append,
            List.count_cons_of_ne (Ne.symm different)] at simple
          omega
        have rightPrefixBound : rightPrefix.count letter ≤ 1 := by
          rw [rightShape, List.count_append,
            List.count_cons_of_ne (Ne.symm different)] at rightSimple
          omega
        by_cases leftOne : leftPrefix.count letter = 1
        · rw [leftOne, prefixIff.mp leftOne]
        · have rightNotOne : rightPrefix.count letter ≠ 1 :=
            fun rightOne => leftOne (prefixIff.mpr rightOne)
          omega
      · have leftMultiple : 2 ≤ left.toList.count letter := by
          have bound := leftBound letter
          omega
        have rightMultiple : 2 ≤ right.toList.count letter := by
          omega
        have lastIff :
            leftPrefix.count letter = left.toList.count letter ↔
              rightPrefix.count letter = right.toList.count letter := by
          rw [← multipleLastBeforeSimple_iff_prefixCount_total
              left different leftShape leftMultiple
                (leftBound letter) leftSeparator,
            ← multipleLastBeforeSimple_iff_prefixCount_total
              right different rightShape rightMultiple
                (rightBound letter) rightSeparator]
          exact same.s5.lastGap letter separator
        have firstIff :
            leftPrefix.count letter = 0 ↔
              rightPrefix.count letter = 0 := by
          rw [← reverseMultipleLastBeforeSimple_iff_prefixCount_zero
              left different leftShape leftMultiple
                (leftBound letter) leftSeparator,
            ← reverseMultipleLastBeforeSimple_iff_prefixCount_zero
              right different rightShape rightMultiple
                (rightBound letter) rightSeparator]
          exact same.s5.firstGap letter separator
        have leftPrefixBound :
            leftPrefix.count letter ≤ left.toList.count letter := by
          rw [leftShape, List.count_append,
            List.count_cons_of_ne (Ne.symm different)]
          omega
        have rightPrefixBound :
            rightPrefix.count letter ≤ right.toList.count letter := by
          rw [rightShape, List.count_append,
            List.count_cons_of_ne (Ne.symm different)]
          omega
        have leftSplit :
            left.toList.count letter =
              leftPrefix.count letter + leftRest.count letter := by
          rw [leftShape, List.count_append,
            List.count_cons_of_ne (Ne.symm different)]
        have rightSplit :
            right.toList.count letter =
              rightPrefix.count letter + rightRest.count letter := by
          rw [rightShape, List.count_append,
            List.count_cons_of_ne (Ne.symm different)]
        by_cases leftZero : leftPrefix.count letter = 0
        · rw [leftZero, firstIff.mp leftZero]
        · by_cases leftTotal :
            leftPrefix.count letter = left.toList.count letter
          · have rightTotal := lastIff.mp leftTotal
            rw [leftTotal, rightTotal, totalEqual]
          · have rightNotZero : rightPrefix.count letter ≠ 0 :=
              fun rightZero => leftZero (firstIff.mpr rightZero)
            have rightNotTotal :
                rightPrefix.count letter ≠ right.toList.count letter :=
              fun rightTotal => leftTotal (lastIff.mpr rightTotal)
            by_cases leftThree : left.toList.count letter = 3
            · have rightThree : right.toList.count letter = 3 := by
                omega
              have leftNotOne : leftPrefix.count letter ≠ 1 :=
                leftCanonical letter separator leftPrefix leftRest
                  leftShape leftThree leftSeparator different
              have rightNotOne : rightPrefix.count letter ≠ 1 :=
                rightCanonical letter separator rightPrefix rightRest
                  rightShape rightThree rightSeparator different
              omega
            · have leftBelowThree :
                  left.toList.count letter < 3 := by
                exact Nat.lt_of_le_of_ne (leftBound letter) leftThree
              have leftTwo : left.toList.count letter = 2 := by
                omega
              have rightTwo : right.toList.count letter = 2 := by
                omega
              omega

/-! ## Ordered simple-variable projection -/

private def simpleProjection (letters : List Nat) : List Nat :=
  letters.filter fun letter => decide (letters.count letter = 1)

private theorem simpleProjection_nodup (letters : List Nat) :
    (simpleProjection letters).Nodup := by
  rw [List.nodup_iff_count]
  intro tested
  have countBound :=
    (List.filter_sublist
      (l := letters)
      (p := fun letter => decide (letters.count letter = 1))).count_le
        tested
  by_cases simple : letters.count tested = 1
  · simpa [simpleProjection, simple] using countBound
  · have absent : tested ∉ simpleProjection letters := by
      simp [simpleProjection, simple]
    rw [List.count_eq_zero.mpr absent]
    omega

private theorem pairProjection_count_of_kept
    (letters : List Nat) (x y selected : Nat)
    (kept : pairKeep x y selected = true) :
    (pairProjection letters x y).count selected =
      letters.count selected := by
  unfold pairProjection
  induction letters with
  | nil => simp
  | cons first rest induction =>
      by_cases equality : first = selected
      · subst first
        simp [kept, induction]
      · by_cases firstKept : pairKeep x y first
        · simp [firstKept, equality, induction]
        · simp [firstKept, equality, induction]

private theorem pairProjection_member
    {letters : List Nat} {x y value : Nat}
    (member : value ∈ pairProjection letters x y) :
    value = x ∨ value = y := by
  have kept := (List.mem_filter.mp member).2
  simpa [pairKeep] using kept

private theorem pairList_length
    {x y : Nat} (different : x ≠ y) :
    ∀ letters : List Nat,
      (∀ value, value ∈ letters -> value = x ∨ value = y) ->
      letters.length = letters.count x + letters.count y
  | [], _ => by simp
  | value :: rest, onlyPair => by
      have headPair := onlyPair value (by simp)
      have restPair :
          ∀ selected, selected ∈ rest -> selected = x ∨ selected = y := by
        intro selected member
        exact onlyPair selected (by simp [member])
      have induction := pairList_length different rest restPair
      rcases headPair with rfl | rfl
      · simp [different, induction]
        omega
      · simp [Ne.symm different, induction]
        omega

private theorem pairList_shape_one_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 1)
    (yCount : letters.count y = 1)
    (onlyPair :
      ∀ value, value ∈ letters -> value = x ∨ value = y) :
    letters = [x, y] ∨ letters = [y, x] := by
  have lengthTwo : letters.length = 2 := by
    rw [pairList_length different letters onlyPair, xCount, yCount]
  rcases letters with _ | ⟨first, rest⟩
  · simp at lengthTwo
  rcases rest with _ | ⟨second, rest⟩
  · simp at lengthTwo
  have restEmpty : rest = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using lengthTwo
  subst rest
  have firstPair := onlyPair first (by simp)
  have secondPair := onlyPair second (by simp)
  rcases firstPair with rfl | rfl
  · rcases secondPair with rfl | rfl
    · simp at xCount
    · exact Or.inl rfl
  · rcases secondPair with rfl | rfl
    · exact Or.inr rfl
    · simp at yCount

private theorem pairProjection_shape_one_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 1)
    (yCount : letters.count y = 1) :
    pairProjection letters x y = [x, y] ∨
      pairProjection letters x y = [y, x] := by
  apply pairList_shape_one_one
  · exact different
  · rw [pairProjection_count_of_kept]
    · exact xCount
    · simp [pairKeep]
  · rw [pairProjection_count_of_kept]
    · exact yCount
    · simp [pairKeep]
  · intro value member
    exact pairProjection_member member

private theorem simplePrecedes_iff_pairProjection
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : word.toList.count x = 1)
    (yCount : word.toList.count y = 1) :
    SemigroupBasis.CoRoots.S5_793Invariant.SimplePrecedes word x y ↔
      pairProjection word.toList x y = [x, y] := by
  rw [SemigroupBasis.CoRoots.S5_793Invariant.SimplePrecedes,
    ← pairScan_eq_orderGapScan]
  rw [pairScan_eq_pairProjection]
  rcases pairProjection_shape_one_one
      word.toList different xCount yCount with shape | shape
  · rw [shape]
    simp [pairScan, different, Ne.symm different,
      SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol,
      SemigroupBasis.CoRoots.S5_793Invariant.orderStep]
  · rw [shape]
    simp [pairScan, different, Ne.symm different,
      SemigroupBasis.CoRoots.S5_793Invariant.orderSymbol,
      SemigroupBasis.CoRoots.S5_793Invariant.orderStep]

private theorem simpleProjection_pairProjection
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xSimple : letters.count x = 1)
    (ySimple : letters.count y = 1) :
    (simpleProjection letters).filter (pairKeep x y) =
      pairProjection letters x y := by
  unfold simpleProjection pairProjection
  rw [List.filter_filter]
  apply List.filter_congr
  intro value _
  by_cases isX : value = x
  · subst value
    simp [pairKeep, xSimple]
  · by_cases isY : value = y
    · subst value
      simp [pairKeep, isX, ySimple]
    · simp [pairKeep, isX, isY]

private theorem nodup_eq_of_pairProjection_head :
    ∀ {left right : List Nat},
      left.Nodup ->
      right.Nodup ->
      (∀ value, value ∈ left ↔ value ∈ right) ->
      (∀ x y,
        x ≠ y ->
        x ∈ left ->
        y ∈ left ->
        (left.filter (pairKeep x y)).head? =
          (right.filter (pairKeep x y)).head?) ->
      left = right
  | [], [], _, _, _, _ => rfl
  | [], head :: tail, _, _, sameMembers, _ => by
      have : head ∈ ([] : List Nat) :=
        (sameMembers head).mpr (by simp)
      simp at this
  | head :: tail, [], _, _, sameMembers, _ => by
      have : head ∈ ([] : List Nat) :=
        (sameMembers head).mp (by simp)
      simp at this
  | leftHead :: leftTail, rightHead :: rightTail,
      leftNodup, rightNodup, sameMembers, sameHeads => by
      simp only [List.nodup_cons] at leftNodup rightNodup
      have headsEqual : leftHead = rightHead := by
        apply Decidable.byContradiction
        intro different
        have leftHeadMember : leftHead ∈ leftHead :: leftTail := by simp
        have rightHeadMember : rightHead ∈ leftHead :: leftTail :=
          (sameMembers rightHead).mpr (by simp)
        have pairHeads :=
          sameHeads leftHead rightHead different
            leftHeadMember rightHeadMember
        simp [pairKeep, different] at pairHeads
      subst rightHead
      have tailMembers :
          ∀ value, value ∈ leftTail ↔ value ∈ rightTail := by
        intro value
        constructor
        · intro member
          have inRight : value ∈ leftHead :: rightTail :=
            (sameMembers value).mp (by simp [member])
          rcases List.mem_cons.mp inRight with equality | tailMember
          · subst value
            exact False.elim (leftNodup.1 member)
          · exact tailMember
        · intro member
          have inLeft : value ∈ leftHead :: leftTail :=
            (sameMembers value).mpr (by simp [member])
          rcases List.mem_cons.mp inLeft with equality | tailMember
          · subst value
            exact False.elim (rightNodup.1 member)
          · exact tailMember
      have tailHeads :
          ∀ x y,
            x ≠ y ->
            x ∈ leftTail ->
            y ∈ leftTail ->
            (leftTail.filter (pairKeep x y)).head? =
              (rightTail.filter (pairKeep x y)).head? := by
        intro x y different xMember yMember
        have xNotHead : x ≠ leftHead := by
          intro equality
          subst x
          exact leftNodup.1 xMember
        have yNotHead : y ≠ leftHead := by
          intro equality
          subst y
          exact leftNodup.1 yMember
        have inherited :=
          sameHeads x y different
            (by simp [xMember]) (by simp [yMember])
        simpa [pairKeep, Ne.symm xNotHead,
          Ne.symm yNotHead] using inherited
      have tailEqual :=
        nodup_eq_of_pairProjection_head
          leftNodup.2 rightNodup.2 tailMembers tailHeads
      rw [tailEqual]

private theorem simpleProjection_eq
    {left right : Word Nat}
    (same : SameFactorSignature left right)
    (leftBound : ∀ letter, left.toList.count letter ≤ 3)
    (rightBound : ∀ letter, right.toList.count letter ≤ 3) :
    simpleProjection left.toList =
      simpleProjection right.toList := by
  have counts : ∀ letter,
      left.toList.count letter = right.toList.count letter :=
    fun letter =>
      same.count_eq_of_le_three letter
        (leftBound letter) (rightBound letter)
  apply nodup_eq_of_pairProjection_head
  · exact simpleProjection_nodup left.toList
  · exact simpleProjection_nodup right.toList
  · intro letter
    constructor
    · intro member
      have leftSimple : left.toList.count letter = 1 := by
        have kept := (List.mem_filter.mp member).2
        simpa [simpleProjection] using kept
      have rightSimple : right.toList.count letter = 1 := by
        rw [← counts letter]
        exact leftSimple
      apply List.mem_filter.mpr
      exact ⟨List.count_pos_iff.mp (by omega), by
        simp [rightSimple]⟩
    · intro member
      have rightSimple : right.toList.count letter = 1 := by
        have kept := (List.mem_filter.mp member).2
        simpa [simpleProjection] using kept
      have leftSimple : left.toList.count letter = 1 := by
        rw [counts letter]
        exact rightSimple
      apply List.mem_filter.mpr
      exact ⟨List.count_pos_iff.mp (by omega), by
        simp [leftSimple]⟩
  · intro x y different xMember yMember
    have leftX : left.toList.count x = 1 := by
      have kept := (List.mem_filter.mp xMember).2
      simpa [simpleProjection] using kept
    have leftY : left.toList.count y = 1 := by
      have kept := (List.mem_filter.mp yMember).2
      simpa [simpleProjection] using kept
    have rightX : right.toList.count x = 1 := by
      rw [← counts x]
      exact leftX
    have rightY : right.toList.count y = 1 := by
      rw [← counts y]
      exact leftY
    rw [simpleProjection_pairProjection
        left.toList different leftX leftY,
      simpleProjection_pairProjection
        right.toList different rightX rightY]
    rcases pairProjection_shape_one_one
        left.toList different leftX leftY with leftXY | leftYX <;>
      rcases pairProjection_shape_one_one
        right.toList different rightX rightY with rightXY | rightYX
    · simp [leftXY, rightXY]
    · have leftOrder :
          SemigroupBasis.CoRoots.S5_793Invariant.SimplePrecedes
            left x y :=
        (simplePrecedes_iff_pairProjection
          left different leftX leftY).2 leftXY
      have rightOrder := (same.s5.simpleSequence x y).mp leftOrder
      have impossible :=
        (simplePrecedes_iff_pairProjection
          right different rightX rightY).1 rightOrder
      rw [rightYX] at impossible
      simp [different] at impossible
    · have rightOrder :
          SemigroupBasis.CoRoots.S5_793Invariant.SimplePrecedes
            right x y :=
        (simplePrecedes_iff_pairProjection
          right different rightX rightY).2 rightXY
      have leftOrder := (same.s5.simpleSequence x y).mpr rightOrder
      have impossible :=
        (simplePrecedes_iff_pairProjection
          left different leftX leftY).1 leftOrder
      rw [leftYX] at impossible
      simp [different] at impossible
    · simp [leftYX, rightYX]

/-! ## Sorted simple-separator decompositions -/

private inductive SimpleSeparatorDecomposition (whole : List Nat) :
    List Nat -> List (List Nat × Nat) -> List Nat -> Prop where
  | final (gap : List Nat)
      (gapRepeated :
        ∀ letter, letter ∈ gap -> 2 ≤ whole.count letter) :
      SimpleSeparatorDecomposition whole gap [] gap
  | step (gap : List Nat) (separator : Nat) (remainder : List Nat)
      (segments : List (List Nat × Nat)) (finalGap : List Nat)
      (separatorSimple : whole.count separator = 1)
      (gapRepeated :
        ∀ letter, letter ∈ gap -> 2 ≤ whole.count letter)
      (tail :
        SimpleSeparatorDecomposition whole remainder segments finalGap) :
      SimpleSeparatorDecomposition
        whole (gap ++ separator :: remainder)
          ((gap, separator) :: segments) finalGap

private theorem prependRepeatedToSimpleSeparatorDecomposition
    {whole remaining : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (letter : Nat) (letterRepeated : 2 ≤ whole.count letter)
    (decomposition :
      SimpleSeparatorDecomposition whole remaining segments finalGap) :
    ∃ newSegments newFinalGap,
      SimpleSeparatorDecomposition
        whole (letter :: remaining) newSegments newFinalGap := by
  induction decomposition with
  | final gap gapRepeated =>
      refine ⟨[], letter :: gap, .final (letter :: gap) ?_⟩
      intro tested member
      rcases List.mem_cons.mp member with equal | inGap
      · subst tested
        exact letterRepeated
      · exact gapRepeated tested inGap
  | step gap separator remainder restSegments restFinal
      separatorSimple gapRepeated tail _tailInduction =>
      have extendedRepeated :
          ∀ tested, tested ∈ letter :: gap ->
            2 ≤ whole.count tested := by
        intro tested member
        rcases List.mem_cons.mp member with equal | inGap
        · subst tested
          exact letterRepeated
        · exact gapRepeated tested inGap
      refine
        ⟨(letter :: gap, separator) :: restSegments, restFinal, ?_⟩
      simpa using
        SimpleSeparatorDecomposition.step
          (whole := whole) (gap := letter :: gap)
          (separator := separator) (remainder := remainder)
          (segments := restSegments) (finalGap := restFinal)
          separatorSimple extendedRepeated tail

private theorem existsSimpleSeparatorDecompositionAux
    (whole : List Nat) :
    ∀ remaining : List Nat,
      (∀ letter, letter ∈ remaining -> letter ∈ whole) ->
      ∃ segments finalGap,
        SimpleSeparatorDecomposition whole remaining segments finalGap
  | [], _ =>
      ⟨[], [], .final [] (by simp)⟩
  | head :: tail, contained => by
      have tailContained :
          ∀ letter, letter ∈ tail -> letter ∈ whole := by
        intro letter member
        exact contained letter (List.mem_cons_of_mem head member)
      obtain ⟨segments, finalGap, decomposition⟩ :=
        existsSimpleSeparatorDecompositionAux whole tail tailContained
      by_cases simple : whole.count head = 1
      · refine ⟨([], head) :: segments, finalGap, ?_⟩
        simpa using
          SimpleSeparatorDecomposition.step
            (whole := whole) (gap := []) (separator := head)
            (remainder := tail) (segments := segments)
            (finalGap := finalGap) simple (by simp) decomposition
      · have headMember : head ∈ whole :=
          contained head (by simp)
        have positive : 0 < whole.count head :=
          List.count_pos_iff.mpr headMember
        have repeated : 2 ≤ whole.count head := by omega
        exact prependRepeatedToSimpleSeparatorDecomposition
          head repeated decomposition

private theorem existsSimpleSeparatorDecomposition (whole : List Nat) :
    ∃ segments finalGap,
      SimpleSeparatorDecomposition whole whole segments finalGap :=
  existsSimpleSeparatorDecompositionAux whole whole
    (by intro letter member; exact member)

private theorem repeatedGap_filter_simple_nil
    (whole gap : List Nat)
    (repeated : ∀ letter, letter ∈ gap -> 2 ≤ whole.count letter) :
    gap.filter (fun letter => decide (whole.count letter = 1)) = [] := by
  induction gap with
  | nil => rfl
  | cons letter gap induction =>
      have letterRepeated := repeated letter (by simp)
      have letterNotSimple : whole.count letter ≠ 1 := by omega
      simp [letterNotSimple, induction (by
        intro tested member
        exact repeated tested (List.Mem.tail letter member))]

namespace SimpleSeparatorDecomposition

private theorem separatorSequence_eq
    {whole source : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      SimpleSeparatorDecomposition whole source segments finalGap) :
    segments.map Prod.snd =
      source.filter (fun letter => decide (whole.count letter = 1)) := by
  induction decomposition with
  | final gap gapRepeated =>
      simpa using repeatedGap_filter_simple_nil whole gap gapRepeated
  | step gap separator remainder segments finalGap
      separatorSimple gapRepeated tail induction =>
      have gapEmpty :=
        repeatedGap_filter_simple_nil whole gap gapRepeated
      simp [List.filter_append, gapEmpty, separatorSimple, induction]

end SimpleSeparatorDecomposition

private def renderSortedSeparatorDecomposition
    (segments : List (List Nat × Nat)) (finalGap : List Nat) :
    List Nat :=
  segments.flatMap (fun segment =>
      uniqueSeparatorSortQuadratic segment.1 ++ [segment.2]) ++
    uniqueSeparatorSortQuadratic finalGap

private theorem sortedQuadratic_eq_of_counts
    (left right : List Nat)
    (counts : ∀ letter, left.count letter = right.count letter) :
    uniqueSeparatorSortQuadratic left =
      uniqueSeparatorSortQuadratic right := by
  have permutation :
      (uniqueSeparatorSortQuadratic left).Perm
        (uniqueSeparatorSortQuadratic right) := by
    rw [List.perm_iff_count]
    intro letter
    rw [(uniqueSeparatorSortQuadratic_perm left).count letter,
      (uniqueSeparatorSortQuadratic_perm right).count letter]
    exact counts letter
  apply List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
  · simpa [uniqueSeparatorSortSquareSegment] using
      uniqueSeparatorSortSquareSegment_sorted
        (UniqueSeparatorSquareSegment.mk left none)
  · simpa [uniqueSeparatorSortSquareSegment] using
      uniqueSeparatorSortSquareSegment_sorted
        (UniqueSeparatorSquareSegment.mk right none)
  · exact permutation

private theorem listDerivesSortedSeparatorDecomposition
    {whole source : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      SimpleSeparatorDecomposition whole source segments finalGap) :
    ∀ (pre : List Nat),
      (∀ letter, (pre ++ source).count letter = whole.count letter) ->
      ListDerives
        (pre ++ source)
        (pre ++ renderSortedSeparatorDecomposition segments finalGap) := by
  induction decomposition with
  | final gap repeated =>
      intro pre counts
      have globallyRepeated :
          ∀ letter, letter ∈ gap ->
            2 ≤ (pre ++ gap ++ []).count letter := by
        intro letter member
        have atLeast := repeated letter member
        have total := counts letter
        simpa using
          (show 2 ≤ (pre ++ gap).count letter by omega)
      have sorted :=
        listDerivesRepeatedPermutation
          (uniqueSeparatorSortQuadratic_perm gap).symm
          pre [] globallyRepeated
      simpa [renderSortedSeparatorDecomposition] using sorted
  | step gap separator remainder segments finalGap
      separatorSimple repeated tail induction =>
      intro pre counts
      have globallyRepeated :
          ∀ letter, letter ∈ gap ->
            2 ≤
              (pre ++ gap ++ (separator :: remainder)).count letter := by
        intro letter member
        have atLeast := repeated letter member
        have total := counts letter
        simpa [List.append_assoc] using
          (show
            2 ≤ (pre ++ (gap ++ separator :: remainder)).count letter by
              omega)
      have firstStep :=
        listDerivesRepeatedPermutation
          (uniqueSeparatorSortQuadratic_perm gap).symm
          pre (separator :: remainder) globallyRepeated
      let nextPre :=
        pre ++ uniqueSeparatorSortQuadratic gap ++ [separator]
      have nextCounts :
          ∀ letter,
            (nextPre ++ remainder).count letter = whole.count letter := by
        intro letter
        calc
          (nextPre ++ remainder).count letter =
              (pre ++ gap ++ separator :: remainder).count letter := by
            simp only [nextPre, List.count_append, List.count_cons,
              List.count_nil]
            rw [(uniqueSeparatorSortQuadratic_perm gap).count letter]
            omega
          _ = whole.count letter := by
            simpa [List.append_assoc] using counts letter
      have restStep := induction nextPre nextCounts
      have firstStep' :
          ListDerives
            (pre ++ gap ++ separator :: remainder)
            (nextPre ++ remainder) := by
        simpa [nextPre, List.append_assoc] using firstStep
      simpa [renderSortedSeparatorDecomposition, nextPre,
        List.append_assoc] using firstStep'.trans restStep

private theorem sortedSeparatorAlignmentAux
    {left right : Word Nat}
    (same : SameFactorSignature left right)
    (leftBound : ∀ letter, left.toList.count letter ≤ 3)
    (rightBound : ∀ letter, right.toList.count letter ≤ 3)
    (leftCanonical : SimpleSplitCanonical left.toList)
    (rightCanonical : SimpleSplitCanonical right.toList)
    {leftSource rightSource : List Nat}
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      SimpleSeparatorDecomposition
        left.toList leftSource leftSegments leftFinal)
    (rightDecomposition :
      SimpleSeparatorDecomposition
        right.toList rightSource rightSegments rightFinal)
    (leftPrefix rightPrefix : List Nat)
    (leftShape : left.toList = leftPrefix ++ leftSource)
    (rightShape : right.toList = rightPrefix ++ rightSource)
    (prefixCounts :
      ∀ letter, leftPrefix.count letter = rightPrefix.count letter)
    (separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd) :
    renderSortedSeparatorDecomposition leftSegments leftFinal =
      renderSortedSeparatorDecomposition rightSegments rightFinal := by
  induction leftDecomposition generalizing
      rightSource rightSegments rightFinal leftPrefix rightPrefix with
  | final leftGap leftRepeated =>
      cases rightDecomposition with
      | final rightRepeated =>
          have totalCounts : ∀ letter,
              left.toList.count letter = right.toList.count letter :=
            fun letter =>
              same.count_eq_of_le_three letter
                (leftBound letter) (rightBound letter)
          have gapCounts :
              ∀ letter, leftGap.count letter = rightSource.count letter := by
            intro letter
            have total := totalCounts letter
            have prefixWords := prefixCounts letter
            rw [leftShape, rightShape,
              List.count_append, List.count_append] at total
            omega
          simp [renderSortedSeparatorDecomposition,
            sortedQuadratic_eq_of_counts leftGap rightSource gapCounts]
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp at separatorEq
  | step leftGap leftSeparator leftRemainder leftRest leftFinal
      leftSeparatorSimple leftRepeated leftTail leftInduction =>
      cases rightDecomposition with
      | final rightGap rightRepeated =>
          simp at separatorEq
      | step rightGap rightSeparator rightRemainder rightRest
          rightFinal rightSeparatorSimple rightRepeated rightTail =>
          simp only [List.map_cons, List.cons.injEq] at separatorEq
          rcases separatorEq with
            ⟨separatorHeadEq, separatorRestEq⟩
          subst rightSeparator
          have leftCutShape :
              left.toList =
                (leftPrefix ++ leftGap) ++
                  leftSeparator :: leftRemainder := by
            rw [leftShape]
            simp [List.append_assoc]
          have rightCutShape :
              right.toList =
                (rightPrefix ++ rightGap) ++
                  leftSeparator :: rightRemainder := by
            rw [rightShape]
            simp [List.append_assoc]
          have cumulativeCounts :
              ∀ letter,
                (leftPrefix ++ leftGap).count letter =
                  (rightPrefix ++ rightGap).count letter :=
            prefixCount_eq same leftBound rightBound
              leftCanonical rightCanonical leftCutShape rightCutShape
              leftSeparatorSimple rightSeparatorSimple
          have gapCounts :
              ∀ letter, leftGap.count letter = rightGap.count letter := by
            intro letter
            have cumulative := cumulativeCounts letter
            have prefixWords := prefixCounts letter
            simp only [List.count_append] at cumulative
            omega
          have headEq :=
            sortedQuadratic_eq_of_counts leftGap rightGap gapCounts
          have nextPrefixCounts :
              ∀ letter,
                (leftPrefix ++ leftGap ++ [leftSeparator]).count letter =
                  (rightPrefix ++ rightGap ++ [leftSeparator]).count
                    letter := by
            intro letter
            have cumulative := cumulativeCounts letter
            simp only [List.count_append, List.count_cons,
              List.count_nil] at cumulative ⊢
            omega
          have leftTailShape :
              left.toList =
                (leftPrefix ++ leftGap ++ [leftSeparator]) ++
                  leftRemainder := by
            rw [leftShape]
            simp [List.append_assoc]
          have rightTailShape :
              right.toList =
                (rightPrefix ++ rightGap ++ [leftSeparator]) ++
                  rightRemainder := by
            rw [rightShape]
            simp [List.append_assoc]
          have tailEq :=
            leftInduction rightTail
              (leftPrefix ++ leftGap ++ [leftSeparator])
              (rightPrefix ++ rightGap ++ [leftSeparator])
              leftTailShape rightTailShape nextPrefixCounts
              separatorRestEq
          calc
            renderSortedSeparatorDecomposition
                ((leftGap, leftSeparator) :: leftRest) leftFinal =
                (uniqueSeparatorSortQuadratic leftGap ++
                    [leftSeparator]) ++
                  renderSortedSeparatorDecomposition
                    leftRest leftFinal := by
              simp [renderSortedSeparatorDecomposition,
                List.append_assoc]
            _ =
                (uniqueSeparatorSortQuadratic rightGap ++
                    [leftSeparator]) ++
                  renderSortedSeparatorDecomposition
                    rightRest rightFinal := by
              rw [headEq, tailEq]
            _ = renderSortedSeparatorDecomposition
                ((rightGap, leftSeparator) :: rightRest) rightFinal := by
              simp [renderSortedSeparatorDecomposition,
                List.append_assoc]

private theorem sortedSeparatorAlignment
    {left right : Word Nat}
    (same : SameFactorSignature left right)
    (leftBound : ∀ letter, left.toList.count letter ≤ 3)
    (rightBound : ∀ letter, right.toList.count letter ≤ 3)
    (leftCanonical : SimpleSplitCanonical left.toList)
    (rightCanonical : SimpleSplitCanonical right.toList)
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      SimpleSeparatorDecomposition
        left.toList left.toList leftSegments leftFinal)
    (rightDecomposition :
      SimpleSeparatorDecomposition
        right.toList right.toList rightSegments rightFinal) :
    renderSortedSeparatorDecomposition leftSegments leftFinal =
      renderSortedSeparatorDecomposition rightSegments rightFinal := by
  have separatorEq :
      leftSegments.map Prod.snd = rightSegments.map Prod.snd := by
    calc
      leftSegments.map Prod.snd =
          simpleProjection left.toList := by
        simpa [simpleProjection] using
          SimpleSeparatorDecomposition.separatorSequence_eq
            leftDecomposition
      _ = simpleProjection right.toList :=
        simpleProjection_eq same leftBound rightBound
      _ = rightSegments.map Prod.snd := by
        simpa [simpleProjection] using
          (SimpleSeparatorDecomposition.separatorSequence_eq
            rightDecomposition).symm
  exact sortedSeparatorAlignmentAux same leftBound rightBound
    leftCanonical rightCanonical
    leftDecomposition rightDecomposition [] []
    (by simp) (by simp) (by simp) separatorEq

/-- The canonical three-limited combinatorial core. -/
theorem listDerivesOfSameFactorSignature_threeLimitedCanonical
    {left right : Word Nat}
    (same : SameFactorSignature left right)
    (leftBound : ∀ letter, left.toList.count letter ≤ 3)
    (rightBound : ∀ letter, right.toList.count letter ≤ 3)
    (leftCanonical : FirstPairCanonical left.toList)
    (rightCanonical : FirstPairCanonical right.toList) :
    ListDerives left.toList right.toList := by
  obtain ⟨leftSegments, leftFinal, leftDecomposition⟩ :=
    existsSimpleSeparatorDecomposition left.toList
  obtain ⟨rightSegments, rightFinal, rightDecomposition⟩ :=
    existsSimpleSeparatorDecomposition right.toList
  have leftNormal :=
    listDerivesSortedSeparatorDecomposition
      leftDecomposition [] (by simp)
  have rightNormal :=
    listDerivesSortedSeparatorDecomposition
      rightDecomposition [] (by simp)
  have normalEq :=
    sortedSeparatorAlignment same leftBound rightBound
      leftCanonical.simpleSplitCanonical
      rightCanonical.simpleSplitCanonical
      leftDecomposition rightDecomposition
  rw [normalEq] at leftNormal
  simpa using leftNormal.trans rightNormal.symm

/-! ## Unrestricted completeness -/

/-- The combined factor signature is derivationally sufficient on arbitrary
nonempty words. -/
theorem derivesOfSameFactorSignature
    {left right : Word Nat}
    (same : SameFactorSignature left right) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          obtain ⟨leftReduced, leftReducedBound, leftReduction⟩ :=
            existsThreeLimited (leftHead :: leftTail)
          obtain ⟨rightReduced, rightReducedBound, rightReduction⟩ :=
            existsThreeLimited (rightHead :: rightTail)
          obtain
            ⟨leftReducedHead, leftReducedTail,
              leftReducedShape, leftReductionWord⟩ :=
            leftReduction.from_cons
          obtain
            ⟨rightReducedHead, rightReducedTail,
              rightReducedShape, rightReductionWord⟩ :=
            rightReduction.from_cons
          obtain
            ⟨leftNormalized, leftCanonicalRaw, leftNormalizedCounts,
              leftNormalization⟩ :=
            existsFirstPairCanonical
              leftReduced leftReducedBound
          obtain
            ⟨rightNormalized, rightCanonicalRaw,
              rightNormalizedCounts, rightNormalization⟩ :=
            existsFirstPairCanonical
              rightReduced rightReducedBound
          have leftNormalizationFromCons :
              ListDerives
                (leftReducedHead :: leftReducedTail)
                leftNormalized := by
            rw [leftReducedShape] at leftNormalization
            exact leftNormalization
          have rightNormalizationFromCons :
              ListDerives
                (rightReducedHead :: rightReducedTail)
                rightNormalized := by
            rw [rightReducedShape] at rightNormalization
            exact rightNormalization
          obtain
            ⟨leftNormalHead, leftNormalTail,
              leftNormalShape, leftNormalizationWord⟩ :=
            leftNormalizationFromCons.from_cons
          obtain
            ⟨rightNormalHead, rightNormalTail,
              rightNormalShape, rightNormalizationWord⟩ :=
            rightNormalizationFromCons.from_cons
          let leftNormal : Word Nat :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              leftNormalHead leftNormalTail
          let rightNormal : Word Nat :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              rightNormalHead rightNormalTail
          have leftNormalToList :
              leftNormal.toList = leftNormalized := by
            simpa [leftNormal,
              SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.toList] using leftNormalShape.symm
          have rightNormalToList :
              rightNormal.toList = rightNormalized := by
            simpa [rightNormal,
              SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.toList] using rightNormalShape.symm
          have leftCanonical :
              FirstPairCanonical leftNormal.toList := by
            rw [leftNormalToList]
            exact leftCanonicalRaw
          have rightCanonical :
              FirstPairCanonical rightNormal.toList := by
            rw [rightNormalToList]
            exact rightCanonicalRaw
          have leftBound :
              ∀ letter, leftNormal.toList.count letter ≤ 3 := by
            intro letter
            rw [leftNormalToList, leftNormalizedCounts letter]
            exact leftReducedBound letter
          have rightBound :
              ∀ letter, rightNormal.toList.count letter ≤ 3 := by
            intro letter
            rw [rightNormalToList, rightNormalizedCounts letter]
            exact rightReducedBound letter
          have leftPath :
              Derives basis
                (Word.mk leftHead leftTail) leftNormal := by
            exact leftReductionWord.trans <| by
              simpa [leftNormal] using leftNormalizationWord
          have rightPath :
              Derives basis
                (Word.mk rightHead rightTail) rightNormal := by
            exact rightReductionWord.trans <| by
              simpa [rightNormal] using rightNormalizationWord
          have leftPathSignature :=
            sameFactorSignatureOfDerives leftPath
          have rightPathSignature :=
            sameFactorSignatureOfDerives rightPath
          have normalSame : SameFactorSignature leftNormal rightNormal :=
            leftPathSignature.symm.trans <|
              same.trans rightPathSignature
          have middleList :=
            listDerivesOfSameFactorSignature_threeLimitedCanonical
              normalSame leftBound rightBound
              leftCanonical rightCanonical
          have middleWord : Derives basis leftNormal rightNormal := by
            simpa [leftNormal, rightNormal,
              SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.toList] using
                SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
                  middleList
          exact leftPath.trans <|
            middleWord.trans rightPath.symm

/-- Every unrestricted identity valid in the two direct factors follows
from the fixed sixteen laws. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (s2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameFactorSignature
    (sameFactorSignatureOfFactorValid identity s2Valid s5Valid)

/-- Unrestricted joint basis for `V(S2_2) ∩ V(S5_400)`.  This single
factor-pair theorem discharges the WO-3 obligation for roots `S6_4089`,
`S6_4199`, and `S6_4295`. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup
      basis where
  leftModels := modelsS2_2
  rightModels := modelsS5_400
  complete := derivesOfFactorValid

/-- Replace the right factor of an intersection basis by a semigroup with
the same identity theory. -/
theorem intersectionBasisOfSameRightTheory
    {A : Type u} {B : Type v} {C : Type w}
    {leftFactor : Semigroup A}
    {sourceRight : Semigroup B} {targetRight : Semigroup C}
    {candidate : List (Identity Nat)}
    (source :
      IntersectionBasis leftFactor sourceRight candidate)
    (sameTheory :
      SameIdentityTheoryOver sourceRight targetRight Nat) :
    IntersectionBasis leftFactor targetRight candidate where
  leftModels := source.leftModels
  rightModels :=
    source.rightModels.transportIdentityTheory sameTheory
  complete := by
    intro identity leftValid rightValid
    exact source.complete identity leftValid
      ((sameTheory identity).mpr rightValid)

/-- The same joint-completeness theorem for `S5_840`, covering its WO-3
roots `S6_8873` and `S6_9017`, is a direct identity-theory transport. -/
def intersectionBasisS5_840 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup
      basis :=
  intersectionBasisOfSameRightTheory
    intersectionBasis sameTheoryS5_400S5_840

end SemigroupBasis.CoRoots.Order6FactorPairS2S5400Normal
