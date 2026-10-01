import SemigroupBasis.CoRoots.Order6S5_107InitialIntersectionFamilies
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S2_2

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude

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
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xxzyy : Word Nat := w 0 [0, 2, 1, 1]
def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xyzxy : Word Nat := w 0 [1, 2, 0, 1]
def xyzyx : Word Nat := w 0 [1, 2, 1, 0]
def xzxyy : Word Nat := w 0 [2, 0, 1, 1]
def xzyxy : Word Nat := w 0 [2, 1, 0, 1]
def xzyyx : Word Nat := w 0 [2, 1, 1, 0]
def yxxzy : Word Nat := w 1 [0, 0, 2, 1]
def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xzxyx : Word Nat := w 0 [2, 0, 1, 0]
def xyyzz : Word Nat := w 0 [1, 1, 2, 2]
def xzyyz : Word Nat := w 0 [2, 1, 1, 2]

def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def tripleLeftContractionLaw : Identity Nat := ⟨xxxyx, xyx⟩
def tripleHeadSwitchLaw : Identity Nat := ⟨xxxyy, yxxxy⟩
def endpointTransferLaw : Identity Nat := ⟨xxyx, xyxx⟩
def splitEndpointContractionLaw : Identity Nat := ⟨xxyxx, xyx⟩
def squareInterleaveLaw : Identity Nat := ⟨xxyy, xyxy⟩
def squareFinalLaw : Identity Nat := ⟨xxyy, xyyx⟩
def squareInitialLaw : Identity Nat := ⟨xxyy, yxxy⟩
def attachmentXXZYYLaw : Identity Nat := ⟨xxyzy, xxzyy⟩
def attachmentXYXZYLaw : Identity Nat := ⟨xxyzy, xyxzy⟩
def attachmentXYYZXLaw : Identity Nat := ⟨xxyzy, xyyzx⟩
def attachmentXYZXYLaw : Identity Nat := ⟨xxyzy, xyzxy⟩
def attachmentXYZYXLaw : Identity Nat := ⟨xxyzy, xyzyx⟩
def attachmentXZXYYLaw : Identity Nat := ⟨xxyzy, xzxyy⟩
def attachmentXZYXYLaw : Identity Nat := ⟨xxyzy, xzyxy⟩
def attachmentXZYYXLaw : Identity Nat := ⟨xxyzy, xzyyx⟩
def attachmentYXXZYLaw : Identity Nat := ⟨xxyzy, yxxzy⟩
def rightTripleExpansionLaw : Identity Nat := ⟨xyx, xyxxx⟩
def blockSwapLaw : Identity Nat := ⟨xyxzx, xzxyx⟩

/-- The exact ordered candidate shared by the WO-3 group containing the
direct `S5_107`, direct/opposite `S5_108`, and direct `S5_109` right
factors.  Its direct `S2_2`/direct `S5_107` roots are `S6_1259`,
`S6_1347`, and `S6_1350`. -/
def basis : List (Identity Nat) :=
  [powerLaw, tripleLeftContractionLaw, tripleHeadSwitchLaw,
    endpointTransferLaw, splitEndpointContractionLaw,
    squareInterleaveLaw, squareFinalLaw, squareInitialLaw,
    attachmentXXZYYLaw, attachmentXYXZYLaw, attachmentXYYZXLaw,
    attachmentXYZXYLaw, attachmentXYZYXLaw, attachmentXZXYYLaw,
    attachmentXZYXYLaw, attachmentXZYYXLaw, attachmentYXXZYLaw,
    rightTripleExpansionLaw, blockSwapLaw]

theorem basis_length : basis.length = 19 := by
  decide

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem s2Checked :
    FiniteCertificate.checkModels
      SemigroupBasis.Generated.S2_2.table basis toFinThree = true := by
  decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem s5Checked :
    FiniteCertificate.checkModels
      SemigroupBasis.Generated.Catalogue.S5_107.table
      basis toFinThree = true := by
  decide

/-- Every displayed law is valid in the direct `S2_2` factor. -/
theorem modelsS2_2 :
    Models SemigroupBasis.Generated.S2_2.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S2_2.table basis toFinThree s2Checked

/-- Every displayed law is valid in the sealed `S5_107` factor. -/
theorem modelsS5_107 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_107.table
    basis toFinThree s5Checked

/-- Sound candidate laws can be replayed in the sealed `S5_107` calculus. -/
theorem derivesInS5_107
    (identity : Identity Nat) (member : identity ∈ basis) :
    Derives SemigroupBasis.CoRoots.S5_107.basis
      identity.lhs identity.rhs :=
  SemigroupBasis.CoRoots.S5_107Family.S5_107.basisFor.2
    identity (modelsS5_107 identity member)

/-- Two semigroups with one complete basis have the same identity theory. -/
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

private def reverseInvolutiveEmbedding
    {A : Type u} {G H : Semigroup A}
    (embedding : Embedding G H)
    (involution :
      ∀ value, embedding.toFun (embedding.toFun value) = value) :
    Embedding H G where
  toFun := embedding.toFun
  map_mul := by
    intro left right
    apply embedding.injective
    rw [involution, embedding.map_mul, involution, involution]
  injective := embedding.injective

private theorem sameIdentityTheoryOverOfMutualEmbeddings
    {A : Type u} {B : Type v} {X : Type w}
    {G : Semigroup A} {H : Semigroup B}
    (intoH : Embedding G H) (intoG : Embedding H G) :
    SameIdentityTheoryOver G H X := by
  intro identity
  exact
    ⟨fun validInG => intoG.pullback_identity identity validInG,
      fun validInH => intoH.pullback_identity identity validInH⟩

private def s5_107IntoOpposite :
    Embedding
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup.opposite :=
  reverseInvolutiveEmbedding
    SemigroupBasis.CoRoots.S5_107Family.S5_107.selfDualEmbedding
    SemigroupBasis.CoRoots.S5_107Family.S5_107.selfDualInvolution

theorem sameTheoryS5_107Opposite :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup.opposite
      Nat :=
  sameIdentityTheoryOverOfMutualEmbeddings
    s5_107IntoOpposite
    SemigroupBasis.CoRoots.S5_107Family.S5_107.selfDualEmbedding

theorem sameTheoryS5_107S5_108 :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.CoRoots.S5_107Family.S5_107.basisFor
    SemigroupBasis.CoRoots.S5_107Family.S5_108.basisFor

theorem sameTheoryS5_107S5_109 :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_109.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.CoRoots.S5_107Family.S5_107.basisFor
    SemigroupBasis.CoRoots.S5_107Family.S5_109.basisFor

private theorem sameIdentityTheoryOverToOpposite
    {A : Type u} {B : Type v} {X : Type w}
    {G : Semigroup A} {H : Semigroup B}
    (selfDual : SameIdentityTheoryOver G G.opposite X)
    (same : SameIdentityTheoryOver G H X) :
    SameIdentityTheoryOver G H.opposite X := by
  intro identity
  constructor
  · intro validInG
    have validInGOpposite := (selfDual identity).mp validInG
    have reversedInG :=
      (Identity.satisfiedBy_opposite_iff_reversed identity G).mp
        validInGOpposite
    have reversedInH := (same identity.reversed).mp reversedInG
    exact
      (Identity.satisfiedBy_opposite_iff_reversed identity H).mpr
        reversedInH
  · intro validInHOpposite
    have reversedInH :=
      (Identity.satisfiedBy_opposite_iff_reversed identity H).mp
        validInHOpposite
    have reversedInG := (same identity.reversed).mpr reversedInH
    have validInGOpposite :=
      (Identity.satisfiedBy_opposite_iff_reversed identity G).mpr
        reversedInG
    exact (selfDual identity).mpr validInGOpposite

theorem sameTheoryS5_107S5_108Opposite :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite
      Nat :=
  sameIdentityTheoryOverToOpposite
    sameTheoryS5_107Opposite sameTheoryS5_107S5_108

theorem modelsS5_108 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup basis :=
  modelsS5_107.transportIdentityTheory sameTheoryS5_107S5_108

theorem modelsS5_108Opposite :
    Models
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite
      basis :=
  modelsS5_107.transportIdentityTheory
    sameTheoryS5_107S5_108Opposite

theorem modelsS5_109 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_109.table.semigroup basis :=
  modelsS5_107.transportIdentityTheory sameTheoryS5_107S5_109

/-- Replace the right factor of an intersection result by a semigroup with
the same identity theory. -/
theorem intersectionBasisOfSameRightTheory
    {A : Type u} {B : Type v} {C : Type w}
    {leftFactor : Semigroup A}
    {sourceRight : Semigroup B} {targetRight : Semigroup C}
    {candidate : List (Identity Nat)}
    (source :
      IntersectionBasis leftFactor sourceRight candidate)
    (same :
      SameIdentityTheoryOver sourceRight targetRight Nat) :
    IntersectionBasis leftFactor targetRight candidate where
  leftModels := source.leftModels
  rightModels := source.rightModels.transportIdentityTheory same
  complete := by
    intro identity leftValid rightValid
    exact source.complete identity leftValid ((same identity).mpr rightValid)

theorem intersectionS2_2S5_108OfS5_107
    (source :
      IntersectionBasis
        SemigroupBasis.Generated.S2_2.table.semigroup
        SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup basis) :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup basis :=
  intersectionBasisOfSameRightTheory source sameTheoryS5_107S5_108

theorem intersectionS2_2S5_108OppositeOfS5_107
    (source :
      IntersectionBasis
        SemigroupBasis.Generated.S2_2.table.semigroup
        SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup basis) :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite
      basis :=
  intersectionBasisOfSameRightTheory
    source sameTheoryS5_107S5_108Opposite

theorem intersectionS2_2S5_109OfS5_107
    (source :
      IntersectionBasis
        SemigroupBasis.Generated.S2_2.table.semigroup
        SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup basis) :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_109.table.semigroup basis :=
  intersectionBasisOfSameRightTheory source sameTheoryS5_107S5_109

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

/-- Contract four consecutive copies of a nonempty block to two. -/
theorem derivesFourToTwo (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have substituted :=
    derivesBasisSubstitution powerLaw (by simp [basis])
      (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted.symm

/-- Contract `u^3 v u` to `u v u`. -/
theorem derivesTripleLeftContraction (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ v) ++ u)
      ((u ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution tripleLeftContractionLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [tripleLeftContractionLaw, xxxyx, xyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Switch the initial block across a triple block and a square block. -/
theorem derivesTripleHeadSwitch (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ v) ++ v)
      ((((v ++ u) ++ u) ++ u) ++ v) := by
  have substituted :=
    derivesBasisSubstitution tripleHeadSwitchLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [tripleHeadSwitchLaw, xxxyy, yxxxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Move one repeated endpoint occurrence from left to right. -/
theorem derivesEndpointTransfer (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ u)
      ((u ++ v) ++ (u ++ u)) := by
  have substituted :=
    derivesBasisSubstitution endpointTransferLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [endpointTransferLaw, xxyx, xyxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Contract two separated endpoint pairs to one pair. -/
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

theorem derivesSquareFinalSwitch (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution squareFinalLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [squareFinalLaw, xxyy, xyyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSquareInitialSwitch (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      (((v ++ u) ++ u) ++ v) := by
  have substituted :=
    derivesBasisSubstitution squareInitialLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [squareInitialLaw, xxyy, yxxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Add two copies at the repeated right endpoint. -/
theorem derivesRightTripleExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u)
      ((((u ++ v) ++ u) ++ u) ++ u) := by
  have substituted :=
    derivesBasisSubstitution rightTripleExpansionLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [rightTripleExpansionLaw, xyx, xyxxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Swap two blocks between three occurrences of an anchor block. -/
theorem derivesAnchoredBlockSwap (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      ((((u ++ z) ++ u) ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution blockSwapLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [blockSwapLaw, xyxzx, xzxyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The tail-square promotion used by the initial-intersection normalizer is
already a prefixed instance of the square-initial switch. -/
theorem derivesTailSquarePromotion
    (guard u v : Word Nat) :
    Derives basis
      (guard ++ ((u ++ u) ++ (v ++ v)))
      (guard ++ (((v ++ u) ++ u) ++ v)) := by
  simpa [Word.append_assoc] using
    Derives.prepend guard (derivesSquareInitialSwitch u v)

def tailSquarePromotionLaw : Identity Nat := ⟨xyyzz, xzyyz⟩

theorem derivesTailSquarePromotionLaw :
    Derives basis tailSquarePromotionLaw.lhs
      tailSquarePromotionLaw.rhs := by
  simpa [tailSquarePromotionLaw, xyyzz, xzyyz, w,
    Word.append, Word.singleton, Word.append_assoc] using
      derivesTailSquarePromotion
        (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)

/-- The parity-preserving portion of the initial-intersection basis. -/
def initialBalancedBasis : List (Identity Nat) :=
  [squareInterleaveLaw, squareFinalLaw,
    attachmentXXZYYLaw, attachmentXYXZYLaw, attachmentXYYZXLaw,
    attachmentXYZXYLaw, attachmentXYZYXLaw, attachmentXZXYYLaw,
    attachmentXZYXYLaw, attachmentXZYYXLaw, blockSwapLaw,
    tailSquarePromotionLaw]

theorem initialBalancedBasis_matches :
    initialBalancedBasis =
      SemigroupBasis.CoRoots.Order6S5_107InitialIntersection.basis.drop 3 := by
  decide

theorem initialBalancedLawDerives
    (identity : Identity Nat) (member : identity ∈ initialBalancedBasis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [initialBalancedBasis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact Derives.fromBasis (e := squareInterleaveLaw) (by simp [basis])
  · exact Derives.fromBasis (e := squareFinalLaw) (by simp [basis])
  · exact Derives.fromBasis (e := attachmentXXZYYLaw) (by simp [basis])
  · exact Derives.fromBasis (e := attachmentXYXZYLaw) (by simp [basis])
  · exact Derives.fromBasis (e := attachmentXYYZXLaw) (by simp [basis])
  · exact Derives.fromBasis (e := attachmentXYZXYLaw) (by simp [basis])
  · exact Derives.fromBasis (e := attachmentXYZYXLaw) (by simp [basis])
  · exact Derives.fromBasis (e := attachmentXZXYYLaw) (by simp [basis])
  · exact Derives.fromBasis (e := attachmentXZYXYLaw) (by simp [basis])
  · exact Derives.fromBasis (e := attachmentXZYYXLaw) (by simp [basis])
  · exact Derives.fromBasis (e := blockSwapLaw) (by simp [basis])
  · exact derivesTailSquarePromotionLaw

/-- Any derivation using only the balanced tail of the initial-intersection
basis transports to the 19-law candidate. -/
theorem transportInitialBalanced
    {left right : Word Nat}
    (derivation :
      Derives
        (SemigroupBasis.CoRoots.Order6S5_107InitialIntersection.basis.drop 3)
        left right) :
    Derives basis left right := by
  rw [← initialBalancedBasis_matches] at derivation
  exact Derives.transport initialBalancedLawDerives derivation

/-- The semantic invariant forced jointly by `S2_2` and `S5_107`. -/
structure SameFactorSignature (left right : Word Nat) : Prop where
  s5 :
    SemigroupBasis.CoRoots.S5_107.SameSimpleAdjacencySignature left right
  parity :
    ∀ letter,
      left.toList.count letter % 2 =
        right.toList.count letter % 2

namespace SameFactorSignature

theorem refl (word : Word Nat) :
    SameFactorSignature word word :=
  ⟨SemigroupBasis.CoRoots.S5_107.SameSimpleAdjacencySignature.refl word,
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
    fun letter =>
      (first.parity letter).trans (second.parity letter)⟩

theorem support {left right : Word Nat}
    (same : SameFactorSignature left right) (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList :=
  same.s5.support letter

/-- Once both counts have been reduced to at most three, capped
multiplicity plus parity determines the exact count. -/
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

def multiplicityState (word : Word Nat) (letter : Nat) : Nat × Nat :=
  (SemigroupBasis.CoRoots.S5_107.cappedMultiplicity word letter,
    word.toList.count letter % 2)

theorem multiplicityState_eq
    {left right : Word Nat}
    (same : SameFactorSignature left right) (letter : Nat) :
    multiplicityState left letter = multiplicityState right letter := by
  apply Prod.ext
  · exact same.s5.capped letter
  · exact same.parity letter

/-- Factor validity yields precisely the simple-adjacency and parity data
needed by a period-two normalizer. -/
theorem sameFactorSignatureOfFactorValid
    (identity : Identity Nat)
    (s2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup) :
    SameFactorSignature identity.lhs identity.rhs := by
  have cyclicValid :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    rw [← SemigroupBasis.Generated.S2_2.table_eq_catalogue_model]
    exact s2Valid
  exact
    ⟨SemigroupBasis.CoRoots.S5_107.valid_sameSimpleAdjacencySignature
        identity s5Valid,
      cyclicValid_parity_eq identity cyclicValid⟩

/-- The direct `S5_108` member of the WO-3 group has the same joint
signature as `S5_107`. -/
theorem sameFactorSignatureOfS5_108FactorValid
    (identity : Identity Nat)
    (s2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup) :
    SameFactorSignature identity.lhs identity.rhs :=
  sameFactorSignatureOfFactorValid identity s2Valid
    ((sameTheoryS5_107S5_108 identity).mpr s5Valid)

/-- The opposite `S5_108` member of the WO-3 group has the same joint
signature as `S5_107`. -/
theorem sameFactorSignatureOfS5_108OppositeFactorValid
    (identity : Identity Nat)
    (s2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite) :
    SameFactorSignature identity.lhs identity.rhs :=
  sameFactorSignatureOfFactorValid identity s2Valid
    ((sameTheoryS5_107S5_108Opposite identity).mpr s5Valid)

/-- The direct `S5_109` member of the WO-3 group has the same joint
signature as `S5_107`. -/
theorem sameFactorSignatureOfS5_109FactorValid
    (identity : Identity Nat)
    (s2Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_109.table.semigroup) :
    SameFactorSignature identity.lhs identity.rhs :=
  sameFactorSignatureOfFactorValid identity s2Valid
    ((sameTheoryS5_107S5_109 identity).mpr s5Valid)

/-- Every derivation from the candidate preserves the combined factor
signature. -/
theorem sameFactorSignatureOfDerives
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameFactorSignature left right := by
  have s2Valid :
      (⟨left, right⟩ : Identity Nat).SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup := by
    intro valuation
    exact derivation.sound modelsS2_2 valuation
  have s5Valid :
      (⟨left, right⟩ : Identity Nat).SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup := by
    intro valuation
    exact derivation.sound modelsS5_107 valuation
  exact
    sameFactorSignatureOfFactorValid
      (⟨left, right⟩ : Identity Nat) s2Valid s5Valid

end SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude
