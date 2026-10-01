import SemigroupBasis.CoRoots.S5_381Family
import SemigroupBasis.CoRoots.S5_443Family
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S5381

open SemigroupBasis
open SemigroupBasis.Examples

/-!
Unrestricted joint completeness for
`S2_2` direct x `S5_381` direct
(`OBL-JOINT-S2_2_direct-S5_381_direct`), covering roots
`S6_4079` and `S6_4288`.

The same `S5_381` common theory is carried by `S5_610`; the final section
therefore exposes the corresponding `S2_2` direct x `S5_610` result as well.
-/

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

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
def yxxzy : Word Nat := w 1 [0, 0, 2, 1]
def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
def xyxzz : Word Nat := w 0 [1, 0, 2, 2]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]
def zxyxz : Word Nat := w 2 [0, 1, 0, 2]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyy : Word Nat := w 0 [2, 1, 1]

def powerLaw : Identity Nat := Identity.mk xx xxxx
def tripleLeftContractionLaw : Identity Nat := Identity.mk xxxyx xyx
def tripleHeadSwitchLaw : Identity Nat := Identity.mk xxxyy yxxxy
def endpointTransferLaw : Identity Nat := Identity.mk xxyx xyxx
def splitEndpointContractionLaw : Identity Nat := Identity.mk xxyxx xyx
def squareInterleaveLaw : Identity Nat := Identity.mk xxyy xyxy
def squareFinalSwitchLaw : Identity Nat := Identity.mk xxyy xyyx
def squareInitialSwitchLaw : Identity Nat := Identity.mk xxyy yxxy
def attachmentYXXZYLaw : Identity Nat := Identity.mk xxyzy yxxzy
def rightTripleExpansionLaw : Identity Nat := Identity.mk xyx xyxxx
def headSquareRotationLaw : Identity Nat := Identity.mk xyxzz xyzzx
def headSquareTransferLaw : Identity Nat := Identity.mk xyxzz zxyxz
def prefixedGatherLaw : Identity Nat := Identity.mk xyzy xzyy

/-- The exact 13-law WO-3 candidate, SHA-256
`ba4e34217dcb083d680a3622a00b4ffbf810ca87acc7aa52c909f98a2fc2f769`. -/
def basis : List (Identity Nat) :=
  [powerLaw, tripleLeftContractionLaw, tripleHeadSwitchLaw,
    endpointTransferLaw, splitEndpointContractionLaw,
    squareInterleaveLaw, squareFinalSwitchLaw, squareInitialSwitchLaw,
    attachmentYXXZYLaw, rightTripleExpansionLaw,
    headSquareRotationLaw, headSquareTransferLaw, prefixedGatherLaw]

theorem basis_length : basis.length = 13 := by
  decide

/-! ## Candidate-law derivations -/

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

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) (((u ++ u) ++ u) ++ u) := by
  have substituted :=
    derivesBasisSubstitution powerLaw
      (by simp [basis])
      (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesFourToTwo (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

theorem derivesTripleLeftContraction (u v : Word Nat) :
    Derives basis
      ((((u ++ u) ++ u) ++ v) ++ u)
      ((u ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution tripleLeftContractionLaw
      (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [tripleLeftContractionLaw, xxxyx, xyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesTripleHeadSwitch (u v : Word Nat) :
    Derives basis
      ((((u ++ u) ++ u) ++ v) ++ v)
      ((((v ++ u) ++ u) ++ u) ++ v) := by
  have substituted :=
    derivesBasisSubstitution tripleHeadSwitchLaw
      (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [tripleHeadSwitchLaw, xxxyy, yxxxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesEndpointTransfer (u v : Word Nat) :
    Derives basis
      (((u ++ u) ++ v) ++ u)
      ((u ++ v) ++ (u ++ u)) := by
  have substituted :=
    derivesBasisSubstitution endpointTransferLaw
      (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [endpointTransferLaw, xxyx, xyxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSplitEndpointContraction (u v : Word Nat) :
    Derives basis
      ((((u ++ u) ++ v) ++ u) ++ u)
      ((u ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution splitEndpointContractionLaw
      (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [splitEndpointContractionLaw, xxyxx, xyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSquareInterleave (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ (v ++ v))
      ((u ++ v) ++ (u ++ v)) := by
  have substituted :=
    derivesBasisSubstitution squareInterleaveLaw
      (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [squareInterleaveLaw, xxyy, xyxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSquareFinalSwitch (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    derivesBasisSubstitution squareFinalSwitchLaw
      (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [squareFinalSwitchLaw, xxyy, xyyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSquareInitialSwitch (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ (v ++ v))
      (((v ++ u) ++ u) ++ v) := by
  have substituted :=
    derivesBasisSubstitution squareInitialSwitchLaw
      (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [squareInitialSwitchLaw, xxyy, yxxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesAttachmentYXXZY (u v z : Word Nat) :
    Derives basis
      ((((u ++ u) ++ v) ++ z) ++ v)
      ((((v ++ u) ++ u) ++ z) ++ v) := by
  have substituted :=
    derivesBasisSubstitution attachmentYXXZYLaw
      (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [attachmentYXXZYLaw, xxyzy, yxxzy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesRightTripleExpansion (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      ((((u ++ v) ++ u) ++ u) ++ u) := by
  have substituted :=
    derivesBasisSubstitution rightTripleExpansionLaw
      (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [rightTripleExpansionLaw, xyx, xyxxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesHeadSquareRotation
    (head middle square : Word Nat) :
    Derives basis
      ((((head ++ middle) ++ head) ++ square) ++ square)
      ((((head ++ middle) ++ square) ++ square) ++ head) := by
  have substituted :=
    derivesBasisSubstitution headSquareRotationLaw
      (by simp [basis])
      (instantiateThreeWords head middle square)
  simpa [headSquareRotationLaw, xyxzz, xyzzx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesHeadSquareTransfer
    (old middle new : Word Nat) :
    Derives basis
      ((((old ++ middle) ++ old) ++ new) ++ new)
      ((((new ++ old) ++ middle) ++ old) ++ new) := by
  have substituted :=
    derivesBasisSubstitution headSquareTransferLaw
      (by simp [basis])
      (instantiateThreeWords old middle new)
  simpa [headSquareTransferLaw, xyxzz, zxyxz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesPrefixedGather
    (pre repeated middle : Word Nat) :
    Derives basis
      (((pre ++ repeated) ++ middle) ++ repeated)
      (((pre ++ middle) ++ repeated) ++ repeated) := by
  have substituted :=
    derivesBasisSubstitution prefixedGatherLaw
      (by simp [basis])
      (instantiateThreeWords pre repeated middle)
  simpa [prefixedGatherLaw, xyzy, xzyy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesPrefixedSquareCommutation
    (pre left right : Word Nat) :
    Derives basis
      (pre ++ ((left ++ left) ++ (right ++ right)))
      (pre ++ ((right ++ right) ++ (left ++ left))) := by
  have first :=
    Derives.prepend pre (derivesSquareFinalSwitch left right)
  have second :=
    derivesPrefixedGather pre left (right ++ right)
  exact first.trans <| by
    simpa [Word.append_assoc] using second

/-! ## Finite-factor soundness -/

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

theorem modelsS2_2 :
    Models Generated.S2_2.table.semigroup basis :=
  modelsOfFiniteChecks Generated.S2_2.table (by decide)

theorem modelsCyclicTwo :
    Models cyclicTwo.semigroup basis := by
  rw [← Generated.S2_2.table_eq_catalogue_model]
  exact modelsS2_2

set_option maxHeartbeats 1000000 in
theorem modelsS5_381 :
    Models Generated.Catalogue.S5_381.table.semigroup basis :=
  modelsOfFiniteChecks Generated.Catalogue.S5_381.table (by decide)

set_option maxHeartbeats 1000000 in
theorem modelsS5_610 :
    Models Generated.Catalogue.S5_610.table.semigroup basis :=
  modelsOfFiniteChecks Generated.Catalogue.S5_610.table (by decide)

/-! ## The common `S4_71` and parity theory -/

private def row7
    (c0 c1 c2 c3 c4 c5 c6 column : Fin 7) : Fin 7 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else
            if column = 5 then c5 else c6

/-- The seven-element subsemigroup of `S4_71 x S2_2` obtained by deleting
the pair `(3, 1)`. It maps onto `S5_614`, whose certified basis is the common
period-two block basis. -/
private def commonBridgeMul (left right : Fin 7) : Fin 7 :=
  if left = 0 then row7 0 1 0 1 0 1 0 right else
    if left = 1 then row7 1 0 1 0 1 0 1 right else
      if left = 2 then row7 0 1 0 1 0 1 2 right else
        if left = 3 then row7 1 0 1 0 1 0 3 right else
          if left = 4 then row7 0 1 2 3 4 5 4 right else
            if left = 5 then row7 1 0 3 2 5 4 5 right else
              row7 0 1 2 3 4 5 6 right

private def commonBridgeTable : FiniteTable where
  order := 7
  mul := commonBridgeMul
  assoc := by decide

private def commonBridgeBlockMap (value : Fin 7) : Fin 4 :=
  match value.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | _ => 3

private def commonBridgeBlockSection (value : Fin 4) : Fin 7 :=
  match value.val with
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | _ => 6

private def commonBridgeBlock :
    SplitSurjection commonBridgeTable.semigroup
      Generated.S4_71.table.semigroup where
  toFun := commonBridgeBlockMap
  map_mul := by decide
  preimage := commonBridgeBlockSection
  right_inverse := by decide

private def commonBridgeCyclicMap (value : Fin 7) : Fin 2 :=
  match value.val with
  | 1 => 1
  | 3 => 1
  | 5 => 1
  | _ => 0

private def commonBridgeCyclicSection (value : Fin 2) : Fin 7 :=
  if value = 0 then 0 else 1

private def commonBridgeCyclic :
    SplitSurjection commonBridgeTable.semigroup
      cyclicTwo.semigroup where
  toFun := commonBridgeCyclicMap
  map_mul := by decide
  preimage := commonBridgeCyclicSection
  right_inverse := by decide

private def commonBridgePair :
    SubdirectPair commonBridgeTable.semigroup
      Generated.S4_71.table.semigroup cyclicTwo.semigroup where
  left := commonBridgeBlock
  right := commonBridgeCyclic
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

private def commonBridgeQuotientMap (value : Fin 7) : Fin 5 :=
  match value.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 3
  | _ => 4

private def commonBridgeQuotientSection (value : Fin 5) : Fin 7 :=
  match value.val with
  | 0 => 0
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | _ => 6

private def commonBridgeQuotient :
    SplitSurjection commonBridgeTable.semigroup
      Generated.Catalogue.S5_614.table.semigroup where
  toFun := commonBridgeQuotientMap
  map_mul := by decide
  preimage := commonBridgeQuotientSection
  right_inverse := by decide

private theorem commonDerivesOfFactorValid
    (identity : Identity Nat)
    (blockValid :
      identity.SatisfiedBy Generated.S4_71.table.semigroup)
    (cyclicValid :
      identity.SatisfiedBy cyclicTwo.semigroup) :
    Derives S5_443Family.basis identity.lhs identity.rhs := by
  have bridgeValid :
      identity.SatisfiedBy commonBridgeTable.semigroup :=
    (commonBridgePair.satisfiedBy_iff identity).2
      ⟨blockValid, cyclicValid⟩
  have quotientValid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_614.table.semigroup :=
    commonBridgeQuotient.pushforwardIdentity identity bridgeValid
  exact
    S5_443Family.S5_614.basis_complete.2 identity quotientValid

private theorem bind_append
    (left right : Word Nat) (sigma : Nat -> Word Nat) :
    (left ++ right).bind sigma =
      left.bind sigma ++ right.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (tau sigma : Nat -> Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay the complete common `S4_71`/parity basis behind a protected
nonempty prefix. The prefix makes the right-gather law one of the advertised
candidate laws. -/
theorem liftCommonUnderPrefix
    {left right : Word Nat}
    (derivation : Derives S5_443Family.basis left right)
    (ctx : Word Nat) (sigma : Nat -> Word Nat) :
    Derives basis
      (ctx ++ left.bind sigma)
      (ctx ++ right.bind sigma) := by
  induction derivation generalizing ctx sigma with
  | fromBasis member =>
      simp only [S5_443Family.basis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · change Derives basis
          (ctx ++ (sigma 0 ++ sigma 0))
          (ctx ++ (((sigma 0 ++ sigma 0) ++ sigma 0) ++ sigma 0))
        exact Derives.prepend ctx (derivesPowerExpansion (sigma 0))
      · change Derives basis
          (ctx ++ ((sigma 0 ++ sigma 1) ++ sigma 0))
          (ctx ++ ((sigma 1 ++ sigma 0) ++ sigma 0))
        simpa only [Word.append_assoc] using
          derivesPrefixedGather ctx (sigma 0) (sigma 1)
      · change Derives basis
          (ctx ++ (((sigma 0 ++ sigma 0) ++ sigma 1) ++ sigma 1))
          (ctx ++ (((sigma 1 ++ sigma 1) ++ sigma 0) ++ sigma 0))
        simpa only [Word.append_assoc] using
          derivesPrefixedSquareCommutation ctx (sigma 0) (sigma 1)
  | refl =>
      exact Derives.refl _
  | symm _ inductionHypothesis =>
      exact (inductionHypothesis ctx sigma).symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact
        (firstHypothesis ctx sigma).trans
          (secondHypothesis ctx sigma)
  | prepend pre _ inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        inductionHypothesis (ctx ++ pre.bind sigma) sigma
  | appendRight _ post inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis ctx sigma) (post.bind sigma)
  | subst _ tau inductionHypothesis =>
      simpa [bind_bind] using
        inductionHypothesis ctx
          (fun letter => (tau letter).bind sigma)

/-! ## Joint semantic signature -/

def SameOccurrenceParity (left right : Word Nat) : Prop :=
  forall letter,
    left.toList.count letter % 2 =
      right.toList.count letter % 2

structure SameJointSignature (left right : Word Nat) : Prop where
  s5 :
    S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
      left right
  parity : SameOccurrenceParity left right

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private theorem cyclicDerivesOfParityEq
    (identity : Identity Nat)
    (parity : SameOccurrenceParity identity.lhs identity.rhs) :
    Derives cyclicTwoBasis identity.lhs identity.rhs := by
  have reducedPerm :
      (parityReduce identity.lhs.toList).Perm
        (parityReduce identity.rhs.toList) :=
    parityReduce_perm_of_parity_eq parity
  have lhsNormal := cyclicDerivesNormal identity.lhs
  have rhsNormal := cyclicDerivesNormal identity.rhs
  cases lhsShape : parityReduce identity.lhs.toList with
  | nil =>
      rw [lhsShape] at reducedPerm
      have rhsShape : parityReduce identity.rhs.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [lhsShape] at lhsNormal
      rw [rhsShape] at rhsNormal
      exact lhsNormal.trans <|
        (cyclicDerivesCommonSquare
          (Word.singleton identity.lhs.head)
          (Word.singleton identity.rhs.head)).trans rhsNormal.symm
  | cons leftHead leftTail =>
      cases rhsShape : parityReduce identity.rhs.toList with
      | nil =>
          rw [lhsShape, rhsShape] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons rightHead rightTail =>
          rw [lhsShape] at lhsNormal
          rw [rhsShape] at rhsNormal
          rw [lhsShape, rhsShape] at reducedPerm
          exact lhsNormal.trans <|
            (cyclicDerivesPermutation
              (wordOfCons leftHead leftTail)
              (wordOfCons rightHead rightTail)
              reducedPerm).trans rhsNormal.symm

private theorem cyclicSatisfiedByOfParityEq
    (identity : Identity Nat)
    (parity : SameOccurrenceParity identity.lhs identity.rhs) :
    identity.SatisfiedBy cyclicTwo.semigroup := by
  intro valuation
  exact
    (cyclicDerivesOfParityEq identity parity).sound
      cyclicTwoBasis_models valuation

theorem sameJointSignature_of_s5_381_factor_valid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_381.table.semigroup) :
    SameJointSignature identity.lhs identity.rhs := by
  have cyclicValid' :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    rw [← Generated.S2_2.table_eq_catalogue_model]
    exact cyclicValid
  exact
    ⟨S5_381FamilyInvariant.S5_381.valid_sameSignature
        identity s5Valid,
      cyclicValid_parity_eq identity cyclicValid'⟩

theorem sameJointSignature_of_s5_610_factor_valid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_610.table.semigroup) :
    SameJointSignature identity.lhs identity.rhs := by
  have cyclicValid' :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    rw [← Generated.S2_2.table_eq_catalogue_model]
    exact cyclicValid
  exact
    ⟨S5_381FamilyInvariant.S5_610.valid_sameSignature
        identity s5Valid,
      cyclicValid_parity_eq identity cyclicValid'⟩

theorem derives_sameJointSignature
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameJointSignature left right := by
  let identity := Identity.mk left right
  have s5Valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_381.table.semigroup :=
    fun valuation => derivation.sound modelsS5_381 valuation
  have cyclicValid :
      identity.SatisfiedBy cyclicTwo.semigroup :=
    fun valuation => derivation.sound modelsCyclicTwo valuation
  exact
    ⟨S5_381FamilyInvariant.S5_381.valid_sameSignature
        identity s5Valid,
      cyclicValid_parity_eq identity cyclicValid⟩

/-! ## Guarded same-head completeness -/

private theorem foldlEvalCongr
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat -> S) :
    forall (letters : List Nat) (initial : S),
      (forall letter, letter ∈ letters ->
        leftValuation letter = rightValuation letter) ->
      letters.foldl
          (fun value letter =>
            semigroup.mul value (leftValuation letter))
          initial =
        letters.foldl
          (fun value letter =>
            semigroup.mul value (rightValuation letter))
          initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply foldlEvalCongr semigroup
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem evalCongrOnSupport
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat -> S)
    (word : Word Nat)
    (agree :
      forall letter, letter ∈ word.toList ->
        leftValuation letter = rightValuation letter) :
    semigroup.eval leftValuation word =
      semigroup.eval rightValuation word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [agree head (by simp [Word.toList])]
      apply foldlEvalCongr semigroup
      intro letter member
      exact agree letter (List.Mem.tail head member)

private theorem suffixValidOfSimplePrefix
    (semigroup : Semigroup S) (one : S)
    (leftIdentity : forall value, semigroup.mul one value = value)
    (head : Nat) (left right : Word Nat)
    (headNotLeft : head ∉ left.toList)
    (headNotRight : head ∉ right.toList)
    (wholeValid :
      (Identity.mk
        (Word.singleton head ++ left)
        (Word.singleton head ++ right)).SatisfiedBy semigroup) :
    (Identity.mk left right).SatisfiedBy semigroup := by
  intro valuation
  let lifted : Nat -> S :=
    fun letter => if letter = head then one else valuation letter
  have leftAgree :
      semigroup.eval valuation left =
        semigroup.eval lifted left := by
    apply evalCongrOnSupport
    intro letter member
    have different : letter ≠ head := by
      intro equality
      subst letter
      exact headNotLeft member
    simp [lifted, different]
  have rightAgree :
      semigroup.eval valuation right =
        semigroup.eval lifted right := by
    apply evalCongrOnSupport
    intro letter member
    have different : letter ≠ head := by
      intro equality
      subst letter
      exact headNotRight member
    simp [lifted, different]
  have evaluated := wholeValid lifted
  simp only [Semigroup.eval_append, Semigroup.eval_singleton] at evaluated
  have liftedHead : lifted head = one := by
    simp [lifted]
  rw [liftedHead, leftIdentity, leftIdentity] at evaluated
  exact leftAgree.trans <| evaluated.trans rightAgree.symm

private theorem s4_71LeftIdentity (value : Fin 4) :
    Generated.S4_71.table.semigroup.mul (3 : Fin 4) value = value := by
  apply Fin.ext
  revert value
  decide

private theorem cyclicTwoLeftIdentity (value : Fin 2) :
    cyclicTwo.semigroup.mul (0 : Fin 2) value = value := by
  apply Fin.ext
  revert value
  decide

private theorem headNotMemTailOfCountOne
    (word : Word Nat)
    (countOne : word.toList.count word.head = 1) :
    word.head ∉ word.tail := by
  have countZero : word.tail.count word.head = 0 := by
    cases word with
    | mk head tail =>
        simpa [Word.toList] using countOne
  exact List.count_eq_zero.mp countZero

private theorem headMemTailOfCountNeOne
    (word : Word Nat)
    (countNotOne : word.toList.count word.head ≠ 1) :
    word.head ∈ word.tail := by
  apply Decidable.byContradiction
  intro absent
  apply countNotOne
  cases word with
  | mk head tail =>
      simp [Word.toList, List.count_eq_zero.mpr absent]

private theorem tailNilOfSameSignature
    {left right : Word Nat}
    (same :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
        left right)
    (heads : left.head = right.head)
    (rightHeadSimple :
      right.toList.count right.head = 1)
    (leftTailEmpty : left.tail = []) :
    right.tail = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter member
  have rightMember : letter ∈ right.toList := by
    cases right
    simp [Word.toList, member]
  have leftMember : letter ∈ left.toList :=
    (same.support letter).2 rightMember
  have letterIsLeftHead : letter = left.head := by
    have headOrTail :
        letter = left.head ∨ letter ∈ left.tail := by
      simpa [Word.toList] using leftMember
    rcases headOrTail with equal | inTail
    · exact equal
    · simp [leftTailEmpty] at inTail
  have letterIsRightHead : letter = right.head :=
    letterIsLeftHead.trans heads
  have rightHeadInTail : right.head ∈ right.tail := by
    simpa [letterIsRightHead] using member
  exact
    (headNotMemTailOfCountOne right rightHeadSimple)
      rightHeadInTail

private abbrev ListDerives :=
  S5_107.ListDerives basis

private theorem listDerivesAddInitialPair
    (head : Nat) (tail : List Nat)
    (headInTail : head ∈ tail) :
    ListDerives
      (head :: tail)
      ([head, head] ++ head :: tail) := by
  rcases List.append_of_mem headInTail with
    ⟨before, after, rfl⟩
  cases before with
  | nil =>
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesPowerExpansion (Word.singleton head))
      simpa [Word.toList_append, List.append_assoc] using
        expanded.append after
  | cons middleHead middleTail =>
      let middle :=
        S5_107.listWordOfCons middleHead middleTail
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesTripleLeftContraction
            (Word.singleton head) middle).symm
      simpa [middle, S5_107.listWordOfCons,
        Word.toList_append, List.append_assoc] using
        expanded.append after

theorem derivesAddInitialPair
    (word : Word Nat)
    (headInTail : word.head ∈ word.tail) :
    Derives basis word
      ((Word.singleton word.head ++ Word.singleton word.head) ++ word) := by
  cases word with
  | mk head tail =>
      have listDerivation :=
        listDerivesAddInitialPair head tail headInTail
      simpa [S5_107.listWordOfCons, Word.singleton,
        Word.append, List.append_assoc] using
        S5_107.ListDerives.toWord listDerivation

private theorem derivesSameHeadOfJointSignature
    {left right : Word Nat}
    (same : SameJointSignature left right)
    (heads : left.head = right.head) :
    Derives basis left right := by
  have wholeCyclic :
      (Identity.mk left right).SatisfiedBy cyclicTwo.semigroup :=
    cyclicSatisfiedByOfParityEq (Identity.mk left right) same.parity
  by_cases leftHeadSimple :
      left.toList.count left.head = 1
  · have leftSimpleInitial :
        S5_107.SimpleInitial left left.head :=
      ⟨leftHeadSimple, rfl⟩
    have rightSimpleInitial :=
      (same.s5.initial left.head).mp leftSimpleInitial
    have rightHeadSimple :
        right.toList.count right.head = 1 := by
      simpa [heads] using rightSimpleInitial.1
    have tailsEmpty :
        left.tail = [] ↔ right.tail = [] := by
      constructor
      · exact tailNilOfSameSignature
          same.s5 heads rightHeadSimple
      · exact tailNilOfSameSignature
          same.s5.symm heads.symm leftHeadSimple
    cases left with
    | mk leftHead leftTail =>
        cases right with
        | mk rightHead rightTail =>
            simp only at heads
            subst rightHead
            cases leftTail with
            | nil =>
                have rightEmpty : rightTail = [] :=
                  tailsEmpty.mp rfl
                subst rightTail
                exact Derives.refl _
            | cons leftSecond leftRest =>
                cases rightTail with
                | nil =>
                    have impossible :
                        leftSecond :: leftRest = [] :=
                      tailsEmpty.mpr rfl
                    contradiction
                | cons rightSecond rightRest =>
                    let leftSuffix : Word Nat :=
                      Word.mk leftSecond leftRest
                    let rightSuffix : Word Nat :=
                      Word.mk rightSecond rightRest
                    have leftHeadAbsent :
                        leftHead ∉ leftSuffix.toList := by
                      change leftHead ∉ leftSecond :: leftRest
                      exact headNotMemTailOfCountOne
                        (Word.mk leftHead (leftSecond :: leftRest))
                        leftHeadSimple
                    have rightHeadAbsent :
                        leftHead ∉ rightSuffix.toList := by
                      change leftHead ∉ rightSecond :: rightRest
                      exact headNotMemTailOfCountOne
                        (Word.mk leftHead (rightSecond :: rightRest))
                        rightHeadSimple
                    have wholeBlock :
                        (Identity.mk
                          (Word.singleton leftHead ++ leftSuffix)
                          (Word.singleton leftHead ++ rightSuffix)).SatisfiedBy
                            Generated.S4_71.table.semigroup := by
                      simpa [leftSuffix, rightSuffix, Word.singleton,
                        Word.append] using same.s5.blockTheory
                    have wholeCyclic' :
                        (Identity.mk
                          (Word.singleton leftHead ++ leftSuffix)
                          (Word.singleton leftHead ++ rightSuffix)).SatisfiedBy
                            cyclicTwo.semigroup := by
                      simpa [leftSuffix, rightSuffix, Word.singleton,
                        Word.append] using wholeCyclic
                    have suffixBlock :=
                      suffixValidOfSimplePrefix
                        Generated.S4_71.table.semigroup (3 : Fin 4)
                        s4_71LeftIdentity leftHead leftSuffix rightSuffix
                        leftHeadAbsent rightHeadAbsent wholeBlock
                    have suffixCyclic :=
                      suffixValidOfSimplePrefix
                        cyclicTwo.semigroup (0 : Fin 2)
                        cyclicTwoLeftIdentity leftHead leftSuffix rightSuffix
                        leftHeadAbsent rightHeadAbsent wholeCyclic'
                    have suffixDerivation :=
                      commonDerivesOfFactorValid
                        (Identity.mk leftSuffix rightSuffix)
                        suffixBlock suffixCyclic
                    have lifted :=
                      liftCommonUnderPrefix suffixDerivation
                        (Word.singleton leftHead) Word.singleton
                    rw [bind_singleton, bind_singleton] at lifted
                    simpa [leftSuffix, rightSuffix, Word.singleton,
                      Word.append] using lifted
  · have rightHeadNotSimple :
        right.toList.count right.head ≠ 1 := by
      intro rightSimple
      have rightSimpleInitial :
          S5_107.SimpleInitial right left.head := by
        exact ⟨by simpa [heads] using rightSimple, heads.symm⟩
      have leftSimpleInitial :=
        (same.s5.initial left.head).mpr rightSimpleInitial
      exact leftHeadSimple leftSimpleInitial.1
    have leftHeadInTail :
        left.head ∈ left.tail :=
      headMemTailOfCountNeOne left leftHeadSimple
    have rightHeadInTail :
        right.head ∈ right.tail :=
      headMemTailOfCountNeOne right rightHeadNotSimple
    have leftExpanded :=
      derivesAddInitialPair left leftHeadInTail
    have rightExpanded :=
      derivesAddInitialPair right rightHeadInTail
    have commonDerivation :=
      commonDerivesOfFactorValid
        (Identity.mk left right)
        same.s5.blockTheory wholeCyclic
    let guardPrefix :=
      Word.singleton left.head ++ Word.singleton left.head
    have lifted :=
      liftCommonUnderPrefix commonDerivation guardPrefix Word.singleton
    rw [bind_singleton, bind_singleton] at lifted
    have guarded :
        Derives basis
          (guardPrefix ++ left) (guardPrefix ++ right) := by
      simpa [guardPrefix, heads] using lifted
    have rightContracted :
        Derives basis (guardPrefix ++ right) right := by
      simpa [guardPrefix, heads] using rightExpanded.symm
    exact leftExpanded.trans <|
      guarded.trans rightContracted

/-! ## Balanced head retargeting -/

private theorem listDerivesGatherPair
    (pre : List Nat) (preNonempty : pre ≠ [])
    (letter : Nat) (middle suffix : List Nat) :
    ListDerives
      (pre ++ [letter] ++ middle ++ [letter] ++ suffix)
      (pre ++ middle ++ [letter, letter] ++ suffix) := by
  cases middle with
  | nil =>
      simpa [List.append_assoc] using
        S5_107.ListDerives.refl
          (basis := basis) (pre ++ [letter, letter] ++ suffix)
  | cons middleHead middleTail =>
      obtain ⟨prefixHead, prefixTail, rfl⟩ :=
        List.exists_cons_of_ne_nil preNonempty
      have gathered :=
        S5_107.ListDerives.ofWord <|
          derivesPrefixedGather
            (S5_107.listWordOfCons prefixHead prefixTail)
            (Word.singleton letter)
            (S5_107.listWordOfCons middleHead middleTail)
      simpa [S5_107.listWordOfCons, Word.singleton,
        Word.append, List.append_assoc] using
        gathered.append suffix

private theorem splitTwoOccurrences (letter : Nat) :
    forall letters : List Nat,
      2 ≤ letters.count letter ->
      ∃ before middle after,
        letters = before ++ letter :: middle ++ letter :: after
  | [], count => by
      simp at count
  | head :: tail, count => by
      by_cases headEq : head = letter
      · subst head
        have tailMember : letter ∈ tail := by
          apply List.count_pos_iff.mp
          simp only [List.count_cons_self] at count
          omega
        rcases List.append_of_mem tailMember with
          ⟨middle, after, tailShape⟩
        exact ⟨[], middle, after, by simp [tailShape]⟩
      · have tailCount : 2 ≤ tail.count letter := by
          rw [List.count_cons_of_ne headEq] at count
          exact count
        rcases splitTwoOccurrences letter tail tailCount with
          ⟨before, middle, after, tailShape⟩
        exact
          ⟨head :: before, middle, after, by
            simp [tailShape, List.append_assoc]⟩

private theorem listDerivesRetargetMultipleHeadBalanced
    (old new : Nat) (tail : List Nat)
    (oldInTail : old ∈ tail)
    (newMultiple : 2 ≤ tail.count new) :
    ∃ switchedTail,
      ListDerives (old :: tail) (new :: switchedTail) := by
  rcases splitTwoOccurrences new tail newMultiple with
    ⟨before, middle, after, tailShape⟩
  let front := old :: before ++ middle
  have expanded :
      ListDerives
        (old :: tail) ([old, old] ++ old :: tail) :=
    listDerivesAddInitialPair old tail oldInTail
  have gatherCore :=
    listDerivesGatherPair
      ([old, old, old] ++ before) (by simp)
      new middle after
  have gathered :
      ListDerives
        ([old, old] ++ old :: tail)
        ([old, old] ++ front ++ [new, new] ++ after) := by
    rw [tailShape]
    simpa [front, List.append_assoc] using gatherCore
  have expose :
      ListDerives
        ([old, old] ++ front ++ [new, new] ++ after)
        ([old, old, new] ++ front ++ [new] ++ after) := by
    simpa [List.append_assoc] using
      (listDerivesGatherPair
        [old, old] (by simp) new front after).symm
  let frontWord :=
    S5_107.listWordOfCons old (before ++ middle)
  have switchedCore :=
    S5_107.ListDerives.ofWord <|
      derivesAttachmentYXXZY
        (Word.singleton old) (Word.singleton new) frontWord
  have switched :
      ListDerives
        ([old, old, new] ++ front ++ [new] ++ after)
        ([new, old, old] ++ front ++ [new] ++ after) := by
    simpa [front, frontWord, S5_107.listWordOfCons, Word.toList,
        Word.singleton, Word.append, List.append_assoc]
      using switchedCore.append after
  let switchedTail :=
    [old, old] ++ front ++ [new] ++ after
  refine ⟨switchedTail, ?_⟩
  simpa [switchedTail, List.append_assoc] using
    expanded.trans <| gathered.trans <| expose.trans switched

theorem derivesRetargetMultipleHeadBalanced
    (word : Word Nat) (new : Nat)
    (different : word.head ≠ new)
    (headRepeated : word.head ∈ word.tail)
    (newMultiple : 2 ≤ word.toList.count new) :
    ∃ switchedTail,
      Derives basis word (Word.mk new switchedTail) := by
  cases word with
  | mk old tail =>
      have tailNewMultiple : 2 ≤ tail.count new := by
        simpa only [Word.toList,
          List.count_cons_of_ne different] using newMultiple
      obtain ⟨switchedTail, listDerivation⟩ :=
        listDerivesRetargetMultipleHeadBalanced
          old new tail headRepeated tailNewMultiple
      refine ⟨switchedTail, ?_⟩
      simpa [S5_107.listWordOfCons] using
        S5_107.ListDerives.toWord listDerivation

private theorem headCountPositive (word : Word Nat) :
    0 < word.toList.count word.head := by
  cases word
  simp [Word.toList]

private theorem cappedMultiplicityEqTwoIff
    (word : Word Nat) (letter : Nat) :
    S5_107.cappedMultiplicity word letter = 2 ↔
      2 ≤ word.toList.count letter := by
  unfold S5_107.cappedMultiplicity
  simp only [Nat.min_def]
  split <;> omega

/-! ## Unrestricted completeness -/

/-- The joint S5 signature and coordinatewise parity are derivationally
sufficient for the fixed 13-law basis. -/
theorem derivesOfSameJointSignature
    {left right : Word Nat}
    (same : SameJointSignature left right) :
    Derives basis left right := by
  by_cases heads : left.head = right.head
  · exact derivesSameHeadOfJointSignature same heads
  · have leftCountNotOne :
        left.toList.count left.head ≠ 1 := by
      intro countOne
      have leftSimple :
          S5_107.SimpleInitial left left.head :=
        ⟨countOne, rfl⟩
      have rightSimple :=
        (same.s5.initial left.head).mp leftSimple
      exact heads rightSimple.2.symm
    have rightCountNotOne :
        right.toList.count right.head ≠ 1 := by
      intro countOne
      have rightSimple :
          S5_107.SimpleInitial right right.head :=
        ⟨countOne, rfl⟩
      have leftSimple :=
        (same.s5.initial right.head).mpr rightSimple
      exact heads leftSimple.2
    have leftHeadRepeated :
        left.head ∈ left.tail :=
      headMemTailOfCountNeOne left leftCountNotOne
    have rightHeadMultiple :
        2 ≤ right.toList.count right.head := by
      have positive := headCountPositive right
      omega
    have leftNewMultiple :
        2 ≤ left.toList.count right.head := by
      have rightCapped :
          S5_107.cappedMultiplicity right right.head = 2 :=
        (cappedMultiplicityEqTwoIff right right.head).2
          rightHeadMultiple
      have leftCapped :
          S5_107.cappedMultiplicity left right.head = 2 :=
        (same.s5.capped right.head).trans rightCapped
      exact
        (cappedMultiplicityEqTwoIff left right.head).1
          leftCapped
    obtain ⟨switchedTail, switch⟩ :=
      derivesRetargetMultipleHeadBalanced
        left right.head heads leftHeadRepeated leftNewMultiple
    let switched : Word Nat := Word.mk right.head switchedTail
    have switchSame :
        SameJointSignature left switched := by
      simpa [switched] using derives_sameJointSignature switch
    have residual :
        SameJointSignature switched right :=
      ⟨switchSame.s5.symm.trans same.s5,
        fun letter =>
          (switchSame.parity letter).symm.trans
            (same.parity letter)⟩
    have residualDerivation :
        Derives basis switched right :=
      derivesSameHeadOfJointSignature residual rfl
    exact switch.trans <| by
      simpa [switched] using residualDerivation

/-- Every unrestricted identity valid in both primary factors is derivable
from the exact WO-3 candidate. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_381.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameJointSignature
    (sameJointSignature_of_s5_381_factor_valid
      identity cyclicValid s5Valid)

/-- Unrestricted joint completeness for
`V(S2_2) intersection V(S5_381)`. -/
def factorIntersectionBasis :
    IntersectionBasis
      Generated.S2_2.table.semigroup
      Generated.Catalogue.S5_381.table.semigroup
      basis where
  leftModels := modelsS2_2
  rightModels := modelsS5_381
  complete := derivesOfFactorValid

abbrev intersectionBasis := factorIntersectionBasis

/-! ## `S5_610` transfer -/

/-- The same derivational theorem applies to `S5_610`, because its certified
family API supplies the identical S5 signature. -/
theorem derivesOfS5_610FactorValid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_610.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameJointSignature
    (sameJointSignature_of_s5_610_factor_valid
      identity cyclicValid s5Valid)

/-- Reusable unrestricted basis for
`V(S2_2) intersection V(S5_610)`, covering the corresponding direct-product
obligations (including roots `S6_6806` and `S6_6950`). -/
def s5_610FactorIntersectionBasis :
    IntersectionBasis
      Generated.S2_2.table.semigroup
      Generated.Catalogue.S5_610.table.semigroup
      basis where
  leftModels := modelsS2_2
  rightModels := modelsS5_610
  complete := derivesOfS5_610FactorValid

abbrev s5_610IntersectionBasis := s5_610FactorIntersectionBasis

end SemigroupBasis.CoRoots.Order6FactorPairS2S5381
