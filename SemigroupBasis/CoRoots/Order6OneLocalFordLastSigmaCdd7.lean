import SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening
import SemigroupBasis.CoRoots.S5_442Invariant
import SemigroupBasis.CoRoots.S5_443Family
import SemigroupBasis.CoRoots.S5_793Family
import SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.Generated.S3_11
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6OneLocalFordLastSigmaCdd7

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-- The exact ten-law displayed system shared by the `cdd7...` obligation
group in the one-local Ford/last family. -/
abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma.Sigma_cdd7bcfee1652ef1.basis

/-! ## Fixed finite-factor soundness -/

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

/-- Reflect an exhaustive check of the fixed three-variable system back to
natural-number variable names. Endpoint wrappers reuse this theorem. -/
theorem modelsOfFiniteChecks
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
    Models SemigroupBasis.Generated.S2_2.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S2_2.table (by decide)

theorem modelsS2_4 :
    Models SemigroupBasis.Generated.S2_4.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S2_4.table (by decide)

theorem modelsS3_11 :
    Models SemigroupBasis.Generated.S3_11.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S3_11.table (by decide)

set_option maxHeartbeats 1000000 in
theorem modelsS5_801 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_801.table.semigroup basis :=
  modelsOfFiniteChecks
    SemigroupBasis.Generated.Catalogue.S5_801.table (by decide)

set_option maxHeartbeats 1000000 in
theorem modelsS5_614 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup basis :=
  modelsOfFiniteChecks
    SemigroupBasis.Generated.Catalogue.S5_614.table (by decide)

set_option maxHeartbeats 1000000 in
theorem modelsS5_843 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_843.table.semigroup basis :=
  modelsOfFiniteChecks
    SemigroupBasis.Generated.Catalogue.S5_843.table (by decide)

/-! ## Exact displayed-system rewrite moves -/

private def instantiateThreeWords
    (first second third : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private theorem basisPowerLaw :
    Derives basis (w 0 [0]) (w 0 [0, 0, 0]) :=
  Derives.fromBasis
    (e := Identity.mk (w 0 [0]) (w 0 [0, 0, 0])) (by decide)

private theorem basisTripleLeftContraction :
    Derives basis (w 0 [0, 0, 1, 0]) (w 0 [1, 0]) :=
  Derives.fromBasis
    (e := Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0])) (by decide)

private theorem basisSquareInterleave :
    Derives basis (w 0 [0, 1, 1]) (w 0 [1, 0, 1]) :=
  Derives.fromBasis
    (e := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])) (by decide)

private theorem basisSquareFinalSwitch :
    Derives basis (w 0 [0, 1, 1]) (w 0 [1, 1, 0]) :=
  Derives.fromBasis
    (e := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0])) (by decide)

private theorem basisPrefixedGather :
    Derives basis (w 0 [1, 2, 1]) (w 0 [2, 1, 1]) :=
  Derives.fromBasis
    (e := Identity.mk (w 0 [1, 2, 1]) (w 0 [2, 1, 1])) (by decide)

theorem derivesPowerExpansion (word : Word Nat) :
    Derives basis
      (word ++ word)
      (((word ++ word) ++ word) ++ word) := by
  have substituted :=
    Derives.subst basisPowerLaw
      (instantiateThreeWords word word word)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesTripleLeftContraction (repeated middle : Word Nat) :
    Derives basis
      ((((repeated ++ repeated) ++ repeated) ++ middle) ++ repeated)
      ((repeated ++ middle) ++ repeated) := by
  have substituted :=
    Derives.subst basisTripleLeftContraction
      (instantiateThreeWords repeated middle middle)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Gather a repeated nonempty word behind an arbitrary protected prefix. -/
theorem derivesPrefixedGather
    (ctx repeated middle : Word Nat) :
    Derives basis
      (((ctx ++ repeated) ++ middle) ++ repeated)
      (((ctx ++ middle) ++ repeated) ++ repeated) := by
  have substituted :=
    Derives.subst basisPrefixedGather
      (instantiateThreeWords ctx repeated middle)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareInterleave (left right : Word Nat) :
    Derives basis
      ((left ++ left) ++ (right ++ right))
      ((left ++ right) ++ (left ++ right)) := by
  have substituted :=
    Derives.subst basisSquareInterleave
      (instantiateThreeWords left right right)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareFinalSwitch (left right : Word Nat) :
    Derives basis
      ((left ++ left) ++ (right ++ right))
      (((left ++ right) ++ right) ++ left) := by
  have substituted :=
    Derives.subst basisSquareFinalSwitch
      (instantiateThreeWords left right right)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The displayed interleave, gather, and final-switch laws derive the square
block commutation required by the common period-two normalizer. -/
theorem derivesPrefixedSquareCommutation
    (ctx left right : Word Nat) :
    Derives basis
      (ctx ++ ((left ++ left) ++ (right ++ right)))
      (ctx ++ ((right ++ right) ++ (left ++ left))) := by
  have interleave :=
    Derives.prepend ctx (derivesSquareInterleave left right)
  have gatherCore :=
    derivesPrefixedGather ctx left right
  have gathered :
      Derives basis
        (ctx ++ ((left ++ right) ++ (left ++ right)))
        (ctx ++ (((right ++ left) ++ left) ++ right)) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight gatherCore right
  have switched :=
    Derives.prepend ctx (derivesSquareFinalSwitch right left)
  exact interleave.trans <|
    gathered.trans <| by
      simpa only [Word.append_assoc] using switched.symm

/-! ## Common `S4_71` plus parity theory -/

private def row7
    (c0 c1 c2 c3 c4 c5 c6 column : Fin 7) : Fin 7 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else
            if column = 5 then c5 else c6

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
      SemigroupBasis.Generated.S4_71.table.semigroup where
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
    SplitSurjection commonBridgeTable.semigroup cyclicTwo.semigroup where
  toFun := commonBridgeCyclicMap
  map_mul := by decide
  preimage := commonBridgeCyclicSection
  right_inverse := by decide

private def commonBridgePair :
    SubdirectPair commonBridgeTable.semigroup
      SemigroupBasis.Generated.S4_71.table.semigroup cyclicTwo.semigroup where
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
      SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup where
  toFun := commonBridgeQuotientMap
  map_mul := by decide
  preimage := commonBridgeQuotientSection
  right_inverse := by decide

private theorem commonDerivesOfFactorValid
    (identity : Identity Nat)
    (blockValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_71.table.semigroup)
    (cyclicValid : identity.SatisfiedBy cyclicTwo.semigroup) :
    Derives S5_443Family.basis identity.lhs identity.rhs := by
  have bridgeValid :
      identity.SatisfiedBy commonBridgeTable.semigroup :=
    (commonBridgePair.satisfiedBy_iff identity).2
      ⟨blockValid, cyclicValid⟩
  have quotientValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup :=
    commonBridgeQuotient.pushforwardIdentity identity bridgeValid
  exact S5_443Family.S5_614.basis_complete.2 identity quotientValid

private theorem bindAppend
    (left right : Word Nat) (substitution : Nat -> Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bindBind
    (word : Word Nat) (first second : Nat -> Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bindSingleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay the complete common block/parity basis behind a protected prefix. -/
theorem liftCommonUnderPrefix
    {left right : Word Nat}
    (derivation : Derives S5_443Family.basis left right)
    (ctx : Word Nat) (substitution : Nat -> Word Nat) :
    Derives basis
      (ctx ++ left.bind substitution)
      (ctx ++ right.bind substitution) := by
  induction derivation generalizing ctx substitution with
  | fromBasis member =>
      simp only [S5_443Family.basis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · change Derives basis
          (ctx ++ (substitution 0 ++ substitution 0))
          (ctx ++ (((substitution 0 ++ substitution 0) ++
            substitution 0) ++ substitution 0))
        exact Derives.prepend ctx
          (derivesPowerExpansion (substitution 0))
      · change Derives basis
          (ctx ++ ((substitution 0 ++ substitution 1) ++
            substitution 0))
          (ctx ++ ((substitution 1 ++ substitution 0) ++
            substitution 0))
        simpa only [Word.append_assoc] using
          derivesPrefixedGather ctx (substitution 0) (substitution 1)
      · change Derives basis
          (ctx ++ (((substitution 0 ++ substitution 0) ++
            substitution 1) ++ substitution 1))
          (ctx ++ (((substitution 1 ++ substitution 1) ++
            substitution 0) ++ substitution 0))
        simpa only [Word.append_assoc] using
          derivesPrefixedSquareCommutation
            ctx (substitution 0) (substitution 1)
  | refl =>
      exact Derives.refl _
  | symm _ inductionHypothesis =>
      exact (inductionHypothesis ctx substitution).symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact
        (firstHypothesis ctx substitution).trans
          (secondHypothesis ctx substitution)
  | prepend pre _ inductionHypothesis =>
      simpa [bindAppend, Word.append_assoc] using
        inductionHypothesis
          (ctx ++ pre.bind substitution) substitution
  | appendRight _ post inductionHypothesis =>
      simpa [bindAppend, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis ctx substitution)
          (post.bind substitution)
  | subst _ first inductionHypothesis =>
      simpa [bindBind] using
        inductionHypothesis ctx
          (fun letter => (first letter).bind substitution)

/-! ## Joint invariant -/

abbrev SameOccurrenceParity :=
  SemigroupBasis.CoRoots.S5_442Invariant.SameOccurrenceParity

/-- The common block theory, common first variable, and coordinatewise
occurrence parity are the exact data consumed by the shared normalizer. -/
structure SameJointSignature (left right : Word Nat) : Prop where
  blockTheory :
    (Identity.mk left right).SatisfiedBy
      SemigroupBasis.Generated.S4_71.table.semigroup
  head : left.head = right.head
  parity : SameOccurrenceParity left right

namespace SameJointSignature

theorem capped {left right : Word Nat}
    (same : SameJointSignature left right) (letter : Nat) :
    S5_107.cappedMultiplicity left letter =
      S5_107.cappedMultiplicity right letter :=
  S5_793Invariant.s4_71Valid_cappedMultiplicity
    (Identity.mk left right) same.blockTheory letter

theorem absent {left right : Word Nat}
    (same : SameJointSignature left right) (letter : Nat) :
    letter ∉ left.toList ↔ letter ∉ right.toList := by
  rw [← List.count_eq_zero, ← List.count_eq_zero,
    ← S5_107.cappedMultiplicity_eq_zero_iff,
    ← S5_107.cappedMultiplicity_eq_zero_iff,
    same.capped letter]

theorem support {left right : Word Nat}
    (same : SameJointSignature left right) (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  simpa using not_congr (same.absent letter)

theorem simple {left right : Word Nat}
    (same : SameJointSignature left right) (letter : Nat) :
    S5_107.SimpleIn left letter ↔ S5_107.SimpleIn right letter := by
  unfold S5_107.SimpleIn
  rw [← S5_107.cappedMultiplicity_eq_one_iff,
    ← S5_107.cappedMultiplicity_eq_one_iff, same.capped letter]

end SameJointSignature

private theorem cyclicSatisfiedByOfParity
    (left right : Word Nat)
    (parity : SameOccurrenceParity left right) :
    (Identity.mk left right).SatisfiedBy cyclicTwo.semigroup :=
  S5_442Invariant.cyclicTwo_equalEval_of_sameOccurrenceParity
    left right parity

/-! ## Necessity from the three lower-order factor pairs -/

theorem sameJointSignatureOfS2_2S5_801Valid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_801.table.semigroup) :
    SameJointSignature identity.lhs identity.rhs := by
  have cyclicValid' :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    rw [← SemigroupBasis.Generated.S2_2.table_eq_catalogue_model]
    exact cyclicValid
  have s5Signature :=
    S5_793FamilyInvariant.S5_801.valid_sameSignature identity s5Valid
  exact
    ⟨s5Signature.blockTheory, s5Signature.first,
      S5_442Invariant.sameOccurrenceParity_of_cyclicTwo_equalEval
        identity.lhs identity.rhs cyclicValid'⟩

theorem sameJointSignatureOfS3_11S5_843Valid
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_11.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_843.table.semigroup) :
    SameJointSignature identity.lhs identity.rhs := by
  have cyclicValid :
      identity.SatisfiedBy cyclicTwo.semigroup :=
    SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening.cyclicEmbeddingS3_11.pullback_identity
      identity s3Valid
  have s5Signature :=
    S5_793FamilyInvariant.S5_843.valid_sameSignature identity s5Valid
  exact
    ⟨s5Signature.blockTheory, s5Signature.first,
      S5_442Invariant.sameOccurrenceParity_of_cyclicTwo_equalEval
        identity.lhs identity.rhs cyclicValid⟩

private def toFinTwo : Nat -> Fin 2
  | 0 => 0
  | _ => 1

private def finiteCommonBasis : List (Identity (Fin 2)) :=
  S5_443Family.basis.map fun identity => identity.map toFinTwo

private theorem commonBasisRoundTripChecked :
    S5_443Family.basis.all (fun identity =>
      decide ((identity.map toFinTwo).map Fin.val = identity)) = true := by
  decide

private theorem commonModelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteCommonBasis.all table.checkIdentity = true) :
    Models table.semigroup S5_443Family.basis := by
  intro identity member
  have finiteMember : identity.map toFinTwo ∈ finiteCommonBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinTwo).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp commonBasisRoundTripChecked) identity member
  rw [restored] at finiteValid
  exact finiteValid

private theorem commonModelsS4_71 :
    Models SemigroupBasis.Generated.S4_71.table.semigroup
      S5_443Family.basis :=
  commonModelsOfFiniteChecks
    SemigroupBasis.Generated.S4_71.table (by decide)

private theorem commonModelsCyclicTwo :
    Models cyclicTwo.semigroup S5_443Family.basis :=
  commonModelsOfFiniteChecks cyclicTwo (by decide)

theorem sameJointSignatureOfS2_4S5_614Valid
    (identity : Identity Nat)
    (leftZeroValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup) :
    SameJointSignature identity.lhs identity.rhs := by
  have commonDerivation :
      Derives S5_443Family.basis identity.lhs identity.rhs :=
    S5_443Family.S5_614.basis_complete.2 identity s5Valid
  have blockValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_71.table.semigroup :=
    fun valuation => commonDerivation.sound commonModelsS4_71 valuation
  have cyclicValid : identity.SatisfiedBy cyclicTwo.semigroup :=
    fun valuation => commonDerivation.sound commonModelsCyclicTwo valuation
  have leftZeroValid' : identity.SatisfiedBy leftZeroTwo.semigroup := by
    rw [← SemigroupBasis.Generated.S2_4.table_eq_catalogue_model]
    exact leftZeroValid
  exact
    ⟨blockValid,
      S5_793Invariant.leftZeroValid_head_eq identity leftZeroValid',
      S5_442Invariant.sameOccurrenceParity_of_cyclicTwo_equalEval
        identity.lhs identity.rhs cyclicValid⟩

/-! ## Unrestricted derivational sufficiency -/

private theorem foldlEvalCongr
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat -> S) :
    ∀ (letters : List Nat) (initial : S),
      (∀ letter, letter ∈ letters ->
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
      ∀ letter, letter ∈ word.toList ->
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
    (leftIdentity : ∀ value, semigroup.mul one value = value)
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
    SemigroupBasis.Generated.S4_71.table.semigroup.mul (3 : Fin 4) value =
      value := by
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

private theorem headCountOneIff
    {left right : Word Nat}
    (same : SameJointSignature left right) :
    left.toList.count left.head = 1 ↔
      right.toList.count right.head = 1 := by
  have simpleIff := same.simple left.head
  simpa [S5_107.SimpleIn, same.head] using simpleIff

private theorem tailNilOfSameSignature
    {left right : Word Nat}
    (same : SameJointSignature left right)
    (rightHeadSimple : right.toList.count right.head = 1)
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
    rcases headOrTail with equality | inTail
    · exact equality
    · simp [leftTailEmpty] at inTail
  have letterIsRightHead : letter = right.head :=
    letterIsLeftHead.trans same.head
  have rightHeadInTail : right.head ∈ right.tail := by
    simpa [letterIsRightHead] using member
  exact
    (headNotMemTailOfCountOne right rightHeadSimple) rightHeadInTail

private theorem tailNilIffOfSameSignature
    {left right : Word Nat}
    (same : SameJointSignature left right)
    (leftHeadSimple : left.toList.count left.head = 1)
    (rightHeadSimple : right.toList.count right.head = 1) :
    left.tail = [] ↔ right.tail = [] := by
  constructor
  · exact tailNilOfSameSignature same rightHeadSimple
  · exact tailNilOfSameSignature
      ⟨fun valuation => (same.blockTheory valuation).symm,
        same.head.symm,
        fun letter => (same.parity letter).symm⟩
      leftHeadSimple

private abbrev ListDerives := S5_107.ListDerives basis

private theorem listDerivesAddInitialPair
    (head : Nat) (tail : List Nat)
    (headInTail : head ∈ tail) :
    ListDerives
      (head :: tail) ([head, head] ++ head :: tail) := by
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
      let middle := S5_107.listWordOfCons middleHead middleTail
      have expanded :=
        S5_107.ListDerives.ofWord
          (derivesTripleLeftContraction
            (Word.singleton head) middle).symm
      simpa [middle, S5_107.listWordOfCons,
        Word.toList_append, List.append_assoc] using
        expanded.append after

theorem derivesAddInitialPair
    (word : Word Nat) (headInTail : word.head ∈ word.tail) :
    Derives basis word
      ((Word.singleton word.head ++ Word.singleton word.head) ++ word) := by
  cases word with
  | mk head tail =>
      have listDerivation :=
        listDerivesAddInitialPair head tail headInTail
      simpa [S5_107.listWordOfCons, Word.singleton,
        Word.append, List.append_assoc] using
        S5_107.ListDerives.toWord listDerivation

/-- The common block/head/parity signature is sufficient for the displayed
ten-law system. This is the shared proof used by all three factor pairs. -/
theorem derivesOfSameJointSignature
    {left right : Word Nat}
    (same : SameJointSignature left right) :
    Derives basis left right := by
  have wholeCyclic :
      (Identity.mk left right).SatisfiedBy cyclicTwo.semigroup :=
    cyclicSatisfiedByOfParity left right same.parity
  have countIff := headCountOneIff same
  by_cases leftHeadSimple : left.toList.count left.head = 1
  · have rightHeadSimple : right.toList.count right.head = 1 :=
      countIff.mp leftHeadSimple
    have tailsEmpty :=
      tailNilIffOfSameSignature
        same leftHeadSimple rightHeadSimple
    cases left with
    | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
        have headsEqual : leftHead = rightHead := same.head
        subst rightHead
        cases leftTail with
        | nil =>
          have rightEmpty : rightTail = [] := tailsEmpty.mp rfl
          subst rightTail
          exact Derives.refl _
        | cons leftSecond leftRest =>
          cases rightTail with
          | nil =>
            have impossible : leftSecond :: leftRest = [] :=
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
                    SemigroupBasis.Generated.S4_71.table.semigroup := by
              simpa [leftSuffix, rightSuffix, Word.singleton,
                Word.append] using same.blockTheory
            have wholeCyclic' :
                (Identity.mk
                  (Word.singleton leftHead ++ leftSuffix)
                  (Word.singleton leftHead ++ rightSuffix)).SatisfiedBy
                    cyclicTwo.semigroup := by
              simpa [leftSuffix, rightSuffix, Word.singleton,
                Word.append] using wholeCyclic
            have suffixBlock :=
              suffixValidOfSimplePrefix
                SemigroupBasis.Generated.S4_71.table.semigroup (3 : Fin 4)
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
            rw [bindSingleton, bindSingleton] at lifted
            simpa [leftSuffix, rightSuffix, Word.singleton,
              Word.append] using lifted
  · have rightHeadNotSimple :
        right.toList.count right.head ≠ 1 := by
      intro rightSimple
      exact leftHeadSimple (countIff.mpr rightSimple)
    have leftHeadInTail : left.head ∈ left.tail :=
      headMemTailOfCountNeOne left leftHeadSimple
    have rightHeadInTail : right.head ∈ right.tail :=
      headMemTailOfCountNeOne right rightHeadNotSimple
    have leftExpanded := derivesAddInitialPair left leftHeadInTail
    have rightExpanded := derivesAddInitialPair right rightHeadInTail
    have commonDerivation :=
      commonDerivesOfFactorValid
        (Identity.mk left right) same.blockTheory wholeCyclic
    let guardPrefix :=
      Word.singleton left.head ++ Word.singleton left.head
    have lifted :=
      liftCommonUnderPrefix commonDerivation guardPrefix Word.singleton
    rw [bindSingleton, bindSingleton] at lifted
    have guarded :
        Derives basis
          (guardPrefix ++ left) (guardPrefix ++ right) := by
      simpa [guardPrefix, same.head] using lifted
    have rightContracted :
        Derives basis (guardPrefix ++ right) right := by
      simpa [guardPrefix, same.head] using rightExpanded.symm
    exact leftExpanded.trans <| guarded.trans rightContracted

/-! ## Three unconditional factor-intersection APIs -/

theorem derivesOfS2_2S5_801Valid
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_801.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameJointSignature <|
    sameJointSignatureOfS2_2S5_801Valid identity leftValid rightValid

def intersectionBasisS2_2S5_801 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_801.table.semigroup
      basis where
  leftModels := modelsS2_2
  rightModels := modelsS5_801
  complete := derivesOfS2_2S5_801Valid

theorem derivesOfS2_4S5_614Valid
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameJointSignature <|
    sameJointSignatureOfS2_4S5_614Valid identity leftValid rightValid

def intersectionBasisS2_4S5_614 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup
      basis where
  leftModels := modelsS2_4
  rightModels := modelsS5_614
  complete := derivesOfS2_4S5_614Valid

theorem derivesOfS3_11S5_843Valid
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_11.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_843.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameJointSignature <|
    sameJointSignatureOfS3_11S5_843Valid identity leftValid rightValid

def intersectionBasisS3_11S5_843 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_843.table.semigroup
      basis where
  leftModels := modelsS3_11
  rightModels := modelsS5_843
  complete := derivesOfS3_11S5_843Valid

end SemigroupBasis.CoRoots.Order6OneLocalFordLastSigmaCdd7
