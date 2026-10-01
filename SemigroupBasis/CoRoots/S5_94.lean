import SemigroupBasis.CoRoots.S5_344Family
import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.Examples.SimpleEndpointsFour
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_94

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := SemigroupBasis.CoRoots.S5_344.xx
def xxx : Word Nat := SemigroupBasis.CoRoots.S5_344.xxx
def xyx : Word Nat := SemigroupBasis.CoRoots.S5_344.xyx
def xxyx : Word Nat := SemigroupBasis.CoRoots.S5_344.xxyx
def xyxx : Word Nat := SemigroupBasis.CoRoots.S5_344.xyxx
def xxyy : Word Nat := SemigroupBasis.CoRoots.S5_344.xxyy
def xyxy : Word Nat := SemigroupBasis.CoRoots.S5_344.xyxy
def xyyx : Word Nat := SemigroupBasis.CoRoots.S5_344.xyyx
def yxxy : Word Nat := w 1 [0, 0, 1]
def xxyz : Word Nat := SemigroupBasis.CoRoots.S5_344.xxyz
def xyxz : Word Nat := SemigroupBasis.CoRoots.S5_344.xyxz
def xyzx : Word Nat := SemigroupBasis.CoRoots.S5_344.xyzx
def xzyx : Word Nat := SemigroupBasis.CoRoots.S5_344.xzyx
def xyzy : Word Nat := SemigroupBasis.CoRoots.S5_344.xyzy
def xzyy : Word Nat := SemigroupBasis.CoRoots.S5_344.xzyy
def xyzt : Word Nat := SemigroupBasis.CoRoots.S5_344.xyzt
def xzyt : Word Nat := SemigroupBasis.CoRoots.S5_344.xzyt

def powerLaw : Identity Nat := SemigroupBasis.CoRoots.S5_344.powerLaw
def leftEndpointDuplicationLaw : Identity Nat :=
  SemigroupBasis.CoRoots.S5_344.leftEndpointDuplicationLaw
def rightEndpointDuplicationLaw : Identity Nat :=
  SemigroupBasis.CoRoots.S5_344.rightEndpointDuplicationLaw
def squareInterleaveLaw : Identity Nat :=
  SemigroupBasis.CoRoots.S5_344.squareInterleaveLaw
def squareFinalSwitchLaw : Identity Nat :=
  SemigroupBasis.CoRoots.S5_344.squareFinalSwitchLaw
def squareInitialSwitchLaw : Identity Nat := ⟨xxyy, yxxy⟩
def doubledInitialMoveLaw : Identity Nat :=
  SemigroupBasis.CoRoots.S5_344.doubledInitialMoveLaw
def closedInteriorSwapLaw : Identity Nat :=
  SemigroupBasis.CoRoots.S5_344.closedInteriorSwapLaw
def repeatedFinalSwapLaw : Identity Nat :=
  SemigroupBasis.CoRoots.S5_344.repeatedFinalSwapLaw
def interiorSwapLaw : Identity Nat :=
  SemigroupBasis.CoRoots.S5_344.interiorSwapLaw

/-- The common exact ten-identity basis of
`S5_94`, `S5_95`, and `S5_104`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftEndpointDuplicationLaw, rightEndpointDuplicationLaw,
    squareInterleaveLaw, squareFinalSwitchLaw, squareInitialSwitchLaw,
    doubledInitialMoveLaw, closedInteriorSwapLaw, repeatedFinalSwapLaw,
    interiorSwapLaw]

private theorem oldBasisMember
    (e : Identity Nat)
    (member : e ∈ SemigroupBasis.CoRoots.S5_344.basis) :
    e ∈ basis := by
  simp only [SemigroupBasis.CoRoots.S5_344.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [basis, powerLaw, leftEndpointDuplicationLaw,
    rightEndpointDuplicationLaw, squareInterleaveLaw,
    squareFinalSwitchLaw, doubledInitialMoveLaw, closedInteriorSwapLaw,
    repeatedFinalSwapLaw, interiorSwapLaw]

private theorem transportOldDerivation {u v : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_344.basis u v) :
    Derives basis u v :=
  derivation.transport fun e member =>
    Derives.fromBasis (oldBasisMember e member)

private theorem firstCappedDerivesOfHeadEqTailPerm
    (u v : Word Nat) (heads : u.head = v.head)
    (tails : u.tail.Perm v.tail) :
    Derives firstCappedMultiplicityFourBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          simp only at heads tails
          subst vHead
          exact firstCappedDerivesTailPermutation uHead tails

private theorem firstCappedValid_of_head_capped
    (e : Identity Nat)
    (heads : e.lhs.head = e.rhs.head)
    (cappedCounts :
      ∀ z, min (e.lhs.toList.count z) 2 =
        min (e.rhs.toList.count z) 2) :
    e.SatisfiedBy firstCappedMultiplicityFour.semigroup := by
  have lhsNormal := firstCappedDerivesNormal e.lhs
  have rhsNormal := firstCappedDerivesNormal e.rhs
  have tailPerm :
      (firstCappedNormal e.lhs).tail.Perm
        (firstCappedNormal e.rhs).tail := by
    rw [List.perm_iff_count]
    intro z
    have wholeCount :
        (firstCappedNormal e.lhs).toList.count z =
          (firstCappedNormal e.rhs).toList.count z := by
      rw [firstCappedNormal_count, firstCappedNormal_count,
        cappedCounts z]
    by_cases hz : z = e.lhs.head
    · subst z
      simpa [Word.toList, firstCappedNormal, heads] using wholeCount
    · have hzRight : z ≠ e.rhs.head := by
        simpa [heads] using hz
      simpa [Word.toList, firstCappedNormal, Ne.symm hz,
        Ne.symm hzRight] using wholeCount
  have middle :
      Derives firstCappedMultiplicityFourBasis
        (firstCappedNormal e.lhs) (firstCappedNormal e.rhs) := by
    apply firstCappedDerivesOfHeadEqTailPerm
    · simpa [firstCappedNormal] using heads
    · exact tailPerm
  have derivation :=
    Derives.trans lhsNormal <|
      Derives.trans middle (Derives.symm rhsNormal)
  intro valuation
  exact derivation.sound
    firstCappedMultiplicityFourBasis_models valuation

private def simpleEndpointsFinalMarkerQuotient :
    SplitSurjection simpleEndpointsFour.semigroup
      finalMarkerThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else ⟨3, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

private def s5_344FinalMarkerHom :
    Hom SemigroupBasis.Generated.Catalogue.S5_344.table.semigroup
      finalMarkerThree.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide

private def s5_344FirstCappedHom :
    Hom SemigroupBasis.Generated.Catalogue.S5_344.table.semigroup
      firstCappedMultiplicityFour.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨0, by decide⟩ else
        if a.val = 2 then ⟨1, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide

private theorem s5_344Factors_injective :
    Function.Injective fun a =>
      (s5_344FinalMarkerHom.toFun a,
        s5_344FirstCappedHom.toFun a) := by
  intro a b
  revert a b
  decide

private theorem valid_s5_344_of_factors
    (e : Identity Nat)
    (firstValid :
      e.SatisfiedBy firstCappedMultiplicityFour.semigroup)
    (finalValid : e.SatisfiedBy finalMarkerThree.semigroup) :
    e.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_344.table.semigroup := by
  intro valuation
  apply s5_344Factors_injective
  apply Prod.ext
  · change
      s5_344FinalMarkerHom.toFun
          (SemigroupBasis.Generated.Catalogue.S5_344.table.semigroup.eval
            valuation e.lhs) =
        s5_344FinalMarkerHom.toFun
          (SemigroupBasis.Generated.Catalogue.S5_344.table.semigroup.eval
            valuation e.rhs)
    rw [s5_344FinalMarkerHom.map_eval,
      s5_344FinalMarkerHom.map_eval]
    exact finalValid fun x =>
      s5_344FinalMarkerHom.toFun (valuation x)
  · change
      s5_344FirstCappedHom.toFun
          (SemigroupBasis.Generated.Catalogue.S5_344.table.semigroup.eval
            valuation e.lhs) =
        s5_344FirstCappedHom.toFun
          (SemigroupBasis.Generated.Catalogue.S5_344.table.semigroup.eval
            valuation e.rhs)
    rw [s5_344FirstCappedHom.map_eval,
      s5_344FirstCappedHom.map_eval]
    exact firstValid fun x =>
      s5_344FirstCappedHom.toFun (valuation x)

private theorem finalMarkerDerivesPrefixPermutation
    {prefix₁ prefix₂ : List Nat} (permutation : prefix₁.Perm prefix₂)
    (final : Nat) :
    Derives finalMarkerThreeBasis
      (wordOfPrefixFinal prefix₁ final)
      (wordOfPrefixFinal prefix₂ final) := by
  induction permutation with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa using Derives.prepend (Word.singleton x) ih
  | swap x y xs =>
      simpa [Word.append_assoc] using
        finalMarkerDerivesPrefixSwap
          (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs final)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans ih₁ ih₂

private theorem finalMarkerDerivesAddExistingPrefix
    (x : Nat) (letters : List Nat) (final : Nat)
    (member : x ∈ letters) :
    Derives finalMarkerThreeBasis
      (wordOfPrefixFinal letters final)
      (wordOfPrefixFinal (x :: letters) final) := by
  have arrange : letters.Perm (x :: letters.erase x) :=
    List.perm_cons_erase member
  have duplicate :=
    finalMarkerDerivesPrefixDuplication
      (Word.singleton x) (wordOfPrefixFinal (letters.erase x) final)
  have restore :
      (x :: x :: letters.erase x).Perm (x :: letters) :=
    (List.Perm.cons x arrange).symm
  exact Derives.trans
    (finalMarkerDerivesPrefixPermutation arrange final) <|
    Derives.trans
      (by simpa [wordOfPrefixFinal, Word.append_assoc] using duplicate)
      (finalMarkerDerivesPrefixPermutation restore final)

private theorem repeatedInitial_count_two
    (initial : Nat) (middle : List Nat) (final : Nat)
    (repeated : initial ∈ middle ∨ final = initial) :
    2 ≤ (wordOfEndpoints initial middle final).toList.count initial := by
  rw [toList_wordOfEndpoints]
  rcases repeated with middleMem | finalEq
  · have positive : 0 < middle.count initial :=
      List.count_pos_iff.mpr middleMem
    simp only [List.count_cons_self, List.count_append,
      List.count_singleton]
    omega
  · subst final
    simp

private theorem multiple_has_prefix_occurrence
    (initial : Nat) (middle : List Nat) (final tested : Nat)
    (multiple :
      2 ≤ (wordOfEndpoints initial middle final).toList.count tested) :
    tested ∈ initial :: middle := by
  rw [toList_wordOfEndpoints, List.count_append] at multiple
  have finalCountBound : [final].count tested ≤ 1 := by
    by_cases finalEq : final = tested <;> simp [finalEq]
  have prefixPositive : 0 < (initial :: middle).count tested := by
    omega
  exact List.count_pos_iff.mp prefixPositive

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- Replace a repeated initial endpoint by another variable occurring at
least twice. The old nine-law basis first inserts a saturated prefix; the new
law then changes the initial endpoint. -/
theorem derivesInitialSwitch
    (old new : Nat) (middle : List Nat) (final : Nat)
    (different : old ≠ new)
    (oldRepeated : old ∈ middle ∨ final = old)
    (newMultiple :
      2 ≤ (wordOfEndpoints old middle final).toList.count new) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints old middle final)
        (wordOfEndpoints new switchedMiddle final) := by
  let source := wordOfEndpoints old middle final
  let arranged := wordOfEndpoints old (old :: new :: new :: middle) final
  have oldMultiple :
      2 ≤ source.toList.count old := by
    simpa [source] using
      repeatedInitial_count_two old middle final oldRepeated
  have sourceList :
      source.toList = old :: middle ++ [final] := by
    simp [source]
  have arrangedList :
      arranged.toList =
        old :: old :: new :: new :: middle ++ [final] := by
    change
      (wordOfEndpoints old (old :: new :: new :: middle) final).toList =
        old :: old :: new :: new :: middle ++ [final]
    rw [toList_wordOfEndpoints]
  have oldMultipleList :
      2 ≤ (old :: middle ++ [final]).count old := by
    rw [← sourceList]
    exact oldMultiple
  have newMultipleList :
      2 ≤ (old :: middle ++ [final]).count new := by
    simpa using newMultiple
  have cappedCounts :
      ∀ z, min (source.toList.count z) 2 =
        min (arranged.toList.count z) 2 := by
    intro z
    rw [sourceList, arrangedList]
    by_cases hzOld : z = old
    · subst z
      simp [Ne.symm different] at oldMultipleList ⊢
      omega
    · by_cases hzNew : z = new
      · subst z
        simp [different] at newMultipleList ⊢
        omega
      · simp only [List.count_cons_of_ne (Ne.symm hzOld),
          List.count_cons_of_ne (Ne.symm hzNew), List.count_append]
  have firstValid :
      (Identity.mk source arranged).SatisfiedBy
        firstCappedMultiplicityFour.semigroup :=
    firstCappedValid_of_head_capped
      (Identity.mk source arranged) (by rfl) cappedCounts
  have newPrefixMem : new ∈ old :: middle :=
    multiple_has_prefix_occurrence old middle final new newMultiple
  have addOld :=
    finalMarkerDerivesAddExistingPrefix
      old (old :: middle) final (by simp)
  have addNew₁ :=
    finalMarkerDerivesAddExistingPrefix
      new (old :: old :: middle) final (by simp [newPrefixMem])
  have addNew₂ :=
    finalMarkerDerivesAddExistingPrefix
      new (new :: old :: old :: middle) final (by simp)
  have reorder :
      (new :: new :: old :: old :: middle).Perm
        (old :: old :: new :: new :: middle) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_cons]
    omega
  have finalDerivation :
      Derives finalMarkerThreeBasis
        (wordOfPrefixFinal (old :: middle) final)
        (wordOfPrefixFinal
          (old :: old :: new :: new :: middle) final) :=
    Derives.trans addOld <|
      Derives.trans addNew₁ <|
        Derives.trans addNew₂ <|
          finalMarkerDerivesPrefixPermutation reorder final
  have finalValid :
      (Identity.mk source arranged).SatisfiedBy
        finalMarkerThree.semigroup := by
    intro valuation
    have sound :=
      finalDerivation.sound finalMarkerThreeBasis_models valuation
    simpa [source, arranged, wordOfEndpoints_eq] using sound
  have oldValid :=
    valid_s5_344_of_factors
      (Identity.mk source arranged) firstValid finalValid
  have oldDerivation :=
    SemigroupBasis.CoRoots.S5_344Family.S5_344.basis_complete.2
      (Identity.mk source arranged) oldValid
  have arrangedDerivation :
      Derives basis source arranged :=
    transportOldDerivation oldDerivation
  have switchBase :
      Derives basis xxyy yxxy :=
    Derives.fromBasis (e := squareInitialSwitchLaw) <| by
      simp [basis, squareInitialSwitchLaw]
  have switchSubstituted :=
    Derives.subst switchBase
      (instantiateTwoWords
        (Word.singleton old) (Word.singleton new))
  have switchContextual :=
    Derives.appendRight switchSubstituted
      (wordOfPrefixFinal middle final)
  refine ⟨old :: old :: new :: middle, ?_⟩
  exact Derives.trans arrangedDerivation <| by
    simpa [source, arranged, squareInitialSwitchLaw, xxyy, yxxy, w,
      instantiateTwoWords, Word.bind, Word.append, Word.singleton,
      wordOfEndpoints_eq, Word.append_assoc] using switchContextual

private def initialSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 3

private theorem simpleInitial_iff_of_valid
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          simpleEndpointsFour.semigroup) :
    ∀ z,
      (initial₁ = z ∧ z ∉ middle₁ ∧ final₁ ≠ z) ↔
        (initial₂ = z ∧ z ∉ middle₂ ∧ final₂ ≠ z) := by
  intro z
  have evaluated := valid (initialSeparator z)
  constructor
  · intro simple₁
    have lhsTwo :
        simpleEndpointsFour.semigroup.eval (initialSeparator z)
          (wordOfEndpoints initial₁ middle₁ final₁) = (2 : Fin 4) := by
      simpa [initialSeparator] using
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          z initial₁ middle₁ final₁).2 simple₁
    have rhsTwo := evaluated.symm.trans lhsTwo
    exact
      (simpleEndpointsEval_initialSeparator_eq_two_iff
        z initial₂ middle₂ final₂).1 <| by
          simpa [initialSeparator] using rhsTwo
  · intro simple₂
    have rhsTwo :
        simpleEndpointsFour.semigroup.eval (initialSeparator z)
          (wordOfEndpoints initial₂ middle₂ final₂) = (2 : Fin 4) := by
      simpa [initialSeparator] using
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          z initial₂ middle₂ final₂).2 simple₂
    have lhsTwo := evaluated.trans rhsTwo
    exact
      (simpleEndpointsEval_initialSeparator_eq_two_iff
        z initial₁ middle₁ final₁).1 <| by
          simpa [initialSeparator] using lhsTwo

/-- Generic unrestricted completeness theorem. A finite table has this basis
once it models the ten laws and every identity descends to the simple-endpoint
factor and pulls back to the commutative exponent-three factor. -/
theorem basis_complete_of_factors
    (T : FiniteTable)
    (models : Models T.semigroup basis)
    (toSimpleEndpoints :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.SatisfiedBy simpleEndpointsFour.semigroup)
    (toExponentThree :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.SatisfiedBy commutativeExponentThree.semigroup) :
    BasisFor T.semigroup basis := by
  refine ⟨models, ?_⟩
  intro e valid
  have deriveSameHead :
      ∀ (identity : Identity Nat),
        identity.SatisfiedBy T.semigroup →
        identity.lhs.head = identity.rhs.head →
        Derives basis identity.lhs identity.rhs := by
    intro identity identityValid heads
    have exponentValid := toExponentThree identity identityValid
    have cappedCounts :=
      exponentValid_capped_count_eq identity exponentValid
    have firstValid :=
      firstCappedValid_of_head_capped identity heads cappedCounts
    have simpleValid := toSimpleEndpoints identity identityValid
    have finalValid :=
      simpleEndpointsFinalMarkerQuotient.pushforwardIdentity
        identity simpleValid
    have oldValid :=
      valid_s5_344_of_factors identity firstValid finalValid
    exact transportOldDerivation <|
      SemigroupBasis.CoRoots.S5_344Family.S5_344.basis_complete.2
        identity oldValid
  have simpleValid := toSimpleEndpoints e valid
  have exponentValid := toExponentThree e valid
  have cappedCounts :=
    exponentValid_capped_count_eq e exponentValid
  rcases e with
    ⟨⟨lhsHead, lhsTail⟩, ⟨rhsHead, rhsTail⟩⟩
  cases lhsTail with
  | nil =>
      cases rhsTail with
      | nil =>
          have heads : lhsHead = rhsHead := by
            apply Decidable.byContradiction
            intro different
            have evaluated :=
              simpleValid
                (fun z =>
                  if z = lhsHead then (0 : Fin 4) else (3 : Fin 4))
            change
              (if lhsHead = lhsHead then (0 : Fin 4) else 3) =
                (if rhsHead = lhsHead then (0 : Fin 4) else (3 : Fin 4))
              at evaluated
            simp [Ne.symm different] at evaluated
          exact deriveSameHead
            (Identity.mk (Word.mk lhsHead []) (Word.mk rhsHead []))
            valid heads
      | cons rhsSecond rhsRest =>
          have evaluated := simpleValid (fun _ => (1 : Fin 4))
          have lhsOne :=
            (simpleEndpointsSingletonSeparator
              (Word.mk lhsHead [])).2 rfl
          have rhsOne := evaluated.symm.trans lhsOne
          have tailNil :=
            (simpleEndpointsSingletonSeparator
              (Word.mk rhsHead (rhsSecond :: rhsRest))).1 rhsOne
          simp at tailNil
  | cons lhsSecond lhsRest =>
      cases rhsTail with
      | nil =>
          have evaluated := simpleValid (fun _ => (1 : Fin 4))
          have rhsOne :=
            (simpleEndpointsSingletonSeparator
              (Word.mk rhsHead [])).2 rfl
          have lhsOne := evaluated.trans rhsOne
          have tailNil :=
            (simpleEndpointsSingletonSeparator
              (Word.mk lhsHead (lhsSecond :: lhsRest))).1 lhsOne
          simp at tailNil
      | cons rhsSecond rhsRest =>
          by_cases heads : lhsHead = rhsHead
          · exact deriveSameHead
              (Identity.mk
                (Word.mk lhsHead (lhsSecond :: lhsRest))
                (Word.mk rhsHead (rhsSecond :: rhsRest)))
              valid heads
          · let lhsSuffix : Word Nat :=
              Word.mk lhsSecond lhsRest
            let rhsSuffix : Word Nat :=
              Word.mk rhsSecond rhsRest
            let lhsSplit := splitPrefixFinal lhsSuffix
            let rhsSplit := splitPrefixFinal rhsSuffix
            have lhsReconstruct :
                wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2 =
                  Word.mk lhsHead (lhsSecond :: lhsRest) := by
              rw [wordOfEndpoints_eq]
              simp only [lhsSplit]
              rw [wordOfPrefixFinal_split lhsSuffix]
              rfl
            have rhsReconstruct :
                wordOfEndpoints rhsHead rhsSplit.1 rhsSplit.2 =
                  Word.mk rhsHead (rhsSecond :: rhsRest) := by
              rw [wordOfEndpoints_eq]
              simp only [rhsSplit]
              rw [wordOfPrefixFinal_split rhsSuffix]
              rfl
            have endpointSimpleValid :
                (Identity.mk
                  (wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2)
                  (wordOfEndpoints rhsHead rhsSplit.1 rhsSplit.2)).SatisfiedBy
                    simpleEndpointsFour.semigroup := by
              rw [lhsReconstruct, rhsReconstruct]
              exact simpleValid
            have simpleInitialIff :=
              simpleInitial_iff_of_valid
                lhsHead lhsSplit.1 lhsSplit.2
                rhsHead rhsSplit.1 rhsSplit.2
                endpointSimpleValid
            have lhsRepeated :
                lhsHead ∈ lhsSplit.1 ∨ lhsSplit.2 = lhsHead := by
              apply Decidable.byContradiction
              intro notRepeated
              have middleAbsent : lhsHead ∉ lhsSplit.1 :=
                fun member => notRepeated (Or.inl member)
              have finalNe : lhsSplit.2 ≠ lhsHead :=
                fun equal => notRepeated (Or.inr equal)
              have rhsSimple :=
                (simpleInitialIff lhsHead).mp
                  ⟨rfl, middleAbsent, finalNe⟩
              exact heads rhsSimple.1.symm
            have rhsRepeated :
                rhsHead ∈ rhsSplit.1 ∨ rhsSplit.2 = rhsHead := by
              apply Decidable.byContradiction
              intro notRepeated
              have middleAbsent : rhsHead ∉ rhsSplit.1 :=
                fun member => notRepeated (Or.inl member)
              have finalNe : rhsSplit.2 ≠ rhsHead :=
                fun equal => notRepeated (Or.inr equal)
              have lhsSimple :=
                (simpleInitialIff rhsHead).mpr
                  ⟨rfl, middleAbsent, finalNe⟩
              exact heads lhsSimple.1
            have rhsMultiple :
                2 ≤
                  (wordOfEndpoints rhsHead rhsSplit.1 rhsSplit.2).toList.count
                    rhsHead :=
              repeatedInitial_count_two
                rhsHead rhsSplit.1 rhsSplit.2 rhsRepeated
            have lhsNewMultiple :
                2 ≤
                  (wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2).toList.count
                    rhsHead := by
              have countEq :
                  min
                      ((wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2).toList.count
                        rhsHead) 2 =
                    min
                      ((wordOfEndpoints rhsHead rhsSplit.1 rhsSplit.2).toList.count
                        rhsHead) 2 := by
                have raw := cappedCounts rhsHead
                change
                  min
                      ((Word.mk lhsHead (lhsSecond :: lhsRest)).toList.count
                        rhsHead) 2 =
                    min
                      ((Word.mk rhsHead (rhsSecond :: rhsRest)).toList.count
                        rhsHead) 2 at raw
                rw [← lhsReconstruct, ← rhsReconstruct] at raw
                exact raw
              omega
            obtain ⟨switchedMiddle, switch⟩ :=
              derivesInitialSwitch
                lhsHead rhsHead lhsSplit.1 lhsSplit.2
                heads lhsRepeated lhsNewMultiple
            rw [lhsReconstruct] at switch
            let switched :=
              wordOfEndpoints rhsHead switchedMiddle lhsSplit.2
            have residualValid :
                (Identity.mk switched
                  (Word.mk rhsHead (rhsSecond :: rhsRest))).SatisfiedBy
                    T.semigroup := by
              intro valuation
              exact
                (switch.sound models valuation).symm.trans
                  (valid valuation)
            have residualHeads :
                switched.head =
                  (Word.mk rhsHead (rhsSecond :: rhsRest)).head := by
              rfl
            exact Derives.trans switch <|
              deriveSameHead
                (Identity.mk switched
                  (Word.mk rhsHead (rhsSecond :: rhsRest)))
                residualValid residualHeads

end SemigroupBasis.CoRoots.S5_94
