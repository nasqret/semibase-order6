import SemigroupBasis.CoRoots.S5_120
import SemigroupBasis.CoRoots.S5_342Family
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Subdirect

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S5353Normal

open SemigroupBasis
open SemigroupBasis.Examples

/-!
Unrestricted joint completeness for factor-pair family
`o6fp-6f3e00dd38cd5a31`, covering the representative roots
`S6_4058`, `S6_4162`, and `S6_4270`.

The `S5_353` factor fixes the first variable and preserves support and the
simple initial/final markers.  The `S2_2` factor adds coordinate parity.
The seventeen laws below normalize every interior multiplicity to one or two,
align a repeated final variable, and then permute the reduced interior.
-/

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
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyxz : Word Nat := w 0 [1, 0, 2]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
def xyxyy : Word Nat := w 0 [1, 0, 1, 1]
def xyyxy : Word Nat := w 0 [1, 1, 0, 1]
def xyyyx : Word Nat := w 0 [1, 1, 1, 0]
def xyz : Word Nat := w 0 [1, 2]
def xyyyz : Word Nat := w 0 [1, 1, 1, 2]
def xyyzy : Word Nat := w 0 [1, 1, 2, 1]
def xyzzz : Word Nat := w 0 [1, 2, 2, 2]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyy : Word Nat := w 0 [2, 1, 1]

def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def tripleLeftContractionLaw : Identity Nat := ⟨xxxyx, xyx⟩
def endpointTransferLaw : Identity Nat := ⟨xxyx, xyxx⟩
def splitEndpointContractionLaw : Identity Nat := ⟨xxyxx, xyx⟩
def squareInterleaveLaw : Identity Nat := ⟨xxyy, xyxy⟩
def squareFinalSwitchLaw : Identity Nat := ⟨xxyy, xyyx⟩
def mixedContractionLaw : Identity Nat := ⟨xxyyy, xyx⟩
def doubledInitialMoveLaw : Identity Nat := ⟨xxyz, xyxz⟩
def attachmentLaw : Identity Nat := ⟨xxyzy, xyyzx⟩
def rightTripleExpansionLaw : Identity Nat := ⟨xyx, xyxxx⟩
def trailingSquareExpansionLaw : Identity Nat := ⟨xyx, xyxyy⟩
def middleSquareExpansionLaw : Identity Nat := ⟨xyx, xyyxy⟩
def middleTripleExpansionLaw : Identity Nat := ⟨xyx, xyyyx⟩
def interiorPowerLaw : Identity Nat := ⟨xyyyz, xyz⟩
def finalPairTransferLaw : Identity Nat := ⟨xyyzy, xyzzz⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩
def repeatedFinalSwapLaw : Identity Nat := ⟨xyzy, xzyy⟩

/-- The exact seventeen-law candidate recorded for
`o6fp-6f3e00dd38cd5a31`. -/
def basis : List (Identity Nat) :=
  [powerLaw, tripleLeftContractionLaw, endpointTransferLaw,
    splitEndpointContractionLaw, squareInterleaveLaw,
    squareFinalSwitchLaw, mixedContractionLaw, doubledInitialMoveLaw,
    attachmentLaw, rightTripleExpansionLaw, trailingSquareExpansionLaw,
    middleSquareExpansionLaw, middleTripleExpansionLaw, interiorPowerLaw,
    finalPairTransferLaw, closedInteriorSwapLaw, repeatedFinalSwapLaw]

private def toFinThree : Nat → Fin 3
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
    Models SemigroupBasis.Generated.S2_2.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S2_2.table (by decide)

set_option maxHeartbeats 1000000 in
theorem modelsS5_353 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_353.table.semigroup basis :=
  modelsOfFiniteChecks
    SemigroupBasis.Generated.Catalogue.S5_353.table (by decide)

set_option maxHeartbeats 1000000 in
private theorem modelsSimpleEndpoints :
    Models simpleEndpointsFour.semigroup basis :=
  modelsOfFiniteChecks simpleEndpointsFour (by decide)

private def finiteS5_342Basis : List (Identity (Fin 3)) :=
  SemigroupBasis.CoRoots.S5_342.basis.map fun identity =>
    identity.map toFinThree

private theorem s5_342BasisRoundTripChecked :
    SemigroupBasis.CoRoots.S5_342.basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

set_option maxHeartbeats 1000000 in
private theorem modelsS5_342BasisSimpleEndpoints :
    Models simpleEndpointsFour.semigroup
      SemigroupBasis.CoRoots.S5_342.basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteS5_342Basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have checked :
      finiteS5_342Basis.all simpleEndpointsFour.checkIdentity = true := by
    decide
  have finiteValid :=
    simpleEndpointsFour.checkIdentityNat_sound
      (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinThree).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp s5_342BasisRoundTripChecked) identity member
  rw [restored] at finiteValid
  exact finiteValid

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem derivesBasisSubstitution
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat → Word Nat) :
    Derives basis
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis member) substitution

/-- Add two copies of a nonempty block strictly between nonempty contexts. -/
theorem derivesInteriorPower
    (leftContext block rightContext : Word Nat) :
    Derives basis
      ((leftContext ++ block) ++ rightContext)
      ((leftContext ++ ((block ++ block) ++ block)) ++ rightContext) := by
  have substituted :=
    derivesBasisSubstitution interiorPowerLaw (by simp [basis])
      (instantiateThreeWords leftContext block rightContext)
  simpa [interiorPowerLaw, xyyyz, xyz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted.symm

theorem derivesDoubledInitialMove (u v z : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ z) (((u ++ v) ++ u) ++ z) := by
  have substituted :=
    derivesBasisSubstitution doubledInitialMoveLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [doubledInitialMoveLaw, xxyz, xyxz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesEndpointTransfer (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ u) ((u ++ v) ++ (u ++ u)) := by
  have substituted :=
    derivesBasisSubstitution endpointTransferLaw (by simp [basis])
      (instantiateThreeWords u v v)
  simpa [endpointTransferLaw, xxyx, xyxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesRepeatedFinalSwap (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ v) (((u ++ z) ++ v) ++ v) := by
  have substituted :=
    derivesBasisSubstitution repeatedFinalSwapLaw (by simp [basis])
      (instantiateThreeWords u v z)
  simpa [repeatedFinalSwapLaw, xyzy, xzyy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Five candidate-law instances derive an arbitrary adjacent block swap
strictly between fixed nonempty prefix and suffix contexts. -/
theorem derivesOpenInteriorSwap
    (leftContext left right rightContext : Word Nat) :
    Derives basis
      (((leftContext ++ left) ++ right) ++ rightContext)
      (((leftContext ++ right) ++ left) ++ rightContext) := by
  have step₁ :=
    derivesInteriorPower leftContext left (right ++ rightContext)
  have step₂ :=
    Derives.prepend (leftContext ++ left)
      (derivesDoubledInitialMove left right rightContext)
  have step₃ :=
    Derives.appendRight
      (Derives.prepend leftContext (derivesEndpointTransfer left right))
      rightContext
  have step₄ :=
    Derives.appendRight
      (derivesRepeatedFinalSwap leftContext left right)
      (left ++ rightContext)
  have step₅ :=
    Derives.symm
      (derivesInteriorPower (leftContext ++ right) left rightContext)
  exact Derives.trans
    (by simpa [Word.append_assoc] using step₁) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step₂) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step₃) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step₄)
      (by simpa [Word.append_assoc] using step₅)

private theorem derivesMiddlePermutation
    (initial final : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis
      (wordOfEndpoints initial left final)
      (wordOfEndpoints initial right final) := by
  induction permutation generalizing initial with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa [wordOfEndpoints_eq, Word.append_assoc] using
        Derives.prepend (Word.singleton initial) (ih x)
  | swap x y xs =>
      simpa [wordOfEndpoints_eq, Word.append_assoc] using
        derivesOpenInteriorSwap
          (Word.singleton initial)
          (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs final)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ initial) (ih₂ initial)

private theorem derivesDeleteInteriorPair
    (initial final x : Nat) (before reduced : List Nat)
    (countEq : reduced.count x = 2) :
    Derives basis
      (wordOfEndpoints initial (before ++ x :: reduced) final)
      (wordOfEndpoints initial (before ++ reduced.erase x) final) := by
  let remainder := (reduced.erase x).erase x
  have firstErase : (reduced.erase x).count x = 1 := by
    rw [List.count_erase_self, countEq]
  have secondErase : remainder.count x = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, firstErase]
  have sourcePerm :
      (before ++ x :: reduced).Perm
        (x :: x :: x :: before ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases equal : z = x
    · subst z
      simp [countEq, secondErase]
    · simp [remainder, equal, Ne.symm equal]
  have eraseHasX : x ∈ reduced.erase x :=
    List.count_pos_iff.mp (by omega)
  have targetPerm :
      (before ++ reduced.erase x).Perm
        (x :: before ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases equal : z = x
    · subst z
      simp [firstErase, secondErase]
    · simp [remainder, equal, Ne.symm equal]
  have contraction :=
    Derives.symm <|
      derivesInteriorPower
        (Word.singleton initial) (Word.singleton x)
        (wordOfPrefixFinal (before ++ remainder) final)
  exact Derives.trans
    (derivesMiddlePermutation initial final sourcePerm) <|
    Derives.trans
      (by
        simpa [wordOfEndpoints_eq, Word.append_assoc] using contraction)
      (derivesMiddlePermutation initial final targetPerm.symm)

private theorem derivesNormalizeMiddleAux :
    ∀ (initial : Nat) (before middle : List Nat) (final : Nat),
      Derives basis
        (wordOfEndpoints initial (before ++ middle) final)
        (wordOfEndpoints initial
          (before ++ positiveParityReduce middle) final)
  | initial, before, [], final =>
      Derives.refl _
  | initial, before, x :: xs, final => by
      have suffixNormal :=
        derivesNormalizeMiddleAux initial (before ++ [x]) xs final
      let reduced := positiveParityReduce xs
      have firstStep :
          Derives basis
            (wordOfEndpoints initial (before ++ x :: xs) final)
            (wordOfEndpoints initial (before ++ x :: reduced) final) := by
        simpa [reduced, List.append_assoc] using suffixNormal
      by_cases countLt : reduced.count x < 2
      · have reducedEq :
            positiveParityReduce (x :: xs) = x :: reduced := by
          simp [positiveParityReduce, reduced, countLt]
        rw [reducedEq]
        exact firstStep
      · have countLe : reduced.count x ≤ 2 := by
          simpa [reduced] using positiveParityReduce_count_le_two x xs
        have countEq : reduced.count x = 2 := by omega
        have reducedEq :
            positiveParityReduce (x :: xs) = reduced.erase x := by
          simp [positiveParityReduce, reduced, countLt]
        rw [reducedEq]
        exact firstStep.trans <|
          derivesDeleteInteriorPair
            initial final x before reduced countEq
termination_by
  _ _ middle _ => middle.length

theorem derivesNormalizeMiddle
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial (positiveParityReduce middle) final) := by
  simpa using derivesNormalizeMiddleAux initial [] middle final

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private theorem wordOfCons_append_singleton
    (head : Nat) (tail : List Nat) (final : Nat) :
    wordOfCons head tail ++ Word.singleton final =
      wordOfPrefixFinal (head :: tail) final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal]
  rfl

private theorem wordOfEndpoints_append_middle
    (initial : Nat) (before suffix : List Nat) (final : Nat) :
    wordOfEndpoints initial (before ++ suffix) final =
      wordOfCons initial before ++ wordOfPrefixFinal suffix final := by
  apply Word.toList_injective
  rw [toList_wordOfEndpoints, Word.toList_append,
    toList_wordOfPrefixFinal]
  simp [wordOfCons, Word.toList, List.append_assoc]

private theorem derivesClosedAddPair
    (endpoint : Nat) (middle : List Nat) :
    Derives basis
      (wordOfEndpoints endpoint middle endpoint)
      (wordOfEndpoints endpoint
        (endpoint :: endpoint :: middle) endpoint) := by
  cases middle with
  | nil =>
      have substituted :=
        derivesBasisSubstitution powerLaw (by simp [basis])
          (instantiateThreeWords
            (Word.singleton endpoint)
            (Word.singleton endpoint)
            (Word.singleton endpoint))
      simpa [powerLaw, xx, xxxx, w, instantiateThreeWords,
        wordOfEndpoints_nil, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using substituted
  | cons x xs =>
      have base :
          Derives basis xyx xxxyx :=
        (Derives.fromBasis
          (e := tripleLeftContractionLaw) (by simp [basis])).symm
      have substituted :=
        Derives.subst base
          (instantiateThreeWords
            (Word.singleton endpoint) (wordOfCons x xs)
            (wordOfCons x xs))
      rw [wordOfEndpoints_eq, wordOfEndpoints_eq]
      have tailEq :=
        wordOfCons_append_singleton x xs endpoint
      change
        wordOfCons x xs ++ Word.singleton endpoint =
          Word.singleton x ++ wordOfPrefixFinal xs endpoint
        at tailEq
      have expanded :
          Derives basis
            (Word.singleton endpoint ++
              (wordOfCons x xs ++ Word.singleton endpoint))
            (Word.singleton endpoint ++
              (Word.singleton endpoint ++
                (Word.singleton endpoint ++
                  (wordOfCons x xs ++ Word.singleton endpoint)))) := by
        simpa [tripleLeftContractionLaw, xyx, xxxyx, w,
          instantiateThreeWords, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using substituted
      rw [tailEq] at expanded
      simpa [wordOfPrefixFinal] using expanded

private theorem derivesSaturate
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (SemigroupBasis.CoRoots.S5_120.saturatedMiddle
          initial middle final) final) := by
  by_cases added : initial = final ∧ initial ∉ middle
  · rcases added with ⟨closed, absent⟩
    subst final
    simpa [SemigroupBasis.CoRoots.S5_120.saturatedMiddle, absent] using
      derivesClosedAddPair initial middle
  · simp [SemigroupBasis.CoRoots.S5_120.saturatedMiddle, added]
    exact Derives.refl _

def normalMiddle
    (initial : Nat) (middle : List Nat) (final : Nat) : List Nat :=
  SemigroupBasis.CoRoots.S5_120.normalMiddle initial middle final

theorem derivesNormalEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (normalMiddle initial middle final) final) := by
  exact (derivesNormalizeMiddle initial middle final).trans <| by
    simpa [normalMiddle, SemigroupBasis.CoRoots.S5_120.normalMiddle] using
      derivesSaturate initial (positiveParityReduce middle) final

private theorem derivesExpandMiddle
    (initial final tested : Nat) (middle : List Nat)
    (member : tested ∈ middle) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (tested :: tested :: tested :: middle.erase tested) final) := by
  have arrange :
      middle.Perm (tested :: middle.erase tested) :=
    List.perm_cons_erase member
  have arranged :=
    derivesMiddlePermutation initial final arrange
  have expanded :=
    derivesInteriorPower
      (Word.singleton initial) (Word.singleton tested)
      (wordOfPrefixFinal (middle.erase tested) final)
  exact arranged.trans <| by
    simpa [wordOfEndpoints_eq, Word.append_assoc] using expanded

private theorem perm_extract_one_two
    {one two : Nat} {letters : List Nat}
    (different : one ≠ two)
    (oneMem : one ∈ letters)
    (twoCount : 2 ≤ letters.count two) :
    letters.Perm
      (one :: two :: two ::
        (((letters.erase one).erase two).erase two)) := by
  have first :
      letters.Perm (one :: letters.erase one) :=
    List.perm_cons_erase oneMem
  have countAfterOne :
      (letters.erase one).count two = letters.count two := by
    rw [List.count_erase_of_ne (Ne.symm different)]
  have twoMem₁ : two ∈ letters.erase one :=
    List.count_pos_iff.mp (by omega)
  have second :
      (letters.erase one).Perm
        (two :: (letters.erase one).erase two) :=
    List.perm_cons_erase twoMem₁
  have countAfterTwo :
      ((letters.erase one).erase two).count two =
        (letters.erase one).count two - 1 := by
    rw [List.count_erase_self]
  have twoMem₂ :
      two ∈ (letters.erase one).erase two :=
    List.count_pos_iff.mp (by omega)
  have third :
      ((letters.erase one).erase two).Perm
        (two :: ((letters.erase one).erase two).erase two) :=
    List.perm_cons_erase twoMem₂
  exact first.trans <|
    (List.Perm.cons one second).trans <|
      List.Perm.cons one (List.Perm.cons two third)

private theorem perm_cons_to_end (x : Nat) :
    ∀ letters : List Nat,
      (x :: letters).Perm (letters ++ [x])
  | [] => List.Perm.refl _
  | y :: ys =>
      (List.Perm.swap y x ys).trans <|
        List.Perm.cons y (perm_cons_to_end x ys)

private theorem perm_two_to_end (x y : Nat) :
    ∀ letters : List Nat,
      (x :: y :: letters).Perm (letters ++ [x, y])
  | [] => List.Perm.refl _
  | z :: zs =>
      (List.Perm.cons x (List.Perm.swap z y zs)).trans <|
        (List.Perm.swap z x (y :: zs)).trans <|
          List.Perm.cons z (perm_two_to_end x y zs)

private theorem derivesFinalPattern
    (initial : Nat) (rest : List Nat) (new old : Nat) :
    Derives basis
      (wordOfEndpoints initial (rest ++ [new, new, old]) old)
      (wordOfEndpoints initial (rest ++ [new, old, old]) new) := by
  have substituted :=
    derivesBasisSubstitution squareFinalSwitchLaw (by simp [basis])
      (instantiateThreeWords
        (Word.singleton new) (Word.singleton old)
        (Word.singleton old))
  have contextual :=
    Derives.prepend (wordOfCons initial rest) substituted
  rw [wordOfEndpoints_append_middle,
    wordOfEndpoints_append_middle]
  simpa [squareFinalSwitchLaw, xxyy, xyyx, w,
    instantiateThreeWords, wordOfCons, Word.bind, Word.append,
    Word.singleton, wordOfPrefixFinal, Word.append_assoc] using
      contextual

private theorem derivesFinalSwitchOfMiddle
    (initial : Nat) (middle : List Nat) (old new : Nat)
    (different : old ≠ new)
    (oldMem : old ∈ middle) (newMem : new ∈ middle) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints initial middle old)
        (wordOfEndpoints initial switchedMiddle new) := by
  let expanded :=
    new :: new :: new :: middle.erase new
  have expand :
      Derives basis
        (wordOfEndpoints initial middle old)
        (wordOfEndpoints initial expanded old) := by
    simpa [expanded] using
      derivesExpandMiddle initial old new middle newMem
  have oldInErase : old ∈ middle.erase new := by
    rw [List.mem_erase_of_ne different]
    exact oldMem
  have oldInExpanded : old ∈ expanded := by
    simp [expanded, oldInErase, Ne.symm different]
  have newCount : 2 ≤ expanded.count new := by
    simp [expanded]
  let rest :=
    (((expanded.erase old).erase new).erase new)
  have arrangeFront :
      expanded.Perm (old :: new :: new :: rest) := by
    simpa [rest] using
      perm_extract_one_two different oldInExpanded newCount
  have moveOld :=
    perm_cons_to_end old (new :: new :: rest)
  have moveNew :=
    (perm_two_to_end new new rest).append_right [old]
  have arrangeEnd :
      expanded.Perm (rest ++ [new, new, old]) := by
    exact arrangeFront.trans <|
      moveOld.trans <| by
        simpa [List.append_assoc] using moveNew
  have arranged :=
    derivesMiddlePermutation initial old arrangeEnd
  refine ⟨rest ++ [new, old, old], ?_⟩
  exact expand.trans <|
    arranged.trans <|
      derivesFinalPattern initial rest new old

private theorem derivesFinalSwitch
    (initial : Nat) (middle : List Nat) (old new : Nat)
    (different : old ≠ new)
    (oldRepeated : old ∈ middle ∨ initial = old)
    (newMem : new ∈ middle) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints initial middle old)
        (wordOfEndpoints initial switchedMiddle new) := by
  by_cases oldMem : old ∈ middle
  · exact derivesFinalSwitchOfMiddle
      initial middle old new different oldMem newMem
  · have closed : initial = old := oldRepeated.resolve_left oldMem
    subst initial
    have addPair := derivesClosedAddPair old middle
    obtain ⟨switchedMiddle, switched⟩ :=
      derivesFinalSwitchOfMiddle
        old (old :: old :: middle) old new different
        (by simp) (by simp [different, newMem])
    exact ⟨switchedMiddle, addPair.trans switched⟩

private theorem derivesAlignFinal
    (initial : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (middle₂ : List Nat) (final₂ : Nat)
    (invariants :
      SemigroupBasis.CoRoots.S5_120.EndpointInvariants
        initial middle₁ final₁ initial middle₂ final₂) :
    ∃ switchedMiddle,
      Derives basis
        (wordOfEndpoints initial middle₁ final₁)
        (wordOfEndpoints initial switchedMiddle final₂) := by
  by_cases finalsEq : final₁ = final₂
  · subst final₂
    exact ⟨middle₁, Derives.refl _⟩
  · have oldRepeated :
        final₁ ∈ middle₁ ∨ initial = final₁ := by
      apply Decidable.byContradiction
      intro notRepeated
      have middleAbsent : final₁ ∉ middle₁ :=
        fun member => notRepeated (Or.inl member)
      have initialNe : initial ≠ final₁ :=
        fun equal => notRepeated (Or.inr equal)
      have prefixAbsent : final₁ ∉ initial :: middle₁ := by
        simpa [Ne.symm initialNe, middleAbsent]
      have matched :=
        (invariants.simpleFinal final₁).mp
          ⟨rfl, prefixAbsent⟩
      exact finalsEq matched.1.symm
    have newMember : final₂ ∈ middle₁ := by
      have targetSupport :
          final₂ ∈ initial :: middle₂ ∨ final₂ = final₂ :=
        Or.inr rfl
      have sourceSupport :=
        (invariants.support final₂).mpr targetSupport
      rcases sourceSupport with sourcePrefix | sourceFinal
      · simp only [List.mem_cons] at sourcePrefix
        rcases sourcePrefix with equal | member
        · apply Decidable.byContradiction
          intro middleAbsent
          have sourceSimpleInitial :
              initial = final₂ ∧
                final₂ ∉ middle₁ ∧ final₁ ≠ final₂ :=
            ⟨equal.symm, middleAbsent, finalsEq⟩
          have targetSimpleInitial :=
            (invariants.simpleInitial final₂).mp
              sourceSimpleInitial
          exact targetSimpleInitial.2.2 rfl
        · exact member
      · exact False.elim (finalsEq sourceFinal)
    exact derivesFinalSwitch
      initial middle₁ final₁ final₂
      finalsEq oldRepeated newMember

/-- Normalize arbitrary endpoint words from their genuine simple-endpoint
and cyclic-two factor invariants, once an independent factor has supplied
their common initial variable. -/
theorem derivesEndpointWordsSameInitial
    (initial : Nat)
    (middle₁ : List Nat) (final₁ : Nat)
    (middle₂ : List Nat) (final₂ : Nat)
    (simpleEqual :
      ∀ valuation : Nat → Fin 4,
        simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial middle₁ final₁) =
          simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial middle₂ final₂))
    (parityEqual :
      ∀ valuation : Nat → Fin 2,
        cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial middle₁ final₁) =
          cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial middle₂ final₂)) :
    Derives basis
      (wordOfEndpoints initial middle₁ final₁)
      (wordOfEndpoints initial middle₂ final₂) := by
  have initialInvariants :=
    SemigroupBasis.CoRoots.S5_120.endpointInvariants_of_factor_equal
      initial middle₁ final₁ initial middle₂ final₂
      simpleEqual parityEqual
  obtain ⟨alignedMiddle, finalDerivation⟩ :=
    derivesAlignFinal
      initial middle₁ final₁ middle₂ final₂ initialInvariants
  have alignedSimpleEqual :
      ∀ valuation : Nat → Fin 4,
        simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial alignedMiddle final₂) =
          simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial middle₂ final₂) := by
    intro valuation
    exact
      (finalDerivation.sound modelsSimpleEndpoints valuation).symm.trans
        (simpleEqual valuation)
  have alignedParityEqual :
      ∀ valuation : Nat → Fin 2,
        cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial alignedMiddle final₂) =
          cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial middle₂ final₂) := by
    intro valuation
    exact
      (finalDerivation.sound
        (by
          simpa [SemigroupBasis.Generated.S2_2.table_eq_catalogue_model] using
            modelsS2_2)
        valuation).symm.trans
          (parityEqual valuation)
  let leftMiddle :=
    normalMiddle initial alignedMiddle final₂
  let rightMiddle :=
    normalMiddle initial middle₂ final₂
  have leftNormal :
      Derives basis
        (wordOfEndpoints initial alignedMiddle final₂)
        (wordOfEndpoints initial leftMiddle final₂) := by
    simpa [leftMiddle] using
      derivesNormalEndpoints initial alignedMiddle final₂
  have rightNormal :
      Derives basis
        (wordOfEndpoints initial middle₂ final₂)
        (wordOfEndpoints initial rightMiddle final₂) := by
    simpa [rightMiddle] using
      derivesNormalEndpoints initial middle₂ final₂
  have normalSimpleEqual :
      ∀ valuation : Nat → Fin 4,
        simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial leftMiddle final₂) =
          simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial rightMiddle final₂) := by
    intro valuation
    exact
      (leftNormal.sound modelsSimpleEndpoints valuation).symm.trans <|
        (alignedSimpleEqual valuation).trans <|
          rightNormal.sound modelsSimpleEndpoints valuation
  have normalParityEqual :
      ∀ valuation : Nat → Fin 2,
        cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial leftMiddle final₂) =
          cyclicTwo.semigroup.eval valuation
            (wordOfEndpoints initial rightMiddle final₂) := by
    intro valuation
    have cyclicModels : Models cyclicTwo.semigroup basis := by
      simpa [SemigroupBasis.Generated.S2_2.table_eq_catalogue_model] using
        modelsS2_2
    exact
      (leftNormal.sound cyclicModels valuation).symm.trans <|
        (alignedParityEqual valuation).trans <|
          rightNormal.sound cyclicModels valuation
  have normalInvariants :=
    SemigroupBasis.CoRoots.S5_120.endpointInvariants_of_factor_equal
      initial leftMiddle final₂ initial rightMiddle final₂
      normalSimpleEqual normalParityEqual
  have middlePerm : leftMiddle.Perm rightMiddle := by
    apply
      SemigroupBasis.CoRoots.S5_120.normalMiddle_perm_of_invariants
        normalInvariants
    · intro z
      simpa [leftMiddle, normalMiddle] using
        SemigroupBasis.CoRoots.S5_120.normalMiddle_count_le_two
          z initial alignedMiddle final₂
    · intro z
      simpa [rightMiddle, normalMiddle] using
        SemigroupBasis.CoRoots.S5_120.normalMiddle_count_le_two
          z initial middle₂ final₂
    · simpa [leftMiddle, normalMiddle] using
        SemigroupBasis.CoRoots.S5_120.normalMiddle_closed
          initial alignedMiddle final₂
    · simpa [rightMiddle, normalMiddle] using
        SemigroupBasis.CoRoots.S5_120.normalMiddle_closed
          initial middle₂ final₂
  exact finalDerivation.trans <|
    leftNormal.trans <|
      (derivesMiddlePermutation initial final₂ middlePerm).trans
        rightNormal.symm

/-- Every identity over an arbitrary `Nat` alphabet that is valid in both
factors follows from the exact seventeen-law candidate. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_353.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have firstValid :=
    SemigroupBasis.CoRoots.S5_342Family.S5_353.valid_firstRepeatedMarkerFour
      identity s5Valid
  have heads :=
    SemigroupBasis.CoRoots.S5_342.valid_head_eq identity firstValid
  have singletonIff :=
    SemigroupBasis.CoRoots.S5_342.valid_tail_nil_iff identity firstValid
  have s5Derivation :=
    SemigroupBasis.CoRoots.S5_342Family.S5_353.basis_complete.2
      identity s5Valid
  have simpleValid :
      identity.SatisfiedBy simpleEndpointsFour.semigroup := by
    intro valuation
    exact
      s5Derivation.sound modelsS5_342BasisSimpleEndpoints valuation
  have parityValid :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    rw [← SemigroupBasis.Generated.S2_2.table_eq_catalogue_model]
    exact cyclicValid
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  change leftHead = rightHead at heads
  change leftTail = [] ↔ rightTail = [] at singletonIff
  subst rightHead
  cases leftTail with
  | nil =>
      have rightNil : rightTail = [] := singletonIff.mp rfl
      subst rightTail
      exact Derives.refl _
  | cons leftSecond leftRest =>
      cases rightTail with
      | nil =>
          have impossible :
              leftSecond :: leftRest = [] :=
            singletonIff.mpr rfl
          simp at impossible
      | cons rightSecond rightRest =>
          let leftSuffix : Word Nat :=
            Word.mk leftSecond leftRest
          let rightSuffix : Word Nat :=
            Word.mk rightSecond rightRest
          let leftSplit := splitPrefixFinal leftSuffix
          let rightSplit := splitPrefixFinal rightSuffix
          have leftReconstruct :
              wordOfEndpoints leftHead leftSplit.1 leftSplit.2 =
                Word.mk leftHead (leftSecond :: leftRest) := by
            rw [wordOfEndpoints_eq]
            simp only [leftSplit]
            rw [wordOfPrefixFinal_split leftSuffix]
            rfl
          have rightReconstruct :
              wordOfEndpoints leftHead rightSplit.1 rightSplit.2 =
                Word.mk leftHead (rightSecond :: rightRest) := by
            rw [wordOfEndpoints_eq]
            simp only [rightSplit]
            rw [wordOfPrefixFinal_split rightSuffix]
            rfl
          have simpleEqual :
              ∀ valuation : Nat → Fin 4,
                simpleEndpointsFour.semigroup.eval valuation
                    (wordOfEndpoints
                      leftHead leftSplit.1 leftSplit.2) =
                  simpleEndpointsFour.semigroup.eval valuation
                    (wordOfEndpoints
                      leftHead rightSplit.1 rightSplit.2) := by
            intro valuation
            rw [leftReconstruct, rightReconstruct]
            exact simpleValid valuation
          have parityEqual :
              ∀ valuation : Nat → Fin 2,
                cyclicTwo.semigroup.eval valuation
                    (wordOfEndpoints
                      leftHead leftSplit.1 leftSplit.2) =
                  cyclicTwo.semigroup.eval valuation
                    (wordOfEndpoints
                      leftHead rightSplit.1 rightSplit.2) := by
            intro valuation
            rw [leftReconstruct, rightReconstruct]
            exact parityValid valuation
          have derivation :=
            derivesEndpointWordsSameInitial
              leftHead leftSplit.1 leftSplit.2
              rightSplit.1 rightSplit.2
              simpleEqual parityEqual
          rw [leftReconstruct, rightReconstruct] at derivation
          exact derivation

/-- Unrestricted joint basis for `V(S2_2) ∩ V(S5_353)`. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_353.table.semigroup basis where
  leftModels := modelsS2_2
  rightModels := modelsS5_353
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6FactorPairS2S5353Normal
