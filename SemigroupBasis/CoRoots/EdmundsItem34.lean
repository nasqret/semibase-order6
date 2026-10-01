import SemigroupBasis.Examples.EdmundsFourTwentySeven

namespace SemigroupBasis.CoRoots.EdmundsItem34

open SemigroupBasis
open SemigroupBasis.Examples

/-- The semantic data that distinguishes the item-34 reduced words. -/
structure NormalInvariants
    (prefix₁ : List Nat) (final₁ : Nat)
    (prefix₂ : List Nat) (final₂ : Nat) : Prop where
  support :
    ∀ z, z ∈ prefix₁ ++ [final₁] ↔ z ∈ prefix₂ ++ [final₂]
  parity :
    ∀ z, (prefix₁ ++ [final₁]).count z % 2 =
      (prefix₂ ++ [final₂]).count z % 2
  simpleFinal :
    ∀ z, (final₁ = z ∧ z ∉ prefix₁) ↔
      (final₂ = z ∧ z ∉ prefix₂)

private theorem derivesPrefixPermutation
    {prefix₁ prefix₂ : List Nat} (hperm : prefix₁.Perm prefix₂)
    (final : Nat) :
    Derives edmundsFourTwentySevenBasis
      (wordOfPrefixFinal prefix₁ final)
      (wordOfPrefixFinal prefix₂ final) := by
  induction hperm with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa using Derives.prepend (Word.singleton x) ih
  | swap x y xs =>
      simpa [Word.append_assoc] using
        edmundsFourTwentySevenDerivesPrefixSwap
          (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs final)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans ih₁ ih₂

private theorem contractLeadingTriple
    (x final : Nat) (rest : List Nat) :
    Derives edmundsFourTwentySevenBasis
      (wordOfPrefixFinal (x :: x :: x :: rest) final)
      (wordOfPrefixFinal (x :: rest) final) := by
  simpa [wordOfPrefixFinal, Word.append_assoc] using
    edmundsFourTwentySevenDerivesPrefixTripleContraction
      (Word.singleton x) (wordOfPrefixFinal rest final)

private theorem deleteThirdPrefixCopy
    (final x : Nat) (reduced : List Nat)
    (hcount : reduced.count x = 2) :
    Derives edmundsFourTwentySevenBasis
      (wordOfPrefixFinal (x :: reduced) final)
      (wordOfPrefixFinal (reduced.erase x) final) := by
  let remainder := (reduced.erase x).erase x
  have sourcePerm :
      (x :: reduced).Perm (x :: x :: x :: remainder) := by
    rw [List.perm_iff_count]
    intro z
    by_cases hz : z = x
    · subst z
      have firstErase : (reduced.erase x).count x = 1 := by
        rw [List.count_erase_self, hcount]
      have secondErase : ((reduced.erase x).erase x).count x = 0 := by
        rw [List.count_erase_self, firstErase]
      simp [remainder, hcount, secondErase]
    · simp [remainder, hz, Ne.symm hz]
  have firstErase : (reduced.erase x).count x = 1 := by
    rw [List.count_erase_self, hcount]
  have eraseHasX : x ∈ reduced.erase x :=
    List.count_pos_iff.mp (by omega)
  have targetPerm :
      (x :: remainder).Perm (reduced.erase x) := by
    simpa [remainder] using
      (List.perm_cons_erase eraseHasX).symm
  exact Derives.trans
    (derivesPrefixPermutation sourcePerm final) <|
    Derives.trans
      (contractLeadingTriple x final remainder)
      (derivesPrefixPermutation targetPerm final)

private theorem derivesNormalizePrefix :
    ∀ (pref : List Nat) (final : Nat),
      Derives edmundsFourTwentySevenBasis
        (wordOfPrefixFinal pref final)
        (wordOfPrefixFinal (positiveParityReduce pref) final)
  | [], final => Derives.refl _
  | x :: xs, final => by
      have suffixNormal := derivesNormalizePrefix xs final
      have prefixed :=
        Derives.prepend (Word.singleton x) suffixNormal
      let reduced := positiveParityReduce xs
      by_cases hcount : reduced.count x < 2
      · have reducedEq :
            positiveParityReduce (x :: xs) = x :: reduced := by
          simp [positiveParityReduce, reduced, hcount]
        rw [reducedEq]
        simpa [wordOfPrefixFinal, reduced] using prefixed
      · have countLe : reduced.count x ≤ 2 := by
          change (positiveParityReduce xs).count x ≤ 2
          exact positiveParityReduce_count_le_two x xs
        have countEq : reduced.count x = 2 := by omega
        have reducedEq :
            positiveParityReduce (x :: xs) = reduced.erase x := by
          simp [positiveParityReduce, reduced, hcount]
        rw [reducedEq]
        have firstStep :
            Derives edmundsFourTwentySevenBasis
              (wordOfPrefixFinal (x :: xs) final)
              (wordOfPrefixFinal (x :: reduced) final) := by
          simpa [wordOfPrefixFinal, reduced] using prefixed
        exact Derives.trans firstStep
          (deleteThirdPrefixCopy final x reduced countEq)
termination_by
  pref _ => pref.length

private theorem repeatedSwitchUnderPrefix
    (rest : List Nat) (oldFinal newFinal : Nat) :
    Derives edmundsFourTwentySevenBasis
      (wordOfPrefixFinal (rest ++ [newFinal, oldFinal]) oldFinal)
      (wordOfPrefixFinal
        (rest ++ [oldFinal, oldFinal, newFinal, newFinal]) newFinal) := by
  induction rest with
  | nil =>
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        edmundsFourTwentySevenDerivesRepeatedTerminalBlockSwitch
          (Word.singleton newFinal) (Word.singleton oldFinal)
  | cons x xs ih =>
      simpa [wordOfPrefixFinal] using
        Derives.prepend (Word.singleton x) ih

private theorem permTwoToEnd
    (a b : Nat) :
    ∀ xs : List Nat, (a :: b :: xs).Perm (xs ++ [a, b])
  | [] => List.Perm.refl _
  | x :: xs =>
      (List.Perm.cons a (List.Perm.swap x b xs)).trans <|
        (List.Perm.swap x a (b :: xs)).trans <|
          List.Perm.cons x (permTwoToEnd a b xs)

private theorem switchRepeatedFinal
    (pref : List Nat) (oldFinal newFinal : Nat)
    (hne : oldFinal ≠ newFinal)
    (hold : oldFinal ∈ pref) (hnew : newFinal ∈ pref) :
    let remainder := (pref.erase newFinal).erase oldFinal
    Derives edmundsFourTwentySevenBasis
      (wordOfPrefixFinal pref oldFinal)
      (wordOfPrefixFinal
        (remainder ++ [oldFinal, oldFinal, newFinal, newFinal])
        newFinal) := by
  dsimp
  have oldInErase : oldFinal ∈ pref.erase newFinal := by
    simpa [hne] using hold
  have arrangeFront :
      pref.Perm
        (newFinal :: oldFinal ::
          (pref.erase newFinal).erase oldFinal) :=
    (List.perm_cons_erase hnew).trans <|
      List.Perm.cons newFinal <|
        List.perm_cons_erase oldInErase
  have arrange :
      pref.Perm
        ((pref.erase newFinal).erase oldFinal ++
          [newFinal, oldFinal]) :=
    arrangeFront.trans <|
      permTwoToEnd newFinal oldFinal _
  exact Derives.trans
    (derivesPrefixPermutation arrange oldFinal)
    (repeatedSwitchUnderPrefix
      ((pref.erase newFinal).erase oldFinal)
      oldFinal newFinal)

private theorem reducedPrefixPerm
    (prefix₁ prefix₂ : List Nat) (final : Nat)
    (leftReduced : ∀ z, prefix₁.count z ≤ 2)
    (rightReduced : ∀ z, prefix₂.count z ≤ 2)
    (support :
      ∀ z, z ∈ prefix₁ ++ [final] ↔ z ∈ prefix₂ ++ [final])
    (parity :
      ∀ z, (prefix₁ ++ [final]).count z % 2 =
        (prefix₂ ++ [final]).count z % 2)
    (finalMembership : final ∈ prefix₁ ↔ final ∈ prefix₂) :
    prefix₁.Perm prefix₂ := by
  rw [List.perm_iff_count]
  intro z
  have prefixSupport : z ∈ prefix₁ ↔ z ∈ prefix₂ := by
    by_cases hz : z = final
    · subst z
      exact finalMembership
    · have h := support z
      simpa [hz, Ne.symm hz] using h
  have prefixParity : prefix₁.count z % 2 = prefix₂.count z % 2 := by
    have h := parity z
    simp only [List.count_append] at h
    by_cases hz : z = final
    · subst z
      simp at h
      omega
    · simp [Ne.symm hz] at h
      exact h
  have leftLe := leftReduced z
  have rightLe := rightReduced z
  by_cases hz : z ∈ prefix₁
  · have leftPos := List.count_pos_iff.mpr hz
    have rightPos := List.count_pos_iff.mpr (prefixSupport.mp hz)
    omega
  · have leftZero := List.count_eq_zero.mpr hz
    have rightZero := List.count_eq_zero.mpr <| by
      intro h
      exact hz (prefixSupport.mpr h)
    omega

/-- A model of the item-34 basis is complete once its concrete table
separates support, parity, and the unrepeated final letter of reduced words. -/
theorem basisForOfSeparatesNormalForms
    {S : Type u} (G : Semigroup S)
    (models : Models G edmundsFourTwentySevenBasis)
    (separates :
      ∀ (prefix₁ : List Nat) (final₁ : Nat)
        (prefix₂ : List Nat) (final₂ : Nat),
        (∀ valuation : Nat → S,
          G.eval valuation (wordOfPrefixFinal prefix₁ final₁) =
            G.eval valuation (wordOfPrefixFinal prefix₂ final₂)) →
        NormalInvariants prefix₁ final₁ prefix₂ final₂) :
    BasisFor G edmundsFourTwentySevenBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  let lhsSplit := splitPrefixFinal e.lhs
  let rhsSplit := splitPrefixFinal e.rhs
  let lhsPrefix := positiveParityReduce lhsSplit.1
  let rhsPrefix := positiveParityReduce rhsSplit.1
  have lhsNormal := edmundsFourTwentySevenDerivesNormal e.lhs
  have rhsNormal := edmundsFourTwentySevenDerivesNormal e.rhs
  dsimp only at lhsNormal rhsNormal
  change
    Derives edmundsFourTwentySevenBasis e.lhs
      (wordOfPrefixFinal lhsPrefix lhsSplit.2) at lhsNormal
  change
    Derives edmundsFourTwentySevenBasis e.rhs
      (wordOfPrefixFinal rhsPrefix rhsSplit.2) at rhsNormal
  have normalizedEval :
      ∀ valuation : Nat → S,
        G.eval valuation
            (wordOfPrefixFinal lhsPrefix lhsSplit.2) =
          G.eval valuation
            (wordOfPrefixFinal rhsPrefix rhsSplit.2) := by
    intro valuation
    have lhsSound := lhsNormal.sound models valuation
    have rhsSound := rhsNormal.sound models valuation
    exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
  have invariants :=
    separates lhsPrefix lhsSplit.2 rhsPrefix rhsSplit.2 normalizedEval
  have normalSupport := invariants.support
  have normalParity := invariants.parity
  have simpleFinalIff := invariants.simpleFinal
  by_cases lhsRepeated : lhsSplit.2 ∈ lhsPrefix
  · have rhsRepeated : rhsSplit.2 ∈ rhsPrefix := by
      apply Decidable.byContradiction
      intro rhsSimple
      have lhsSimpleAtRight :=
        (simpleFinalIff rhsSplit.2).2 ⟨rfl, rhsSimple⟩
      exact lhsSimpleAtRight.2 <| by
        simpa [lhsSimpleAtRight.1] using lhsRepeated
    by_cases finalsEq : lhsSplit.2 = rhsSplit.2
    · have prefixPerm : lhsPrefix.Perm rhsPrefix := by
        rw [← finalsEq] at normalSupport normalParity rhsRepeated
        exact reducedPrefixPerm
          lhsPrefix rhsPrefix lhsSplit.2
          (by
            intro z
            exact positiveParityReduce_count_le_two z lhsSplit.1)
          (by
            intro z
            exact positiveParityReduce_count_le_two z rhsSplit.1)
          normalSupport normalParity
          ⟨fun _ => rhsRepeated, fun _ => lhsRepeated⟩
      rw [← finalsEq] at rhsNormal
      exact Derives.trans lhsNormal <|
        Derives.trans
          (derivesPrefixPermutation prefixPerm lhsSplit.2)
          (Derives.symm rhsNormal)
    · have newInLeft : rhsSplit.2 ∈ lhsPrefix := by
        have rhsFull : rhsSplit.2 ∈ rhsPrefix ++ [rhsSplit.2] := by
          simp
        have lhsFull := (normalSupport rhsSplit.2).mpr rhsFull
        rcases List.mem_append.mp lhsFull with h | h
        · exact h
        · simp only [List.mem_singleton] at h
          exact False.elim (finalsEq h.symm)
      let remainder :=
        (lhsPrefix.erase rhsSplit.2).erase lhsSplit.2
      let switchedPrefix :=
        remainder ++
          [lhsSplit.2, lhsSplit.2, rhsSplit.2, rhsSplit.2]
      have switch :
          Derives edmundsFourTwentySevenBasis
            (wordOfPrefixFinal lhsPrefix lhsSplit.2)
            (wordOfPrefixFinal switchedPrefix rhsSplit.2) := by
        exact switchRepeatedFinal
          lhsPrefix lhsSplit.2 rhsSplit.2 finalsEq
          lhsRepeated newInLeft
      have switchedNormal :=
        derivesNormalizePrefix switchedPrefix rhsSplit.2
      have switchedToRightEval :
          ∀ valuation : Nat → S,
            G.eval valuation
                (wordOfPrefixFinal
                  (positiveParityReduce switchedPrefix) rhsSplit.2) =
              G.eval valuation
                (wordOfPrefixFinal rhsPrefix rhsSplit.2) := by
        intro valuation
        have switchSound := switch.sound models valuation
        have switchedNormalSound :=
          switchedNormal.sound models valuation
        exact switchedNormalSound.symm.trans <|
          switchSound.symm.trans (normalizedEval valuation)
      have switchedInvariants :=
        separates
          (positiveParityReduce switchedPrefix) rhsSplit.2
          rhsPrefix rhsSplit.2 switchedToRightEval
      have switchedFinalMem :
          rhsSplit.2 ∈ positiveParityReduce switchedPrefix := by
        rw [mem_positiveParityReduce_iff]
        simp [switchedPrefix]
      have prefixPerm :
          (positiveParityReduce switchedPrefix).Perm rhsPrefix :=
        reducedPrefixPerm
          (positiveParityReduce switchedPrefix) rhsPrefix rhsSplit.2
          (by
            intro z
            exact positiveParityReduce_count_le_two z switchedPrefix)
          (by
            intro z
            exact positiveParityReduce_count_le_two z rhsSplit.1)
          switchedInvariants.support switchedInvariants.parity
          ⟨fun _ => rhsRepeated, fun _ => switchedFinalMem⟩
      exact Derives.trans lhsNormal <|
        Derives.trans switch <|
          Derives.trans switchedNormal <|
            Derives.trans
              (derivesPrefixPermutation prefixPerm rhsSplit.2)
              (Derives.symm rhsNormal)
  · have rightSimple :=
      (simpleFinalIff lhsSplit.2).1 ⟨rfl, lhsRepeated⟩
    have finalsEq : rhsSplit.2 = lhsSplit.2 := rightSimple.1
    have prefixPerm : lhsPrefix.Perm rhsPrefix := by
      rw [finalsEq] at normalSupport normalParity
      exact reducedPrefixPerm
        lhsPrefix rhsPrefix lhsSplit.2
        (by
          intro z
          exact positiveParityReduce_count_le_two z lhsSplit.1)
        (by
          intro z
          exact positiveParityReduce_count_le_two z rhsSplit.1)
        normalSupport normalParity
        ⟨fun h => (lhsRepeated h).elim,
          fun h => (rightSimple.2 h).elim⟩
    rw [finalsEq] at rhsNormal
    exact Derives.trans lhsNormal <|
      Derives.trans
        (derivesPrefixPermutation prefixPerm lhsSplit.2)
        (Derives.symm rhsNormal)

end SemigroupBasis.CoRoots.EdmundsItem34
