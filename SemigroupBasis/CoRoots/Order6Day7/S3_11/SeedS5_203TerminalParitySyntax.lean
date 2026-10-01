import SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank008
import SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008
import SemigroupBasis.CoRoots.S5_203Family
import SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal

/-!
# Exact D008 terminal-state / parity frozen-law calculus

The complete ten-law S5_203 basis and the existing eight-law S5_83/parity
basis both contain axioms FALSE for the exact D008 factor intersection.
Neither calculus is transported.  Every positive-parity prefix operation,
terminal-doubleton guard, penultimate retarget, and non-doubleton terminal
cube transition below is instead derived from the literal frozen 26 laws.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_203

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

private abbrev targetBasis : List (Identity Nat) := Rank008.basis

private abbrev ListDerives (left right : List Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis left right

private abbrev terminalWord :=
  SemigroupBasis.CoRoots.S5_203.terminalPairWord

private def word (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

private def instantiateFour
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | letter + 4 => Word.singleton (letter + 4)

private def surround
    (front : Option (Word Nat)) (middle : Word Nat)
    (suffix : Option (Word Nat)) : Word Nat :=
  match front, suffix with
  | none, none => middle
  | some before, none => before ++ middle
  | none, some after => middle ++ after
  | some before, some after => (before ++ middle) ++ after

private theorem displayedForward
    (identity : Identity Nat) (member : identity ∈ targetBasis)
    (substitution : Nat → Word Nat)
    (front suffix : Option (Word Nat)) :
    Derives targetBasis
      (surround front (identity.lhs.bind substitution) suffix)
      (surround front (identity.rhs.bind substitution) suffix) := by
  have primitive := Derives.subst (Derives.fromBasis member) substitution
  cases front with
  | none =>
      cases suffix with
      | none => exact primitive
      | some after => exact Derives.appendRight primitive after
  | some before =>
      cases suffix with
      | none => exact Derives.prepend before primitive
      | some after =>
          exact Derives.appendRight (Derives.prepend before primitive) after

/-- Delete exactly TWO initial copies while two terminal blocks remain. -/
theorem derivesLongPrefixContraction
    (first second third : Word Nat) :
    Derives targetBasis
      ((((first ++ first) ++ first) ++ second) ++ third)
      ((first ++ second) ++ third) := by
  have primitive :
      Derives targetBasis (word 0 [0, 0, 1, 2]) (word 0 [1, 2]) :=
    Derives.fromBasis (e := Rank008.law04)
      (show Rank008.law04 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateFour first second third third)
  simpa [word, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The square-free open-prefix swap needs FOUR separately typed frozen edges. -/
private theorem openPrefixSwapPrimitive :
    Derives targetBasis (word 0 [1, 2, 3]) (word 1 [0, 2, 3]) := by
  have step00 :
      Derives targetBasis (word 0 [1, 2, 3])
        (word 0 [1, 1, 1, 2, 3]) := by
    exact (displayedForward Rank008.law04
      (show Rank008.law04 ∈ targetBasis by decide)
      (instantiateFour (word 1 []) (word 2 []) (word 3 []) (word 3 []))
      (some (word 0 [])) none).symm
  have step01 :
      Derives targetBasis (word 0 [1, 1, 1, 2, 3])
        (word 1 [1, 0, 1, 2, 3]) := by
    exact (displayedForward Rank008.law07
      (show Rank008.law07 ∈ targetBasis by decide)
      (instantiateFour (word 1 []) (word 0 []) (word 2 []) (word 3 []))
      none (some (word 2 [3]))).symm
  have step02 :
      Derives targetBasis (word 1 [1, 0, 1, 2, 3])
        (word 1 [0, 0, 0, 2, 3]) := by
    exact displayedForward Rank008.law06
      (show Rank008.law06 ∈ targetBasis by decide)
      (instantiateFour (word 1 []) (word 0 []) (word 2 []) (word 3 []))
      none (some (word 2 [3]))
  have step03 :
      Derives targetBasis (word 1 [0, 0, 0, 2, 3])
        (word 1 [0, 2, 3]) := by
    exact displayedForward Rank008.law04
      (show Rank008.law04 ∈ targetBasis by decide)
      (instantiateFour (word 0 []) (word 2 []) (word 3 []) (word 3 []))
      (some (word 1 [])) none
  exact step00.trans (step01.trans (step02.trans step03))

/-- Arbitrary nonempty prefix blocks commute before two fixed terminal blocks. -/
theorem derivesOpenPrefixSwap
    (first second third fourth : Word Nat) :
    Derives targetBasis
      (((first ++ second) ++ third) ++ fourth)
      (((second ++ first) ++ third) ++ fourth) := by
  have substituted :=
    Derives.subst openPrefixSwapPrimitive
      (instantiateFour first second third fourth)
  simpa [word, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- A penultimate marker can change only with matching parity compensation. -/
private theorem penultimateMarkerTransferPrimitive :
    Derives targetBasis (word 0 [1, 1, 2])
      (word 1 [1, 0, 0, 0, 2]) := by
  have step00 :
      Derives targetBasis (word 0 [1, 1, 2])
        (word 1 [0, 1, 2]) := by
    exact (displayedForward Rank008.law22
      (show Rank008.law22 ∈ targetBasis by decide)
      (instantiateFour (word 1 []) (word 0 []) (word 2 []) (word 2 []))
      none none).symm
  have step01 :
      Derives targetBasis (word 1 [0, 1, 2])
        (word 1 [1, 0, 0, 0, 2]) := by
    exact (displayedForward Rank008.law09
      (show Rank008.law09 ∈ targetBasis by decide)
      (instantiateFour (word 1 []) (word 0 []) (word 2 []) (word 2 []))
      none (some (word 2 []))).symm
  exact step00.trans step01

/-- Frozen two-edge parity-preserving retarget under arbitrary substitutions. -/
theorem derivesPenultimateMarkerTransfer
    (newMarker oldMarker final : Word Nat) :
    Derives targetBasis
      (((newMarker ++ oldMarker) ++ oldMarker) ++ final)
      (((((oldMarker ++ oldMarker) ++ newMarker) ++ newMarker) ++
        newMarker) ++ final) := by
  have substituted :=
    Derives.subst penultimateMarkerTransferPrimitive
      (instantiateFour newMarker oldMarker final final)
  simpa [word, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Turn a separated repeated final into a literal terminal cube safely. -/
theorem derivesTerminalCube
    (final penultimate : Word Nat) :
    Derives targetBasis
      ((final ++ penultimate) ++ final)
      ((((penultimate ++ final) ++ final) ++ final) ++ final) := by
  have primitive :
      Derives targetBasis (word 0 [1, 0])
        (word 1 [0, 0, 0, 0]) :=
    Derives.fromBasis (e := Rank008.law14)
      (show Rank008.law14 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive
      (instantiateFour final penultimate final final)
  simpa [word, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Switch a genuine terminal cube, never a protected terminal doubleton. -/
private theorem terminalCubeMarkerSwitchPrimitive :
    Derives targetBasis (word 0 [1, 1, 1]) (word 1 [0, 0, 0]) := by
  have step00 :
      Derives targetBasis (word 0 [1, 1, 1])
        (word 1 [1, 0, 1]) := by
    exact (displayedForward Rank008.law07
      (show Rank008.law07 ∈ targetBasis by decide)
      (instantiateFour (word 1 []) (word 0 []) (word 0 []) (word 0 []))
      none none).symm
  have step01 :
      Derives targetBasis (word 1 [1, 0, 1])
        (word 1 [0, 0, 0]) := by
    exact displayedForward Rank008.law06
      (show Rank008.law06 ∈ targetBasis by decide)
      (instantiateFour (word 1 []) (word 0 []) (word 0 []) (word 0 []))
      none none
  exact step00.trans step01

/-- Arbitrary-block terminal-cube retarget preserves every variable parity. -/
theorem derivesTerminalCubeMarkerSwitch
    (newMarker oldMarker : Word Nat) :
    Derives targetBasis
      (((newMarker ++ oldMarker) ++ oldMarker) ++ oldMarker)
      (((oldMarker ++ newMarker) ++ newMarker) ++ newMarker) := by
  have substituted :=
    Derives.subst terminalCubeMarkerSwitchPrimitive
      (instantiateFour newMarker oldMarker oldMarker oldMarker)
  simpa [word, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem retargetDerives
    {source target newSource newTarget : Word Nat}
    (derivation : Derives targetBasis source target)
    (sourceToList : source.toList = newSource.toList)
    (targetToList : target.toList = newTarget.toList) :
    Derives targetBasis newSource newTarget := by
  have sourceEqual := Word.toList_injective sourceToList
  have targetEqual := Word.toList_injective targetToList
  cases sourceEqual
  cases targetEqual
  exact derivation

/-- Every stem permutation is allowed with both terminal letters untouched. -/
theorem derivesPrefixPermutation
    {left right : List Nat}
    (permutation : left.Perm right)
    (penultimate final : Nat) :
    Derives targetBasis
      (terminalWord left penultimate final)
      (terminalWord right penultimate final) := by
  induction permutation with
  | nil => exact Derives.refl _
  | cons head _ induction =>
      simpa [terminalWord, SemigroupBasis.CoRoots.S5_203.terminalPairWord,
        wordOfPrefixFinal, List.append_assoc] using
          Derives.prepend (Word.singleton head) induction
  | swap first second suffix =>
      simpa [terminalWord, SemigroupBasis.CoRoots.S5_203.terminalPairWord,
        wordOfPrefixFinal, Word.append_assoc, List.append_assoc] using
          derivesOpenPrefixSwap
            (Word.singleton second) (Word.singleton first)
            (wordOfPrefixFinal suffix penultimate)
            (Word.singleton final)
  | trans _ _ first second => exact first.trans second

private theorem derivesContractLeadingTriple
    (letter : Nat) (rest : List Nat)
    (penultimate final : Nat) :
    Derives targetBasis
      (terminalWord (letter :: letter :: letter :: rest) penultimate final)
      (terminalWord (letter :: rest) penultimate final) := by
  have raw :=
    derivesLongPrefixContraction
      (Word.singleton letter)
      (wordOfPrefixFinal rest penultimate)
      (Word.singleton final)
  apply retargetDerives raw
  · rw [SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord]
    simp [Word.toList]
    simpa only [List.append_assoc, List.singleton_append] using
      congrArg (fun letters => letters ++ [final])
        (toList_wordOfPrefixFinal rest penultimate)
  · rw [SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord]
    simp [Word.toList]
    simpa only [List.append_assoc, List.singleton_append] using
      congrArg (fun letters => letters ++ [final])
        (toList_wordOfPrefixFinal rest penultimate)

private theorem derivesDeleteThirdPrefixCopy
    (letter : Nat) (before reduced : List Nat)
    (penultimate final : Nat)
    (countEqual : reduced.count letter = 2) :
    Derives targetBasis
      (terminalWord (before ++ letter :: reduced) penultimate final)
      (terminalWord (before ++ reduced.erase letter) penultimate final) := by
  let remainder := (reduced.erase letter).erase letter
  have firstErase : (reduced.erase letter).count letter = 1 := by
    rw [List.count_erase_self, countEqual]
  have secondErase : remainder.count letter = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, firstErase]
  have sourcePermutation :
      (before ++ letter :: reduced).Perm
        (letter :: letter :: letter :: before ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = letter
    · subst tested
      simp [countEqual, secondErase]
    · simp [remainder, equal, Ne.symm equal]
  have targetPermutation :
      (before ++ reduced.erase letter).Perm
        (letter :: before ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = letter
    · subst tested
      simp [firstErase, secondErase]
    · simp [remainder, equal, Ne.symm equal]
  exact
    (derivesPrefixPermutation
      sourcePermutation penultimate final).trans <|
      (derivesContractLeadingTriple
        letter (before ++ remainder) penultimate final).trans <|
        derivesPrefixPermutation
          targetPermutation.symm penultimate final

private theorem derivesNormalizePrefixAux :
    ∀ (before stem : List Nat) (penultimate final : Nat),
      Derives targetBasis
        (terminalWord (before ++ stem) penultimate final)
        (terminalWord
          (before ++ positiveParityReduce stem) penultimate final)
  | before, [], penultimate, final => Derives.refl _
  | before, letter :: rest, penultimate, final => by
      have suffixNormal :=
        derivesNormalizePrefixAux
          (before ++ [letter]) rest penultimate final
      let reduced := positiveParityReduce rest
      have firstStep :
          Derives targetBasis
            (terminalWord (before ++ letter :: rest) penultimate final)
            (terminalWord (before ++ letter :: reduced) penultimate final) := by
        simpa [reduced, List.append_assoc] using suffixNormal
      by_cases countLess : reduced.count letter < 2
      · have reducedEqual :
            positiveParityReduce (letter :: rest) = letter :: reduced := by
          simp [positiveParityReduce, reduced, countLess]
        rw [reducedEqual]
        exact firstStep
      · have countBound : reduced.count letter ≤ 2 := by
          simpa [reduced] using
            positiveParityReduce_count_le_two letter rest
        have countEqual : reduced.count letter = 2 := by omega
        have reducedEqual :
            positiveParityReduce (letter :: rest) = reduced.erase letter := by
          simp [positiveParityReduce, reduced, countLess]
        rw [reducedEqual]
        exact firstStep.trans <|
          derivesDeleteThirdPrefixCopy
            letter before reduced penultimate final countEqual
termination_by _ stem _ _ => stem.length

/-- Normalize all stem multiplicities to one odd or two positive-even copies. -/
theorem derivesNormalizePrefix
    (stem : List Nat) (penultimate final : Nat) :
    Derives targetBasis
      (terminalWord stem penultimate final)
      (terminalWord (positiveParityReduce stem) penultimate final) := by
  simpa using derivesNormalizePrefixAux [] stem penultimate final

private theorem prefixParityOfRenderedParity
    {left right : List Nat} (penultimate final : Nat)
    (parity : ∀ letter,
      (left ++ [penultimate, final]).count letter % 2 =
        (right ++ [penultimate, final]).count letter % 2) :
    ∀ letter, left.count letter % 2 = right.count letter % 2 := by
  intro tested
  have whole := parity tested
  simp only [List.count_append] at whole
  omega

/-- Aligned terminal pairs normalize from exact support and variable parity;
both endpoint-membership hypotheses preserve S5_203 terminal strata. -/
theorem derivesAlignedTerminalPair
    (left right : List Nat) (penultimate final : Nat)
    (support : ∀ letter,
      letter ∈ left ++ [penultimate, final] ↔
        letter ∈ right ++ [penultimate, final])
    (parity : ∀ letter,
      (left ++ [penultimate, final]).count letter % 2 =
        (right ++ [penultimate, final]).count letter % 2)
    (penultimateMembership : penultimate ∈ left ↔ penultimate ∈ right)
    (finalMembership : final ∈ left ↔ final ∈ right) :
    Derives targetBasis
      (terminalWord left penultimate final)
      (terminalWord right penultimate final) := by
  have stemSupport : ∀ letter, letter ∈ left ↔ letter ∈ right := by
    intro letter
    by_cases isPenultimate : letter = penultimate
    · subst letter
      exact penultimateMembership
    · by_cases isFinal : letter = final
      · subst letter
        exact finalMembership
      · simpa [isPenultimate, isFinal,
          Ne.symm isPenultimate, Ne.symm isFinal] using support letter
  have stemParity := prefixParityOfRenderedParity penultimate final parity
  have permutation := positiveParityReduce_perm stemSupport stemParity
  exact
    (derivesNormalizePrefix left penultimate final).trans <|
      (derivesPrefixPermutation permutation penultimate final).trans <|
        (derivesNormalizePrefix right penultimate final).symm

private theorem permConsToEnd (letter : Nat) :
    ∀ rest : List Nat, (letter :: rest).Perm (rest ++ [letter])
  | [] => List.Perm.refl _
  | head :: tail =>
      (List.Perm.swap head letter tail).trans <|
        List.Perm.cons head (permConsToEnd letter tail)

private theorem permTwoToEnd (first second : Nat) :
    ∀ rest : List Nat,
      (first :: second :: rest).Perm (rest ++ [first, second])
  | [] => List.Perm.refl _
  | head :: tail =>
      (List.Perm.cons first (List.Perm.swap head second tail)).trans <|
        (List.Perm.swap head first (second :: tail)).trans <|
          List.Perm.cons head (permTwoToEnd first second tail)

private theorem derivesOfListDerivesToList
    (left right : Word Nat)
    (derivation : ListDerives left.toList right.toList) :
    Derives targetBasis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord derivation

/-- A repeated final outside the protected doubleton stratum becomes a
literal terminal cube with its marker still present in the stem. -/
theorem derivesMakeNonDoubletonFinal
    (stem : List Nat) (penultimate final : Nat)
    (finalMember : final ∈ stem) :
    ∃ cubeStem,
      Derives targetBasis
        (terminalWord stem penultimate final)
        (terminalWord cubeStem final final) ∧
      final ∈ cubeStem := by
  let remainder := stem.erase final
  have arrange : stem.Perm (remainder ++ [final]) :=
    (List.perm_cons_erase finalMember).trans <|
      permConsToEnd final remainder
  have arranged := derivesPrefixPermutation arrange penultimate final
  have cube := derivesTerminalCube
    (Word.singleton final) (Word.singleton penultimate)
  have prefixed :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.prepend remainder
      (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord cube)
  let cubeStem := remainder ++ [penultimate, final, final]
  have converted :
      Derives targetBasis
        (terminalWord (remainder ++ [final]) penultimate final)
        (terminalWord cubeStem final final) := by
    apply derivesOfListDerivesToList
    simpa [cubeStem,
      SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord,
      Word.toList_append, Word.toList_singleton,
      List.append_assoc] using prefixed
  exact ⟨cubeStem, arranged.trans converted, by simp [cubeStem]⟩

/-- Change a genuine terminal cube marker; both old and new markers must
already occur in its stem, so a terminal doubleton is never weakened. -/
theorem derivesSwitchTerminalCube
    (stem : List Nat) (oldMarker newMarker : Nat)
    (oldMember : oldMarker ∈ stem)
    (newMember : newMarker ∈ stem) :
    ∃ switchedStem,
      Derives targetBasis
        (terminalWord stem oldMarker oldMarker)
        (terminalWord switchedStem newMarker newMarker) ∧
      newMarker ∈ switchedStem := by
  by_cases equal : newMarker = oldMarker
  · subst newMarker
    exact ⟨stem, Derives.refl _, oldMember⟩
  · have oldInErase : oldMarker ∈ stem.erase newMarker :=
      (List.mem_erase_of_ne (Ne.symm equal)).mpr oldMember
    let remainder := (stem.erase newMarker).erase oldMarker
    have arrangeFront : stem.Perm (newMarker :: oldMarker :: remainder) :=
      (List.perm_cons_erase newMember).trans <|
        List.Perm.cons newMarker <| by
          simpa [remainder] using List.perm_cons_erase oldInErase
    have arrange : stem.Perm (remainder ++ [newMarker, oldMarker]) :=
      arrangeFront.trans (permTwoToEnd newMarker oldMarker remainder)
    have arranged := derivesPrefixPermutation arrange oldMarker oldMarker
    have switch := derivesTerminalCubeMarkerSwitch
      (Word.singleton newMarker) (Word.singleton oldMarker)
    have prefixed :=
      SemigroupBasis.CoRoots.S5_107.ListDerives.prepend remainder
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord switch)
    let switchedStem := remainder ++ [oldMarker, newMarker]
    have converted :
        Derives targetBasis
          (terminalWord (remainder ++ [newMarker, oldMarker])
            oldMarker oldMarker)
          (terminalWord switchedStem newMarker newMarker) := by
      apply derivesOfListDerivesToList
      simpa [switchedStem,
        SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using prefixed
    exact ⟨switchedStem, arranged.trans converted,
      by simp [switchedStem]⟩

/-- Retarget a repeated penultimate while preserving its unique final and
the exact old/new parity corrections recorded by the two-edge frozen path. -/
theorem derivesSwitchRepeatedPenultimate
    (stem : List Nat) (oldMarker newMarker final : Nat)
    (oldMember : oldMarker ∈ stem)
    (newSupported : newMarker ∈ stem ∨ newMarker = oldMarker)
    (oldNeFinal : oldMarker ≠ final)
    (newNeFinal : newMarker ≠ final)
    (finalAbsent : final ∉ stem) :
    ∃ switchedStem,
      Derives targetBasis
        (terminalWord stem oldMarker final)
        (terminalWord switchedStem newMarker final) ∧
      newMarker ∈ switchedStem ∧ final ∉ switchedStem := by
  by_cases equal : newMarker = oldMarker
  · subst newMarker
    exact ⟨stem, Derives.refl _, oldMember, finalAbsent⟩
  · have newMember : newMarker ∈ stem :=
      newSupported.resolve_right equal
    have oldInErase : oldMarker ∈ stem.erase newMarker :=
      (List.mem_erase_of_ne (Ne.symm equal)).mpr oldMember
    let remainder := (stem.erase newMarker).erase oldMarker
    have arrangeFront : stem.Perm (newMarker :: oldMarker :: remainder) :=
      (List.perm_cons_erase newMember).trans <|
        List.Perm.cons newMarker <| by
          simpa [remainder] using List.perm_cons_erase oldInErase
    have arrange : stem.Perm (remainder ++ [newMarker, oldMarker]) :=
      arrangeFront.trans (permTwoToEnd newMarker oldMarker remainder)
    have arranged := derivesPrefixPermutation arrange oldMarker final
    have transfer := derivesPenultimateMarkerTransfer
      (Word.singleton newMarker)
      (Word.singleton oldMarker)
      (Word.singleton final)
    have prefixed :=
      SemigroupBasis.CoRoots.S5_107.ListDerives.prepend remainder
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord transfer)
    let switchedStem :=
      remainder ++ [oldMarker, oldMarker, newMarker, newMarker]
    have converted :
        Derives targetBasis
          (terminalWord (remainder ++ [newMarker, oldMarker])
            oldMarker final)
          (terminalWord switchedStem newMarker final) := by
      apply derivesOfListDerivesToList
      simpa [switchedStem,
        SemigroupBasis.CoRoots.S5_203.toList_terminalPairWord,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using prefixed
    refine ⟨switchedStem, arranged.trans converted, ?_, ?_⟩
    · simp [switchedStem]
    · simp [switchedStem, remainder, finalAbsent,
        Ne.symm oldNeFinal, Ne.symm newNeFinal]

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_203
