import SemigroupBasis.CoRoots.Order6FactorPairS2S5356Normal
import SemigroupBasis.CoRoots.S5_441ParityEnvelopeInteriorNormalize
import SemigroupBasis.CoRoots.S5_83Family
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Order6.FactorPairJoin

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_83

/-!
Unrestricted joint completeness for factor-pair family
`o6fp-f86c0cf5f9df6673`.

The `S5_83` factor classifies words by support and their longest globally
unique terminal suffix, capped at length two. The `S2_2` factor adds the
parity of every coordinate. The exact eight laws below provide a parity-safe
version of the `S5_83` normalization:

* `xxxyz = xyz` removes two prefix copies while two terminal blocks remain;
* `xxyx = xyyy` and `xyx = yxx` derive square-free prefix swaps;
* `xxyy = xyyx` and `xyx = yxx` transfer a repeated terminal marker without
  changing coordinate parity;
* `xx = xxxx` absorbs a redundant pair of a fixed repeated endpoint.

The remaining displayed laws are retained because this module proves
completeness for the exact ranked candidate, not a smaller equivalent list.
-/

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  { head := head, tail := tail }

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xyz : Word Nat := w 0 [1, 2]
def xxxyz : Word Nat := w 0 [0, 0, 1, 2]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyyy : Word Nat := w 0 [1, 1, 1]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xxyyy : Word Nat := w 0 [0, 1, 1, 1]
def xyx : Word Nat := w 0 [1, 0]
def xyyyx : Word Nat := w 0 [1, 1, 1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]

def powerLaw : Identity Nat := { lhs := xx, rhs := xxxx }
def longPrefixLaw : Identity Nat := { lhs := xxxyz, rhs := xyz }
def balanceLaw : Identity Nat := { lhs := xxyx, rhs := xyyy }
def squareFinalSwitchLaw : Identity Nat := { lhs := xxyy, rhs := xyyx }
def mixedContractionLaw : Identity Nat := { lhs := xxyyy, rhs := xyx }
def envelopePowerLaw : Identity Nat := { lhs := xyx, rhs := xyyyx }
def rotateLaw : Identity Nat := { lhs := xyx, rhs := yxx }
def closedInteriorSwapLaw : Identity Nat := { lhs := xyzx, rhs := xzyx }

/-- The exact ranked eight-law candidate for `S2_2 x S5_83`. -/
def basis : List (Identity Nat) :=
  [powerLaw, longPrefixLaw, balanceLaw, squareFinalSwitchLaw,
    mixedContractionLaw, envelopePowerLaw, rotateLaw,
    closedInteriorSwapLaw]

theorem basis_length : basis.length = 8 := by
  decide

private theorem retargetDerives
    {source target newSource newTarget : Word Nat}
    (derivation : Derives basis source target)
    (sourceToList : source.toList = newSource.toList)
    (targetToList : target.toList = newTarget.toList) :
    Derives basis newSource newTarget := by
  have sourceEq : source = newSource :=
    Word.toList_injective sourceToList
  have targetEq : target = newTarget :=
    Word.toList_injective targetToList
  cases sourceEq
  cases targetEq
  exact derivation

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
    Models SemigroupBasis.Generated.S2_2.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S2_2.table (by decide)

set_option maxHeartbeats 1000000 in
theorem modelsS5_83 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup basis :=
  modelsOfFiniteChecks
    SemigroupBasis.Generated.Catalogue.S5_83.table (by decide)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat -> Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

private theorem derivesBasisSubstitution
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat -> Word Nat) :
    Derives basis
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis member) substitution

theorem derivesFourToTwo (block : Word Nat) :
    Derives basis
      (((block ++ block) ++ block) ++ block)
      (block ++ block) := by
  have substituted :=
    derivesBasisSubstitution powerLaw (by simp [basis])
      (instantiateThreeWords block block block)
  simpa [powerLaw, xx, xxxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

/-- Remove two leading copies of a block while retaining two nonempty
trailing blocks. -/
theorem derivesLongPrefixContraction
    (block second third : Word Nat) :
    Derives basis
      ((((block ++ block) ++ block) ++ second) ++ third)
      ((block ++ second) ++ third) := by
  have substituted :=
    derivesBasisSubstitution longPrefixLaw (by simp [basis])
      (instantiateThreeWords block second third)
  simpa [longPrefixLaw, xxxyz, xyz, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesLongPrefixInsertion
    (block second third : Word Nat) :
    Derives basis
      ((block ++ second) ++ third)
      ((((block ++ block) ++ block) ++ second) ++ third) :=
  (derivesLongPrefixContraction block second third).symm

theorem derivesBalance (left right : Word Nat) :
    Derives basis
      (((left ++ left) ++ right) ++ left)
      (left ++ ((right ++ right) ++ right)) := by
  have substituted :=
    derivesBasisSubstitution balanceLaw (by simp [basis])
      (instantiateThreeWords left right right)
  simpa [balanceLaw, xxyx, xyyy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareFinalSwitch (left right : Word Nat) :
    Derives basis
      ((left ++ left) ++ (right ++ right))
      (((left ++ right) ++ right) ++ left) := by
  have substituted :=
    derivesBasisSubstitution squareFinalSwitchLaw (by simp [basis])
      (instantiateThreeWords left right right)
  simpa [squareFinalSwitchLaw, xxyy, xyyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesMixedContraction (left right : Word Nat) :
    Derives basis
      ((left ++ left) ++ ((right ++ right) ++ right))
      ((left ++ right) ++ left) := by
  have substituted :=
    derivesBasisSubstitution mixedContractionLaw (by simp [basis])
      (instantiateThreeWords left right right)
  simpa [mixedContractionLaw, xxyyy, xyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesEnvelopePower (envelope block : Word Nat) :
    Derives basis
      ((envelope ++ block) ++ envelope)
      ((((envelope ++ block) ++ block) ++ block) ++ envelope) := by
  have substituted :=
    derivesBasisSubstitution envelopePowerLaw (by simp [basis])
      (instantiateThreeWords envelope block block)
  simpa [envelopePowerLaw, xyx, xyyyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesRotate (left middle : Word Nat) :
    Derives basis
      ((left ++ middle) ++ left)
      ((middle ++ left) ++ left) := by
  have substituted :=
    derivesBasisSubstitution rotateLaw (by simp [basis])
      (instantiateThreeWords left middle middle)
  simpa [rotateLaw, xyx, yxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesClosedInteriorSwap
    (envelope left right : Word Nat) :
    Derives basis
      (((envelope ++ left) ++ right) ++ envelope)
      (((envelope ++ right) ++ left) ++ envelope) := by
  have substituted :=
    derivesBasisSubstitution closedInteriorSwapLaw (by simp [basis])
      (instantiateThreeWords envelope left right)
  simpa [closedInteriorSwapLaw, xyzx, xzyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- The square-free prefix swap is derived rather than listed separately. Insert a pair of the
second block, rebalance it against the first block, rotate twice, and remove
the exposed first-block pair. -/
theorem derivesOpenPrefixSwap
    (left right third fourth : Word Nat) :
    Derives basis
      (((left ++ right) ++ third) ++ fourth)
      (((right ++ left) ++ third) ++ fourth) := by
  have step1 :=
    Derives.prepend left
      (derivesLongPrefixInsertion right third fourth)
  have step2 :=
    Derives.appendRight
      (Derives.symm (derivesBalance left right))
      (third ++ fourth)
  have step3 :=
    Derives.appendRight
      (Derives.prepend left (derivesRotate left right))
      (third ++ fourth)
  have step4 :=
    Derives.appendRight
      (derivesRotate left right)
      ((left ++ third) ++ fourth)
  have step5 :=
    Derives.prepend right
      (derivesLongPrefixContraction left third fourth)
  simp only [Word.append_assoc] at step1 step2 step3 step4 step5 ⊢
  exact
    step1.trans <|
      step2.trans <|
        step3.trans <|
          step4.trans step5

/-- Transfer a repeated terminal marker from `oldMarker` to `newMarker`
without changing either support or coordinate parity:
`new old old = old old new new new`. -/
theorem derivesRepeatedMarkerTransfer
    (newMarker oldMarker : Word Nat) :
    Derives basis
      ((newMarker ++ oldMarker) ++ oldMarker)
      ((((oldMarker ++ oldMarker) ++ newMarker) ++ newMarker) ++
        newMarker) := by
  have step1 :=
    derivesLongPrefixInsertion newMarker oldMarker oldMarker
  have step2 :=
    Derives.prepend newMarker
      (derivesSquareFinalSwitch newMarker oldMarker)
  have step3 :=
    Derives.prepend newMarker
      (derivesRotate newMarker (oldMarker ++ oldMarker))
  have step4 :=
    Derives.appendRight
      (derivesRotate newMarker (oldMarker ++ oldMarker))
      newMarker
  simp only [Word.append_assoc] at step1 step2 step3 step4 ⊢
  exact
    step1.trans <|
      step2.trans <|
        step3.trans step4

/-- Every permutation of the stem before two fixed terminal letters is
derivable. -/
theorem derivesPrefixPermutation
    {left right : List Nat}
    (permutation : left.Perm right)
    (penultimate final : Nat) :
    Derives basis
      (wordOfTerminalPair left penultimate final)
      (wordOfTerminalPair right penultimate final) := by
  induction permutation with
  | nil =>
      exact Derives.refl _
  | cons head _ ih =>
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        List.append_assoc] using
        Derives.prepend (Word.singleton head) ih
  | swap left right suffix =>
      simpa [wordOfTerminalPair, wordOfPrefixFinal,
        Word.append_assoc, List.append_assoc] using
        derivesOpenPrefixSwap
          (Word.singleton right) (Word.singleton left)
          (wordOfPrefixFinal suffix penultimate)
          (Word.singleton final)
  | trans _ _ first second =>
      exact first.trans second

private theorem derivesContractLeadingTriple
    (letter : Nat) (rest : List Nat)
    (penultimate final : Nat) :
    Derives basis
      (wordOfTerminalPair
        (letter :: letter :: letter :: rest) penultimate final)
      (wordOfTerminalPair
        (letter :: rest) penultimate final) := by
  have raw :=
    derivesLongPrefixContraction
      (Word.singleton letter)
      (wordOfPrefixFinal rest penultimate)
      (Word.singleton final)
  apply retargetDerives raw
  · rw [toList_wordOfTerminalPair]
    simp [Word.toList, List.append_assoc]
    simpa only [List.append_assoc, List.singleton_append] using
      congrArg (fun letters => letters ++ [final])
        (toList_wordOfPrefixFinal rest penultimate)
  · rw [toList_wordOfTerminalPair]
    simp [Word.toList, List.append_assoc]
    simpa only [List.append_assoc, List.singleton_append] using
      congrArg (fun letters => letters ++ [final])
        (toList_wordOfPrefixFinal rest penultimate)

private theorem derivesDeleteThirdPrefixCopy
    (letter : Nat) (before reduced : List Nat)
    (penultimate final : Nat)
    (countEq : reduced.count letter = 2) :
    Derives basis
      (wordOfTerminalPair
        (before ++ letter :: reduced) penultimate final)
      (wordOfTerminalPair
        (before ++ reduced.erase letter) penultimate final) := by
  let remainder := (reduced.erase letter).erase letter
  have firstErase : (reduced.erase letter).count letter = 1 := by
    rw [List.count_erase_self, countEq]
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
      simp [countEq, secondErase]
    · simp [remainder, equal, Ne.symm equal]
  have eraseHasLetter : letter ∈ reduced.erase letter :=
    List.count_pos_iff.mp (by omega)
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
    forall (before stem : List Nat) (penultimate final : Nat),
      Derives basis
        (wordOfTerminalPair (before ++ stem) penultimate final)
        (wordOfTerminalPair
          (before ++ positiveParityReduce stem) penultimate final)
  | before, [], penultimate, final =>
      Derives.refl _
  | before, letter :: rest, penultimate, final => by
      have suffixNormal :=
        derivesNormalizePrefixAux
          (before ++ [letter]) rest penultimate final
      let reduced := positiveParityReduce rest
      have firstStep :
          Derives basis
            (wordOfTerminalPair
              (before ++ letter :: rest) penultimate final)
            (wordOfTerminalPair
              (before ++ letter :: reduced) penultimate final) := by
        simpa [reduced, List.append_assoc] using suffixNormal
      by_cases countLt : reduced.count letter < 2
      · have reducedEq :
            positiveParityReduce (letter :: rest) =
              letter :: reduced := by
          simp [positiveParityReduce, reduced, countLt]
        rw [reducedEq]
        exact firstStep
      · have countLe : reduced.count letter <= 2 := by
          simpa [reduced] using
            positiveParityReduce_count_le_two letter rest
        have countEq : reduced.count letter = 2 := by
          omega
        have reducedEq :
            positiveParityReduce (letter :: rest) =
              reduced.erase letter := by
          simp [positiveParityReduce, reduced, countLt]
        rw [reducedEq]
        exact firstStep.trans <|
          derivesDeleteThirdPrefixCopy
            letter before reduced penultimate final countEq
termination_by
  _ stem _ _ => stem.length

/-- Normalize every stem multiplicity to one copy when odd and two copies
when positive even, while retaining the terminal pair literally. -/
theorem derivesNormalizePrefix
    (stem : List Nat) (penultimate final : Nat) :
    Derives basis
      (wordOfTerminalPair stem penultimate final)
      (wordOfTerminalPair
        (positiveParityReduce stem) penultimate final) := by
  simpa using
    derivesNormalizePrefixAux [] stem penultimate final

private abbrev fixedEndpointParityReduce :=
  SemigroupBasis.CoRoots.S5_441.fixedEndpointParityReduce

private theorem derivesRemoveRepeatedEndpointPair
    (endpoint : Nat) (reduced : List Nat)
    (countEq : reduced.count endpoint = 2) :
    Derives basis
      (wordOfTerminalPair reduced endpoint endpoint)
      (wordOfTerminalPair
        ((reduced.erase endpoint).erase endpoint)
        endpoint endpoint) := by
  let remainder := (reduced.erase endpoint).erase endpoint
  have firstErase : (reduced.erase endpoint).count endpoint = 1 := by
    rw [List.count_erase_self, countEq]
  have secondErase : remainder.count endpoint = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, firstErase]
  have arrange :
      reduced.Perm (remainder ++ [endpoint, endpoint]) := by
    rw [List.perm_iff_count]
    intro tested
    by_cases equal : tested = endpoint
    · subst tested
      simp [remainder, countEq, firstErase, secondErase]
    · simp [remainder, equal, Ne.symm equal]
  have arranged :=
    derivesPrefixPermutation arrange endpoint endpoint
  have contract :
      Derives basis
        (wordOfTerminalPair
          (remainder ++ [endpoint, endpoint]) endpoint endpoint)
        (wordOfTerminalPair remainder endpoint endpoint) := by
    cases remainder with
    | nil =>
        simpa [wordOfTerminalPair, wordOfPrefixFinal,
          Word.append_assoc] using
          derivesFourToTwo (Word.singleton endpoint)
    | cons head tail =>
        have prefixed :=
          Derives.prepend (w head tail)
            (derivesFourToTwo (Word.singleton endpoint))
        apply retargetDerives prefixed
        · rw [toList_wordOfTerminalPair]
          simp [w, Word.toList, List.append_assoc]
        · rw [toList_wordOfTerminalPair]
          simp [w, Word.toList, List.append_assoc]
  simpa [remainder] using arranged.trans contract

/-- If both terminal letters are the same fixed endpoint, an additional
pair of that endpoint in the stem is redundant. Other positive
multiplicities retain the usual one-or-two parity representative. -/
theorem derivesNormalizeRepeatedEndpoint
    (stem : List Nat) (endpoint : Nat) :
    Derives basis
      (wordOfTerminalPair stem endpoint endpoint)
      (wordOfTerminalPair
        (fixedEndpointParityReduce endpoint stem)
        endpoint endpoint) := by
  have positiveNormal :=
    derivesNormalizePrefix stem endpoint endpoint
  by_cases countEq :
      (positiveParityReduce stem).count endpoint = 2
  · have remove :=
      derivesRemoveRepeatedEndpointPair
        endpoint (positiveParityReduce stem) countEq
    simpa [fixedEndpointParityReduce,
      SemigroupBasis.CoRoots.S5_441.fixedEndpointParityReduce,
      countEq] using
      positiveNormal.trans remove
  · simpa [fixedEndpointParityReduce,
      SemigroupBasis.CoRoots.S5_441.fixedEndpointParityReduce,
      countEq] using positiveNormal

private theorem prefixParityOfRenderedParity
    {left right : List Nat} (penultimate final : Nat)
    (parity :
      forall z,
        (left ++ [penultimate, final]).count z % 2 =
          (right ++ [penultimate, final]).count z % 2) :
    forall z, left.count z % 2 = right.count z % 2 := by
  intro tested
  have whole := parity tested
  simp only [List.count_append] at whole
  omega

private theorem positiveReductionsPermOfRenderedInvariants
    {left right : List Nat} (penultimate final : Nat)
    (support :
      forall z,
        z ∈ left ++ [penultimate, final] <->
          z ∈ right ++ [penultimate, final])
    (parity :
      forall z,
        (left ++ [penultimate, final]).count z % 2 =
          (right ++ [penultimate, final]).count z % 2)
    (penultimateMember :
      penultimate ∈ left <-> penultimate ∈ right)
    (finalMember : final ∈ left <-> final ∈ right) :
    (positiveParityReduce left).Perm
      (positiveParityReduce right) := by
  apply positiveParityReduce_perm
  · intro tested
    by_cases testedPenultimate : tested = penultimate
    · subst tested
      exact penultimateMember
    · by_cases testedFinal : tested = final
      · subst tested
        exact finalMember
      · have whole := support tested
        simpa [testedPenultimate, testedFinal,
          Ne.symm testedPenultimate, Ne.symm testedFinal] using whole
  · exact prefixParityOfRenderedParity penultimate final parity

private theorem derivesAlignedTerminalPair
    (left right : List Nat) (penultimate final : Nat)
    (support :
      forall z,
        z ∈ left ++ [penultimate, final] <->
          z ∈ right ++ [penultimate, final])
    (parity :
      forall z,
        (left ++ [penultimate, final]).count z % 2 =
          (right ++ [penultimate, final]).count z % 2)
    (penultimateMember :
      penultimate ∈ left <-> penultimate ∈ right)
    (finalMember : final ∈ left <-> final ∈ right) :
    Derives basis
      (wordOfTerminalPair left penultimate final)
      (wordOfTerminalPair right penultimate final) := by
  have leftNormal :=
    derivesNormalizePrefix left penultimate final
  have rightNormal :=
    derivesNormalizePrefix right penultimate final
  have reducedPermutation :=
    positiveReductionsPermOfRenderedInvariants
      penultimate final support parity
      penultimateMember finalMember
  have middle :=
    derivesPrefixPermutation
      reducedPermutation penultimate final
  exact leftNormal.trans (middle.trans rightNormal.symm)

private theorem derivesAlignedRepeatedEndpoint
    (left right : List Nat) (endpoint : Nat)
    (support :
      forall z,
        z ∈ left ++ [endpoint, endpoint] <->
          z ∈ right ++ [endpoint, endpoint])
    (parity :
      forall z,
        (left ++ [endpoint, endpoint]).count z % 2 =
          (right ++ [endpoint, endpoint]).count z % 2) :
    Derives basis
      (wordOfTerminalPair left endpoint endpoint)
      (wordOfTerminalPair right endpoint endpoint) := by
  have stemSupport :
      forall z, z ≠ endpoint -> (z ∈ left <-> z ∈ right) := by
    intro tested different
    have whole := support tested
    simpa [different, Ne.symm different] using whole
  have stemParity :
      forall z, left.count z % 2 = right.count z % 2 :=
    prefixParityOfRenderedParity endpoint endpoint parity
  have reducedPermutation :=
    SemigroupBasis.CoRoots.S5_441.fixedEndpointParityReduce_perm
      stemSupport stemParity
  have leftNormal :=
    derivesNormalizeRepeatedEndpoint left endpoint
  have rightNormal :=
    derivesNormalizeRepeatedEndpoint right endpoint
  have middle :=
    derivesPrefixPermutation
      reducedPermutation endpoint endpoint
  exact leftNormal.trans (middle.trans rightNormal.symm)

private theorem permConsToEnd (letter : Nat) :
    forall rest : List Nat,
      (letter :: rest).Perm (rest ++ [letter])
  | [] => List.Perm.refl _
  | head :: tail =>
      (List.Perm.swap head letter tail).trans <|
        List.Perm.cons head (permConsToEnd letter tail)

private theorem permTwoToEnd (first second : Nat) :
    forall rest : List Nat,
      (first :: second :: rest).Perm
        (rest ++ [first, second])
  | [] => List.Perm.refl _
  | head :: tail =>
      (List.Perm.cons first
        (List.Perm.swap head second tail)).trans <|
        (List.Perm.swap head first (second :: tail)).trans <|
          List.Perm.cons head
            (permTwoToEnd first second tail)

private theorem derivesOfListDerivesToList
    (left right : Word Nat)
    (derivation :
      SemigroupBasis.CoRoots.S5_107.ListDerives
        basis left.toList right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord derivation

private theorem listPrefixMarkerTransfer
    (pref : List Nat) (newMarker oldMarker : Nat) :
    Derives basis
      (wordOfPrefixFinal
        (pref ++ [newMarker, oldMarker]) oldMarker)
      (wordOfPrefixFinal
        (pref ++ [oldMarker, oldMarker,
          newMarker, newMarker]) newMarker) := by
  have transfer :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesRepeatedMarkerTransfer
        (Word.singleton newMarker) (Word.singleton oldMarker))
  have prefixed :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.prepend pref transfer
  exact
    derivesOfListDerivesToList
      (wordOfPrefixFinal (pref ++ [newMarker, oldMarker]) oldMarker)
      (wordOfPrefixFinal
        (pref ++ [oldMarker, oldMarker, newMarker, newMarker]) newMarker) <| by
      simpa [toList_wordOfPrefixFinal,
        List.append_assoc] using prefixed

/-- Turn any repeated final variable into a literal repeated terminal pair. -/
private theorem derivesMakeRepeatedFinal
    (stem : List Nat) (penultimate final : Nat)
    (repeated :
      final = penultimate ∨ final ∈ stem) :
    exists repeatedStem,
      Derives basis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair repeatedStem final final) := by
  rcases repeated with equal | finalMember
  · subst penultimate
    exact ⟨stem, Derives.refl _⟩
  · by_cases equal : final = penultimate
    · subst penultimate
      exact ⟨stem, Derives.refl _⟩
    · have arrange :
          stem.Perm (stem.erase final ++ [final]) :=
        (List.perm_cons_erase finalMember).trans <|
          permConsToEnd final (stem.erase final)
      have arranged :=
        derivesPrefixPermutation arrange penultimate final
      have rotatedList :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.prepend
          (stem.erase final)
          (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
            (derivesRotate
              (Word.singleton final)
              (Word.singleton penultimate)))
      have rotated :=
        derivesOfListDerivesToList
          (wordOfTerminalPair
            (stem.erase final ++ [final]) penultimate final)
          (wordOfTerminalPair
            (stem.erase final ++ [penultimate]) final final) <| by
          simpa [toList_wordOfTerminalPair,
            List.append_assoc] using rotatedList
      exact
        ⟨stem.erase final ++ [penultimate],
          arranged.trans rotated⟩

/-- Once the final marker is literally repeated, switch it to any other
supported marker while retaining coordinate parity. -/
private theorem derivesSwitchRepeatedFinal
    (stem : List Nat) (oldMarker newMarker : Nat)
    (newSupported : newMarker ∈ stem ∨ newMarker = oldMarker) :
    exists switchedStem,
      Derives basis
        (wordOfTerminalPair stem oldMarker oldMarker)
        (wordOfTerminalPair switchedStem newMarker newMarker) := by
  by_cases equal : newMarker = oldMarker
  · subst newMarker
    exact ⟨stem, Derives.refl _⟩
  · have newMember : newMarker ∈ stem :=
      newSupported.resolve_right equal
    have arrange :
        stem.Perm (stem.erase newMarker ++ [newMarker]) :=
      (List.perm_cons_erase newMember).trans <|
        permConsToEnd newMarker (stem.erase newMarker)
    have arranged :=
      derivesPrefixPermutation arrange oldMarker oldMarker
    have switched :=
      listPrefixMarkerTransfer
        (stem.erase newMarker) newMarker oldMarker
    refine
      ⟨stem.erase newMarker ++
          [oldMarker, oldMarker, newMarker],
        arranged.trans ?_⟩
    simpa [wordOfTerminalPair, wordOfPrefixFinal,
      List.append_assoc] using switched

/-- Switch a repeated penultimate variable while retaining a globally unique
final variable. The returned stem contains the new marker twice. -/
private theorem derivesSwitchRepeatedPenultimate
    (stem : List Nat) (oldMarker newMarker final : Nat)
    (oldMember : oldMarker ∈ stem)
    (newSupported :
      newMarker ∈ stem ∨ newMarker = oldMarker)
    (oldNeFinal : oldMarker ≠ final)
    (newNeFinal : newMarker ≠ final)
    (finalAbsent : final ∉ stem) :
    exists switchedStem,
      Derives basis
        (wordOfTerminalPair stem oldMarker final)
        (wordOfTerminalPair switchedStem newMarker final) ∧
      newMarker ∈ switchedStem ∧
      final ∉ switchedStem := by
  by_cases equal : newMarker = oldMarker
  · subst newMarker
    exact ⟨stem, Derives.refl _, oldMember, finalAbsent⟩
  · have newMember : newMarker ∈ stem :=
      newSupported.resolve_right equal
    have oldInErase :
        oldMarker ∈ stem.erase newMarker := by
      exact (List.mem_erase_of_ne (Ne.symm equal)).mpr oldMember
    let remainder := (stem.erase newMarker).erase oldMarker
    have arrangeFront :
        stem.Perm (newMarker :: oldMarker :: remainder) := by
      exact (List.perm_cons_erase newMember).trans <|
        List.Perm.cons newMarker <| by
          simpa [remainder] using
            List.perm_cons_erase oldInErase
    have arrange :
        stem.Perm (remainder ++ [newMarker, oldMarker]) :=
      arrangeFront.trans <|
        permTwoToEnd newMarker oldMarker remainder
    have arranged :=
      derivesPrefixPermutation arrange oldMarker final
    have transferWithFinal :=
      Derives.appendRight
        (derivesRepeatedMarkerTransfer
          (Word.singleton newMarker)
          (Word.singleton oldMarker))
        (Word.singleton final)
    have prefixedTransferList :=
      SemigroupBasis.CoRoots.S5_107.ListDerives.prepend remainder
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          transferWithFinal)
    have prefixedTransfer :=
      derivesOfListDerivesToList
        (wordOfTerminalPair
          (remainder ++ [newMarker, oldMarker]) oldMarker final)
        (wordOfTerminalPair
          (remainder ++ [oldMarker, oldMarker, newMarker, newMarker])
            newMarker final) <| by
        simpa [toList_wordOfTerminalPair,
          List.append_assoc] using prefixedTransferList
    let switchedStem :=
      remainder ++ [oldMarker, oldMarker, newMarker, newMarker]
    refine ⟨switchedStem, arranged.trans ?_, ?_⟩
    · simpa [switchedStem] using prefixedTransfer
    · constructor
      · simp [switchedStem]
      · simp [switchedStem, remainder, finalAbsent,
          Ne.symm oldNeFinal, Ne.symm newNeFinal]

private theorem signatureOfDerivation
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    SameTerminalUniqueSuffixSignature left right := by
  let identity : Identity Nat := { lhs := left, rhs := right }
  have valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup := by
    intro valuation
    exact derivation.sound modelsS5_83 valuation
  exact
    SemigroupBasis.CoRoots.S5_83Factors.S5_83.valid_signature
      identity valid

private theorem parityOfTableValid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup) :
    forall tested,
      identity.lhs.toList.count tested % 2 =
        identity.rhs.toList.count tested % 2 := by
  have cyclicValid :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    rw [← SemigroupBasis.Generated.S2_2.table_eq_catalogue_model]
    exact valid
  exact cyclicValid_parity_eq identity cyclicValid

private theorem satisfiedAfterDerivations
    {carrier : Type}
    {semigroup : Semigroup carrier}
    (models : Models semigroup basis)
    {sourceLeft sourceRight targetLeft targetRight : Word Nat}
    (valid :
      ({ lhs := sourceLeft, rhs := sourceRight } :
        Identity Nat).SatisfiedBy semigroup)
    (leftDerivation : Derives basis sourceLeft targetLeft)
    (rightDerivation : Derives basis sourceRight targetRight) :
    ({ lhs := targetLeft, rhs := targetRight } :
      Identity Nat).SatisfiedBy semigroup := by
  intro valuation
  have leftSound := leftDerivation.sound models valuation
  have rightSound := rightDerivation.sound models valuation
  exact leftSound.symm.trans ((valid valuation).trans rightSound)

private theorem transformedSupportAndParity
    {sourceLeft sourceRight targetLeft targetRight : Word Nat}
    (s5Valid :
      ({ lhs := sourceLeft, rhs := sourceRight } :
        Identity Nat).SatisfiedBy
          SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup)
    (cyclicValid :
      ({ lhs := sourceLeft, rhs := sourceRight } :
        Identity Nat).SatisfiedBy
          SemigroupBasis.Generated.S2_2.table.semigroup)
    (leftDerivation : Derives basis sourceLeft targetLeft)
    (rightDerivation : Derives basis sourceRight targetRight) :
    SameSupport targetLeft targetRight ∧
      (forall tested,
        targetLeft.toList.count tested % 2 =
          targetRight.toList.count tested % 2) := by
  let targetIdentity : Identity Nat :=
    { lhs := targetLeft, rhs := targetRight }
  have targetS5Valid :
      targetIdentity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup :=
    satisfiedAfterDerivations
      modelsS5_83 s5Valid leftDerivation rightDerivation
  have targetCyclicValid :
      targetIdentity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup :=
    satisfiedAfterDerivations
      modelsS2_2 cyclicValid leftDerivation rightDerivation
  have targetSignature :=
    SemigroupBasis.CoRoots.S5_83Factors.S5_83.valid_signature
      targetIdentity targetS5Valid
  exact
    ⟨targetSignature.support,
      parityOfTableValid targetIdentity targetCyclicValid⟩

private theorem terminalPairHeadMember
    (stem : List Nat) (penultimate final : Nat) :
    (wordOfTerminalPair stem penultimate final).head ∈
      (wordOfTerminalPair stem penultimate final).toList := by
  simp [Word.toList]

private theorem terminalPairHeadSupportedBeforeFinal
    (stem : List Nat) (penultimate final : Nat) :
    (wordOfTerminalPair stem penultimate final).head ∈ stem ∨
      (wordOfTerminalPair stem penultimate final).head = penultimate := by
  cases stem with
  | nil =>
      simp [wordOfTerminalPair, wordOfPrefixFinal]
  | cons head tail =>
      simp [wordOfTerminalPair, wordOfPrefixFinal]

private theorem terminalPairHeadNeFinal
    (stem : List Nat) (penultimate final : Nat)
    (finalNePenultimate : final ≠ penultimate)
    (finalAbsent : final ∉ stem) :
    (wordOfTerminalPair stem penultimate final).head ≠ final := by
  intro equal
  rcases terminalPairHeadSupportedBeforeFinal
      stem penultimate final with member | penultimateEq
  · exact finalAbsent (equal ▸ member)
  · exact finalNePenultimate (equal.symm.trans penultimateEq)

/-- Every identity over an arbitrary `Nat` alphabet that is valid in both
`S2_2` and `S5_83` follows from the exact ranked eight-law candidate. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  classical
  have same :=
    SemigroupBasis.CoRoots.S5_83Factors.S5_83.valid_signature
      identity s5Valid
  have leftReconstruct := terminalSplit_renderWord identity.lhs
  have rightReconstruct := terminalSplit_renderWord identity.rhs
  cases leftSplitEq : terminalSplit identity.lhs with
  | singleton leftFinal =>
      cases rightSplitEq : terminalSplit identity.rhs with
      | singleton rightFinal =>
          have rightUnique :
              UniqueFinal identity.rhs leftFinal :=
            (same.uniqueFinal leftFinal).mp <| by
              simp [UniqueFinal, leftSplitEq]
          have finals : rightFinal = leftFinal := by
            simpa [UniqueFinal, rightSplitEq] using rightUnique
          subst rightFinal
          rw [leftSplitEq] at leftReconstruct
          rw [rightSplitEq] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct]
          exact Derives.refl _
      | pair rightStem rightPenultimate rightFinal =>
          have leftSingleton : IsSingletonWord identity.lhs := by
            simp [IsSingletonWord, leftSplitEq]
          have rightSingleton := same.singleton.mp leftSingleton
          simp [IsSingletonWord, rightSplitEq] at rightSingleton
  | pair leftStem leftPenultimate leftFinal =>
      cases rightSplitEq : terminalSplit identity.rhs with
      | singleton rightFinal =>
          have rightSingleton : IsSingletonWord identity.rhs := by
            simp [IsSingletonWord, rightSplitEq]
          have leftSingleton := same.singleton.mpr rightSingleton
          simp [IsSingletonWord, leftSplitEq] at leftSingleton
      | pair rightStem rightPenultimate rightFinal =>
          rw [leftSplitEq] at leftReconstruct
          rw [rightSplitEq] at rightReconstruct
          let leftWord :=
            wordOfTerminalPair leftStem leftPenultimate leftFinal
          let rightWord :=
            wordOfTerminalPair rightStem rightPenultimate rightFinal
          let renderedIdentity : Identity Nat :=
            { lhs := leftWord, rhs := rightWord }
          have renderedS5Valid :
              renderedIdentity.SatisfiedBy
                SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup := by
            intro valuation
            dsimp only [renderedIdentity, leftWord, rightWord]
            have valid := s5Valid valuation
            rw [← leftReconstruct, ← rightReconstruct] at valid
            simpa only [terminalSplit_pair_renderWord] using valid
          have renderedCyclicValid :
              renderedIdentity.SatisfiedBy
                SemigroupBasis.Generated.S2_2.table.semigroup := by
            intro valuation
            dsimp only [renderedIdentity, leftWord, rightWord]
            have valid := cyclicValid valuation
            rw [← leftReconstruct, ← rightReconstruct] at valid
            simpa only [terminalSplit_pair_renderWord] using valid
          have renderedSignature :=
            SemigroupBasis.CoRoots.S5_83Factors.S5_83.valid_signature
              renderedIdentity renderedS5Valid
          have renderedParity :=
            parityOfTableValid renderedIdentity renderedCyclicValid
          rw [← leftReconstruct, ← rightReconstruct]
          change Derives basis leftWord rightWord
          by_cases leftFinalRepeated :
              leftFinal = leftPenultimate ∨
                leftFinal ∈ leftStem
          · have rightFinalRepeated :
                rightFinal = rightPenultimate ∨
                  rightFinal ∈ rightStem := by
              apply Decidable.byContradiction
              intro rightNotRepeated
              have rightParts := not_or.mp rightNotRepeated
              have rightUnique :
                  UniqueFinal identity.rhs rightFinal := by
                simp [UniqueFinal, rightSplitEq,
                  rightParts.1, rightParts.2]
              have leftUnique :=
                (same.uniqueFinal rightFinal).mpr rightUnique
              have leftParts :
                  leftFinal = rightFinal ∧
                    leftFinal ≠ leftPenultimate ∧
                    leftFinal ∉ leftStem := by
                simpa [UniqueFinal, leftSplitEq] using leftUnique
              rcases leftFinalRepeated with equal | member
              · exact leftParts.2.1 equal
              · exact leftParts.2.2 member
            let marker := leftWord.head
            have markerInLeft : marker ∈ leftWord.toList := by
              exact terminalPairHeadMember
                leftStem leftPenultimate leftFinal
            have markerInRight : marker ∈ rightWord.toList :=
              (renderedSignature.support marker).mp markerInLeft
            obtain ⟨leftRepeatedStem, leftMake⟩ :=
              derivesMakeRepeatedFinal
                leftStem leftPenultimate leftFinal leftFinalRepeated
            obtain ⟨rightRepeatedStem, rightMake⟩ :=
              derivesMakeRepeatedFinal
                rightStem rightPenultimate rightFinal rightFinalRepeated
            have markerInLeftRepeated :
                marker ∈ leftRepeatedStem ∨ marker = leftFinal := by
              have transformed :=
                (signatureOfDerivation leftMake).support marker
              have targetMember := transformed.mp markerInLeft
              simpa [List.mem_append, or_assoc] using targetMember
            have markerInRightRepeated :
                marker ∈ rightRepeatedStem ∨ marker = rightFinal := by
              have transformed :=
                (signatureOfDerivation rightMake).support marker
              have targetMember := transformed.mp markerInRight
              simpa [List.mem_append, or_assoc] using targetMember
            obtain ⟨leftSwitchedStem, leftSwitch⟩ :=
              derivesSwitchRepeatedFinal
                leftRepeatedStem leftFinal marker
                markerInLeftRepeated
            obtain ⟨rightSwitchedStem, rightSwitch⟩ :=
              derivesSwitchRepeatedFinal
                rightRepeatedStem rightFinal marker
                markerInRightRepeated
            have leftTransform :
                Derives basis leftWord
                  (wordOfTerminalPair
                    leftSwitchedStem marker marker) :=
              leftMake.trans leftSwitch
            have rightTransform :
                Derives basis rightWord
                  (wordOfTerminalPair
                    rightSwitchedStem marker marker) :=
              rightMake.trans rightSwitch
            have transformed :=
              transformedSupportAndParity
                renderedS5Valid renderedCyclicValid
                leftTransform rightTransform
            have targetSupport :
                forall tested,
                  tested ∈ leftSwitchedStem ++ [marker, marker] <->
                    tested ∈ rightSwitchedStem ++ [marker, marker] := by
              intro tested
              simpa using transformed.1 tested
            have targetParity :
                forall tested,
                  (leftSwitchedStem ++ [marker, marker]).count tested % 2 =
                    (rightSwitchedStem ++
                      [marker, marker]).count tested % 2 := by
              intro tested
              simpa using transformed.2 tested
            have middle :=
              derivesAlignedRepeatedEndpoint
                leftSwitchedStem rightSwitchedStem marker
                targetSupport targetParity
            exact
              leftTransform.trans <|
                middle.trans rightTransform.symm
          · have leftFinalParts := not_or.mp leftFinalRepeated
            have leftUnique :
                UniqueFinal identity.lhs leftFinal := by
              simp [UniqueFinal, leftSplitEq,
                leftFinalParts.1, leftFinalParts.2]
            have rightUnique :=
              (same.uniqueFinal leftFinal).mp leftUnique
            have rightFinalParts :
                rightFinal = leftFinal ∧
                  rightFinal ≠ rightPenultimate ∧
                  rightFinal ∉ rightStem := by
              simpa [UniqueFinal, rightSplitEq] using rightUnique
            have rightFinalEq : rightFinal = leftFinal :=
              rightFinalParts.1
            subst rightFinal
            by_cases leftPenultimateRepeated :
                leftPenultimate ∈ leftStem
            · have rightPenultimateRepeated :
                  rightPenultimate ∈ rightStem := by
                apply Decidable.byContradiction
                intro rightPenultimateUnique
                have rightPair :
                    UniqueTerminalPair identity.rhs
                      rightPenultimate leftFinal := by
                  simp [UniqueTerminalPair, rightSplitEq,
                    rightPenultimateUnique,
                    rightFinalParts.2.1,
                    rightFinalParts.2.2]
                have leftPair :=
                  (same.uniqueTerminalPair
                    rightPenultimate leftFinal).mpr rightPair
                have leftPairParts :
                    leftPenultimate = rightPenultimate ∧
                      leftFinal = leftFinal ∧
                      rightPenultimate ∉ leftStem ∧
                      leftFinal ≠ rightPenultimate ∧
                      leftFinal ∉ leftStem := by
                  simpa [UniqueTerminalPair, leftSplitEq] using leftPair
                exact leftPairParts.2.2.1 <| by
                  simpa [leftPairParts.1] using
                    leftPenultimateRepeated
              let marker := leftWord.head
              have markerInLeft : marker ∈ leftWord.toList := by
                exact terminalPairHeadMember
                  leftStem leftPenultimate leftFinal
              have markerInRight : marker ∈ rightWord.toList :=
                (renderedSignature.support marker).mp markerInLeft
              have markerNeFinal : marker ≠ leftFinal := by
                exact terminalPairHeadNeFinal
                  leftStem leftPenultimate leftFinal
                  leftFinalParts.1 leftFinalParts.2
              have markerSupportedLeft :
                  marker ∈ leftStem ∨ marker = leftPenultimate :=
                terminalPairHeadSupportedBeforeFinal
                  leftStem leftPenultimate leftFinal
              have markerSupportedRight :
                  marker ∈ rightStem ∨ marker = rightPenultimate := by
                simpa [rightWord, List.mem_append, markerNeFinal,
                  Ne.symm markerNeFinal, or_assoc] using markerInRight
              obtain
                  ⟨leftSwitchedStem, leftTransform,
                    leftMarkerMember, leftFinalAbsent⟩ :=
                derivesSwitchRepeatedPenultimate
                  leftStem leftPenultimate marker leftFinal
                  leftPenultimateRepeated markerSupportedLeft
                  (Ne.symm leftFinalParts.1) markerNeFinal
                  leftFinalParts.2
              obtain
                  ⟨rightSwitchedStem, rightTransform,
                    rightMarkerMember, rightFinalAbsent⟩ :=
                derivesSwitchRepeatedPenultimate
                  rightStem rightPenultimate marker leftFinal
                  rightPenultimateRepeated markerSupportedRight
                  (Ne.symm rightFinalParts.2.1) markerNeFinal
                  rightFinalParts.2.2
              have transformed :=
                transformedSupportAndParity
                  renderedS5Valid renderedCyclicValid
                  leftTransform rightTransform
              have targetSupport :
                  forall tested,
                    tested ∈
                        leftSwitchedStem ++ [marker, leftFinal] <->
                      tested ∈
                        rightSwitchedStem ++ [marker, leftFinal] := by
                intro tested
                simpa using transformed.1 tested
              have targetParity :
                  forall tested,
                    (leftSwitchedStem ++
                        [marker, leftFinal]).count tested % 2 =
                      (rightSwitchedStem ++
                        [marker, leftFinal]).count tested % 2 := by
                intro tested
                simpa using transformed.2 tested
              have middle :=
                derivesAlignedTerminalPair
                  leftSwitchedStem rightSwitchedStem
                  marker leftFinal targetSupport targetParity
                  ⟨fun _ => rightMarkerMember,
                    fun _ => leftMarkerMember⟩
                  ⟨fun member =>
                      False.elim (leftFinalAbsent member),
                    fun member =>
                      False.elim (rightFinalAbsent member)⟩
              exact
                leftTransform.trans <|
                  middle.trans rightTransform.symm
            · have leftPair :
                  UniqueTerminalPair identity.lhs
                    leftPenultimate leftFinal := by
                simp [UniqueTerminalPair, leftSplitEq,
                  leftPenultimateRepeated,
                  leftFinalParts.1, leftFinalParts.2]
              have rightPair :=
                (same.uniqueTerminalPair
                  leftPenultimate leftFinal).mp leftPair
              have rightPairParts :
                  rightPenultimate = leftPenultimate ∧
                    leftFinal = leftFinal ∧
                    leftPenultimate ∉ rightStem ∧
                    leftFinal ≠ leftPenultimate ∧
                    leftFinal ∉ rightStem := by
                simpa [UniqueTerminalPair, rightSplitEq] using rightPair
              have rightPenultimateEq :
                  rightPenultimate = leftPenultimate :=
                rightPairParts.1
              subst rightPenultimate
              have targetSupport :
                  forall tested,
                    tested ∈
                        leftStem ++ [leftPenultimate, leftFinal] <->
                      tested ∈
                        rightStem ++ [leftPenultimate, leftFinal] := by
                intro tested
                simpa [renderedIdentity, leftWord, rightWord] using
                  renderedSignature.support tested
              have targetParity :
                  forall tested,
                    (leftStem ++
                        [leftPenultimate, leftFinal]).count tested % 2 =
                      (rightStem ++
                        [leftPenultimate, leftFinal]).count tested % 2 := by
                intro tested
                simpa [renderedIdentity, leftWord, rightWord] using
                  renderedParity tested
              exact
                derivesAlignedTerminalPair
                  leftStem rightStem leftPenultimate leftFinal
                  targetSupport targetParity
                  ⟨fun member =>
                      False.elim (leftPenultimateRepeated member),
                    fun member =>
                      False.elim
                        (rightPairParts.2.2.1 member)⟩
                  ⟨fun member =>
                      False.elim (leftFinalParts.2 member),
                    fun member =>
                      False.elim
                        (rightPairParts.2.2.2.2 member)⟩

/-- Unrestricted finite basis theorem for
`V(S2_2) ∩ V(S5_83)`. -/
def factorIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup basis where
  leftModels := modelsS2_2
  rightModels := modelsS5_83
  complete := derivesOfFactorValid

abbrev intersectionBasis := factorIntersectionBasis

end SemigroupBasis.CoRoots.Order6FactorPairS2S583Normal
