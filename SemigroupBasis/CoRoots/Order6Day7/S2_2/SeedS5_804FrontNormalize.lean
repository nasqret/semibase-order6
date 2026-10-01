import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_804FrontEnvelope
import SemigroupBasis.CoRoots.S5_442ParityEnvelopeNormalize
import SemigroupBasis.Examples.CommutativeParityThree

/-!
# Fixed-endpoint parity normalization for the exact reversed rank092 basis

The derivational architecture follows S5_442, but its endpoint-changing
xyx=yxyxy helper is NOT imported as a target law. The needed interior cube
contraction is proved here by three exact rewrite edges and one closed
interior permutation. Pure positive/fixed-endpoint count combinatorics are
reused; all derivational fields have the actual reversed eleven-law basis.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank092.Front

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots

private def wn (head : Nat) (tail : List Nat) : Word Nat := ⟨head, tail⟩

private def instantiateThreeWords (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- Exact closed certificate for the interior cube move; no changing-endpoint
S5_442 axiom is used. -/
theorem literalCubeWithTrailing :
    Derives basis (wn 0 [1, 1, 1, 2, 0]) (wn 0 [1, 2, 0]) := by
  have first : Derives basis (wn 0 [1, 1, 1, 2, 0]) (wn 0 [1, 1, 2, 1, 0]) :=
    ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
      (chain := [
        { lawIndex := 10
          direction := .backward
          leftContext := []
          rightContext := []
          substitution := [[0], [1], [1, 1, 2]] }]) (by decide)
  have second : Derives basis (wn 0 [1, 1, 2, 1, 0]) (wn 0 [1, 1, 2, 2, 1, 2, 0]) :=
    ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
      (chain := [
        { lawIndex := 6
          direction := .forward
          leftContext := [0, 1]
          rightContext := [0]
          substitution := [[1], [2], [2]] }]) (by decide)
  have permuted : ListDerives [0, 1, 1, 2, 2, 1, 2, 0] [0, 1, 2, 1, 2, 1, 2, 0] := by
    simpa [parityEnvelopeRender, S5_441.parityEnvelopeRender] using
      listDerivesParityEnvelopeInteriorPermutation 0 []
        (show ([1, 1, 2, 2, 1, 2] : List Nat).Perm [1, 2, 1, 2, 1, 2] from by decide)
  have third : Derives basis (wn 0 [1, 1, 2, 2, 1, 2, 0]) (wn 0 [1, 2, 1, 2, 1, 2, 0]) :=
    S5_107.ListDerives.toWord permuted
  have fourth : Derives basis (wn 0 [1, 2, 1, 2, 1, 2, 0]) (wn 0 [1, 2, 0]) :=
    ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
      (chain := [
        { lawIndex := 5
          direction := .backward
          leftContext := []
          rightContext := []
          substitution := [[0], [1, 2], [2]] }]) (by decide)
  exact first.trans (second.trans (third.trans fourth))

private theorem derivesEnvelopeBlockThreeToOneWithTrailing
    (anchor block trailing : Word Nat) :
    Derives basis
      (((((anchor ++ block) ++ block) ++ block) ++ trailing) ++ anchor)
      (((anchor ++ block) ++ trailing) ++ anchor) := by
  have substituted := Derives.subst literalCubeWithTrailing
    (instantiateThreeWords anchor block trailing)
  simpa [wn, instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem listDerivesEnvelopeBlockThreeToOne
    (anchor block : Word Nat) (trailing : List Nat) :
    ListDerives
      (anchor.toList ++ block.toList ++ block.toList ++ block.toList ++
        trailing ++ anchor.toList)
      (anchor.toList ++ block.toList ++ trailing ++ anchor.toList) := by
  cases trailing with
  | nil =>
      simpa [Word.toList_append, List.append_assoc] using
        (ListDerives.ofWord
          (derivesEnvelopePower anchor block).symm)
  | cons trailingHead trailingTail =>
      let trailingWord :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [trailingWord, S5_107.listWordOfCons, Word.toList,
        Word.toList_append, List.append_assoc] using
          (ListDerives.ofWord
            (derivesEnvelopeBlockThreeToOneWithTrailing
              anchor block trailingWord))

private theorem bind_append (u v : Word Nat) (sigma : Nat → Word Nat) :
    (u ++ v).bind sigma = u.bind sigma ++ v.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (tau sigma : Nat → Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun x => (tau x).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private theorem listDerivesParityEnvelopeInteriorPowerExact
    (endpoint : Nat) (block : Word Nat) (suffix : List Nat) :
    ListDerives
      (parityEnvelopeRender endpoint block.toList suffix)
      (parityEnvelopeRender endpoint
        (block.toList ++ block.toList ++ block.toList) suffix) := by
  simpa [parityEnvelopeRender, S5_441.parityEnvelopeRender,
    Word.append, Word.toList_append, Word.toList_singleton,
    List.append_assoc] using
    ListDerives.append
      (ListDerives.ofWord
        (derivesEnvelopePower (Word.singleton endpoint) block))
      suffix

private theorem listDerivesParityEnvelopeInteriorSwapExact
    (endpoint : Nat) (left right : Word Nat)
    (suffix : List Nat) :
    ListDerives
      (parityEnvelopeRender endpoint
        (left.toList ++ right.toList) suffix)
      (parityEnvelopeRender endpoint
        (right.toList ++ left.toList) suffix) := by
  simpa [parityEnvelopeRender, S5_441.parityEnvelopeRender,
    Word.append, Word.toList_append, Word.toList_singleton,
    List.append_assoc] using
    ListDerives.append
      (ListDerives.ofWord
        (derivesInteriorSwap
          (Word.singleton endpoint) left right))
      suffix

/-- Add two copies of a nonempty block at an arbitrary position inside a
fixed singleton endpoint envelope. Interior permutations expose the block at
the front, and the envelope power is replayed with the remaining interior as
its retained trailing filler. -/
theorem listDerivesParityEnvelopeInteriorPowerContext
    (endpoint : Nat) (before after suffix : List Nat)
    (block : Word Nat) :
    ListDerives
      (parityEnvelopeRender endpoint
        (before ++ block.toList ++ after) suffix)
      (parityEnvelopeRender endpoint
        (before ++ block.toList ++ block.toList ++
          block.toList ++ after) suffix) := by
  by_cases emptyContext : before = [] ∧ after = []
  · rcases emptyContext with ⟨rfl, rfl⟩
    simpa using
      listDerivesParityEnvelopeInteriorPowerExact
        endpoint block suffix
  have moveToFrontPermutation :
      (before ++ block.toList ++ after).Perm
        (block.toList ++ before ++ after) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    omega
  have moveToFront :
      ListDerives
        (parityEnvelopeRender endpoint
          (before ++ block.toList ++ after) suffix)
        (parityEnvelopeRender endpoint
          (block.toList ++ before ++ after) suffix) :=
    listDerivesParityEnvelopeInteriorPermutation
      endpoint suffix moveToFrontPermutation
  have expandFront :
      ListDerives
        (parityEnvelopeRender endpoint
          (block.toList ++ before ++ after) suffix)
        (parityEnvelopeRender endpoint
          (block.toList ++ block.toList ++ block.toList ++
            before ++ after) suffix) := by
    simpa [parityEnvelopeRender, S5_441.parityEnvelopeRender,
      Word.append, Word.toList_singleton, List.append_assoc] using
        ListDerives.append
          (ListDerives.symm
            (listDerivesEnvelopeBlockThreeToOne
              (Word.singleton endpoint) block (before ++ after)))
          suffix
  have moveBackPermutation :
      (block.toList ++ block.toList ++ block.toList ++
          before ++ after).Perm
        (before ++ block.toList ++ block.toList ++
          block.toList ++ after) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    omega
  have moveBack :
      ListDerives
        (parityEnvelopeRender endpoint
          (block.toList ++ block.toList ++ block.toList ++
            before ++ after) suffix)
        (parityEnvelopeRender endpoint
          (before ++ block.toList ++ block.toList ++
            block.toList ++ after) suffix) :=
    listDerivesParityEnvelopeInteriorPermutation
      endpoint suffix moveBackPermutation
  exact
    ListDerives.trans moveToFront
      (ListDerives.trans expandFront moveBack)

/-- Swap two adjacent nonempty blocks at an arbitrary position inside a
fixed singleton endpoint envelope. -/
theorem listDerivesParityEnvelopeInteriorSwapContext
    (endpoint : Nat) (before after suffix : List Nat)
    (left right : Word Nat) :
    ListDerives
      (parityEnvelopeRender endpoint
        (before ++ left.toList ++ right.toList ++ after) suffix)
      (parityEnvelopeRender endpoint
        (before ++ right.toList ++ left.toList ++ after) suffix) := by
  by_cases emptyContext : before = [] ∧ after = []
  · rcases emptyContext with ⟨rfl, rfl⟩
    simpa using
      listDerivesParityEnvelopeInteriorSwapExact
        endpoint left right suffix
  have permutation :
      (before ++ left.toList ++ right.toList ++ after).Perm
        (before ++ right.toList ++ left.toList ++ after) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    omega
  exact
    listDerivesParityEnvelopeInteriorPermutation
      endpoint suffix permutation

/-- Replay every derivation for `x = xxx`, `xy = yx` at an arbitrary
position inside fixed matching singleton endpoint contexts. The power and
commutativity basis steps are realized by the exact reversed rank092 envelope power and
interior swap architecture. -/
theorem liftInteriorParity
    {u v : Word Nat}
    (derivation : Derives commutativeParityBasis u v)
    (endpoint : Nat) (before after suffix : List Nat)
    (sigma : Nat → Word Nat) :
    ListDerives
      (parityEnvelopeRender endpoint
        (before ++ (u.bind sigma).toList ++ after) suffix)
      (parityEnvelopeRender endpoint
        (before ++ (v.bind sigma).toList ++ after) suffix) := by
  induction derivation generalizing before after sigma with
  | fromBasis member =>
      simp only [commutativeParityBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [parityPowerLaw, parityX, parityXXX,
          Word.bind, Word.append, Word.singleton,
          parityEnvelopeRender, List.append_assoc] using
          listDerivesParityEnvelopeInteriorPowerContext
            endpoint before after suffix (sigma 0)
      · simpa [parityCommutativityLaw, parityXY, parityYX,
          Word.bind, Word.append, Word.singleton,
          parityEnvelopeRender, List.append_assoc] using
          listDerivesParityEnvelopeInteriorSwapContext
            endpoint before after suffix (sigma 0) (sigma 1)
  | refl =>
      exact ListDerives.refl _
  | symm _ ih =>
      exact ListDerives.symm (ih before after sigma)
  | trans _ _ ihFirst ihSecond =>
      exact
        ListDerives.trans
          (ihFirst before after sigma)
          (ihSecond before after sigma)
  | prepend preWord _ ih =>
      simpa [bind_append, Word.toList_append,
        List.append_assoc] using
        ih (before ++ (preWord.bind sigma).toList) after sigma
  | appendRight _ postWord ih =>
      simpa [bind_append, Word.toList_append,
        List.append_assoc] using
        ih before ((postWord.bind sigma).toList ++ after) sigma
  | subst _ tau ih =>
      simpa [bind_bind] using
        ih before after (fun x => (tau x).bind sigma)

/-- Normalize positive interior multiplicities to one copy when odd and two
copies when even, without yet treating the endpoint specially. -/
theorem listDerivesParityEnvelopePositiveParityReduce
    (endpoint : Nat) (interior suffix : List Nat) :
    ListDerives
      (parityEnvelopeRender endpoint interior suffix)
      (parityEnvelopeRender endpoint
        (positiveParityReduce interior) suffix) := by
  cases interior with
  | nil =>
      exact ListDerives.refl _
  | cons head tail =>
      have normalized :=
        positiveParityDerivesNormal (wordOfCons head tail)
      change
        match positiveParityReduce (head :: tail) with
        | [] => False
        | nextHead :: nextTail =>
            Derives commutativeParityBasis
              (wordOfCons head tail)
              (Word.mk nextHead nextTail)
        at normalized
      cases reduced :
          positiveParityReduce (head :: tail) with
      | nil =>
          have present :
              head ∈ positiveParityReduce (head :: tail) :=
            (mem_positiveParityReduce_iff
              head (head :: tail)).mpr (by simp)
          simp [reduced] at present
      | cons nextHead nextTail =>
          rw [reduced] at normalized
          have lifted :=
            liftInteriorParity normalized endpoint
              [] [] suffix Word.singleton
          rw [bind_singleton, bind_singleton] at lifted
          simpa [wordOfCons, Word.toList, reduced] using lifted

/-- Remove two internal copies of the fixed endpoint. For an empty remaining
interior this is the four-to-two endpoint contraction; otherwise it is the
reverse left-envelope power law. -/
theorem listDerivesParityEnvelopeRemoveEndpointPair
    (endpoint : Nat) (middle suffix : List Nat) :
    ListDerives
      (parityEnvelopeRender endpoint
        ([endpoint, endpoint] ++ middle) suffix)
      (parityEnvelopeRender endpoint middle suffix) := by
  cases middle with
  | nil =>
      simpa [parityEnvelopeRender, Word.toList_append,
        Word.toList_singleton, List.append_assoc] using
        ListDerives.append
          (ListDerives.symm
            (ListDerives.ofWord
              (derivesBlockSquarePower
                (Word.singleton endpoint))))
          suffix
  | cons middleHead middleTail =>
      let middleWord :=
        S5_107.listWordOfCons middleHead middleTail
      simpa [parityEnvelopeRender, middleWord,
        S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
        ListDerives.append
          (ListDerives.symm
            (ListDerives.ofWord
              (derivesLeftEnvelopePower
                (Word.singleton endpoint) middleWord)))
          suffix

/-- Fixed-endpoint interior normal form. Non-endpoint positive
multiplicities are represented once when odd and twice when even. The
endpoint itself is represented zero times when even and once when odd,
because an internal endpoint pair can be absorbed by the fixed envelope. -/
abbrev fixedEndpointParityReduce := S5_442.fixedEndpointParityReduce

private theorem two_endpoint_copies_perm
    (endpoint : Nat) (letters : List Nat)
    (countEq : letters.count endpoint = 2) :
    letters.Perm
      (endpoint :: endpoint ::
        (letters.erase endpoint).erase endpoint) := by
  have present : endpoint ∈ letters :=
    List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase present
  have eraseCount : (letters.erase endpoint).count endpoint = 1 := by
    rw [List.count_erase_self, countEq]
  have remains : endpoint ∈ letters.erase endpoint :=
    List.count_pos_iff.mp (by omega)
  exact
    List.Perm.trans first
      (List.Perm.cons endpoint
        (List.perm_cons_erase remains))

/-- Derive the fixed-endpoint normal form of one interior. -/
theorem listDerivesParityEnvelopeFixedEndpointReduce
    (endpoint : Nat) (interior suffix : List Nat) :
    ListDerives
      (parityEnvelopeRender endpoint interior suffix)
      (parityEnvelopeRender endpoint
        (fixedEndpointParityReduce endpoint interior) suffix) := by
  have positiveReduction :=
    listDerivesParityEnvelopePositiveParityReduce
      endpoint interior suffix
  by_cases countEq :
      (positiveParityReduce interior).count endpoint = 2
  · let remainder :=
      ((positiveParityReduce interior).erase endpoint).erase endpoint
    have arrangePermutation :
        (positiveParityReduce interior).Perm
          ([endpoint, endpoint] ++ remainder) := by
      simpa [remainder] using
        two_endpoint_copies_perm endpoint
          (positiveParityReduce interior) countEq
    have arrange :
        ListDerives
          (parityEnvelopeRender endpoint
            (positiveParityReduce interior) suffix)
          (parityEnvelopeRender endpoint
            ([endpoint, endpoint] ++ remainder) suffix) :=
      listDerivesParityEnvelopeInteriorPermutation
        endpoint suffix arrangePermutation
    have removePair :=
      listDerivesParityEnvelopeRemoveEndpointPair
        endpoint remainder suffix
    exact
      ListDerives.trans positiveReduction <| by
        simpa [fixedEndpointParityReduce, S5_442.fixedEndpointParityReduce, countEq, remainder] using
          ListDerives.trans arrange removePair
  · simpa [fixedEndpointParityReduce, S5_442.fixedEndpointParityReduce, countEq] using
      positiveReduction

/-- Fixed-endpoint parity normalization. Support must agree only away from
the endpoint; equal endpoint parity is enough because an internal endpoint
pair is removable. -/
theorem listDerivesParityEnvelopeInteriorNormalizeFixedEndpoint
    (endpoint : Nat) (suffix : List Nat)
    {left right : List Nat}
    (supportEq :
      ∀ z, z ≠ endpoint → (z ∈ left ↔ z ∈ right))
    (parityEq :
      ∀ z, left.count z % 2 = right.count z % 2) :
    ListDerives
      (parityEnvelopeRender endpoint left suffix)
      (parityEnvelopeRender endpoint right suffix) := by
  have reducedPermutation :=
    S5_442.fixedEndpointParityReduce_perm supportEq parityEq
  have leftNormal :=
    listDerivesParityEnvelopeFixedEndpointReduce
      endpoint left suffix
  have rightNormal :=
    listDerivesParityEnvelopeFixedEndpointReduce
      endpoint right suffix
  have middle :=
    listDerivesParityEnvelopeInteriorPermutation
      endpoint suffix reducedPermutation
  exact
    ListDerives.trans leftNormal
      (ListDerives.trans middle
        (ListDerives.symm rightNormal))

/-- Interior support and coordinate parity determine a derivation between
two parity envelopes with the same fixed endpoint and suffix. -/
theorem listDerivesParityEnvelopeInteriorNormalize
    (endpoint : Nat) (suffix : List Nat)
    {left right : List Nat}
    (supportEq : ∀ z, z ∈ left ↔ z ∈ right)
    (parityEq :
      ∀ z, left.count z % 2 = right.count z % 2) :
    ListDerives
      (parityEnvelopeRender endpoint left suffix)
      (parityEnvelopeRender endpoint right suffix) :=
  listDerivesParityEnvelopeInteriorNormalizeFixedEndpoint
    endpoint suffix (fun z _ => supportEq z) parityEq

private theorem mem_parityEnvelopeRender_empty_iff_of_ne
    (endpoint tested : Nat) (interior : List Nat)
    (different : tested ≠ endpoint) :
    tested ∈ parityEnvelopeRender endpoint interior [] ↔
      tested ∈ interior := by
  simp [S5_441.parityEnvelopeRender, different]

private theorem parityEnvelopeRender_empty_count_mod_two
    (endpoint tested : Nat) (interior : List Nat) :
    (parityEnvelopeRender endpoint interior []).count tested % 2 =
      interior.count tested % 2 := by
  by_cases same : endpoint = tested
  · subst tested
    simp [S5_441.parityEnvelopeRender]
    omega
  · simp [S5_441.parityEnvelopeRender, same]

/-- Closed fixed-endpoint form stated directly on the full rendered support
and parity invariants. The two displayed endpoint copies cancel from every
coordinate parity comparison, while their guaranteed support makes internal
endpoint support irrelevant. -/
theorem listDerivesParityEnvelopeInteriorNormalizeOfRenderedInvariants
    (endpoint : Nat) {left right : List Nat}
    (supportEq :
      ∀ z,
        z ∈ parityEnvelopeRender endpoint left [] ↔
          z ∈ parityEnvelopeRender endpoint right [])
    (parityEq :
      ∀ z,
        (parityEnvelopeRender endpoint left []).count z % 2 =
          (parityEnvelopeRender endpoint right []).count z % 2) :
    ListDerives
      (parityEnvelopeRender endpoint left [])
      (parityEnvelopeRender endpoint right []) := by
  have interiorSupport :
      ∀ z, z ≠ endpoint → (z ∈ left ↔ z ∈ right) := by
    intro z different
    rw [← mem_parityEnvelopeRender_empty_iff_of_ne
        endpoint z left different,
      ← mem_parityEnvelopeRender_empty_iff_of_ne
        endpoint z right different]
    exact supportEq z
  have interiorParity :
      ∀ z, left.count z % 2 = right.count z % 2 := by
    intro z
    rw [← parityEnvelopeRender_empty_count_mod_two
        endpoint z left,
      ← parityEnvelopeRender_empty_count_mod_two
        endpoint z right]
    exact parityEq z
  exact
    listDerivesParityEnvelopeInteriorNormalizeFixedEndpoint
      endpoint [] interiorSupport interiorParity

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank092.Front
