import SemigroupBasis.CoRoots.S5_378GapMerge

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_378

open SemigroupBasis

/-- Sort an envelope interior into ascending order. Equal letters therefore
form adjacent blocks. -/
@[reducible] def sortGapInterior (interior : List Nat) : List Nat :=
  interior.mergeSort
    (fun left right : Nat => decide (left ≤ right))

theorem sortGapInterior_perm (interior : List Nat) :
    interior.Perm (sortGapInterior interior) := by
  exact
    (List.mergeSort_perm interior
      (fun left right : Nat => decide (left ≤ right))).symm

theorem sortGapInterior_count
    (interior : List Nat) (tested : Nat) :
    (sortGapInterior interior).count tested =
      interior.count tested := by
  exact
    (List.perm_iff_count.mp
      (List.mergeSort_perm interior
        (fun left right : Nat => decide (left ≤ right)))) tested

theorem sortGapInterior_sorted (interior : List Nat) :
    (sortGapInterior interior).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right leftMiddle middleRight
    exact decide_eq_true <|
      Nat.le_trans
        (of_decide_eq_true leftMiddle)
        (of_decide_eq_true middleRight)
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) ||
          decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with leftRight | rightLeft
    · simp [leftRight]
    · simp [rightLeft]
  exact
    (List.pairwise_mergeSort transitive total interior).imp
      (fun relation => of_decide_eq_true relation)

/-- Interior permutations lift to B378 envelope derivations. The underlying
S5_379 derivation is transported through `strongerBasisDerives`. -/
theorem listDerivesGapEnvelopeInteriorPermutation
    (endpoint : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    ListDerives
      (gapEnvelopeRender endpoint left)
      (gapEnvelopeRender endpoint right) := by
  apply ListDerives.ofS5_379
  simpa [gapEnvelopeRender, List.append_assoc] using
    SemigroupBasis.CoRoots.S5_379.listDerivesInteriorPermutation
      endpoint [] permutation

theorem listDerivesSortGapInterior
    (endpoint : Nat) (interior : List Nat) :
    ListDerives
      (gapEnvelopeRender endpoint interior)
      (gapEnvelopeRender endpoint (sortGapInterior interior)) :=
  listDerivesGapEnvelopeInteriorPermutation endpoint
    (sortGapInterior_perm interior)

/-- Rendering preserves an interior permutation. -/
theorem gapEnvelopeRender_perm
    (endpoint : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    (gapEnvelopeRender endpoint left).Perm
      (gapEnvelopeRender endpoint right) := by
  rw [List.perm_iff_count]
  intro tested
  have interiorCount :=
    List.perm_iff_count.mp permutation tested
  simp only [gapEnvelopeRender, List.count_cons,
    List.count_append, List.count_nil]
  omega

/-- Retarget an envelope from `x` to a doubled interior letter `y`. The empty
remainder uses the two square-switch laws; a nonempty remainder uses the
recorded envelope-switch chain. -/
theorem listDerivesRetargetGapEnvelope
    (x y : Nat) (remainder : List Nat) :
    ListDerives
      (gapEnvelopeRender x ([y, y] ++ remainder))
      (gapEnvelopeRender y ([x, x] ++ remainder)) := by
  cases remainder with
  | nil =>
      have switch :
          Derives basis
            ((((Word.singleton x ++ Word.singleton y) ++
                Word.singleton y) ++ Word.singleton x))
            ((((Word.singleton y ++ Word.singleton x) ++
                Word.singleton x) ++ Word.singleton y)) :=
        (derivesSquareFinalSwitch
          (Word.singleton x) (Word.singleton y)).symm.trans
            (derivesSquareInitialSwitch
              (Word.singleton x) (Word.singleton y))
      simpa [gapEnvelopeRender, Word.toList_append,
        List.append_assoc] using
          (S5_107.ListDerives.ofWord switch)
  | cons head tail =>
      let remainderWord := S5_107.listWordOfCons head tail
      simpa [gapEnvelopeRender, remainderWord,
        S5_107.listWordOfCons, Word.toList,
        Word.toList_append, List.append_assoc] using
          (S5_107.ListDerives.ofWord
            (derivesEnvelopeSwitch
              (Word.singleton x) (Word.singleton y)
              remainderWord))

/-- Endpoint retargeting is an exact permutation. -/
theorem retargetGapEnvelope_perm
    (x y : Nat) (remainder : List Nat) :
    (gapEnvelopeRender x ([y, y] ++ remainder)).Perm
      (gapEnvelopeRender y ([x, x] ++ remainder)) := by
  rw [List.perm_iff_count]
  intro tested
  simp only [gapEnvelopeRender, List.count_cons,
    List.count_append, List.count_nil]
  omega

private theorem existsTwoOccurrenceSplit
    (letter : Nat) :
    ∀ {letters : List Nat},
      2 ≤ letters.count letter →
        ∃ before middle after,
          letters =
            before ++ letter :: middle ++ letter :: after
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
        exact
          ⟨[], middle, after,
            by simp [split, List.append_assoc]⟩
      · have restCount : 2 ≤ rest.count letter := by
          simpa [equality] using count
        obtain ⟨before, middle, after, split⟩ :=
          existsTwoOccurrenceSplit letter restCount
        exact
          ⟨first :: before, middle, after,
            by simp [split, List.append_assoc]⟩

private theorem existsLeastMember :
    ∀ {candidates : List Nat},
      candidates ≠ [] →
        ∃ least,
          least ∈ candidates ∧
          ∀ tested, tested ∈ candidates → least ≤ tested
  | [], nonempty => False.elim (nonempty rfl)
  | head :: tail, _ => by
      cases tail with
      | nil =>
          refine ⟨head, by simp, ?_⟩
          intro tested member
          have testedEq : tested = head := by simpa using member
          omega
      | cons next rest =>
          obtain ⟨least, leastMember, leastBound⟩ :=
            existsLeastMember
              (candidates := next :: rest) (by simp)
          rcases Nat.le_total head least with headLeast | leastHead
          · refine ⟨head, by simp, ?_⟩
            intro tested member
            rcases List.mem_cons.mp member with rfl | tailMember
            · exact Nat.le_refl _
            · exact Nat.le_trans headLeast
                (leastBound tested tailMember)
          · refine
              ⟨least, List.Mem.tail head leastMember, ?_⟩
            intro tested member
            rcases List.mem_cons.mp member with rfl | tailMember
            · exact leastHead
            · exact leastBound tested tailMember

/-- The canonical-gap refinement is derivable from B378. The endpoint is the
least source letter of multiplicity at least two, the interior is globally
sorted, and the full envelope retains the exact cap-two count of every source
letter. -/
theorem canonicalGapRefinement :
    CanonicalGapRefinementObligation := by
  intro source endpoint interior endpointAbsent _twoLimited capped
  have interiorEndpointCount : interior.count endpoint = 0 :=
    List.count_eq_zero.mpr endpointAbsent
  have endpointTargetCount :
      (gapEnvelopeRender endpoint interior).count endpoint = 2 := by
    simp [gapEnvelopeRender, interiorEndpointCount]
  have sourceEndpointMultiple : 2 ≤ source.count endpoint := by
    have endpointCapped := capped endpoint
    rw [endpointTargetCount] at endpointCapped
    omega
  have endpointInSource : endpoint ∈ source :=
    List.count_pos_iff.mp (by omega)
  let multiples :=
    source.filter
      (fun tested => decide (2 ≤ source.count tested))
  have endpointInMultiples : endpoint ∈ multiples := by
    apply List.mem_filter.mpr
    exact
      ⟨endpointInSource,
        decide_eq_true sourceEndpointMultiple⟩
  have multiplesNonempty : multiples ≠ [] :=
    List.ne_nil_of_mem endpointInMultiples
  obtain
    ⟨canonicalEndpoint, canonicalMember, canonicalLeastMember⟩ :=
      existsLeastMember multiplesNonempty
  have canonicalMultiple :
      2 ≤ source.count canonicalEndpoint :=
    of_decide_eq_true (List.mem_filter.mp canonicalMember).2
  have canonicalLeast :
      ∀ tested,
        2 ≤ source.count tested → canonicalEndpoint ≤ tested := by
    intro tested testedMultiple
    have testedInSource : tested ∈ source :=
      List.count_pos_iff.mp (by omega)
    have testedInMultiples : tested ∈ multiples := by
      apply List.mem_filter.mpr
      exact
        ⟨testedInSource, decide_eq_true testedMultiple⟩
    exact canonicalLeastMember tested testedInMultiples
  have canonicalTargetCount :
      (gapEnvelopeRender endpoint interior).count
          canonicalEndpoint = 2 := by
    calc
      (gapEnvelopeRender endpoint interior).count
          canonicalEndpoint =
          min (source.count canonicalEndpoint) 2 :=
        capped canonicalEndpoint
      _ = 2 := Nat.min_eq_right canonicalMultiple
  by_cases sameEndpoint : canonicalEndpoint = endpoint
  · have sortedDerivation :=
      listDerivesSortGapInterior endpoint interior
    have sortedPermutation :
        (gapEnvelopeRender endpoint interior).Perm
          (gapEnvelopeRender endpoint
            (sortGapInterior interior)) :=
      gapEnvelopeRender_perm endpoint
        (sortGapInterior_perm interior)
    have sortedEndpointAbsent :
        endpoint ∉ sortGapInterior interior := by
      apply List.count_eq_zero.mp
      rw [sortGapInterior_count]
      exact interiorEndpointCount
    refine
      ⟨endpoint, sortGapInterior interior,
        sortedDerivation, sortedEndpointAbsent,
        sortGapInterior_sorted interior, ?_, ?_⟩
    · intro tested
      have permutationCount :=
        List.perm_iff_count.mp sortedPermutation tested
      exact permutationCount.symm.trans (capped tested)
    · intro tested testedMultiple
      have least := canonicalLeast tested testedMultiple
      simpa [sameEndpoint] using least
  · have canonicalInteriorCount :
        interior.count canonicalEndpoint = 2 := by
      simpa [gapEnvelopeRender, sameEndpoint,
        Ne.symm sameEndpoint] using canonicalTargetCount
    obtain ⟨before, middle, after, interiorShape⟩ :=
      existsTwoOccurrenceSplit
        (letters := interior) canonicalEndpoint (by omega)
    let remainder := before ++ middle ++ after
    have arrangePermutation :
        interior.Perm
          ([canonicalEndpoint, canonicalEndpoint] ++ remainder) := by
      rw [interiorShape, List.perm_iff_count]
      intro tested
      simp only [remainder, List.count_append,
        List.count_cons, List.count_nil]
      omega
    have arrangeDerivation :
        ListDerives
          (gapEnvelopeRender endpoint interior)
          (gapEnvelopeRender endpoint
            ([canonicalEndpoint, canonicalEndpoint] ++ remainder)) :=
      listDerivesGapEnvelopeInteriorPermutation
        endpoint arrangePermutation
    let retargetedInterior := [endpoint, endpoint] ++ remainder
    have retargetDerivation :
        ListDerives
          (gapEnvelopeRender endpoint
            ([canonicalEndpoint, canonicalEndpoint] ++ remainder))
          (gapEnvelopeRender canonicalEndpoint
            retargetedInterior) := by
      simpa [retargetedInterior] using
        listDerivesRetargetGapEnvelope
          endpoint canonicalEndpoint remainder
    have sortDerivation :
        ListDerives
          (gapEnvelopeRender canonicalEndpoint
            retargetedInterior)
          (gapEnvelopeRender canonicalEndpoint
            (sortGapInterior retargetedInterior)) :=
      listDerivesSortGapInterior
        canonicalEndpoint retargetedInterior
    have combinedDerivation :
        ListDerives
          (gapEnvelopeRender endpoint interior)
          (gapEnvelopeRender canonicalEndpoint
            (sortGapInterior retargetedInterior)) :=
      arrangeDerivation.trans <|
        retargetDerivation.trans sortDerivation
    have arrangeRenderPermutation :
        (gapEnvelopeRender endpoint interior).Perm
          (gapEnvelopeRender endpoint
            ([canonicalEndpoint, canonicalEndpoint] ++ remainder)) :=
      gapEnvelopeRender_perm endpoint arrangePermutation
    have retargetRenderPermutation :
        (gapEnvelopeRender endpoint
            ([canonicalEndpoint, canonicalEndpoint] ++ remainder)).Perm
          (gapEnvelopeRender canonicalEndpoint
            retargetedInterior) := by
      simpa [retargetedInterior] using
        retargetGapEnvelope_perm
          endpoint canonicalEndpoint remainder
    have sortRenderPermutation :
        (gapEnvelopeRender canonicalEndpoint
            retargetedInterior).Perm
          (gapEnvelopeRender canonicalEndpoint
            (sortGapInterior retargetedInterior)) :=
      gapEnvelopeRender_perm canonicalEndpoint
        (sortGapInterior_perm retargetedInterior)
    have fullPermutation :
        (gapEnvelopeRender endpoint interior).Perm
          (gapEnvelopeRender canonicalEndpoint
            (sortGapInterior retargetedInterior)) :=
      arrangeRenderPermutation.trans <|
        retargetRenderPermutation.trans sortRenderPermutation
    have sortedCanonicalAbsent :
        canonicalEndpoint ∉ sortGapInterior retargetedInterior := by
      apply List.count_eq_zero.mp
      have totalCount :=
        List.perm_iff_count.mp fullPermutation canonicalEndpoint
      rw [canonicalTargetCount] at totalCount
      simp only [gapEnvelopeRender, List.count_cons_self,
        List.count_append, List.count_nil] at totalCount
      omega
    refine
      ⟨canonicalEndpoint, sortGapInterior retargetedInterior,
        combinedDerivation, sortedCanonicalAbsent,
        sortGapInterior_sorted retargetedInterior, ?_, canonicalLeast⟩
    intro tested
    have permutationCount :=
      List.perm_iff_count.mp fullPermutation tested
    exact permutationCount.symm.trans (capped tested)

/- The separator/simple signature determines every global multiplicity after
capping at two. -/
namespace SameSeparatorSimpleSignature

theorem cappedCount_eq
    {left right : Word Nat}
    (same : SameSeparatorSimpleSignature left right)
    (tested : Nat) :
    min (left.toList.count tested) 2 =
      min (right.toList.count tested) 2 := by
  by_cases leftZero : left.toList.count tested = 0
  · have leftAbsent : tested ∉ left.toList :=
      List.count_eq_zero.mp leftZero
    have rightAbsent : tested ∉ right.toList := by
      intro rightMember
      exact leftAbsent ((same.support tested).2 rightMember)
    have rightZero : right.toList.count tested = 0 :=
      List.count_eq_zero.mpr rightAbsent
    simp [leftZero, rightZero]
  · by_cases leftOne : left.toList.count tested = 1
    · have rightOne : right.toList.count tested = 1 :=
        (same.globallySimple tested).1 leftOne
      simp [leftOne, rightOne]
    · have leftAtLeastTwo :
          2 ≤ left.toList.count tested := by
        omega
      have leftMember : tested ∈ left.toList :=
        List.count_pos_iff.mp (by omega)
      have rightMember : tested ∈ right.toList :=
        (same.support tested).1 leftMember
      have rightPositive : 0 < right.toList.count tested :=
        List.count_pos_iff.mpr rightMember
      have rightNotOne : right.toList.count tested ≠ 1 := by
        intro rightOne
        exact leftOne ((same.globallySimple tested).2 rightOne)
      have rightAtLeastTwo :
          2 ≤ right.toList.count tested := by
        omega
      rw [Nat.min_eq_right leftAtLeastTwo,
        Nat.min_eq_right rightAtLeastTwo]

end SameSeparatorSimpleSignature

/-- The exact remaining whole-word lemma after canonical gap refinement.
It must align the deterministic exact-cut separator skeletons, normalize each
exact-cut-free gap under its surrounding context, and assemble one common
target. No inhabitant is asserted in this packet. -/
def ExactCutAssemblyObligation : Prop :=
  ∀ {left right : Word Nat},
    SameSupport left right →
      SameExactCutSignature left right →
      (∀ tested,
        min (left.toList.count tested) 2 =
          min (right.toList.count tested) 2) →
      ∃ common : List Nat,
        ListDerives left.toList common ∧
        ListDerives right.toList common

end SemigroupBasis.CoRoots.S5_378
