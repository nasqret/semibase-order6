import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSemanticGapInvariant
import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSourceBlockValue
import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedFirstReturnBridgeCut

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSpanDetector

open MaximalFactors CanonicalPresentation FirstReturnBridgeCut RootSpanIsolation

def valuation (region : List Nat) (marker letter : Nat) : Fin 6 :=
  if letter ∈ region then 4 else if letter = marker then 2 else 5

theorem valuation_four_iff (region : List Nat) (marker letter : Nat) :
    valuation region marker letter = (4 : Fin 6) ↔ letter ∈ region := by
  by_cases member : letter ∈ region
  · exact ⟨fun _ => member, fun _ => by simp only [valuation, if_pos member]⟩
  · constructor
    · intro same
      by_cases marked : letter = marker
      · have bad : (2 : Fin 6) = (4 : Fin 6) := by
          simpa only [valuation, if_neg member, if_pos marked] using same
        exact False.elim ((by decide : (2 : Fin 6) ≠ (4 : Fin 6)) bad)
      · have bad : (5 : Fin 6) = (4 : Fin 6) := by
          simpa only [valuation, if_neg member, if_neg marked] using same
        exact False.elim ((by decide : (5 : Fin 6) ≠ (4 : Fin 6)) bad)
    · intro impossible
      exact False.elim (member impossible)

theorem marker_absent (source : Word Nat) (left middle after : List Nat) (marker : Nat)
    (literal : source.toList = left ++ (middle ++ marker :: after))
    (simple : source.toList.count marker = 1) :
    marker ∉ left ∧ marker ∉ middle ∧ marker ∉ after := by
  have counts := simple
  rw [literal, List.count_append, List.count_append, List.count_cons_self] at counts
  refine ⟨?_, ?_, ?_⟩
  · intro member
    have positive := List.count_pos_iff.mpr member
    omega
  · intro member
    have positive := List.count_pos_iff.mpr member
    omega
  · intro member
    have positive := List.count_pos_iff.mpr member
    omega

/-- The actual cut support, not a supplied valuation, has the required source
value. The middle is nonempty and isolated; the marker is genuinely simple. -/
theorem isolated_cut_value (source : Word Nat) (left middle after : List Nat) (marker : Nat)
    (literal : source.toList = left ++ (middle ++ marker :: after))
    (leftNonempty : left ≠ []) (middleNonempty : middle ≠ [])
    (isolated : ∀ x ∈ middle, x ∉ left ++ marker :: after)
    (simple : source.toList.count marker = 1) :
    table.semigroup.eval (valuation middle marker) source = (1 : Fin 6) := by
  let leftWord : Word Nat := OccurrenceMacro.nonemptyWord left leftNonempty
  let middleWord : Word Nat := OccurrenceMacro.nonemptyWord middle middleNonempty
  have leftList : leftWord.toList = left := OccurrenceMacro.nonemptyWord_toList left leftNonempty
  have middleList : middleWord.toList = middle := OccurrenceMacro.nonemptyWord_toList middle middleNonempty
  obtain ⟨notLeft, notMiddle, notAfter⟩ := marker_absent source left middle after marker literal simple
  apply SourceBlockValue.source_block_value (valuation middle marker) source leftWord middleWord marker after
  · simpa only [leftList, middleList] using literal
  · intro x member
    rw [leftList] at member
    have notRegion : x ∉ middle := fun inside =>
      isolated x inside (List.mem_append.mpr (Or.inl member))
    have notMarker : x ≠ marker := fun same => notLeft (same ▸ member)
    simp only [valuation, if_neg notRegion, if_neg notMarker]
  · intro x member
    rw [middleList] at member
    simp only [valuation, if_pos member]
  · rw [valuation, if_neg notMiddle, if_pos (rfl : marker = marker)]
  · intro x member
    have notRegion : x ∉ middle := fun inside =>
      isolated x inside (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem marker member)))
    have notMarker : x ≠ marker := fun same => notAfter (same ▸ member)
    simp only [valuation, if_neg notRegion, if_neg notMarker]

/-- Semantic equality forces every target root to lie entirely inside or
entirely outside any such actual isolated source region. -/
theorem isolated_cut_target_membership (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target) (form : Form target)
    (left middle after : List Nat) (marker : Nat)
    (literal : source.toList = left ++ (middle ++ marker :: after))
    (leftNonempty : left ≠ []) (middleNonempty : middle ≠ [])
    (isolated : ∀ x ∈ middle, x ∉ left ++ marker :: after)
    (simple : source.toList.count marker = 1)
    (root : Word Nat) (rootMember : root ∈ form.roots)
    (x y : Nat) (inX : x ∈ root.toList) (inY : y ∈ root.toList) :
    x ∈ middle ↔ y ∈ middle := by
  have sourceValue := isolated_cut_value source left middle after marker literal
    leftNonempty middleNonempty isolated simple
  have targetNonzero : table.semigroup.eval (valuation middle marker) target ≠ (0 : Fin 6) := by
    rw [← equalEval (valuation middle marker), sourceValue]
    decide
  have targetSimple := SemanticGapInvariant.semantic_simple_marker source target equalEval marker simple
  have offMarker : ∀ z, z ≠ marker → valuation middle marker z = 4 ∨ valuation middle marker z = 5 := by
    intro z different
    by_cases member : z ∈ middle
    · exact Or.inl (by simp only [valuation, if_pos member])
    · exact Or.inr (by simp only [valuation, if_neg member, if_neg different])
  have agreement := SimpleMarkerRootRange.simple_marker_root_values_agree
    (valuation middle marker) target form marker targetSimple offMarker root rootMember targetNonzero x y inX inY
  exact (valuation_four_iff middle marker x).symm.trans
    ((show valuation middle marker x = (4 : Fin 6) ↔ valuation middle marker y = (4 : Fin 6) from
      ⟨fun h => agreement.symm.trans h, fun h => agreement.trans h⟩).trans
      (valuation_four_iff middle marker y))

/-- Both repaired detector regions are actual contiguous isolated blocks.
The original c-prime region may be empty; its branch is used only if a chosen
letter belongs to it. The b-union-c-prime region is always nonempty. -/
theorem return_cut_regions (source : Word Nat) (roots : List (Word Nat))
    (before inside tail : List (Word Nat))
    (isolated : ∀ x ∈ flatten inside, x ∉ flatten (before ++ tail))
    (cut : ReturnCut roots source before inside tail) :
    (∀ x ∈ flatten cut.between,
      x ∉ (flatten before ++ flatten inside) ++ cut.marker.head ::
        (cut.marker.tail ++ ((cut.bridge ++ cut.bridge).toList ++ flatten cut.after))) ∧
    (∀ x ∈ flatten inside ++ flatten cut.between,
      x ∉ flatten before ++ cut.marker.head ::
        (cut.marker.tail ++ ((cut.bridge ++ cut.bridge).toList ++ flatten cut.after))) := by
  have betweenOutside : ∀ x ∈ flatten cut.between,
      x ∉ (flatten before ++ flatten inside) ++ cut.marker.toList ++
        ((cut.bridge ++ cut.bridge).toList ++ flatten cut.after) := by
    simpa only [FactorBoundaries.flatten_append, flatten, List.append_assoc] using cut.between_isolated
  constructor
  · simpa only [Word.toList, List.cons_append, List.append_assoc] using betweenOutside
  · intro x member exterior
    have outside : x ∈ flatten before ++ (cut.marker.toList ++
        ((cut.bridge ++ cut.bridge).toList ++ flatten cut.after)) := by
      simpa only [Word.toList, List.cons_append, List.append_assoc] using exterior
    rcases List.mem_append.mp member with inInside | inBetween
    · apply isolated x inInside
      rw [FactorBoundaries.flatten_append]
      rcases List.mem_append.mp outside with inBefore | inRest
      · exact List.mem_append.mpr (Or.inl inBefore)
      · apply List.mem_append.mpr
        right
        rw [cut.tail_eq, FactorBoundaries.flatten_append]
        exact List.mem_append.mpr (Or.inr inRest)
    · apply betweenOutside x inBetween
      rcases List.mem_append.mp outside with inBefore | inRest
      · have inPrefix : x ∈ flatten before ++ flatten inside :=
          List.mem_append.mpr (Or.inl inBefore)
        have withMarker : x ∈ (flatten before ++ flatten inside) ++ cut.marker.toList :=
          List.mem_append.mpr (Or.inl inPrefix)
        exact List.mem_append.mpr (Or.inl withMarker)
      · rcases List.mem_append.mp inRest with inMarker | inAfter
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr inMarker)))
        · exact List.mem_append.mpr (Or.inr inAfter)

/-- The two-branch correction is now unrestricted Lean: equality of actual
C8 word functions prevents a target root from straddling an isolated source
span. No target root-partition or matching gap-order premise is supplied. -/
theorem return_cut_target_span (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target) (form : Form target)
    (roots : List (Word Nat)) (before inside tail : List (Word Nat))
    (beforeNonempty : before ≠ []) (insideNonempty : inside ≠ [])
    (isolated : ∀ x ∈ flatten inside, x ∉ flatten (before ++ tail))
    (cut : ReturnCut roots source before inside tail)
    (root : Word Nat) (rootMember : root ∈ form.roots)
    (x y : Nat) (inX : x ∈ root.toList) (inY : y ∈ root.toList) :
    x ∈ flatten inside ↔ y ∈ flatten inside := by
  have leftNonempty := ConnectedTerminalEndpoints.flatten_nonempty before beforeNonempty
  have insideLettersNonempty := ConnectedTerminalEndpoints.flatten_nonempty inside insideNonempty
  have markerSimple : source.toList.count cut.marker.head = 1 :=
    cut.marker_simple cut.marker.head List.mem_cons_self
  obtain ⟨betweenIsolated, unionIsolated⟩ := return_cut_regions source roots before inside tail isolated cut
  let after : List Nat := cut.marker.tail ++ ((cut.bridge ++ cut.bridge).toList ++ flatten cut.after)
  have literalUnion : source.toList = flatten before ++
      ((flatten inside ++ flatten cut.between) ++ cut.marker.head :: after) := by
    simpa only [after, Word.toList, List.cons_append, List.append_assoc] using cut.word_eq
  have unionNonempty : flatten inside ++ flatten cut.between ≠ [] := by
    intro empty
    exact insideLettersNonempty (List.append_eq_nil_iff.mp empty).1
  have unionAgreement := isolated_cut_target_membership source target equalEval form
    (flatten before) (flatten inside ++ flatten cut.between) after cut.marker.head
    literalUnion leftNonempty unionNonempty unionIsolated markerSimple root rootMember x y inX inY
  have insideNotBetween : ∀ z ∈ flatten inside, z ∉ flatten cut.between := by
    intro z member also
    apply isolated z member
    rw [FactorBoundaries.flatten_append]
    apply List.mem_append.mpr
    right
    rw [cut.tail_eq, FactorBoundaries.flatten_append]
    exact List.mem_append.mpr (Or.inl also)
  have betweenAgreement : x ∈ flatten cut.between ↔ y ∈ flatten cut.between := by
    by_cases empty : flatten cut.between = []
    · simp only [empty, List.not_mem_nil]
    · have prefixNonempty : flatten before ++ flatten inside ≠ [] := by
        intro nil
        exact leftNonempty (List.append_eq_nil_iff.mp nil).1
      have literalBetween : source.toList = (flatten before ++ flatten inside) ++
          (flatten cut.between ++ cut.marker.head :: after) := by
        simpa only [List.append_assoc] using literalUnion
      exact isolated_cut_target_membership source target equalEval form
        (flatten before ++ flatten inside) (flatten cut.between) after cut.marker.head
        literalBetween prefixNonempty empty betweenIsolated markerSimple root rootMember x y inX inY
  constructor
  · intro member
    rcases List.mem_append.mp (unionAgreement.mp (List.mem_append.mpr (Or.inl member))) with yes | no
    · exact yes
    · exact False.elim (insideNotBetween x member (betweenAgreement.mpr no))
  · intro member
    rcases List.mem_append.mp (unionAgreement.mpr (List.mem_append.mpr (Or.inl member))) with yes | no
    · exact yes
    · exact False.elim (insideNotBetween y member (betweenAgreement.mp no))

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSpanDetector

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSpanDetector.valuation_four_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSpanDetector.marker_absent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSpanDetector.isolated_cut_value
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSpanDetector.isolated_cut_target_membership
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSpanDetector.return_cut_regions
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSpanDetector.return_cut_target_span
