import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSemanticSpanDetector

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticFormSpans

open MaximalFactors CanonicalPresentation FirstReturnBridgeCut RootSpanIsolation

theorem root_letter_in_span (root : Word Nat) (inside : List (Word Nat))
    (shape : SpanShape (root ++ root) inside) (letter : Nat) (member : letter ∈ root.toList) :
    letter ∈ flatten inside := by
  obtain ⟨rest, _initial, starts, _ends⟩ := span_endpoints (root ++ root) inside shape
  rw [starts]
  change letter ∈ (root ++ root).toList ++ flatten rest
  apply List.mem_append.mpr
  left
  rw [Word.toList_append]
  exact List.mem_append.mpr (Or.inl member)

/-- Every actual noninitial canonical root has an isolated span whose support
is a union of target-root supports. The cut and detector are derived, not inputs. -/
theorem noninitial_span_invariant (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target)
    (left : Form source) (right : Form target) (selected : Word Nat)
    (selectedMember : selected ∈ left.roots) (noninitial : (selected ++ selected) ≠ left.first) :
    ∃ before inside tail : List (Word Nat),
      left.first :: expand left.chunks = before ++ (inside ++ tail) ∧
      SpanShape (selected ++ selected) inside ∧
      (∀ letter ∈ flatten inside, letter ∉ flatten (before ++ tail)) ∧
      (∀ root ∈ right.roots, ∀ x ∈ root.toList, ∀ y ∈ root.toList,
        x ∈ flatten inside ↔ y ∈ flatten inside) := by
  obtain ⟨before, inside, tail, split, shape, isolated, available⟩ :=
    form_noninitial_root_cut source left selected selectedMember noninitial
  obtain ⟨cut⟩ := available
  have beforeNonempty := form_span_before_nonempty source left selected before inside tail split shape noninitial
  have insideNonempty : inside ≠ [] := by
    obtain ⟨rest, _initial, starts, _ends⟩ := span_endpoints (selected ++ selected) inside shape
    rw [starts]
    exact List.cons_ne_nil (selected ++ selected) rest
  refine ⟨before, inside, tail, split, shape, isolated, ?_⟩
  intro root rootMember x inX y inY
  exact SemanticSpanDetector.return_cut_target_span source target equalEval right
    left.roots before inside tail beforeNonempty insideNonempty isolated cut root rootMember x y inX inY

/-- Any target root sharing a letter with the selected source root lies wholly
inside its chosen actual span. Full equality of root partitions remains later work. -/
theorem target_root_stays_in_source_span (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target)
    (left : Form source) (right : Form target) (selected : Word Nat)
    (selectedMember : selected ∈ left.roots) (noninitial : (selected ++ selected) ≠ left.first) :
    ∃ before inside tail : List (Word Nat),
      left.first :: expand left.chunks = before ++ (inside ++ tail) ∧
      SpanShape (selected ++ selected) inside ∧
      (∀ root ∈ right.roots, ∀ shared ∈ selected.toList, shared ∈ root.toList →
        ∀ letter ∈ root.toList, letter ∈ flatten inside) := by
  obtain ⟨before, inside, tail, split, shape, _isolated, uniform⟩ :=
    noninitial_span_invariant source target equalEval left right selected selectedMember noninitial
  refine ⟨before, inside, tail, split, shape, ?_⟩
  intro root rootMember shared inSelected inRoot letter member
  exact (uniform root rootMember shared inRoot letter member).mp
    (root_letter_in_span selected inside shape shared inSelected)

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticFormSpans

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticFormSpans.root_letter_in_span
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticFormSpans.noninitial_span_invariant
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticFormSpans.target_root_stays_in_source_span
