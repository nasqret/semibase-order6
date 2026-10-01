import SemigroupBasis.CoRoots.Order6SporadicSection18BasisReduction
import SemigroupBasis.CoRoots.Order6SporadicSection18CanonicalWord

/-! Discharge the canonicalizer's boundary hypotheses on the unrestricted
reduction domain. A connected factor has nonsimple first and last letters;
this remains true when arbitrary many such factors are concatenated. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6SporadicSection12

private theorem word_nonempty (word : Word Nat) : word.toList ≠ [] := by
  cases word
  simp [Word.toList]

theorem connected_head_nonsimple (word : Word Nat) (connected : Connected word) :
    word.toList.count word.head ≠ 1 := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          have impossible : 2 ≤ 1 := by
            simpa only [Word.toList, List.length_cons, List.length_nil] using connected.1
          omega
      | cons next rest =>
          intro one
          have equation : (next :: rest).count head + 1 = 1 := by
            simpa only [Word.toList, List.count_cons_self] using one
          have zero : (next :: rest).count head = 0 := by omega
          have absent : head ∉ next :: rest := List.count_eq_zero.mp zero
          apply connected.2
          refine ⟨Word.singleton head, Word.mk next rest, rfl, ?_⟩
          intro letter leftMember rightMember
          have equal : letter = head := by simpa using leftMember
          subst letter
          exact absent rightMember

theorem connected_last_nonsimple (word : Word Nat) (connected : Connected word)
    (before : List Nat) (last : Nat) (shape : word.toList = before ++ [last]) :
    word.toList.count last ≠ 1 := by
  intro one
  have beforeNonempty : before ≠ [] := by
    intro empty
    have long := connected.1
    rw [shape, empty] at long
    simp only [List.nil_append, List.length_cons, List.length_nil] at long
    omega
  have equation : before.count last + 1 = 1 := by
    simpa only [shape, List.count_append, List.count_cons_self, List.count_nil] using one
  have zero : before.count last = 0 := by omega
  have absent : last ∉ before := List.count_eq_zero.mp zero
  obtain ⟨head, tail, beforeShape⟩ := List.exists_cons_of_ne_nil beforeNonempty
  let prefixWord : Word Nat := ⟨head, tail⟩
  have wordShape : word = prefixWord ++ Word.singleton last := by
    apply Word.toList_injective
    simpa only [prefixWord, Word.toList_append, Word.toList_singleton, Word.toList, beforeShape] using shape
  apply connected.2
  refine ⟨prefixWord, Word.singleton last, wordShape, ?_⟩
  intro letter leftMember rightMember
  have equal : letter = last := by simpa using rightMember
  subst letter
  apply absent
  simpa only [beforeShape, prefixWord, Word.toList] using leftMember

theorem connected_nonsimpleEnds (word : Word Nat) (connected : Connected word) :
    Canonical.StartsN word.toList ∧ Canonical.EndsN word.toList := by
  refine ⟨⟨word.head, word.tail, rfl, connected_head_nonsimple word connected⟩, ?_⟩
  have reverseNonempty : word.toList.reverse ≠ [] := by
    intro empty
    have reversed := congrArg List.reverse empty
    exact word_nonempty word (by simpa only [List.reverse_reverse, List.reverse_nil] using reversed)
  obtain ⟨last, beforeRev, reversedShape⟩ := List.exists_cons_of_ne_nil reverseNonempty
  have shape : word.toList = beforeRev.reverse ++ [last] := by
    have reversed := congrArg List.reverse reversedShape
    simpa only [List.reverse_reverse, List.reverse_cons] using reversed
  exact ⟨beforeRev.reverse, last, shape, connected_last_nonsimple word connected _ _ shape⟩

theorem nonsimpleEnds_append (left right : Word Nat)
    (leftEnds : Canonical.StartsN left.toList ∧ Canonical.EndsN left.toList)
    (rightEnds : Canonical.StartsN right.toList ∧ Canonical.EndsN right.toList) :
    Canonical.StartsN (left ++ right).toList ∧ Canonical.EndsN (left ++ right).toList := by
  obtain ⟨head, tail, leftShape, headNotOne⟩ := leftEnds.1
  obtain ⟨before, last, rightShape, lastNotOne⟩ := rightEnds.2
  have headPositive : 0 < left.toList.count head := by
    apply List.count_pos_iff.mpr
    rw [leftShape]
    exact List.Mem.head tail
  have lastPositive : 0 < right.toList.count last := by
    apply List.count_pos_iff.mpr
    rw [rightShape]
    exact List.mem_append.mpr (Or.inr (List.Mem.head []))
  constructor
  · refine ⟨head, tail ++ right.toList, ?_, ?_⟩
    · rw [Word.toList_append, leftShape]
      rfl
    · change (left ++ right).toList.count head ≠ 1
      rw [Word.toList_append, List.count_append]
      omega
  · refine ⟨left.toList ++ before, last, ?_, ?_⟩
    · rw [Word.toList_append, rightShape, List.append_assoc]
    · change (left ++ right).toList.count last ≠ 1
      rw [Word.toList_append, List.count_append]
      omega

private theorem appendFactors_nonsimpleEnds
    (first : Word Nat) (rest : List (Word Nat))
    (firstEnds : Canonical.StartsN first.toList ∧ Canonical.EndsN first.toList)
    (restEnds : ∀ word ∈ rest, Canonical.StartsN word.toList ∧ Canonical.EndsN word.toList) :
    Canonical.StartsN (appendFactors first rest).toList ∧
      Canonical.EndsN (appendFactors first rest).toList := by
  induction rest generalizing first with
  | nil => exact firstEnds
  | cons next rest ih =>
      have nextEnds := restEnds next (List.Mem.head rest)
      have combined := nonsimpleEnds_append first next firstEnds nextEnds
      exact ih (first ++ next) combined (fun word member => restEnds word (List.Mem.tail next member))

theorem pairwiseConnected_nonsimpleEnds (word : Word Nat)
    (product : PairwiseDisjointConnectedProduct word) :
    Canonical.StartsN word.toList ∧ Canonical.EndsN word.toList := by
  obtain ⟨first, rest, connected, _, shape⟩ := product
  rw [shape]
  apply appendFactors_nonsimpleEnds
  · exact connected_nonsimpleEnds first (connected first (List.Mem.head rest))
  · intro factor member
    exact connected_nonsimpleEnds factor (connected factor (List.Mem.tail first member))

/-- Both nonsimple-end hypotheses are now consequences of the actual finite-
support reduction domain, not extra assumptions on an arbitrary identity. -/
theorem canonicalize_pairwiseConnected_identity (identity : Identity Nat)
    (valid : identity.SatisfiedBy Actual.table.semigroup)
    (leftProduct : PairwiseDisjointConnectedProduct identity.lhs)
    (rightProduct : PairwiseDisjointConnectedProduct identity.rhs)
    (simple : Canonical.HasSimple identity.lhs.toList) :
    ∃ left right, Canonical.CanonicalForm left ∧ Canonical.CanonicalForm right ∧
      ListDerives identity.lhs.toList left ∧ ListDerives identity.rhs.toList right ∧ Actual.SameEval left right := by
  have leftEnds := pairwiseConnected_nonsimpleEnds identity.lhs leftProduct
  have rightEnds := pairwiseConnected_nonsimpleEnds identity.rhs rightProduct
  exact Canonical.canonicalize_identity identity valid
    leftEnds.1 leftEnds.2 rightEnds.1 rightEnds.2 simple

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.connected_head_nonsimple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.connected_last_nonsimple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.connected_nonsimpleEnds
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.nonsimpleEnds_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.pairwiseConnected_nonsimpleEnds
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.canonicalize_pairwiseConnected_identity

end SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction
