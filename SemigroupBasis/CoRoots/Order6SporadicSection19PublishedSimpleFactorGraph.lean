import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedCanonicalPresentation

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorGraph

/-- Literal list occurrence, with both exterior contexts retained. -/
def Occurs (piece whole : List Nat) : Prop :=
  ∃ before after : List Nat, whole = before ++ piece ++ after

def Adjacent (whole : List Nat) (first second : Nat) : Prop :=
  ∃ before after : List Nat, whole = before ++ first :: second :: after

def SimpleLetters (whole piece : List Nat) : Prop :=
  ∀ letter ∈ piece, whole.count letter = 1

/-- Every literal edge of the proposed piece is an edge of the whole list. -/
def Trace (whole piece : List Nat) : Prop :=
  ∀ (before : List Nat) (first second : Nat) (after : List Nat),
    piece = before ++ first :: second :: after → Adjacent whole first second

def SameSimple (source target : List Nat) : Prop :=
  ∀ letter, source.count letter = 1 ↔ target.count letter = 1

def SameEdges (source target : List Nat) : Prop :=
  ∀ first second, first ≠ second → source.count first = 1 → source.count second = 1 →
    (Adjacent source first second ↔ Adjacent target first second)

/-- Nonempty maximal simple literal factors. This does not include empty
canonical gaps and does not assert their global left-to-right order. -/
def MaximalSimple (whole piece : List Nat) : Prop :=
  piece ≠ [] ∧ SimpleLetters whole piece ∧ Occurs piece whole ∧
  (∀ letter, whole.count letter = 1 → ¬ Occurs (letter :: piece) whole) ∧
  (∀ letter, whole.count letter = 1 → ¬ Occurs (piece ++ [letter]) whole)

theorem split_no_member (whole : List Nat) (tested : Nat) (before after : List Nat)
    (literal : whole = before ++ tested :: after) (once : whole.count tested = 1) :
    tested ∉ before ∧ tested ∉ after := by
  have total := once
  rw [literal, List.count_append, List.count_cons_self] at total
  constructor
  · exact List.count_eq_zero.mp (by omega : before.count tested = 0)
  · exact List.count_eq_zero.mp (by omega : after.count tested = 0)

/-- A marked letter not occurring in either left context fixes both contexts. -/
theorem unique_splits (tested : Nat) :
    ∀ (before1 before2 after1 after2 : List Nat),
      tested ∉ before1 → tested ∉ before2 →
      before1 ++ tested :: after1 = before2 ++ tested :: after2 →
      before1 = before2 ∧ after1 = after2 := by
  intro before1
  induction before1 with
  | nil =>
    intro before2 after1 after2 _absent1 absent2 equal
    cases before2 with
    | nil =>
      simp only [List.nil_append] at equal
      exact ⟨rfl, (List.cons.inj equal).2⟩
    | cons letter rest =>
      simp only [List.nil_append, List.cons_append] at equal
      have testedEq : tested = letter := (List.cons.inj equal).1
      exact False.elim (absent2 (List.mem_cons.mpr (Or.inl testedEq)))
  | cons letter rest ih =>
    intro before2 after1 after2 absent1 absent2 equal
    cases before2 with
    | nil =>
      simp only [List.cons_append, List.nil_append] at equal
      have testedEq : tested = letter := (List.cons.inj equal).1.symm
      exact False.elim (absent1 (List.mem_cons.mpr (Or.inl testedEq)))
    | cons other rest2 =>
      simp only [List.cons_append] at equal
      have parts := List.cons.inj equal
      have tailsEqual := ih rest2 after1 after2
        (fun member => absent1 (List.mem_cons.mpr (Or.inr member)))
        (fun member => absent2 (List.mem_cons.mpr (Or.inr member))) parts.2
      constructor
      · rw [parts.1, tailsEqual.1]
      · exact tailsEqual.2

theorem adjacent_tail (whole : List Nat) (first second : Nat) (before rest : List Nat)
    (literal : whole = before ++ first :: rest) (once : whole.count first = 1)
    (edge : Adjacent whole first second) :
    ∃ ending : List Nat, rest = second :: ending := by
  obtain ⟨otherBefore, ending, otherLiteral⟩ := edge
  have absent1 := (split_no_member whole first before rest literal once).1
  have absent2 := (split_no_member whole first otherBefore (second :: ending)
    otherLiteral once).1
  exact ⟨ending, (unique_splits first before otherBefore rest (second :: ending)
    absent1 absent2 (literal.symm.trans otherLiteral)).2⟩

theorem trace_cons_tail (whole : List Nat) (head : Nat) (tail : List Nat)
    (trace : Trace whole (head :: tail)) : Trace whole tail := by
  intro before first second after split
  apply trace (head :: before) first second after
  rw [split]
  simp only [List.cons_append]

theorem trace_of_occurs (whole piece : List Nat) (occurs : Occurs piece whole) :
    Trace whole piece := by
  obtain ⟨outerBefore, outerAfter, literal⟩ := occurs
  intro before first second after split
  refine ⟨outerBefore ++ before, after ++ outerAfter, ?_⟩
  calc
    whole = outerBefore ++ piece ++ outerAfter := literal
    _ = (outerBefore ++ before) ++ first :: second :: (after ++ outerAfter) := by
      rw [split]
      simp only [List.append_assoc, List.cons_append]

/-- Edge compatibility becomes one contiguous occurrence by unique anchoring. -/
theorem anchored_trace (whole : List Nat) :
    ∀ (tail : List Nat) (first : Nat) (before after : List Nat),
      whole = before ++ first :: after → SimpleLetters whole (first :: tail) →
      Trace whole (first :: tail) → ∃ ending : List Nat, after = tail ++ ending := by
  intro tail
  induction tail with
  | nil =>
    intro first before after _literal _simple _trace
    exact ⟨after, by simp only [List.nil_append]⟩
  | cons second rest ih =>
    intro first before after literal simple trace
    have edge : Adjacent whole first second :=
      trace [] first second rest (by simp only [List.nil_append])
    have once : whole.count first = 1 := simple first List.mem_cons_self
    obtain ⟨nextAfter, afterEq⟩ := adjacent_tail whole first second before after literal once edge
    have nextLiteral : whole = (before ++ [first]) ++ second :: nextAfter := by
      calc
        whole = before ++ first :: after := literal
        _ = before ++ first :: second :: nextAfter := by rw [afterEq]
        _ = (before ++ [first]) ++ second :: nextAfter := by
          simp only [List.append_assoc, List.cons_append, List.nil_append]
    have nextSimple : SimpleLetters whole (second :: rest) := by
      intro letter member
      exact simple letter (List.mem_cons_of_mem first member)
    have nextTrace : Trace whole (second :: rest) :=
      trace_cons_tail whole first (second :: rest) trace
    obtain ⟨ending, endingEq⟩ := ih second (before ++ [first]) nextAfter
      nextLiteral nextSimple nextTrace
    refine ⟨ending, ?_⟩
    calc
      after = second :: nextAfter := afterEq
      _ = second :: (rest ++ ending) := by rw [endingEq]
      _ = (second :: rest) ++ ending := by rw [List.cons_append]

theorem trace_reconstruct (whole piece : List Nat) (nonempty : piece ≠ [])
    (simple : SimpleLetters whole piece) (trace : Trace whole piece) :
    Occurs piece whole := by
  cases piece with
  | nil => exact False.elim (nonempty rfl)
  | cons first tail =>
    have once : whole.count first = 1 := simple first List.mem_cons_self
    have member : first ∈ whole := List.count_pos_iff.mp (by omega)
    obtain ⟨before, after, literal⟩ := List.mem_iff_append.mp member
    obtain ⟨ending, afterEq⟩ := anchored_trace whole tail first before after literal simple trace
    refine ⟨before, ending, ?_⟩
    calc
      whole = before ++ first :: after := literal
      _ = before ++ first :: (tail ++ ending) := by rw [afterEq]
      _ = before ++ (first :: tail) ++ ending := by
        simp only [List.append_assoc, List.cons_append]

theorem simple_edge_distinct (whole : List Nat) (first second : Nat)
    (once : whole.count first = 1) (edge : Adjacent whole first second) : first ≠ second := by
  intro equal
  subst second
  obtain ⟨before, after, literal⟩ := edge
  have total := once
  rw [literal, List.count_append] at total
  simp only [List.count_cons_self] at total
  omega

theorem same_simple_symm (source target : List Nat) (sameSimple : SameSimple source target) :
    SameSimple target source := fun letter => (sameSimple letter).symm

theorem same_edges_symm (source target : List Nat) (sameSimple : SameSimple source target)
    (sameEdges : SameEdges source target) : SameEdges target source := by
  intro first second different firstOnce secondOnce
  exact (sameEdges first second different ((sameSimple first).mpr firstOnce)
    ((sameSimple second).mpr secondOnce)).symm

theorem simple_letters_transfer (source target piece : List Nat)
    (sameSimple : SameSimple source target) (simple : SimpleLetters source piece) :
    SimpleLetters target piece := by
  intro letter member
  exact (sameSimple letter).mp (simple letter member)

/-- Only the simple vertex/edge data enter this arbitrary-list transfer. -/
theorem simple_occurs_transfer (source target piece : List Nat)
    (sameSimple : SameSimple source target) (sameEdges : SameEdges source target)
    (nonempty : piece ≠ []) (simple : SimpleLetters source piece)
    (occurs : Occurs piece source) : Occurs piece target := by
  apply trace_reconstruct target piece nonempty (simple_letters_transfer source target piece sameSimple simple)
  intro before first second after split
  have firstMember : first ∈ piece := by
    rw [split]
    exact List.mem_append_right before List.mem_cons_self
  have secondMember : second ∈ piece := by
    rw [split]
    exact List.mem_append_right before (List.mem_cons_of_mem first List.mem_cons_self)
  have firstOnce : source.count first = 1 := simple first firstMember
  have secondOnce : source.count second = 1 := simple second secondMember
  have edge : Adjacent source first second :=
    trace_of_occurs source piece occurs before first second after split
  exact (sameEdges first second (simple_edge_distinct source first second firstOnce edge)
    firstOnce secondOnce).mp edge

theorem simple_occurs_iff (source target piece : List Nat)
    (sameSimple : SameSimple source target) (sameEdges : SameEdges source target)
    (nonempty : piece ≠ []) (simple : SimpleLetters source piece) :
    Occurs piece source ↔ Occurs piece target := by
  constructor
  · exact simple_occurs_transfer source target piece sameSimple sameEdges nonempty simple
  · exact simple_occurs_transfer target source piece (same_simple_symm source target sameSimple)
      (same_edges_symm source target sameSimple sameEdges) nonempty
      (simple_letters_transfer source target piece sameSimple simple)

theorem maximal_simple_transfer (source target piece : List Nat)
    (sameSimple : SameSimple source target) (sameEdges : SameEdges source target)
    (maximal : MaximalSimple source piece) : MaximalSimple target piece := by
  obtain ⟨nonempty, simple, occurs, noLeft, noRight⟩ := maximal
  refine ⟨nonempty, simple_letters_transfer source target piece sameSimple simple, ?_, ?_, ?_⟩
  · exact simple_occurs_transfer source target piece sameSimple sameEdges nonempty simple occurs
  · intro letter once extension
    have sourceOnce : source.count letter = 1 := (sameSimple letter).mpr once
    have extendedSimple : SimpleLetters source (letter :: piece) := by
      intro tested member
      rcases List.mem_cons.mp member with same | oldMember
      · rw [same]
        exact sourceOnce
      · exact simple tested oldMember
    have extendedNonempty : letter :: piece ≠ [] := by
      intro impossible
      cases impossible
    have sourceExtension : Occurs (letter :: piece) source :=
      (simple_occurs_iff source target (letter :: piece) sameSimple sameEdges
        extendedNonempty extendedSimple).mpr extension
    exact noLeft letter sourceOnce sourceExtension
  · intro letter once extension
    have sourceOnce : source.count letter = 1 := (sameSimple letter).mpr once
    have extendedSimple : SimpleLetters source (piece ++ [letter]) := by
      intro tested member
      rcases List.mem_append.mp member with oldMember | lastMember
      · exact simple tested oldMember
      · have same : tested = letter := List.mem_singleton.mp lastMember
        rw [same]
        exact sourceOnce
    have extendedNonempty : piece ++ [letter] ≠ [] := by
      intro impossible
      have empty : [letter] = [] := (List.append_eq_nil_iff.mp impossible).2
      cases empty
    have sourceExtension : Occurs (piece ++ [letter]) source :=
      (simple_occurs_iff source target (piece ++ [letter]) sameSimple sameEdges
        extendedNonempty extendedSimple).mpr extension
    exact noRight letter sourceOnce sourceExtension

/-- Equality of simple-letter membership and ordered simple adjacency
determines the set of nonempty maximal simple factors, for arbitrary lists. -/
theorem maximal_simple_iff (source target piece : List Nat)
    (sameSimple : SameSimple source target) (sameEdges : SameEdges source target) :
    MaximalSimple source piece ↔ MaximalSimple target piece := by
  constructor
  · exact maximal_simple_transfer source target piece sameSimple sameEdges
  · exact maximal_simple_transfer target source piece (same_simple_symm source target sameSimple)
      (same_edges_symm source target sameSimple sameEdges)

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorGraph

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorGraph.unique_splits
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorGraph.adjacent_tail
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorGraph.anchored_trace
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorGraph.trace_reconstruct
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorGraph.simple_occurs_transfer
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorGraph.simple_occurs_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorGraph.maximal_simple_transfer
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorGraph.maximal_simple_iff
