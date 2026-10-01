import SemigroupBasis.CoRoots.Order6Astra.C8BranchIsolation

namespace SemigroupBasis.CoRoots.Order6Astra.C8BranchPieces

open Order6SporadicSection19.Published
open MaximalFactors FactorBoundaries BlockAlignment CanonicalPresentation RootSpanIsolation

def afterPieces (square : Word Nat) : List (List (Word Nat)) → List (Word Nat)
  | [] => []
  | gap :: rest => gap ++ square :: afterPieces square rest

def beforePieces (square : Word Nat) : List (List (Word Nat)) → List (Word Nat)
  | [] => []
  | gap :: rest => square :: (gap ++ beforePieces square rest)

theorem chain_prefix (square : Word Nat) (gaps : List (List (Word Nat))) :
    square :: afterPieces square gaps = beforePieces square gaps ++ [square] := by
  induction gaps with
  | nil => rfl
  | cons gap rest ih =>
    simpa only [afterPieces, beforePieces, List.cons_append, List.append_assoc] using
      congrArg (fun tail : List (Word Nat) => square :: (gap ++ tail)) ih

theorem afterPieces_append (square : Word Nat) (left right : List (List (Word Nat))) :
    afterPieces square (left ++ right) = afterPieces square left ++ afterPieces square right := by
  induction left with
  | nil => rfl
  | cons gap rest ih => simp only [List.cons_append, afterPieces, ih, List.append_assoc]

/-- Split every occurrence of the chosen square. The finite factor list is
arbitrary; this is an exact syntax decomposition, not a bounded search. -/
theorem split_closed (square : Word Nat) (initial : List (Word Nat)) :
    ∃ gap : List (Word Nat), ∃ rest : List (List (Word Nat)),
      initial ++ [square] = afterPieces square (gap :: rest) ∧
      ∀ part ∈ gap :: rest, square ∉ part := by
  induction initial with
  | nil =>
    refine ⟨[], [], rfl, ?_⟩
    intro part member
    have eq := List.mem_singleton.mp member
    subst part
    simp
  | cons first initial ih =>
    obtain ⟨gap, rest, split, absent⟩ := ih
    by_cases same : first = square
    · subst first
      refine ⟨[], gap :: rest, ?_, ?_⟩
      · simp only [List.cons_append, afterPieces, List.nil_append, split]
      · intro part member
        rcases List.mem_cons.mp member with empty | remaining
        · subst part
          simp
        · exact absent part remaining
    · refine ⟨first :: gap, rest, ?_, ?_⟩
      · simpa only [List.cons_append, afterPieces] using congrArg (List.cons first) split
      · intro part member
        rcases List.mem_cons.mp member with head | later
        · subst part
          intro present
          rcases List.mem_cons.mp present with equal | inside
          · exact same equal.symm
          · exact absent gap List.mem_cons_self inside
        · exact absent part (List.mem_cons_of_mem gap later)

/-- A closed factor list beginning at the chosen square splits into the
literal gaps between its consecutive occurrences. -/
theorem split_from_first (square : Word Nat) (tail : List (Word Nat))
    (closed : ∃ initial : List (Word Nat), square :: tail = initial ++ [square]) :
    ∃ gaps : List (List (Word Nat)),
      tail = afterPieces square gaps ∧ ∀ gap ∈ gaps, square ∉ gap := by
  obtain ⟨initial, closed⟩ := closed
  obtain ⟨gap, rest, split, absent⟩ := split_closed square initial
  have whole : square :: tail = afterPieces square (gap :: rest) := closed.trans split
  cases gap with
  | nil =>
    refine ⟨rest, ?_, ?_⟩
    · exact (List.cons.inj whole).2
    · intro part member
      exact absent part (List.mem_cons_of_mem [] member)
  | cons first gap =>
    have headEqual : square = first := (List.cons.inj whole).1
    exact False.elim (absent (first :: gap) List.mem_cons_self
      (List.mem_cons.mpr (Or.inl headEqual)))

theorem form_closed (word : Word Nat) (form : Form word) :
    ∃ initial : List (Word Nat),
      form.first :: expand form.chunks = initial ++ [form.first] := by
  obtain ⟨actualBefore, rootBefore, last, actual, roots⟩ := final_root_data form.first form.chunks
  obtain ⟨endBefore, ends⟩ := form.endpoints
  have lastEqual : last = form.first := last_eq_of_suffix rootBefore last endBefore form.first
    (roots.symm.trans ends)
  exact ⟨actualBefore, by simpa only [lastEqual] using actual⟩

theorem form_gaps (word : Word Nat) (form : Form word) :
    ∃ gaps : List (List (Word Nat)),
      expand form.chunks = afterPieces form.first gaps ∧
      (∀ gap ∈ gaps, form.first ∉ gap) ∧
      word.toList = form.first.toList ++ flatten (afterPieces form.first gaps) := by
  obtain ⟨gaps, split, absent⟩ := split_from_first form.first (expand form.chunks)
    (form_closed word form)
  refine ⟨gaps, split, absent, ?_⟩
  rw [← split, flatten_expand]
  exact form.literal

/-- One gap's exact exterior contexts, for application of the G1/G2 lemmas. -/
theorem gap_context (square : Word Nat) (before after : List (List (Word Nat)))
    (gap : List (Word Nat)) :
    square :: afterPieces square (before ++ gap :: after) =
      (beforePieces square before) ++ (square :: (gap ++ square :: afterPieces square after)) := by
  have context := congrArg
    (fun tail : List (Word Nat) => tail ++ (gap ++ square :: afterPieces square after))
    (chain_prefix square before)
  simpa only [afterPieces_append, afterPieces, List.cons_append, List.append_assoc,
    List.nil_append] using context

end SemigroupBasis.CoRoots.Order6Astra.C8BranchPieces

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchPieces.split_from_first
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchPieces.form_gaps
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8BranchPieces.gap_context
