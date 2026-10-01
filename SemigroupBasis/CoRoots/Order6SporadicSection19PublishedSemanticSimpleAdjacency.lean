import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedCanonicalPresentation

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSimpleAdjacency

open RootFamily CanonicalPresentation

/-- Typed boundary for the frozen table; numerical probes live in Fin6. -/
abbrev mul6 (left right : Fin 6) : Fin 6 := table.mul left right

theorem mul6_assoc (left middle right : Fin 6) :
    mul6 (mul6 left middle) right = mul6 left (mul6 middle right) :=
  table.assoc left middle right

/-- Actual equality of C8 word functions, not a derivation or a finite screen. -/
def EqualEval (source target : Word Nat) : Prop :=
  ∀ valuation : Nat → Fin 6,
    table.semigroup.eval valuation source = table.semigroup.eval valuation target

def run (valuation : Nat → Fin 6) (initial : Fin 6) (letters : List Nat) : Fin 6 :=
  letters.foldl (fun state letter => mul6 state (valuation letter)) initial

theorem run_nil (valuation : Nat → Fin 6) (initial : Fin 6) :
    run valuation initial [] = initial := by
  simp only [run, List.foldl_nil]

theorem run_cons (valuation : Nat → Fin 6) (initial : Fin 6)
    (letter : Nat) (rest : List Nat) :
    run valuation initial (letter :: rest) =
      run valuation (mul6 initial (valuation letter)) rest := by
  simp only [run, List.foldl_cons]

theorem run_append (valuation : Nat → Fin 6) (initial : Fin 6) (left right : List Nat) :
    run valuation initial (left ++ right) = run valuation (run valuation initial left) right := by
  simp only [run, List.foldl_append]

/-- The padded list evaluator is exactly left multiplication of the actual
nonempty-word evaluation. The extra initial state is not a new variable. -/
theorem run_word_left (valuation : Nat → Fin 6) (word : Word Nat) (left : Fin 6) :
    run valuation left word.toList = mul6 left (table.semigroup.eval valuation word) := by
  have foldMul : ∀ (letters : List Nat) (initial : Fin 6),
      run valuation (mul6 left initial) letters =
        mul6 left (run valuation initial letters) := by
    intro letters
    induction letters with
    | nil =>
      intro initial
      simp only [run_nil]
    | cons letter rest ih =>
      intro initial
      simp only [run_cons]
      rw [mul6_assoc]
      exact ih (mul6 initial (valuation letter))
  cases word with
  | mk first rest =>
    change run valuation left (first :: rest) =
      mul6 left (run valuation (valuation first) rest)
    rw [run_cons]
    exact foldMul rest (valuation first)

def occurrenceProbe (tested letter : Nat) : Fin 6 := if letter = tested then 1 else 5

theorem occurrence_first (tested : Nat) : occurrenceProbe tested tested = 1 := by
  unfold occurrenceProbe
  exact if_pos rfl

theorem occurrence_other (tested letter : Nat) (different : letter ≠ tested) :
    occurrenceProbe tested letter = 5 := by
  unfold occurrenceProbe
  exact if_neg different

def countValue : Nat → Fin 6
  | 0 => 5
  | 1 => 1
  | _ + 2 => 0

theorem occurrence_step (tested letter hits : Nat) :
    mul6 (countValue hits) (occurrenceProbe tested letter) =
      countValue (hits + if letter = tested then 1 else 0) := by
  by_cases same : letter = tested
  · subst letter
    rw [occurrence_first, if_pos (rfl : tested = tested)]
    cases hits with
    | zero => decide
    | succ rest =>
      cases rest with
      | zero => decide
      | succ rest =>
        change mul6 (0 : Fin 6) 1 = 0
        decide
  · rw [occurrence_other tested letter same, if_neg same, Nat.add_zero]
    cases hits with
    | zero => decide
    | succ rest =>
      cases rest with
      | zero => decide
      | succ rest =>
        change mul6 (0 : Fin 6) 5 = 0
        decide

theorem occurrence_fold (tested : Nat) (letters : List Nat) (hits : Nat) :
    run (occurrenceProbe tested) (countValue hits) letters =
      countValue (hits + letters.count tested) := by
  induction letters generalizing hits with
  | nil => simp only [run_nil, List.count_nil, Nat.add_zero]
  | cons letter rest ih =>
    rw [run_cons, occurrence_step, ih]
    by_cases same : letter = tested
    · subst letter
      rw [if_pos (rfl : tested = tested), List.count_cons_self]
      apply congrArg countValue
      omega
    · rw [if_neg same, Nat.add_zero, List.count_cons_of_ne same]

/-- The actual frozen {0,1,5} submonoid distinguishes zero, one and at least
two occurrences. This is an arbitrary-word induction, not a bounded count. -/
theorem occurrence_eval (tested : Nat) (word : Word Nat) :
    mul6 5 (table.semigroup.eval (occurrenceProbe tested) word) =
      countValue (word.toList.count tested) := by
  calc
    mul6 5 (table.semigroup.eval (occurrenceProbe tested) word) =
        run (occurrenceProbe tested) 5 word.toList := (run_word_left _ word 5).symm
    _ = countValue (word.toList.count tested) := by
      simpa only [Nat.zero_add] using occurrence_fold tested word.toList 0

theorem countValue_zero_iff (hits : Nat) : countValue hits = 5 ↔ hits = 0 := by
  cases hits with
  | zero => decide
  | succ rest =>
    cases rest with
    | zero => decide
    | succ rest =>
      constructor
      · intro equal
        exact False.elim ((by decide : (0 : Fin 6) ≠ 5) equal)
      · intro impossible
        omega

theorem countValue_one_iff (hits : Nat) : countValue hits = 1 ↔ hits = 1 := by
  cases hits with
  | zero => decide
  | succ rest =>
    cases rest with
    | zero => decide
    | succ rest =>
      constructor
      · intro equal
        exact False.elim ((by decide : (0 : Fin 6) ≠ 1) equal)
      · intro impossible
        omega

theorem countValue_many_iff (hits : Nat) : countValue hits = 0 ↔ 2 ≤ hits := by
  cases hits with
  | zero => decide
  | succ rest =>
    cases rest with
    | zero => decide
    | succ rest =>
      constructor
      · intro _equal
        omega
      · intro _many
        rfl

theorem semantic_occurrence_categories (source target : Word Nat)
    (equalEval : EqualEval source target) (tested : Nat) :
    (source.toList.count tested = 0 ↔ target.toList.count tested = 0) ∧
    (source.toList.count tested = 1 ↔ target.toList.count tested = 1) ∧
    (2 ≤ source.toList.count tested ↔ 2 ≤ target.toList.count tested) := by
  have states : countValue (source.toList.count tested) = countValue (target.toList.count tested) :=
    (occurrence_eval tested source).symm.trans
      ((congrArg (fun value : Fin 6 => mul6 5 value) (equalEval (occurrenceProbe tested))).trans
        (occurrence_eval tested target))
  refine ⟨?_, ?_, ?_⟩
  · calc
      source.toList.count tested = 0 ↔ countValue (source.toList.count tested) = 5 :=
        (countValue_zero_iff _).symm
      _ ↔ countValue (target.toList.count tested) = 5 := by rw [states]
      _ ↔ target.toList.count tested = 0 := countValue_zero_iff _
  · calc
      source.toList.count tested = 1 ↔ countValue (source.toList.count tested) = 1 :=
        (countValue_one_iff _).symm
      _ ↔ countValue (target.toList.count tested) = 1 := by rw [states]
      _ ↔ target.toList.count tested = 1 := countValue_one_iff _
  · calc
      2 ≤ source.toList.count tested ↔ countValue (source.toList.count tested) = 0 :=
        (countValue_many_iff _).symm
      _ ↔ countValue (target.toList.count tested) = 0 := by rw [states]
      _ ↔ 2 ≤ target.toList.count tested := countValue_many_iff _

def edgeProbe (first second letter : Nat) : Fin 6 :=
  if letter = first then 4 else if letter = second then 2 else 5

theorem probe_first (first second : Nat) : edgeProbe first second first = 4 := by
  unfold edgeProbe
  exact if_pos rfl

theorem probe_second (first second : Nat) (different : first ≠ second) :
    edgeProbe first second second = 2 := by
  unfold edgeProbe
  rw [if_neg (Ne.symm different)]
  exact if_pos rfl

theorem probe_other (first second letter : Nat) (notFirst : letter ≠ first)
    (notSecond : letter ≠ second) : edgeProbe first second letter = 5 := by
  simp only [edgeProbe, if_neg notFirst, if_neg notSecond]

def Avoid (first second : Nat) (letters : List Nat) : Prop :=
  first ∉ letters ∧ second ∉ letters

theorem avoid_nil (first second : Nat) : Avoid first second [] := by
  constructor <;> intro member <;> cases member

theorem avoid_tail (first second letter : Nat) (rest : List Nat)
    (avoiding : Avoid first second (letter :: rest)) : Avoid first second rest := by
  exact ⟨fun member => avoiding.1 (List.mem_cons.mpr (Or.inr member)),
    fun member => avoiding.2 (List.mem_cons.mpr (Or.inr member))⟩

theorem avoid_cons (first second letter : Nat) (rest : List Nat)
    (notFirst : letter ≠ first) (notSecond : letter ≠ second)
    (avoiding : Avoid first second rest) : Avoid first second (letter :: rest) := by
  constructor
  · intro member
    rcases List.mem_cons.mp member with equal | later
    · exact notFirst equal.symm
    · exact avoiding.1 later
  · intro member
    rcases List.mem_cons.mp member with equal | later
    · exact notSecond equal.symm
    · exact avoiding.2 later

def Adjacent (first second : Nat) (letters : List Nat) : Prop :=
  ∃ before after : List Nat, letters = before ++ first :: second :: after

def CleanEdge (first second : Nat) (letters : List Nat) : Prop :=
  ∃ before after : List Nat, letters = before ++ first :: second :: after ∧
    Avoid first second before ∧ Avoid first second after

theorem probe_from_zero (first second : Nat) (letters : List Nat) :
    run (edgeProbe first second) 0 letters = 0 := by
  induction letters with
  | nil => exact run_nil _ _
  | cons letter rest ih =>
    have zero : ∀ value : Fin 6, mul6 0 value = 0 := by decide
    rw [run_cons, zero]
    exact ih

theorem probe_run_avoiding (first second : Nat) (initial : Fin 6)
    (stable : mul6 initial 5 = initial) :
    ∀ letters : List Nat, Avoid first second letters →
      run (edgeProbe first second) initial letters = initial := by
  intro letters
  induction letters with
  | nil =>
    intro _avoiding
    exact run_nil _ _
  | cons letter rest ih =>
    intro avoiding
    have notFirst : letter ≠ first := fun equal =>
      avoiding.1 (List.mem_cons.mpr (Or.inl equal.symm))
    have notSecond : letter ≠ second := fun equal =>
      avoiding.2 (List.mem_cons.mpr (Or.inl equal.symm))
    rw [run_cons, probe_other first second letter notFirst notSecond, stable]
    exact ih (avoid_tail first second letter rest avoiding)

/-- Once the accepting state 1 is reached, exactly the letters different
from both probes may follow. Both tested values would send it to zero. -/
theorem probe_from_one_iff (first second : Nat) (different : first ≠ second)
    (letters : List Nat) :
    run (edgeProbe first second) 1 letters = 1 ↔ Avoid first second letters := by
  induction letters with
  | nil => exact ⟨fun _ => avoid_nil _ _, fun _ => run_nil _ _⟩
  | cons letter rest ih =>
    by_cases isFirst : letter = first
    · subst letter
      have step : mul6 (1 : Fin 6) 4 = 0 := by decide
      rw [run_cons, probe_first, step, probe_from_zero]
      constructor
      · intro impossible
        exact False.elim ((by decide : (0 : Fin 6) ≠ 1) impossible)
      · intro avoiding
        exact False.elim (avoiding.1 (List.mem_cons.mpr (Or.inl rfl)))
    · by_cases isSecond : letter = second
      · subst letter
        have step : mul6 (1 : Fin 6) 2 = 0 := by decide
        rw [run_cons, probe_second first second different, step, probe_from_zero]
        constructor
        · intro impossible
          exact False.elim ((by decide : (0 : Fin 6) ≠ 1) impossible)
        · intro avoiding
          exact False.elim (avoiding.2 (List.mem_cons.mpr (Or.inl rfl)))
      · have step : mul6 (1 : Fin 6) 5 = 1 := by decide
        rw [run_cons, probe_other first second letter isFirst isSecond, step, ih]
        exact ⟨avoid_cons first second letter rest isFirst isSecond,
          avoid_tail first second letter rest⟩

/-- With no further first probe available, state 3 can accept only an
IMMEDIATE second probe followed by a clean suffix. An intervening ordinary
letter sends state 3 to zero: literal adjacency is essential. -/
theorem probe_from_three_edge (first second : Nat) (different : first ≠ second)
    (letters : List Nat) (firstAbsent : first ∉ letters)
    (evaluated : run (edgeProbe first second) 3 letters = 1) :
    ∃ after : List Nat, letters = second :: after ∧ Avoid first second after := by
  cases letters with
  | nil =>
    have impossible : (3 : Fin 6) = 1 := by simpa only [run_nil] using evaluated
    exact False.elim ((by decide : (3 : Fin 6) ≠ 1) impossible)
  | cons letter rest =>
    have notFirst : letter ≠ first := fun equal =>
      firstAbsent (List.mem_cons.mpr (Or.inl equal.symm))
    by_cases isSecond : letter = second
    · subst letter
      have step : mul6 (3 : Fin 6) 2 = 1 := by decide
      have accepted : run (edgeProbe first second) 1 rest = 1 := by
        simpa only [run_cons, probe_second first second different, step] using evaluated
      exact ⟨rest, rfl, (probe_from_one_iff first second different rest).mp accepted⟩
    · have step : mul6 (3 : Fin 6) 5 = 0 := by decide
      have impossible : (0 : Fin 6) = 1 := by
        simpa only [run_cons, probe_other first second letter notFirst isSecond,
          step, probe_from_zero] using evaluated
      exact False.elim ((by decide : (0 : Fin 6) ≠ 1) impossible)

/-- Acceptance with exactly one first probe forces the actual clean
two-letter substring. No assumption of a canonical presentation is needed. -/
theorem probe_from_five_edge (first second : Nat) (different : first ≠ second) :
    ∀ letters : List Nat, letters.count first = 1 →
      run (edgeProbe first second) 5 letters = 1 → CleanEdge first second letters := by
  intro letters
  induction letters with
  | nil =>
    intro once _evaluated
    have impossible : (0 : Nat) = 1 := by simpa only [List.count_nil] using once
    omega
  | cons letter rest ih =>
    intro once evaluated
    by_cases isFirst : letter = first
    · subst letter
      have remaining : rest.count first = 0 := by
        rw [List.count_cons_self] at once
        omega
      have firstAbsent : first ∉ rest := List.count_eq_zero.mp remaining
      have step : mul6 (5 : Fin 6) 4 = 3 := by decide
      have afterFirst : run (edgeProbe first second) 3 rest = 1 := by
        simpa only [run_cons, probe_first, step] using evaluated
      obtain ⟨after, literal, avoiding⟩ :=
        probe_from_three_edge first second different rest firstAbsent afterFirst
      refine ⟨[], after, ?_, avoid_nil _ _, avoiding⟩
      simpa only [List.nil_append] using congrArg (fun tail : List Nat => first :: tail) literal
    · by_cases isSecond : letter = second
      · subst letter
        have step : mul6 (5 : Fin 6) 2 = 1 := by decide
        have accepted : run (edgeProbe first second) 1 rest = 1 := by
          simpa only [run_cons, probe_second first second different, step] using evaluated
        have avoiding : Avoid first second rest :=
          (probe_from_one_iff first second different rest).mp accepted
        have noFirst : rest.count first = 0 := List.count_eq_zero.mpr avoiding.1
        have oneFirst : rest.count first = 1 := by
          simpa only [List.count_cons_of_ne (Ne.symm different)] using once
        omega
      · have step : mul6 (5 : Fin 6) 5 = 5 := by decide
        have restOnce : rest.count first = 1 := by
          simpa only [List.count_cons_of_ne isFirst] using once
        have restEvaluated : run (edgeProbe first second) 5 rest = 1 := by
          simpa only [run_cons, probe_other first second letter isFirst isSecond, step] using evaluated
        obtain ⟨before, after, literal, beforeClean, afterClean⟩ := ih restOnce restEvaluated
        refine ⟨letter :: before, after, ?_,
          avoid_cons first second letter before isFirst isSecond beforeClean, afterClean⟩
        simp only [List.cons_append, literal]

theorem clean_edge_probe (first second : Nat) (different : first ≠ second)
    (letters : List Nat) (edge : CleanEdge first second letters) :
    run (edgeProbe first second) 5 letters = 1 := by
  obtain ⟨before, after, literal, beforeClean, afterClean⟩ := edge
  have startStable : mul6 (5 : Fin 6) 5 = 5 := by decide
  have firstStep : mul6 (5 : Fin 6) 4 = 3 := by decide
  have secondStep : mul6 (3 : Fin 6) 2 = 1 := by decide
  have finalStable : mul6 (1 : Fin 6) 5 = 1 := by decide
  have prefixRun := probe_run_avoiding first second 5 startStable before beforeClean
  rw [literal, run_append, prefixRun, run_cons, probe_first, firstStep,
    run_cons, probe_second first second different, secondStep]
  exact probe_run_avoiding first second 1 finalStable after afterClean

theorem clean_edge_of_counts (first second : Nat) (different : first ≠ second)
    (letters : List Nat) (firstOnce : letters.count first = 1)
    (secondOnce : letters.count second = 1) (edge : Adjacent first second letters) :
    CleanEdge first second letters := by
  obtain ⟨before, after, literal⟩ := edge
  have firstCount := firstOnce
  rw [literal, List.count_append, List.count_cons_self,
    List.count_cons_of_ne (Ne.symm different)] at firstCount
  have secondCount := secondOnce
  rw [literal, List.count_append, List.count_cons_of_ne different,
    List.count_cons_self] at secondCount
  have beforeFirst : before.count first = 0 := by omega
  have afterFirst : after.count first = 0 := by omega
  have beforeSecond : before.count second = 0 := by omega
  have afterSecond : after.count second = 0 := by omega
  exact ⟨before, after, literal,
    ⟨List.count_eq_zero.mp beforeFirst, List.count_eq_zero.mp beforeSecond⟩,
    ⟨List.count_eq_zero.mp afterFirst, List.count_eq_zero.mp afterSecond⟩⟩

theorem adjacency_probe_iff (first second : Nat) (different : first ≠ second)
    (letters : List Nat) (firstOnce : letters.count first = 1)
    (secondOnce : letters.count second = 1) :
    run (edgeProbe first second) 5 letters = 1 ↔ Adjacent first second letters := by
  constructor
  · intro evaluated
    obtain ⟨before, after, literal, _beforeClean, _afterClean⟩ :=
      probe_from_five_edge first second different letters firstOnce evaluated
    exact ⟨before, after, literal⟩
  · intro edge
    exact clean_edge_probe first second different letters
      (clean_edge_of_counts first second different letters firstOnce secondOnce edge)

/-- Equal C8 evaluations preserve literal ordered adjacency of distinct
simple letters. Neither deleting other letters nor comparing their supports
would prove this statement. Simplicity on the target is derived semantically. -/
theorem semantic_simple_adjacency (source target : Word Nat)
    (equalEval : EqualEval source target) (first second : Nat) (different : first ≠ second)
    (firstOnce : source.toList.count first = 1) (secondOnce : source.toList.count second = 1) :
    Adjacent first second source.toList ↔ Adjacent first second target.toList := by
  have targetFirst : target.toList.count first = 1 :=
    (semantic_occurrence_categories source target equalEval first).2.1.mp firstOnce
  have targetSecond : target.toList.count second = 1 :=
    (semantic_occurrence_categories source target equalEval second).2.1.mp secondOnce
  have padded : run (edgeProbe first second) 5 source.toList =
      run (edgeProbe first second) 5 target.toList := by
    calc
      run (edgeProbe first second) 5 source.toList =
          mul6 5 (table.semigroup.eval (edgeProbe first second) source) := run_word_left _ source 5
      _ = mul6 5 (table.semigroup.eval (edgeProbe first second) target) :=
        congrArg (fun value : Fin 6 => mul6 5 value) (equalEval (edgeProbe first second))
      _ = run (edgeProbe first second) 5 target.toList := (run_word_left _ target 5).symm
  calc
    Adjacent first second source.toList ↔ run (edgeProbe first second) 5 source.toList = 1 :=
      (adjacency_probe_iff first second different source.toList firstOnce secondOnce).symm
    _ ↔ run (edgeProbe first second) 5 target.toList = 1 := by rw [padded]
    _ ↔ Adjacent first second target.toList :=
      adjacency_probe_iff first second different target.toList targetFirst targetSecond

/-- The nonsimple-set part of the canonical comparison now follows from
semantic equality, rather than being supplied as a comparison hypothesis.
Equality of the partition into individual perfect roots remains separate. -/
theorem semantic_covered_iff (source target : Word Nat) (equalEval : EqualEval source target)
    (sourceForm : Form source) (targetForm : Form target) (letter : Nat) :
    Covered sourceForm.roots letter ↔ Covered targetForm.roots letter := by
  calc
    Covered sourceForm.roots letter ↔ 2 ≤ source.toList.count letter := sourceForm.coverage letter
    _ ↔ 2 ≤ target.toList.count letter :=
      (semantic_occurrence_categories source target equalEval letter).2.2
    _ ↔ Covered targetForm.roots letter := (targetForm.coverage letter).symm

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSimpleAdjacency

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSimpleAdjacency.occurrence_eval
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSimpleAdjacency.semantic_occurrence_categories
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSimpleAdjacency.probe_from_one_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSimpleAdjacency.probe_from_three_edge
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSimpleAdjacency.probe_from_five_edge
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSimpleAdjacency.clean_edge_probe
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSimpleAdjacency.adjacency_probe_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSimpleAdjacency.semantic_simple_adjacency
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticSimpleAdjacency.semantic_covered_iff
