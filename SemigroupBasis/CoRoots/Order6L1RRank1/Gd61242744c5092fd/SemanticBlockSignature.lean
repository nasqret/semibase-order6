import SemigroupBasis.CoRoots.Order6L1RRank1.CanonicalSearch
import SemigroupBasis.Generated.CatalogueOrder4

/-!
# Exact catalogue-table signature for the Gd right factor

Off-tree design draft.  The cheap probe fields precede the complete term
function vector so derived equality can reject most candidates before the
exponential field is reduced.  The complete vector is the authoritative
semantic field.
-/

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd

open SemigroupBasis

namespace SemanticBlockSignature

/-- The exact public catalogue table selected as the Gd right factor. -/
abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_71.table

/-- Values of the four-element carrier, in the enumeration order used by
the term-function vector. -/
@[reducible] def carrier : List (Fin 4) := [0, 1, 2, 3]

/-- All tuples of the requested length, with the leftmost coordinate changing
slowest. -/
@[reducible] def assignments : Nat → List (List (Fin 4))
  | 0 => [[]]
  | length + 1 =>
      carrier.flatMap fun value =>
        (assignments length).map fun suffix => value :: suffix

/-- Interpret a tuple against a support list.  The default is the two-sided
identity of the selected table; it is unreachable on a covered word. -/
@[reducible] def assignmentValuation :
    List Nat → List (Fin 4) → Nat → Fin 4
  | [], _, _ => 3
  | _, [], _ => 3
  | supportHead :: supportTail, valueHead :: valueTail, letter =>
      if letter = supportHead then valueHead
      else assignmentValuation supportTail valueTail letter

/-- Detect absence, one occurrence, or at least two occurrences of one
selected letter. -/
@[reducible] def multiplicityValuation
    (selected : Nat) : Nat → Fin 4 :=
  fun letter => if letter = selected then 1 else 3

/-- Detect the simple-order and multiple-last-gap relation of an ordered
letter pair.  Equal pair entries are harmless redundant probes. -/
@[reducible] def orderGapValuation
    (first second : Nat) : Nat → Fin 4 :=
  fun letter =>
    if letter = first then 2
    else if letter = second then 1
    else 3

@[reducible] def multiplicityValuations
    (support : List Nat) : List (Nat → Fin 4) :=
  support.map multiplicityValuation

@[reducible] def orderGapValuations
    (support : List Nat) : List (Nat → Fin 4) :=
  support.flatMap fun first =>
    support.map fun second => orderGapValuation first second

@[reducible] def termValuations
    (support : List Nat) : List (Nat → Fin 4) :=
  (assignments support.length).map fun values =>
    assignmentValuation support values

@[reducible] def evaluationVector
    (valuations : List (Nat → Fin 4))
    (word : Word Nat) : List (Fin 4) :=
  valuations.map fun valuation => table.semigroup.eval valuation word

/-- Exact right-factor signature.  Field order is intentional: the linear
and quadratic probes are equality accelerators, while `termTable` is the
complete term function on the literal support. -/
structure Data where
  multiplicityProbes : List (Fin 4)
  orderGapProbes : List (Fin 4)
  termTable : List (Fin 4)
deriving DecidableEq, Repr

@[reducible] def make (support : List Nat) (word : Word Nat) : Data :=
  ⟨evaluationVector (multiplicityValuations support) word,
    evaluationVector (orderGapValuations support) word,
    evaluationVector (termValuations support) word⟩

/-- Validity in the selected table preserves any fixed evaluation vector. -/
theorem evaluationVector_eq_of_valid
    {left right : Word Nat}
    (valuations : List (Nat → Fin 4))
    (valid :
      (Identity.mk left right).SatisfiedBy table.semigroup) :
    evaluationVector valuations left =
      evaluationVector valuations right := by
  apply List.map_congr_left
  intro valuation _
  exact valid valuation

/-- The complete semantic relation preserves the complete accelerated
signature whenever both sides use the same support enumeration. -/
theorem make_eq_of_valid
    {left right : Word Nat}
    (support : List Nat)
    (valid :
      (Identity.mk left right).SatisfiedBy table.semigroup) :
    make support left = make support right := by
  unfold make
  rw [evaluationVector_eq_of_valid (multiplicityValuations support) valid,
    evaluationVector_eq_of_valid (orderGapValuations support) valid,
    evaluationVector_eq_of_valid (termValuations support) valid]

/-- Same theorem with independently computed supports. -/
theorem make_eq_of_support_eq_of_valid
    {left right : Word Nat}
    {leftSupport rightSupport : List Nat}
    (supportEqual : leftSupport = rightSupport)
    (valid :
      (Identity.mk left right).SatisfiedBy table.semigroup) :
    make leftSupport left = make rightSupport right := by
  subst rightSupport
  exact make_eq_of_valid leftSupport valid

private theorem mem_carrier (value : Fin 4) :
    value ∈ carrier := by
  simp only [carrier, List.mem_cons, List.not_mem_nil, or_false]
  have possibilities :
      value.val = 0 ∨ value.val = 1 ∨
        value.val = 2 ∨ value.val = 3 := by
    omega
  rcases possibilities with first | second | third | fourth
  · left
    apply Fin.ext
    exact first
  · right; left
    apply Fin.ext
    exact second
  · right; right; left
    apply Fin.ext
    exact third
  · right; right; right
    apply Fin.ext
    exact fourth

/-- Every pointwise valuation tuple over a support occurs in the exhaustive
assignment enumeration. -/
private theorem map_mem_assignments (valuation : Nat → Fin 4) :
    ∀ support : List Nat,
      support.map valuation ∈ assignments support.length
  | [] => by simp [assignments]
  | head :: tail => by
      simp only [List.map_cons, List.length_cons, assignments,
        List.mem_flatMap, List.mem_map]
      refine ⟨valuation head, mem_carrier (valuation head),
        tail.map valuation, ?_, rfl⟩
      exact map_mem_assignments valuation tail

/-- Interpreting the tuple obtained by mapping a valuation over the support
recovers that valuation at every supported letter.  Duplicate support entries
are harmless because every occurrence carries the same value. -/
private theorem assignmentValuation_map_eq
    (valuation : Nat → Fin 4) :
    ∀ (support : List Nat) (letter : Nat),
      letter ∈ support →
        assignmentValuation support (support.map valuation) letter =
          valuation letter
  | [], _, member => by simp at member
  | head :: tail, letter, member => by
      simp only [List.map_cons, assignmentValuation]
      by_cases equal : letter = head
      · subst letter
        simp
      · rw [if_neg equal]
        apply assignmentValuation_map_eq valuation tail letter
        exact (List.mem_cons.mp member).resolve_left equal

private theorem foldl_eval_congr
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S) :
    ∀ (letters : List Nat) (initial : S),
      (∀ letter, letter ∈ letters →
        leftValuation letter = rightValuation letter) →
      letters.foldl
          (fun value letter =>
            semigroup.mul value (leftValuation letter))
          initial =
        letters.foldl
          (fun value letter =>
            semigroup.mul value (rightValuation letter))
          initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply foldl_eval_congr semigroup
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem eval_congr_on_support
    (semigroup : Semigroup S)
    (leftValuation rightValuation : Nat → S)
    (word : Word Nat)
    (agree :
      ∀ letter, letter ∈ word.toList →
        leftValuation letter = rightValuation letter) :
    semigroup.eval leftValuation word =
      semigroup.eval rightValuation word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [agree head (by simp [Word.toList])]
      apply foldl_eval_congr semigroup
      intro letter member
      exact agree letter (List.Mem.tail head member)

/-- Equality of evaluation vectors gives equality at every listed valuation.
This uses the position of the valuation, not merely membership of the result
value, so repeated coordinates cause no loss of information. -/
private theorem evaluationVector_eq_at
    {left right : Word Nat} (valuation : Nat → Fin 4) :
    ∀ valuations : List (Nat → Fin 4),
      valuation ∈ valuations →
      evaluationVector valuations left =
        evaluationVector valuations right →
      table.semigroup.eval valuation left =
        table.semigroup.eval valuation right
  | [], member, _ => by simp at member
  | head :: tail, member, same => by
      change
        table.semigroup.eval head left ::
            evaluationVector tail left =
          table.semigroup.eval head right ::
            evaluationVector tail right at same
      rcases List.mem_cons.mp member with equal | tailMember
      · subst valuation
        exact (List.cons.inj same).1
      · exact evaluationVector_eq_at valuation tail tailMember
          (List.cons.inj same).2

/-- The complete term-function coordinate is semantically exact for words
whose letters are covered by the supplied support. -/
theorem valid_of_termTable_eq
    {left right : Word Nat}
    (support : List Nat)
    (leftCovered :
      ∀ letter, letter ∈ left.toList → letter ∈ support)
    (rightCovered :
      ∀ letter, letter ∈ right.toList → letter ∈ support)
    (same :
      (make support left).termTable =
        (make support right).termTable) :
    (Identity.mk left right).SatisfiedBy table.semigroup := by
  change evaluationVector (termValuations support) left =
    evaluationVector (termValuations support) right at same
  intro valuation
  let induced : Nat → Fin 4 :=
    assignmentValuation support (support.map valuation)
  have inducedMember : induced ∈ termValuations support := by
    unfold termValuations induced
    exact List.mem_map.mpr
      ⟨support.map valuation,
        map_mem_assignments valuation support, rfl⟩
  have inducedEqual :
      table.semigroup.eval induced left =
        table.semigroup.eval induced right :=
    evaluationVector_eq_at induced (termValuations support)
      inducedMember same
  have leftAgree :
      table.semigroup.eval induced left =
        table.semigroup.eval valuation left := by
    apply eval_congr_on_support
    intro letter member
    exact assignmentValuation_map_eq valuation support letter
      (leftCovered letter member)
  have rightAgree :
      table.semigroup.eval induced right =
        table.semigroup.eval valuation right := by
    apply eval_congr_on_support
    intro letter member
    exact assignmentValuation_map_eq valuation support letter
      (rightCovered letter member)
  exact leftAgree.symm.trans (inducedEqual.trans rightAgree)

theorem termTable_eq_iff_valid
    {left right : Word Nat}
    (support : List Nat)
    (leftCovered :
      ∀ letter, letter ∈ left.toList → letter ∈ support)
    (rightCovered :
      ∀ letter, letter ∈ right.toList → letter ∈ support) :
    (make support left).termTable =
        (make support right).termTable ↔
      (Identity.mk left right).SatisfiedBy table.semigroup := by
  constructor
  · exact valid_of_termTable_eq support leftCovered rightCovered
  · intro valid
    exact congrArg Data.termTable (make_eq_of_valid support valid)

end SemanticBlockSignature

end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
