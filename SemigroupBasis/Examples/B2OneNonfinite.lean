import SemigroupBasis.FiniteTable
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Nonfinite
import SemigroupBasis.Nonfinite.B2One.PerkinsCriterion
import SemigroupBasis.Transfer

namespace SemigroupBasis.Examples.B2One

open SemigroupBasis

/-!
The six-element Brandt monoid `B₂¹` in the source order

`0, a, ab, ba, 1, b`.

Perkins proved this monoid nonfinitely based in Theorem 7 of:

P. Perkins, "Bases for equational theories of semigroups",
Journal of Algebra 11 (1969), 298-314.
DOI: 10.1016/0021-8693(69)90058-1.

The local order-six catalogue stores the same monoid as `S6_8564` in a
different order. This file checks both multiplication tables, the exact
relabeling, the induced equality of identity theories, Perkins's full
identity family, the required failed identity, and both required isoterms.
The remaining source boundary is Sapir's semantic Condition (III) for one
bounded contextual rewrite. All derivation closure and transport to
`S6_8564` are internal to Lean.
-/

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then 0
  else if left = 1 then
    if right = 3 then 1
    else if right = 4 then 1
    else if right = 5 then 2
    else 0
  else if left = 2 then
    if right = 1 then 1
    else if right = 2 then 2
    else if right = 4 then 2
    else 0
  else if left = 3 then
    if right = 3 then 3
    else if right = 4 then 3
    else if right = 5 then 5
    else 0
  else if left = 4 then right
  else
    if right = 1 then 3
    else if right = 2 then 5
    else if right = 4 then 5
    else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem table_rows :
    List.ofFn (fun left : Fin 6 =>
      List.ofFn (fun right : Fin 6 => (table.mul left right).val)) =
      [[0, 0, 0, 0, 0, 0],
       [0, 0, 0, 1, 1, 2],
       [0, 1, 2, 0, 2, 0],
       [0, 0, 0, 3, 3, 5],
       [0, 1, 2, 3, 4, 5],
       [0, 3, 5, 0, 5, 0]] := by
  decide

def zero : Fin 6 := 0
def a : Fin 6 := 1
def ab : Fin 6 := 2
def ba : Fin 6 := 3
def one : Fin 6 := 4
def b : Fin 6 := 5

@[simp] theorem zero_mul (value : Fin 6) : mul zero value = zero := by
  revert value
  decide

@[simp] theorem mul_zero (value : Fin 6) : mul value zero = zero := by
  revert value
  decide

@[simp] theorem one_mul (value : Fin 6) : mul one value = value := by
  revert value
  decide

@[simp] theorem mul_one (value : Fin 6) : mul value one = value := by
  revert value
  decide

@[simp] theorem a_mul_a : mul a a = zero := by decide
@[simp] theorem b_mul_b : mul b b = zero := by decide
@[simp] theorem a_mul_b : mul a b = ab := by decide
@[simp] theorem b_mul_a : mul b a = ba := by decide

theorem a_mul_b_mul_a : mul (mul a b) a = a := by decide
theorem b_mul_a_mul_b : mul (mul b a) b = b := by decide

/-- Every table element is one of the six standard Brandt normal forms. -/
theorem carrier_normal_forms (value : Fin 6) :
    value = zero ∨ value = a ∨ value = mul a b ∨
      value = mul b a ∨ value = one ∨ value = b := by
  revert value
  decide

/-- Published-source labels to zero-based `S6_8564` catalogue labels.
In one-based notation this is `(1,2,3,4,5,6) ↦ (1,2,4,5,6,3)`. -/
def publishedToCatalogue (value : Fin 6) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 3
  else if value = 3 then 4
  else if value = 4 then 5
  else 2

def catalogueToPublished (value : Fin 6) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 5
  else if value = 3 then 2
  else if value = 4 then 3
  else 4

theorem published_to_catalogue_values :
    List.ofFn (fun value : Fin 6 => (publishedToCatalogue value).val) =
      [0, 1, 3, 4, 5, 2] := by
  decide

theorem catalogue_to_published_values :
    List.ofFn (fun value : Fin 6 => (catalogueToPublished value).val) =
      [0, 1, 5, 2, 3, 4] := by
  decide

@[simp]
theorem catalogueToPublished_publishedToCatalogue (value : Fin 6) :
    catalogueToPublished (publishedToCatalogue value) = value := by
  revert value
  decide

@[simp]
theorem publishedToCatalogue_catalogueToPublished (value : Fin 6) :
    publishedToCatalogue (catalogueToPublished value) = value := by
  revert value
  decide

def catalogueMul (left right : Fin 6) : Fin 6 :=
  publishedToCatalogue
    (mul (catalogueToPublished left) (catalogueToPublished right))

def catalogueTable : FiniteTable where
  order := 6
  mul := catalogueMul
  assoc := by decide

/-- The zero-based Cayley table stored for `S6_8564`. -/
theorem catalogue_table_rows :
    List.ofFn (fun left : Fin 6 =>
      List.ofFn (fun right : Fin 6 =>
        (catalogueTable.mul left right).val)) =
      [[0, 0, 0, 0, 0, 0],
       [0, 0, 3, 0, 1, 1],
       [0, 4, 0, 2, 0, 2],
       [0, 1, 0, 3, 0, 3],
       [0, 0, 2, 0, 4, 4],
       [0, 1, 2, 3, 4, 5]] := by
  decide

theorem publishedToCatalogue_map_mul (left right : Fin 6) :
    publishedToCatalogue (mul left right) =
      catalogueMul (publishedToCatalogue left) (publishedToCatalogue right) := by
  revert left right
  decide

theorem catalogueToPublished_map_mul (left right : Fin 6) :
    catalogueToPublished (catalogueMul left right) =
      mul (catalogueToPublished left) (catalogueToPublished right) := by
  revert left right
  decide

def publishedIntoCatalogue :
    Embedding table.semigroup catalogueTable.semigroup where
  toFun := publishedToCatalogue
  map_mul := publishedToCatalogue_map_mul
  injective := by
    intro left right equality
    have inverseEquality := congrArg catalogueToPublished equality
    simpa using inverseEquality

def catalogueIntoPublished :
    Embedding catalogueTable.semigroup table.semigroup where
  toFun := catalogueToPublished
  map_mul := catalogueToPublished_map_mul
  injective := by
    intro left right equality
    have inverseEquality := congrArg publishedToCatalogue equality
    simpa using inverseEquality

/-- The published Brandt table and the stored `S6_8564` table have exactly
the same semigroup identities. -/
theorem sameIdentityTheory_catalogue :
    SameIdentityTheory table.semigroup catalogueTable.semigroup := by
  intro identity
  constructor
  · exact catalogueIntoPublished.pullback_identity identity
  · exact publishedIntoCatalogue.pullback_identity identity

/-- The involution witnessing self-duality in published-source labels. -/
def dual (value : Fin 6) : Fin 6 :=
  if value = zero then zero
  else if value = a then b
  else if value = ab then ab
  else if value = ba then ba
  else if value = one then one
  else a

@[simp]
theorem dual_dual (value : Fin 6) : dual (dual value) = value := by
  revert value
  decide

theorem dual_mul (left right : Fin 6) :
    dual (mul left right) = mul (dual right) (dual left) := by
  revert left right
  decide

/-! ## Perkins's infinite identity family -/

private def forwardValue (valuation : Nat → Fin 6) : Nat → Fin 6
  | 0 => valuation 1
  | extra + 1 =>
      mul (forwardValue valuation extra) (valuation (extra + 2))

private def reverseValue (valuation : Nat → Fin 6) : Nat → Fin 6
  | 0 => valuation 1
  | extra + 1 =>
      mul (valuation (extra + 2)) (reverseValue valuation extra)

private theorem eval_forwardY (valuation : Nat → Fin 6) (extra : Nat) :
    table.semigroup.eval valuation
        (SemigroupBasis.Nonfinite.B2One.forwardY extra) =
      forwardValue valuation extra := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      simp only [SemigroupBasis.Nonfinite.B2One.forwardY, List.range_succ,
        List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [Semigroup.eval_append]
      have ih' :
          table.semigroup.eval valuation
              (List.foldl
                (fun current index =>
                  current ++ Word.singleton (index + 2))
                (Word.singleton 1) (List.range extra)) =
            forwardValue valuation extra := by
        simpa only [SemigroupBasis.Nonfinite.B2One.forwardY] using ih
      rw [ih']
      rfl

private theorem eval_reverseY (valuation : Nat → Fin 6) (extra : Nat) :
    table.semigroup.eval valuation
        (SemigroupBasis.Nonfinite.B2One.forwardY extra).reverse =
      reverseValue valuation extra := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      simp only [SemigroupBasis.Nonfinite.B2One.forwardY, List.range_succ,
        List.foldl_append,
        List.foldl_cons, List.foldl_nil, Word.reverse_append]
      rw [Semigroup.eval_append]
      have ih' :
          table.semigroup.eval valuation
              (List.foldl
                (fun current index =>
                  current ++ Word.singleton (index + 2))
                (Word.singleton 1) (List.range extra)).reverse =
            reverseValue valuation extra := by
        simpa only [SemigroupBasis.Nonfinite.B2One.forwardY] using ih
      rw [ih']
      rfl

/-- All pairs consisting of a product and the reverse-order product of the
same nonempty list of Brandt-monoid elements. -/
private def mirrorPairs : List (Fin 6 × Fin 6) :=
  [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5),
   (0, 1), (1, 0), (2, 3), (0, 5), (5, 0), (3, 2),
   (0, 3), (2, 0), (0, 2), (3, 0)]

private theorem mirrorPairs_base (value : Fin 6) :
    (value, value) ∈ mirrorPairs := by
  revert value
  decide

private theorem mirrorPairs_step
    {forward reverse : Fin 6}
    (member : (forward, reverse) ∈ mirrorPairs)
    (value : Fin 6) :
    (mul forward value, mul value reverse) ∈ mirrorPairs := by
  revert forward reverse value
  decide

private theorem forward_reverse_mem
    (valuation : Nat → Fin 6) (extra : Nat) :
    (forwardValue valuation extra, reverseValue valuation extra) ∈
      mirrorPairs := by
  induction extra with
  | zero => exact mirrorPairs_base (valuation 1)
  | succ extra ih =>
      exact mirrorPairs_step ih (valuation (extra + 2))

private theorem mirror_sandwich_commutes
    {forward reverse : Fin 6}
    (member : (forward, reverse) ∈ mirrorPairs)
    (outside : Fin 6) :
    mul (mul (mul outside forward) outside) reverse =
      mul (mul (mul outside reverse) outside) forward := by
  revert forward reverse outside
  decide

theorem perkins_identity_valid (extra : Nat) :
    (SemigroupBasis.Nonfinite.B2One.perkinsIdentity extra).SatisfiedBy
      table.semigroup := by
  intro valuation
  simp only [SemigroupBasis.Nonfinite.B2One.perkinsIdentity,
    SemigroupBasis.Nonfinite.B2One.perkinsLeft,
    SemigroupBasis.Nonfinite.B2One.perkinsRight,
    SemigroupBasis.Nonfinite.B2One.x, Semigroup.eval_append]
  rw [eval_forwardY, eval_reverseY]
  exact mirror_sandwich_commutes
    (forward_reverse_mem valuation extra) (valuation 0)

/-! ## Finite evaluation certificates for Perkins's two isoterms -/

private def absenceValuation (excluded letter : Nat) : Fin 6 :=
  if letter = excluded then zero else one

private theorem foldl_from_zero
    (valuation : Nat → Fin 6) (letters : List Nat) :
    letters.foldl (fun current letter => mul current (valuation letter)) zero =
      zero := by
  induction letters with
  | nil => rfl
  | cons letter letters ih =>
      simp only [List.foldl_cons, zero_mul]
      exact ih

private theorem foldl_absence_of_mem
    (excluded : Nat) (letters : List Nat) (initial : Fin 6)
    (member : excluded ∈ letters) :
    letters.foldl
        (fun current letter =>
          mul current (absenceValuation excluded letter))
        initial =
      zero := by
  induction letters generalizing initial with
  | nil => simp at member
  | cons letter letters ih =>
      simp only [List.foldl_cons]
      by_cases equality : letter = excluded
      · subst letter
        simp only [absenceValuation, if_pos, mul_zero]
        exact foldl_from_zero (absenceValuation excluded) letters
      · have tailMember : excluded ∈ letters := by
          have excludedNe : excluded ≠ letter := Ne.symm equality
          simpa [excludedNe] using member
        simp only [absenceValuation, if_neg equality, mul_one]
        exact ih initial tailMember

private theorem foldl_absence_of_not_mem
    (excluded : Nat) (letters : List Nat)
    (absent : excluded ∉ letters) :
    letters.foldl
        (fun current letter =>
          mul current (absenceValuation excluded letter))
        one =
      one := by
  induction letters with
  | nil => rfl
  | cons letter letters ih =>
      have headNe : letter ≠ excluded := by
        intro equality
        apply absent
        simp [equality]
      have tailAbsent : excluded ∉ letters := by
        intro member
        exact absent (List.Mem.tail letter member)
      simp only [List.foldl_cons, absenceValuation, if_neg headNe, one_mul]
      exact ih tailAbsent

private theorem eval_absence_of_mem
    (excluded : Nat) (word : Word Nat)
    (member : excluded ∈ word.toList) :
    table.semigroup.eval (absenceValuation excluded) word = zero := by
  cases word with
  | mk head tail =>
      simp only [Word.toList, List.mem_cons] at member
      unfold Semigroup.eval
      rcases member with headEq | tailMember
      · subst head
        simp only [absenceValuation, if_pos]
        exact foldl_from_zero (absenceValuation excluded) tail
      · by_cases headEq : head = excluded
        · subst head
          simp only [absenceValuation, if_pos]
          exact foldl_from_zero (absenceValuation excluded) tail
        · simp only [absenceValuation, if_neg headEq]
          exact foldl_absence_of_mem excluded tail one tailMember

private theorem eval_absence_of_not_mem
    (excluded : Nat) (word : Word Nat)
    (absent : excluded ∉ word.toList) :
    table.semigroup.eval (absenceValuation excluded) word = one := by
  cases word with
  | mk head tail =>
      have headNe : head ≠ excluded := by
        intro equality
        apply absent
        simp [Word.toList, equality]
      have tailAbsent : excluded ∉ tail := by
        intro member
        exact absent (by simp [Word.toList, member])
      unfold Semigroup.eval
      simp only [absenceValuation, if_neg headNe]
      exact foldl_absence_of_not_mem excluded tail tailAbsent

private theorem valid_identity_support_subset
    {left right : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup) :
    ∀ letter, letter ∈ right.toList → letter ∈ left.toList := by
  intro letter rightMember
  by_cases leftMember : letter ∈ left.toList
  · exact leftMember
  · exfalso
    have equality := valid (absenceValuation letter)
    rw [eval_absence_of_not_mem letter left leftMember,
      eval_absence_of_mem letter right rightMember] at equality
    exact (by decide : one ≠ zero) equality

private def evalList (valuation : Nat → Fin 6) (letters : List Nat) : Fin 6 :=
  letters.foldl (fun current letter => mul current (valuation letter)) one

private theorem evalList_toList (valuation : Nat → Fin 6)
    (word : Word Nat) :
    evalList valuation word.toList =
      table.semigroup.eval valuation word := by
  cases word with
  | mk head tail =>
      simp only [evalList, Word.toList, List.foldl_cons, Semigroup.eval]
      rw [one_mul]
      rfl

private def deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6) (letter : Nat) : Fin 6 :=
  if keep letter then valuation letter else one

private theorem foldl_deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6)
    (letters : List Nat) (initial : Fin 6) :
    letters.foldl
        (fun current letter =>
          mul current (deletionValuation keep valuation letter))
        initial =
      (letters.filter keep).foldl
        (fun current letter => mul current (valuation letter))
        initial := by
  induction letters generalizing initial with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons, List.filter_cons]
      by_cases kept : keep letter
      · rw [ih]
        simp [deletionValuation, kept]
      · rw [ih]
        simp [deletionValuation, kept, mul_one]

private theorem evalList_deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6)
    (letters : List Nat) :
    evalList (deletionValuation keep valuation) letters =
      evalList valuation (letters.filter keep) := by
  simp only [evalList]
  exact foldl_deletionValuation keep valuation letters one

private theorem filtered_eval_equal
    {left right : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup)
    (keep : Nat → Bool) (valuation : Nat → Fin 6) :
    evalList valuation (left.toList.filter keep) =
      evalList valuation (right.toList.filter keep) := by
  rw [← evalList_deletionValuation, ← evalList_deletionValuation,
    evalList_toList, evalList_toList]
  exact valid (deletionValuation keep valuation)

private theorem filtered_eq_of_isoterm
    {left right isotermWord : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup)
    (isoterm :
      SemigroupBasis.Nonfinite.B2One.Isoterm table.semigroup isotermWord)
    (keep : Nat → Bool)
    (leftFiltered : left.toList.filter keep = isotermWord.toList) :
    right.toList.filter keep = isotermWord.toList := by
  have headInLeftFiltered :
      isotermWord.head ∈ left.toList.filter keep := by
    rw [leftFiltered]
    simp [Word.toList]
  have headKept : keep isotermWord.head = true :=
    (List.mem_filter.mp headInLeftFiltered).2
  have headInLeft : isotermWord.head ∈ left.toList :=
    (List.mem_filter.mp headInLeftFiltered).1
  have reverseValid :
      (Identity.mk right left).SatisfiedBy table.semigroup := by
    intro valuation
    exact (valid valuation).symm
  have headInRight :=
    valid_identity_support_subset reverseValid isotermWord.head headInLeft
  have headInRightFiltered :
      isotermWord.head ∈ right.toList.filter keep :=
    List.mem_filter.mpr ⟨headInRight, headKept⟩
  cases filtered : right.toList.filter keep with
  | nil => simp [filtered] at headInRightFiltered
  | cons head tail =>
      let filteredWord : Word Nat := ⟨head, tail⟩
      have filteredWordList :
          filteredWord.toList = right.toList.filter keep := by
        rw [filtered]
        rfl
      have filteredValid :
          (Identity.mk isotermWord filteredWord).SatisfiedBy
            table.semigroup := by
        intro valuation
        rw [← evalList_toList, ← evalList_toList, filteredWordList,
          ← leftFiltered]
        exact filtered_eval_equal valid keep valuation
      have equality := isoterm filteredWord filteredValid
      exact congrArg Word.toList equality

def dualIntoOpposite :
    Embedding table.semigroup table.semigroup.opposite where
  toFun := dual
  map_mul := dual_mul
  injective := by
    intro left right equality
    have := congrArg dual equality
    simpa using this

def oppositeIntoDual :
    Embedding table.semigroup.opposite table.semigroup where
  toFun := dual
  map_mul := by
    intro left right
    exact dual_mul right left
  injective := by
    intro left right equality
    have := congrArg dual equality
    simpa using this

private theorem reversed_identity_valid
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.reversed.SatisfiedBy table.semigroup := by
  have oppositeValid :
      identity.SatisfiedBy table.semigroup.opposite :=
    oppositeIntoDual.pullback_identity identity valid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity
      table.semigroup).mp oppositeValid

private theorem reverse_isoterm
    {word : Word Nat}
    (isoterm :
      SemigroupBasis.Nonfinite.B2One.Isoterm table.semigroup word) :
    SemigroupBasis.Nonfinite.B2One.Isoterm table.semigroup word.reverse := by
  intro other valid
  have reversedValid := reversed_identity_valid valid
  have equality : other.reverse = word := by
    apply isoterm other.reverse
    simpa [Identity.reversed] using reversedValid
  have := congrArg Word.reverse equality
  simpa using this

private def UsesXYZ (letters : List Nat) : Prop :=
  ∀ letter, letter ∈ letters →
    letter = 0 ∨ letter = 1 ∨ letter = 2

private theorem xytyx_valid_rhs_usesXYZ
    {right : Word Nat}
    (valid :
      (Identity.mk SemigroupBasis.Nonfinite.B2One.xytyx right).SatisfiedBy
        table.semigroup) :
    UsesXYZ right.toList := by
  intro letter member
  have targetMember :=
    valid_identity_support_subset valid letter member
  simp only [SemigroupBasis.Nonfinite.B2One.xytyx, Word.toList,
    List.mem_cons, List.not_mem_nil, or_false] at targetMember
  rcases targetMember with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl

private theorem xtyxy_valid_rhs_usesXYZ
    {right : Word Nat}
    (valid :
      (Identity.mk SemigroupBasis.Nonfinite.B2One.xtyxy right).SatisfiedBy
        table.semigroup) :
    UsesXYZ right.toList := by
  intro letter member
  have targetMember :=
    valid_identity_support_subset valid letter member
  simp only [SemigroupBasis.Nonfinite.B2One.xtyxy, Word.toList,
    List.mem_cons, List.not_mem_nil, or_false] at targetMember
  rcases targetMember with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)

private abbrev EvalState := Fin 6 × Fin 6 × Fin 6

private def firstValuation0 (letter : Nat) : Fin 6 :=
  if letter = 0 then 4
  else if letter = 1 then 5
  else if letter = 2 then 1
  else 4

private def firstValuation1 (letter : Nat) : Fin 6 :=
  if letter = 0 then 5
  else if letter = 1 then 1
  else if letter = 2 then 5
  else 4

private def firstValuation2 (letter : Nat) : Fin 6 :=
  if letter = 0 then 5
  else if letter = 1 then 4
  else if letter = 2 then 1
  else 4

private def firstInitial (letter : Nat) : EvalState :=
  (firstValuation0 letter, firstValuation1 letter, firstValuation2 letter)

private def firstStep (state : EvalState) (letter : Nat) : EvalState :=
  (mul state.1 (firstValuation0 letter),
    mul state.2.1 (firstValuation1 letter),
    mul state.2.2 (firstValuation2 letter))

private def firstRun (state : EvalState) (letters : List Nat) : EvalState :=
  (letters.foldl
      (fun current letter => mul current (firstValuation0 letter)) state.1,
    letters.foldl
      (fun current letter => mul current (firstValuation1 letter)) state.2.1,
    letters.foldl
      (fun current letter => mul current (firstValuation2 letter)) state.2.2)

private def firstEvalState (word : Word Nat) : EvalState :=
  (table.semigroup.eval firstValuation0 word,
    table.semigroup.eval firstValuation1 word,
    table.semigroup.eval firstValuation2 word)

private theorem firstEvalState_mk (head : Nat) (tail : List Nat) :
    firstEvalState ⟨head, tail⟩ = firstRun (firstInitial head) tail :=
  rfl

private def firstTarget : EvalState := (5, 5, 5)
private def firstStage0 : EvalState := (4, 5, 5)
private def firstStage1 : EvalState := (5, 3, 5)
private def firstStage2 : EvalState := (3, 5, 3)
private def firstStage3 : EvalState := (5, 3, 3)

/-- The complete backward-reachable set of the three-valuation product
automaton for the target fingerprint `(5,5,5)`. -/
private def firstCanReach (state : EvalState) : Prop :=
  state ∈
    [(5, 5, 5), (5, 3, 3), (5, 4, 3), (5, 3, 4), (5, 4, 4),
     (3, 5, 3), (4, 5, 3), (3, 5, 4), (4, 5, 4), (5, 3, 5),
     (5, 4, 5), (3, 5, 5), (4, 5, 5), (3, 3, 3), (3, 4, 3),
     (3, 3, 4), (3, 4, 4), (4, 3, 3), (4, 4, 3), (4, 3, 4),
     (4, 4, 4)]

private theorem fin6_cases (value : Fin 6) :
    value = 0 ∨ value = 1 ∨ value = 2 ∨
      value = 3 ∨ value = 4 ∨ value = 5 := by
  omega

set_option maxHeartbeats 2000000 in
private theorem first_predecessor_closed
    (state : EvalState) (letter : Nat)
    (letterXYZ : letter = 0 ∨ letter = 1 ∨ letter = 2)
    (reachable : firstCanReach (firstStep state letter)) :
    firstCanReach state := by
  rcases state with ⟨first, second, third⟩
  rcases letterXYZ with rfl | rfl | rfl <;>
    rcases fin6_cases first with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin6_cases second with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin6_cases third with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [firstCanReach, firstStep, firstValuation0, firstValuation1,
      firstValuation2, mul] at reachable ⊢

private theorem firstCanReach_of_run
    (state : EvalState) (letters : List Nat)
    (uses : UsesXYZ letters)
    (equality : firstRun state letters = firstTarget) :
    firstCanReach state := by
  induction letters generalizing state with
  | nil =>
      have stateEq : state = firstTarget := by
        simpa [firstRun] using equality
      subst state
      simp [firstCanReach, firstTarget]
  | cons letter letters ih =>
      have headXYZ := uses letter (List.Mem.head letters)
      have tailUses : UsesXYZ letters := by
        intro value member
        exact uses value (List.Mem.tail letter member)
      apply first_predecessor_closed state letter headXYZ
      apply ih (state := firstStep state letter) tailUses
      simpa [firstRun, firstStep] using equality

private theorem firstRun_target
    (letters : List Nat) (uses : UsesXYZ letters)
    (equality : firstRun firstTarget letters = firstTarget) :
    letters = [] := by
  cases letters with
  | nil => rfl
  | cons letter letters =>
      have headXYZ := uses letter (List.Mem.head letters)
      have tailUses : UsesXYZ letters := by
        intro value member
        exact uses value (List.Mem.tail letter member)
      have reachable :
          firstCanReach (firstStep firstTarget letter) := by
        apply firstCanReach_of_run
          (state := firstStep firstTarget letter) letters tailUses
        simpa [firstRun, firstStep] using equality
      rcases headXYZ with rfl | rfl | rfl <;>
        simp [firstCanReach, firstStep, firstTarget, firstValuation0,
          firstValuation1, firstValuation2, mul] at reachable

private theorem firstRun_stage3
    (letters : List Nat) (uses : UsesXYZ letters)
    (equality : firstRun firstStage3 letters = firstTarget) :
    letters = [0] := by
  cases letters with
  | nil => simp [firstRun, firstStage3, firstTarget] at equality
  | cons letter letters =>
      have headXYZ := uses letter (List.Mem.head letters)
      have tailUses : UsesXYZ letters := by
        intro value member
        exact uses value (List.Mem.tail letter member)
      have reachable :
          firstCanReach (firstStep firstStage3 letter) := by
        apply firstCanReach_of_run
          (state := firstStep firstStage3 letter) letters tailUses
        simpa [firstRun, firstStep] using equality
      rcases headXYZ with rfl | rfl | rfl
      · have tailEq : firstRun firstTarget letters = firstTarget := by
          simpa [firstRun, firstStep, firstStage3, firstTarget] using equality
        rw [firstRun_target letters tailUses tailEq]
      · simp [firstCanReach, firstStep, firstStage3, firstValuation0,
          firstValuation1, firstValuation2, mul] at reachable
      · simp [firstCanReach, firstStep, firstStage3, firstValuation0,
          firstValuation1, firstValuation2, mul] at reachable

private theorem firstRun_stage2
    (letters : List Nat) (uses : UsesXYZ letters)
    (equality : firstRun firstStage2 letters = firstTarget) :
    letters = [1, 0] := by
  cases letters with
  | nil => simp [firstRun, firstStage2, firstTarget] at equality
  | cons letter letters =>
      have headXYZ := uses letter (List.Mem.head letters)
      have tailUses : UsesXYZ letters := by
        intro value member
        exact uses value (List.Mem.tail letter member)
      have reachable :
          firstCanReach (firstStep firstStage2 letter) := by
        apply firstCanReach_of_run
          (state := firstStep firstStage2 letter) letters tailUses
        simpa [firstRun, firstStep] using equality
      rcases headXYZ with rfl | rfl | rfl
      · simp [firstCanReach, firstStep, firstStage2, firstValuation0,
          firstValuation1, firstValuation2, mul] at reachable
      · have tailEq : firstRun firstStage3 letters = firstTarget := by
          simpa [firstRun, firstStep, firstStage2, firstStage3] using equality
        rw [firstRun_stage3 letters tailUses tailEq]
      · simp [firstCanReach, firstStep, firstStage2, firstValuation0,
          firstValuation1, firstValuation2, mul] at reachable

private theorem firstRun_stage1
    (letters : List Nat) (uses : UsesXYZ letters)
    (equality : firstRun firstStage1 letters = firstTarget) :
    letters = [2, 1, 0] := by
  cases letters with
  | nil => simp [firstRun, firstStage1, firstTarget] at equality
  | cons letter letters =>
      have headXYZ := uses letter (List.Mem.head letters)
      have tailUses : UsesXYZ letters := by
        intro value member
        exact uses value (List.Mem.tail letter member)
      have reachable :
          firstCanReach (firstStep firstStage1 letter) := by
        apply firstCanReach_of_run
          (state := firstStep firstStage1 letter) letters tailUses
        simpa [firstRun, firstStep] using equality
      rcases headXYZ with rfl | rfl | rfl
      · simp [firstCanReach, firstStep, firstStage1, firstValuation0,
          firstValuation1, firstValuation2, mul] at reachable
      · simp [firstCanReach, firstStep, firstStage1, firstValuation0,
          firstValuation1, firstValuation2, mul] at reachable
      · have tailEq : firstRun firstStage2 letters = firstTarget := by
          simpa [firstRun, firstStep, firstStage1, firstStage2] using equality
        rw [firstRun_stage2 letters tailUses tailEq]

private theorem firstRun_stage0
    (letters : List Nat) (uses : UsesXYZ letters)
    (equality : firstRun firstStage0 letters = firstTarget) :
    letters = [1, 2, 1, 0] := by
  cases letters with
  | nil => simp [firstRun, firstStage0, firstTarget] at equality
  | cons letter letters =>
      have headXYZ := uses letter (List.Mem.head letters)
      have tailUses : UsesXYZ letters := by
        intro value member
        exact uses value (List.Mem.tail letter member)
      have reachable :
          firstCanReach (firstStep firstStage0 letter) := by
        apply firstCanReach_of_run
          (state := firstStep firstStage0 letter) letters tailUses
        simpa [firstRun, firstStep] using equality
      rcases headXYZ with rfl | rfl | rfl
      · simp [firstCanReach, firstStep, firstStage0, firstValuation0,
          firstValuation1, firstValuation2, mul] at reachable
      · have tailEq : firstRun firstStage1 letters = firstTarget := by
          simpa [firstRun, firstStep, firstStage0, firstStage1] using equality
        rw [firstRun_stage1 letters tailUses tailEq]
      · simp [firstCanReach, firstStep, firstStage0, firstValuation0,
          firstValuation1, firstValuation2, mul] at reachable

private theorem xytyx_unique_of_certificate
    (word : Word Nat) (uses : UsesXYZ word.toList)
    (stateEq : firstEvalState word = firstTarget) :
    word = SemigroupBasis.Nonfinite.B2One.xytyx := by
  cases word with
  | mk head tail =>
      have headXYZ : head = 0 ∨ head = 1 ∨ head = 2 := by
        exact uses head (by simp [Word.toList])
      have tailUses : UsesXYZ tail := by
        intro letter member
        exact uses letter (by simp [Word.toList, member])
      change firstRun (firstInitial head) tail = firstTarget at stateEq
      have reachable : firstCanReach (firstInitial head) := by
        apply firstCanReach_of_run
          (state := firstInitial head) tail tailUses
        simpa [firstEvalState_mk] using stateEq
      rcases headXYZ with rfl | rfl | rfl
      · have tailEq : firstRun firstStage0 tail = firstTarget := by
          simpa [firstInitial, firstStage0] using stateEq
        have shape := firstRun_stage0 tail tailUses tailEq
        subst tail
        rfl
      · simp [firstCanReach, firstInitial, firstValuation0,
          firstValuation1, firstValuation2] at reachable
      · simp [firstCanReach, firstInitial, firstValuation0,
          firstValuation1, firstValuation2] at reachable

private theorem first_target_eval :
    firstEvalState SemigroupBasis.Nonfinite.B2One.xytyx = firstTarget := by
  decide

theorem xytyx_isoterm :
    SemigroupBasis.Nonfinite.B2One.Isoterm table.semigroup
      SemigroupBasis.Nonfinite.B2One.xytyx := by
  intro other valid
  apply xytyx_unique_of_certificate other (xytyx_valid_rhs_usesXYZ valid)
  rw [← first_target_eval]
  apply Prod.ext
  · exact (valid firstValuation0).symm
  · apply Prod.ext
    · exact (valid firstValuation1).symm
    · exact (valid firstValuation2).symm

private def secondValuation0 (letter : Nat) : Fin 6 :=
  if letter = 0 then 1
  else if letter = 1 then 5
  else if letter = 2 then 3
  else 4

private def secondValuation1 (letter : Nat) : Fin 6 :=
  if letter = 0 then 4
  else if letter = 1 then 2
  else if letter = 2 then 5
  else 4

private def secondValuation2 (letter : Nat) : Fin 6 :=
  if letter = 0 then 1
  else if letter = 1 then 4
  else if letter = 2 then 5
  else 4

private def secondInitial (letter : Nat) : EvalState :=
  (secondValuation0 letter, secondValuation1 letter, secondValuation2 letter)

private def secondStep (state : EvalState) (letter : Nat) : EvalState :=
  (mul state.1 (secondValuation0 letter),
    mul state.2.1 (secondValuation1 letter),
    mul state.2.2 (secondValuation2 letter))

private def secondRun (state : EvalState) (letters : List Nat) : EvalState :=
  (letters.foldl
      (fun current letter => mul current (secondValuation0 letter)) state.1,
    letters.foldl
      (fun current letter => mul current (secondValuation1 letter)) state.2.1,
    letters.foldl
      (fun current letter => mul current (secondValuation2 letter)) state.2.2)

private def secondEvalState (word : Word Nat) : EvalState :=
  (table.semigroup.eval secondValuation0 word,
    table.semigroup.eval secondValuation1 word,
    table.semigroup.eval secondValuation2 word)

private def secondTarget : EvalState := (2, 5, 1)
private def secondStage0 : EvalState := (1, 4, 1)
private def secondStage1 : EvalState := (1, 5, 2)
private def secondStage2 : EvalState := (2, 5, 2)
private def secondStage3 : EvalState := (1, 5, 1)

/-- The complete backward-reachable set for the `xtyxy` certificate. -/
private def secondCanReach (state : EvalState) : Prop :=
  state ∈
    [(2, 5, 1), (1, 5, 1), (2, 5, 2), (4, 5, 2), (2, 5, 4),
     (4, 5, 4), (1, 5, 2), (1, 5, 4), (1, 3, 1), (1, 4, 1),
     (2, 3, 2), (4, 3, 2), (2, 3, 4), (4, 3, 4), (2, 4, 2),
     (4, 4, 2), (2, 4, 4), (4, 4, 4)]

set_option maxHeartbeats 2000000 in
private theorem second_predecessor_closed
    (state : EvalState) (letter : Nat)
    (letterXYZ : letter = 0 ∨ letter = 1 ∨ letter = 2)
    (reachable : secondCanReach (secondStep state letter)) :
    secondCanReach state := by
  rcases state with ⟨first, second, third⟩
  rcases letterXYZ with rfl | rfl | rfl <;>
    rcases fin6_cases first with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin6_cases second with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin6_cases third with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [secondCanReach, secondStep, secondValuation0, secondValuation1,
      secondValuation2, mul] at reachable ⊢

private theorem secondCanReach_of_run
    (state : EvalState) (letters : List Nat)
    (uses : UsesXYZ letters)
    (equality : secondRun state letters = secondTarget) :
    secondCanReach state := by
  induction letters generalizing state with
  | nil =>
      have stateEq : state = secondTarget := by
        simpa [secondRun] using equality
      subst state
      simp [secondCanReach, secondTarget]
  | cons letter letters ih =>
      have headXYZ := uses letter (List.Mem.head letters)
      have tailUses : UsesXYZ letters := by
        intro value member
        exact uses value (List.Mem.tail letter member)
      apply second_predecessor_closed state letter headXYZ
      apply ih (state := secondStep state letter) tailUses
      simpa [secondRun, secondStep] using equality

private theorem secondRun_target
    (letters : List Nat) (uses : UsesXYZ letters)
    (equality : secondRun secondTarget letters = secondTarget) :
    letters = [] := by
  cases letters with
  | nil => rfl
  | cons letter letters =>
      have headXYZ := uses letter (List.Mem.head letters)
      have tailUses : UsesXYZ letters := by
        intro value member
        exact uses value (List.Mem.tail letter member)
      have reachable :
          secondCanReach (secondStep secondTarget letter) := by
        apply secondCanReach_of_run
          (state := secondStep secondTarget letter) letters tailUses
        simpa [secondRun, secondStep] using equality
      rcases headXYZ with rfl | rfl | rfl <;>
        simp [secondCanReach, secondStep, secondTarget, secondValuation0,
          secondValuation1, secondValuation2, mul] at reachable

private theorem secondRun_stage3
    (letters : List Nat) (uses : UsesXYZ letters)
    (equality : secondRun secondStage3 letters = secondTarget) :
    letters = [1] := by
  cases letters with
  | nil => simp [secondRun, secondStage3, secondTarget] at equality
  | cons letter letters =>
      have headXYZ := uses letter (List.Mem.head letters)
      have tailUses : UsesXYZ letters := by
        intro value member
        exact uses value (List.Mem.tail letter member)
      have reachable :
          secondCanReach (secondStep secondStage3 letter) := by
        apply secondCanReach_of_run
          (state := secondStep secondStage3 letter) letters tailUses
        simpa [secondRun, secondStep] using equality
      rcases headXYZ with rfl | rfl | rfl
      · simp [secondCanReach, secondStep, secondStage3, secondValuation0,
          secondValuation1, secondValuation2, mul] at reachable
      · have tailEq : secondRun secondTarget letters = secondTarget := by
          simpa [secondRun, secondStep, secondStage3, secondTarget] using
            equality
        rw [secondRun_target letters tailUses tailEq]
      · simp [secondCanReach, secondStep, secondStage3, secondValuation0,
          secondValuation1, secondValuation2, mul] at reachable

private theorem secondRun_stage2
    (letters : List Nat) (uses : UsesXYZ letters)
    (equality : secondRun secondStage2 letters = secondTarget) :
    letters = [0, 1] := by
  cases letters with
  | nil => simp [secondRun, secondStage2, secondTarget] at equality
  | cons letter letters =>
      have headXYZ := uses letter (List.Mem.head letters)
      have tailUses : UsesXYZ letters := by
        intro value member
        exact uses value (List.Mem.tail letter member)
      have reachable :
          secondCanReach (secondStep secondStage2 letter) := by
        apply secondCanReach_of_run
          (state := secondStep secondStage2 letter) letters tailUses
        simpa [secondRun, secondStep] using equality
      rcases headXYZ with rfl | rfl | rfl
      · have tailEq : secondRun secondStage3 letters = secondTarget := by
          simpa [secondRun, secondStep, secondStage2, secondStage3] using
            equality
        rw [secondRun_stage3 letters tailUses tailEq]
      · simp [secondCanReach, secondStep, secondStage2, secondValuation0,
          secondValuation1, secondValuation2, mul] at reachable
      · simp [secondCanReach, secondStep, secondStage2, secondValuation0,
          secondValuation1, secondValuation2, mul] at reachable

private theorem secondRun_stage1
    (letters : List Nat) (uses : UsesXYZ letters)
    (equality : secondRun secondStage1 letters = secondTarget) :
    letters = [1, 0, 1] := by
  cases letters with
  | nil => simp [secondRun, secondStage1, secondTarget] at equality
  | cons letter letters =>
      have headXYZ := uses letter (List.Mem.head letters)
      have tailUses : UsesXYZ letters := by
        intro value member
        exact uses value (List.Mem.tail letter member)
      have reachable :
          secondCanReach (secondStep secondStage1 letter) := by
        apply secondCanReach_of_run
          (state := secondStep secondStage1 letter) letters tailUses
        simpa [secondRun, secondStep] using equality
      rcases headXYZ with rfl | rfl | rfl
      · simp [secondCanReach, secondStep, secondStage1, secondValuation0,
          secondValuation1, secondValuation2, mul] at reachable
      · have tailEq : secondRun secondStage2 letters = secondTarget := by
          simpa [secondRun, secondStep, secondStage1, secondStage2] using
            equality
        rw [secondRun_stage2 letters tailUses tailEq]
      · simp [secondCanReach, secondStep, secondStage1, secondValuation0,
          secondValuation1, secondValuation2, mul] at reachable

private theorem secondRun_stage0
    (letters : List Nat) (uses : UsesXYZ letters)
    (equality : secondRun secondStage0 letters = secondTarget) :
    letters = [2, 1, 0, 1] := by
  cases letters with
  | nil => simp [secondRun, secondStage0, secondTarget] at equality
  | cons letter letters =>
      have headXYZ := uses letter (List.Mem.head letters)
      have tailUses : UsesXYZ letters := by
        intro value member
        exact uses value (List.Mem.tail letter member)
      have reachable :
          secondCanReach (secondStep secondStage0 letter) := by
        apply secondCanReach_of_run
          (state := secondStep secondStage0 letter) letters tailUses
        simpa [secondRun, secondStep] using equality
      rcases headXYZ with rfl | rfl | rfl
      · simp [secondCanReach, secondStep, secondStage0, secondValuation0,
          secondValuation1, secondValuation2, mul] at reachable
      · simp [secondCanReach, secondStep, secondStage0, secondValuation0,
          secondValuation1, secondValuation2, mul] at reachable
      · have tailEq : secondRun secondStage1 letters = secondTarget := by
          simpa [secondRun, secondStep, secondStage0, secondStage1] using
            equality
        rw [secondRun_stage1 letters tailUses tailEq]

private theorem xtyxy_unique_of_certificate
    (word : Word Nat) (uses : UsesXYZ word.toList)
    (stateEq : secondEvalState word = secondTarget) :
    word = SemigroupBasis.Nonfinite.B2One.xtyxy := by
  cases word with
  | mk head tail =>
      have headXYZ : head = 0 ∨ head = 1 ∨ head = 2 := by
        exact uses head (by simp [Word.toList])
      have tailUses : UsesXYZ tail := by
        intro letter member
        exact uses letter (by simp [Word.toList, member])
      change secondRun (secondInitial head) tail = secondTarget at stateEq
      have reachable : secondCanReach (secondInitial head) := by
        apply secondCanReach_of_run
          (state := secondInitial head) tail tailUses stateEq
      rcases headXYZ with rfl | rfl | rfl
      · have tailEq : secondRun secondStage0 tail = secondTarget := by
          simpa [secondInitial, secondStage0] using stateEq
        have shape := secondRun_stage0 tail tailUses tailEq
        subst tail
        rfl
      · simp [secondCanReach, secondInitial, secondValuation0,
          secondValuation1, secondValuation2] at reachable
      · simp [secondCanReach, secondInitial, secondValuation0,
          secondValuation1, secondValuation2] at reachable

private theorem second_target_eval :
    secondEvalState SemigroupBasis.Nonfinite.B2One.xtyxy = secondTarget := by
  decide

theorem xtyxy_isoterm :
    SemigroupBasis.Nonfinite.B2One.Isoterm table.semigroup
      SemigroupBasis.Nonfinite.B2One.xtyxy := by
  intro other valid
  apply xtyxy_unique_of_certificate other (xtyxy_valid_rhs_usesXYZ valid)
  rw [← second_target_eval]
  apply Prod.ext
  · exact (valid secondValuation0).symm
  · apply Prod.ext
    · exact (valid secondValuation1).symm
    · exact (valid secondValuation2).symm

private def fourLetterCountervaluation (letter : Nat) : Fin 6 :=
  if letter = 0 then a
  else if letter = 1 then b
  else one

theorem xyxy_not_satisfied :
    ¬(Identity.mk SemigroupBasis.Nonfinite.B2One.xyxy
        SemigroupBasis.Nonfinite.B2One.xyyx).SatisfiedBy table.semigroup := by
  intro valid
  have equality := valid fourLetterCountervaluation
  simp [SemigroupBasis.Nonfinite.B2One.xyxy,
    SemigroupBasis.Nonfinite.B2One.xyyx, Semigroup.eval,
    fourLetterCountervaluation, table, a, b, one] at equality
  change mul (mul (mul a b) a) b = mul (mul (mul a b) b) a at equality
  exact (by decide : ¬
    mul (mul (mul a b) a) b = mul (mul (mul a b) b) a) equality

private def xyyxYxxyFin : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 0]⟩, ⟨1, [0, 0, 1]⟩⟩

private theorem xyyxYxxyFin_checked :
    table.checkIdentity xyyxYxxyFin = true := by
  decide

/-- The four-letter identity used in Sapir's reconstruction of Perkins's
argument. -/
theorem xyyx_yxxy_valid :
    (Identity.mk SemigroupBasis.Nonfinite.B2One.xyyx
      SemigroupBasis.Nonfinite.B2One.yxxy).SatisfiedBy table.semigroup := by
  have checked :=
    table.checkIdentityNat_sound xyyxYxxyFin xyyxYxxyFin_checked
  simpa [xyyxYxxyFin, Identity.map, Word.map,
    SemigroupBasis.Nonfinite.B2One.xyyx,
    SemigroupBasis.Nonfinite.B2One.yxxy] using checked

/-- Therefore the second alternating four-letter possibility is excluded as
well. -/
theorem xyxy_yxxy_not_satisfied :
    ¬(Identity.mk SemigroupBasis.Nonfinite.B2One.xyxy
      SemigroupBasis.Nonfinite.B2One.yxxy).SatisfiedBy table.semigroup := by
  intro alternating
  apply xyxy_not_satisfied
  intro valuation
  exact
    (alternating valuation).trans
      (xyyx_yxxy_valid valuation).symm

theorem perkins_hypotheses :
    SemigroupBasis.Nonfinite.B2One.PerkinsHypotheses table.semigroup where
  hasIdentity := ⟨one, one_mul, mul_one⟩
  identityFamily := fun extra _ => perkins_identity_valid extra
  separatesFourLetterWords := xyxy_not_satisfied
  xytyxIsoterm := xytyx_isoterm
  xtyxyIsoterm := xtyxy_isoterm

/-- The exact bounded derivational nonredundancy needed by Perkins's
criterion. -/
def PerkinsInfiniteWordLemma : Prop :=
  SemigroupBasis.Nonfinite.B2One.BoundedPerkinsUnderivability
    table.semigroup

/-- Sapir's exact Condition (III), specialized to the printed Brandt table.

Besides the stable occurrence order, the current contextual word must satisfy
an identity with the original Perkins obstruction left side.  The compiled
counterexample in `BoundaryCounterexample.lean` shows that omitting this
semantic-class hypothesis makes the statement false.
-/
def PerkinsSemanticOccurrenceLemma : Prop :=
  SemigroupBasis.Nonfinite.B2One.BoundedPerkinsOccurrenceOrderPreservation
    table.semigroup

/-- The remaining local content of Sapir's Condition (III).

For each distinguished middle letter `z`, the semantic identity-class
hypothesis and one bounded contextual rewrite preserve the ordered projection
`x₁ y₁ z₁ x₂ z₂ y₁`.
-/
def PerkinsSemanticProjectionLemma : Prop :=
  ∀ bound (identity : Identity Nat),
    identity.SatisfiedBy table.semigroup →
    identity.UsesAtMost bound →
    ∀ pre post substitution,
      (Identity.mk
        (SemigroupBasis.Nonfinite.B2One.obstruction bound).lhs
        (SemigroupBasis.Nonfinite.B2One.contextWord pre
          (identity.lhs.bind substitution) post)).SatisfiedBy
            table.semigroup →
      SemigroupBasis.Nonfinite.B2One.OccurrencePattern
          (4 * bound + 7)
          (SemigroupBasis.Nonfinite.B2One.contextWord pre
            (identity.lhs.bind substitution) post).toList →
      ∀ z,
        z ∈ SemigroupBasis.Nonfinite.B2One.middleVariables
            (4 * bound + 7) →
          SemigroupBasis.Nonfinite.B2One.occurrenceProjection z
              (SemigroupBasis.Nonfinite.B2One.contextWord pre
                (identity.rhs.bind substitution) post).toList =
            [0, 1, z, 0, z, 1]

theorem perkinsSemanticOccurrence_of_projection
    (localOrder : PerkinsSemanticProjectionLemma) :
    PerkinsSemanticOccurrenceLemma := by
  intro bound identity valid uses pre post substitution
  dsimp only
  intro anchor pattern
  apply
    SemigroupBasis.Nonfinite.B2One.occurrencePattern_of_domain_and_projections
      (4 * bound + 7)
      (SemigroupBasis.Nonfinite.B2One.contextWord pre
        (identity.rhs.bind substitution) post).toList
      (by omega)
  · intro letter member
    apply pattern.mem
    rw [SemigroupBasis.Nonfinite.B2One.contextWord_toList] at member ⊢
    rcases List.mem_append.mp member with inPrefix | inPost
    · rcases List.mem_append.mp inPrefix with inPre | inRight
      · exact List.mem_append.mpr
          (Or.inl (List.mem_append.mpr (Or.inl inPre)))
      · rw [Word.toList_bind] at inRight
        rcases List.mem_flatMap.mp inRight with
          ⟨source, sourceRight, letterInSubstitution⟩
        have sourceLeft :=
          valid_identity_support_subset valid source sourceRight
        have inLeft :
            letter ∈ (identity.lhs.bind substitution).toList := by
          rw [Word.toList_bind]
          exact List.mem_flatMap.mpr
            ⟨source, sourceLeft, letterInSubstitution⟩
        exact List.mem_append.mpr
          (Or.inl (List.mem_append.mpr (Or.inr inLeft)))
    · exact List.mem_append.mpr (Or.inr inPost)
  · intro z zMiddle
    exact localOrder bound identity valid uses pre post substitution
      anchor pattern z zMiddle

theorem perkinsInfiniteWordLemma_of_semanticOccurrence
    (occurrenceOrder : PerkinsSemanticOccurrenceLemma) :
    PerkinsInfiniteWordLemma :=
  SemigroupBasis.Nonfinite.B2One.boundedPerkinsUnderivability_of_occurrenceOrderPreservation
    occurrenceOrder

/-- Perkins's checked hypotheses and bounded infinite-word lemma imply the
nonfinite-basis theorem for the printed `B₂¹` table. -/
theorem table_nonfinitelyBased_of_perkins
    (infiniteWord : PerkinsInfiniteWordLemma) :
    NonfinitelyBased table.semigroup :=
  SemigroupBasis.Nonfinite.B2One.nonfinitelyBased_of_perkins
    perkins_hypotheses infiniteWord

theorem table_nonfinitelyBased_of_semanticOccurrence
    (localOrder : PerkinsSemanticOccurrenceLemma) :
    NonfinitelyBased table.semigroup :=
  table_nonfinitelyBased_of_perkins
    (perkinsInfiniteWordLemma_of_semanticOccurrence localOrder)

theorem table_nonfinitelyBased_of_semanticProjection
    (localOrder : PerkinsSemanticProjectionLemma) :
    NonfinitelyBased table.semigroup :=
  table_nonfinitelyBased_of_semanticOccurrence
    (perkinsSemanticOccurrence_of_projection localOrder)

/-- Perkins's nonfinite-basis result transported through the checked
relabeling to the exact local catalogue representative `S6_8564`. -/
theorem s6_8564_nonfinitelyBased_of_perkins
    (infiniteWord : PerkinsInfiniteWordLemma) :
    NonfinitelyBased catalogueTable.semigroup :=
  (nonfinitelyBased_iff_of_sameIdentityTheory
    sameIdentityTheory_catalogue).mp
      (table_nonfinitelyBased_of_perkins infiniteWord)

theorem s6_8564_nonfinitelyBased_of_semanticOccurrence
    (localOrder : PerkinsSemanticOccurrenceLemma) :
    NonfinitelyBased catalogueTable.semigroup :=
  s6_8564_nonfinitelyBased_of_perkins
    (perkinsInfiniteWordLemma_of_semanticOccurrence localOrder)

theorem s6_8564_nonfinitelyBased_of_semanticProjection
    (localOrder : PerkinsSemanticProjectionLemma) :
    NonfinitelyBased catalogueTable.semigroup :=
  s6_8564_nonfinitelyBased_of_semanticOccurrence
    (perkinsSemanticOccurrence_of_projection localOrder)

end SemigroupBasis.Examples.B2One
