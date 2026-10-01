import SemigroupBasis.FiniteReflection
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples.LeeL

open SemigroupBasis

/-- Lee's six-element semigroup in the source order `0, a, b, c, d, e`.

This is also the zero-based Smallsemi catalogue table `S6_3843`.
-/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then 0
  else if left = 1 then
    if right = 5 then 1 else 0
  else if left = 2 then
    if right = 5 then 2 else 0
  else if left = 3 then
    if right = 2 then 1
    else if right = 4 then 3
    else if right = 5 then 1
    else 0
  else if left = 4 then
    if right = 2 then 2
    else if right = 4 then 4
    else if right = 5 then 2
    else 0
  else
    if right = 1 then 1
    else if right = 2 then 1
    else if right = 3 then 3
    else if right = 4 then 3
    else if right = 5 then 5
    else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem table_rows :
    List.ofFn (fun left : Fin 6 =>
      List.ofFn (fun right : Fin 6 => (table.mul left right).val)) =
      [[0, 0, 0, 0, 0, 0],
       [0, 0, 0, 0, 0, 1],
       [0, 0, 0, 0, 0, 2],
       [0, 0, 1, 0, 3, 1],
       [0, 0, 2, 0, 4, 2],
       [0, 1, 1, 3, 3, 5]] := by
  decide

/-- The involution witnessing the self-duality of `L`; it swaps `b` and `c`. -/
def dual (value : Fin 6) : Fin 6 :=
  if value = 2 then 3 else if value = 3 then 2 else value

@[simp]
theorem dual_dual (value : Fin 6) : dual (dual value) = value := by
  revert value
  decide

theorem dual_mul (left right : Fin 6) :
    dual (mul left right) = mul (dual right) (dual left) := by
  revert left right
  decide

theorem dual_square (value : Fin 6) :
    dual (mul value value) = mul value value := by
  revert value
  decide

theorem sandwich_dual (outside middle : Fin 6) :
    mul (mul outside (dual middle)) outside =
      mul (mul outside middle) outside := by
  revert outside middle
  decide

def x : Word Nat := Word.singleton 0

/-- The square block for `y_i`, with the paper's `y_1` represented by `i = 0`. -/
def ySquare (i : Nat) : Word Nat :=
  ⟨i + 1, [i + 1]⟩

/-- The nonempty middle word `y_1^2 ... y_n^2`, with `n = extra + 1`. -/
def forwardMiddle (extra : Nat) : Word Nat :=
  (List.range extra).foldl
    (fun current i => current ++ ySquare (i + 1))
    (ySquare 0)

def p (n : Nat) : Word Nat :=
  match n with
  | 0 => x ++ x
  | extra + 1 => x ++ forwardMiddle extra ++ x

def q (n : Nat) : Word Nat :=
  match n with
  | 0 => x ++ x
  | extra + 1 => x ++ (forwardMiddle extra).reverse ++ x

def obstruction (bound : Nat) : Identity Nat :=
  let n := max 2 bound
  ⟨p n, q n⟩

private def forwardValue (valuation : Nat → Fin 6) : Nat → Fin 6
  | 0 => mul (valuation 1) (valuation 1)
  | extra + 1 =>
      mul (forwardValue valuation extra)
        (mul (valuation (extra + 2)) (valuation (extra + 2)))

private def reverseValue (valuation : Nat → Fin 6) : Nat → Fin 6
  | 0 => mul (valuation 1) (valuation 1)
  | extra + 1 =>
      mul (mul (valuation (extra + 2)) (valuation (extra + 2)))
        (reverseValue valuation extra)

private theorem eval_forwardMiddle (valuation : Nat → Fin 6) (extra : Nat) :
    table.semigroup.eval valuation (forwardMiddle extra) =
      forwardValue valuation extra := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      simp only [forwardMiddle, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [Semigroup.eval_append]
      have ih' :
          table.semigroup.eval valuation
              (List.foldl (fun current i => current ++ ySquare (i + 1))
                (ySquare 0) (List.range extra)) =
            forwardValue valuation extra := by
        simpa only [forwardMiddle] using ih
      rw [ih']
      rfl

private theorem eval_reverseMiddle (valuation : Nat → Fin 6) (extra : Nat) :
    table.semigroup.eval valuation (forwardMiddle extra).reverse =
      reverseValue valuation extra := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      simp only [forwardMiddle, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil, Word.reverse_append]
      rw [Semigroup.eval_append]
      have ih' :
          table.semigroup.eval valuation
              (List.foldl (fun current i => current ++ ySquare (i + 1))
                (ySquare 0) (List.range extra)).reverse =
            reverseValue valuation extra := by
        simpa only [forwardMiddle] using ih
      rw [ih']
      rfl

private theorem dual_forwardValue (valuation : Nat → Fin 6) (extra : Nat) :
    dual (forwardValue valuation extra) = reverseValue valuation extra := by
  induction extra with
  | zero => exact dual_square (valuation 1)
  | succ extra ih =>
      rw [forwardValue, reverseValue, dual_mul, dual_square, ih]

theorem p_q_valid (n : Nat) :
    (Identity.mk (p n) (q n)).SatisfiedBy table.semigroup := by
  intro valuation
  cases n with
  | zero => rfl
  | succ extra =>
      simp only [p, q, Semigroup.eval_append]
      rw [eval_forwardMiddle, eval_reverseMiddle]
      rw [← dual_forwardValue valuation extra]
      simpa [x, table] using
        (sandwich_dual (valuation 0) (forwardValue valuation extra)).symm

theorem obstruction_valid (bound : Nat) :
    (obstruction bound).SatisfiedBy table.semigroup :=
  p_q_valid (max 2 bound)

/-- A power block in the fixed alphabet `x = 0`, `y_i = i + 1`. -/
def powerBlock (i exponent : Nat) : List Nat :=
  List.replicate exponent (i + 1)

def orderedBlocks (indices : List Nat) (exponents : Nat → Nat) : List Nat :=
  indices.flatMap fun i => powerBlock i (exponents i)

/-- The source set `P_n`, specialized to the fixed obstruction alphabet. -/
def ListInP (n : Nat) (letters : List Nat) : Prop :=
  ∃ leftExponent rightExponent exponents,
    1 ≤ leftExponent ∧
    1 ≤ rightExponent ∧
    (∀ i, i < n → 2 ≤ exponents i) ∧
    letters =
      List.replicate leftExponent 0 ++
        orderedBlocks (List.range n) exponents ++
        List.replicate rightExponent 0

def InP (n : Nat) (word : Word Nat) : Prop :=
  ListInP n word.toList

/-- The source set `Q_n`; reversing a `Q_n` word gives a `P_n` word. -/
def InQ (n : Nat) (word : Word Nat) : Prop :=
  InP n word.reverse

private theorem toList_forwardMiddle (extra : Nat) :
    (forwardMiddle extra).toList =
      orderedBlocks (List.range (extra + 1)) (fun _ => 2) := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      simp only [forwardMiddle, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil, Word.toList_append]
      have ih' :
          (List.foldl (fun current i => current ++ ySquare (i + 1))
            (ySquare 0) (List.range extra)).toList =
            orderedBlocks (List.range (extra + 1)) (fun _ => 2) := by
        simpa only [forwardMiddle] using ih
      rw [ih']
      simp [orderedBlocks, powerBlock, ySquare, Word.toList,
        List.range_succ]

theorem p_inP {n : Nat} (positive : 1 ≤ n) : InP n (p n) := by
  cases n with
  | zero => omega
  | succ extra =>
      refine ⟨1, 1, fun _ => 2, by decide, by decide, ?_, ?_⟩
      · intro i hi
        exact Nat.le_refl 2
      · simp only [p, Word.toList_append, List.replicate_one]
        rw [toList_forwardMiddle]
        rfl

theorem q_inQ {n : Nat} (positive : 1 ≤ n) : InQ n (q n) := by
  cases n with
  | zero => omega
  | succ extra =>
      simpa [InQ, p, q, Word.reverse_append] using
        (p_inP (n := extra + 1) (by omega))

private def firstNonzero : List Nat → Option Nat
  | [] => none
  | 0 :: rest => firstNonzero rest
  | (value + 1) :: _ => some (value + 1)

private theorem firstNonzero_zero_replicate (count : Nat) (rest : List Nat) :
    firstNonzero (List.replicate count 0 ++ rest) = firstNonzero rest := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change firstNonzero (0 :: (List.replicate count 0 ++ rest)) =
        firstNonzero rest
      simp only [firstNonzero]
      exact ih

private theorem firstNonzero_positive_replicate
    (value count : Nat) (positive : 1 ≤ count) (rest : List Nat) :
    firstNonzero (List.replicate count (value + 1) ++ rest) =
      some (value + 1) := by
  cases count with
  | zero => omega
  | succ count =>
      change firstNonzero
          ((value + 1) :: (List.replicate count (value + 1) ++ rest)) =
        some (value + 1)
      rfl

private theorem firstNonzero_orderedBlocks
    {n : Nat} (positive : 1 ≤ n) (exponents : Nat → Nat)
    (large : ∀ i, i < n → 2 ≤ exponents i) (rest : List Nat) :
    firstNonzero (orderedBlocks (List.range n) exponents ++ rest) = some 1 := by
  cases n with
  | zero => omega
  | succ n =>
      unfold orderedBlocks
      rw [List.range_succ_eq_map]
      simp only [List.flatMap_cons, List.flatMap_map]
      rw [List.append_assoc]
      unfold powerBlock
      change firstNonzero
          (List.replicate (exponents 0) 1 ++
            (List.flatMap
                (fun a => List.replicate (exponents a.succ) (a.succ + 1))
                (List.range n) ++
              rest)) =
        some 1
      exact firstNonzero_positive_replicate 0 (exponents 0)
        (by have := large 0 (by omega); omega)
        (List.flatMap
            (fun a => List.replicate (exponents a.succ) (a.succ + 1))
            (List.range n) ++
          rest)

theorem InP.firstNonzero {n : Nat} {word : Word Nat}
    (positive : 1 ≤ n) (membership : InP n word) :
    firstNonzero word.toList = some 1 := by
  rcases membership with
    ⟨leftExponent, rightExponent, exponents, leftPositive, _,
      large, wordShape⟩
  rw [wordShape, List.append_assoc, firstNonzero_zero_replicate,
    firstNonzero_orderedBlocks positive exponents large]

private theorem firstNonzero_reverse_forwardMiddle
    (extra : Nat) (rest : List Nat) :
    firstNonzero ((forwardMiddle extra).reverse.toList ++ rest) =
      some (extra + 1) := by
  cases extra with
  | zero =>
      change firstNonzero (1 :: 1 :: rest) = some 1
      rfl
  | succ extra =>
      simp only [forwardMiddle, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil, Word.reverse_append,
        Word.toList_append]
      rw [List.append_assoc]
      change firstNonzero
          ((extra + 2) :: (extra + 2) ::
            ((List.foldl (fun current i => current ++ ySquare (i + 1))
              (ySquare 0) (List.range extra)).reverse.toList ++ rest)) =
        some (extra + 2)
      rfl

theorem q_not_inP {n : Nat} (atLeastTwo : 2 ≤ n) : ¬InP n (q n) := by
  intro membership
  have fromP := membership.firstNonzero (by omega)
  cases n with
  | zero => omega
  | succ extra =>
      have fromQ : firstNonzero (q (extra + 1)).toList = some (extra + 1) := by
        simp only [q, x, Word.toList_append, Word.toList_singleton]
        change firstNonzero
            (0 :: ((forwardMiddle extra).reverse.toList ++ [0])) =
          some (extra + 1)
        simp only [firstNonzero]
        exact firstNonzero_reverse_forwardMiddle extra [0]
      rw [fromQ] at fromP
      have equality : extra + 1 = 1 := Option.some.inj fromP
      omega

/-- A rewrite preserves `P_n` in every semigroup context and after every
nonempty-word substitution. This is the closure property used in the paper's
deduction-sequence argument. -/
def ContextuallyEquivalentInP (n : Nat) (left right : Word Nat) : Prop :=
  ∀ pre post substitution,
    ListInP n
        (pre ++ (left.bind substitution).toList ++ post) ↔
      ListInP n
        (pre ++ (right.bind substitution).toList ++ post)

private theorem bind_append (left right : Word Nat)
    (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp only [Word.toList_bind, Word.toList_append, List.flatMap_append]

private theorem bind_bind (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun v => (first v).bind second) := by
  apply Word.toList_injective
  simp only [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  rw [Word.toList_bind]
  induction word.toList with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.flatMap_cons, Word.toList_singleton,
        List.singleton_append]
      have ih' : List.flatMap (fun x => [x]) tail = tail := by
        simpa only [Word.toList_singleton] using ih
      rw [ih']

theorem Derives.contextuallyEquivalentInP
    {basis : List (Identity Nat)} {left right : Word Nat}
    (axiomPreserves :
      ∀ identity, identity ∈ basis →
        ContextuallyEquivalentInP n identity.lhs identity.rhs)
    (derivation : Derives basis left right) :
    ContextuallyEquivalentInP n left right := by
  induction derivation with
  | fromBasis member =>
      exact axiomPreserves _ member
  | refl =>
      intro pre post substitution
      exact Iff.rfl
  | symm _ ih =>
      intro pre post substitution
      exact (ih pre post substitution).symm
  | trans _ _ ihLeft ihRight =>
      intro pre post substitution
      exact (ihLeft pre post substitution).trans
        (ihRight pre post substitution)
  | prepend preWord _ ih =>
      intro pre post substitution
      rw [bind_append, bind_append, Word.toList_append,
        Word.toList_append, ← List.append_assoc, ← List.append_assoc]
      exact ih
        (pre ++ (preWord.bind substitution).toList)
        post substitution
  | appendRight _ postWord ih =>
      intro pre post substitution
      rw [bind_append, bind_append, Word.toList_append,
        Word.toList_append]
      simpa only [List.append_assoc] using
        ih pre ((postWord.bind substitution).toList ++ post)
          substitution
  | subst _ first ih =>
      intro pre post second
      rw [bind_bind, bind_bind]
      exact ih pre post
        (fun v => (first v).bind second)

theorem Identity.UsesAtMost.mono {identity : Identity Nat}
    {small large : Nat} (uses : identity.UsesAtMost small)
    (bound : small ≤ large) :
    identity.UsesAtMost large := by
  rcases uses with ⟨variables, lengthBound, only⟩
  exact ⟨variables, Nat.le_trans lengthBound bound, only⟩

/-- A convenient sufficient preservation statement for closing the generic
obstruction argument.

This is deliberately stronger than Zhang--Luo Lemma 6, which applies only to
connected identities. The paper instead first replaces a hypothetical finite
basis by a connected basis using Lemmas 2--3, then applies Lemma 6 to each
rewrite. No instance of this stronger proposition is assumed below.
-/
def BoundedValidIdentitiesPreserveP : Prop :=
  ∀ n (identity : Identity Nat),
    2 ≤ n →
    identity.SatisfiedBy table.semigroup →
    identity.UsesAtMost n →
    ContextuallyEquivalentInP n identity.lhs identity.rhs

theorem obstruction_underivable_of_preservation
    (preservation : BoundedValidIdentitiesPreserveP)
    (bound : Nat) (basis : List (Identity Nat))
    (models : Models table.semigroup basis)
    (bounded : BasisUsesAtMost basis bound) :
    ¬Derives basis (obstruction bound).lhs (obstruction bound).rhs := by
  let n := max 2 bound
  have nAtLeastTwo : 2 ≤ n := Nat.le_max_left 2 bound
  have boundLeN : bound ≤ n := Nat.le_max_right 2 bound
  intro derivation
  have axiomPreserves :
      ∀ identity, identity ∈ basis →
        ContextuallyEquivalentInP n identity.lhs identity.rhs := by
    intro identity member
    exact preservation n identity nAtLeastTwo
      (models identity member)
      (Identity.UsesAtMost.mono (bounded identity member) boundLeN)
  have invariant :=
    SemigroupBasis.Examples.LeeL.Derives.contextuallyEquivalentInP
      axiomPreserves derivation
      ([] : List Nat) ([] : List Nat) Word.singleton
  have invariant' : InP n (p n) ↔ InP n (q n) := by
    simpa [obstruction, n, InP, bind_singleton] using invariant
  exact q_not_inP nAtLeastTwo (invariant'.mp (p_inP (by omega)))

theorem nonfinitelyBased_of_preservation
    (preservation : BoundedValidIdentitiesPreserveP) :
    NonfinitelyBased table.semigroup :=
  nonfinitelyBased_of_variable_bound_obstructions
    obstruction obstruction_valid
    (obstruction_underivable_of_preservation preservation)

/-- The three values used in Zhang--Luo Lemma 1: no occurrence gives `e`,
one occurrence gives `a`, and two or more occurrences give `0`. -/
private def multiplicityValue : Nat → Fin 6
  | 0 => 5
  | 1 => 1
  | _ + 2 => 0

private theorem multiplicityValue_mul_hit (count : Nat) :
    mul (multiplicityValue count) 1 = multiplicityValue (count + 1) := by
  cases count with
  | zero => rfl
  | succ count =>
      cases count <;> rfl

private theorem multiplicityValue_mul_miss (count : Nat) :
    mul (multiplicityValue count) 5 = multiplicityValue count := by
  cases count with
  | zero => rfl
  | succ count =>
      cases count <;> rfl

private theorem fold_multiplicityValue (tested : Nat)
    (letters : List Nat) (initial : Nat) :
    letters.foldl
        (fun current v =>
          mul current (if v = tested then 1 else 5))
        (multiplicityValue initial) =
      multiplicityValue (initial + letters.count tested) := by
  induction letters generalizing initial with
  | nil =>
      simp
  | cons v rest ih =>
      simp only [List.foldl_cons]
      by_cases hit : v = tested
      · subst v
        rw [if_pos rfl, multiplicityValue_mul_hit, ih,
          List.count_cons_self]
        congr 1
        omega
      · rw [if_neg hit, multiplicityValue_mul_miss, ih,
          List.count_cons_of_ne hit]

private theorem eval_multiplicityValue (tested : Nat) (word : Word Nat) :
    table.semigroup.eval
        (fun v => if v = tested then (1 : Fin 6) else (5 : Fin 6)) word =
      multiplicityValue (word.toList.count tested) := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, Word.toList]
      by_cases hit : head = tested
      · subst head
        rw [if_pos rfl]
        change tail.foldl
            (fun current v => mul current (if v = tested then 1 else 5))
            (multiplicityValue 1) =
          multiplicityValue ((tested :: tail).count tested)
        rw [fold_multiplicityValue]
        simp only [List.count_cons_self]
        congr 1
        omega
      · rw [if_neg hit]
        change tail.foldl
            (fun current v => mul current (if v = tested then 1 else 5))
            (multiplicityValue 0) =
          multiplicityValue ((head :: tail).count tested)
        rw [fold_multiplicityValue]
        simp only [List.count_cons_of_ne hit, Nat.zero_add]

private theorem multiplicityValue_eq_five_iff (count : Nat) :
    multiplicityValue count = 5 ↔ count = 0 := by
  cases count with
  | zero => simp [multiplicityValue]
  | succ count =>
      cases count <;> simp [multiplicityValue]

private theorem multiplicityValue_eq_one_iff (count : Nat) :
    multiplicityValue count = 1 ↔ count = 1 := by
  cases count with
  | zero => simp [multiplicityValue]
  | succ count =>
      cases count <;> simp [multiplicityValue]

/-- Zhang--Luo Lemma 1, support part. -/
theorem valid_identity_preserves_absence
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) (tested : Nat) :
    identity.lhs.toList.count tested = 0 ↔
      identity.rhs.toList.count tested = 0 := by
  have evaluated := valid
    (fun v => if v = tested then (1 : Fin 6) else (5 : Fin 6))
  rw [eval_multiplicityValue, eval_multiplicityValue] at evaluated
  constructor
  · intro leftZero
    have rightValue : multiplicityValue
        (identity.rhs.toList.count tested) = 5 := by
      rw [← evaluated, leftZero]
      rfl
    exact (multiplicityValue_eq_five_iff _).mp rightValue
  · intro rightZero
    have leftValue : multiplicityValue
        (identity.lhs.toList.count tested) = 5 := by
      rw [evaluated, rightZero]
      rfl
    exact (multiplicityValue_eq_five_iff _).mp leftValue

/-- Zhang--Luo Lemma 1, simple-letter part. -/
theorem valid_identity_preserves_simplicity
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy table.semigroup) (tested : Nat) :
    identity.lhs.toList.count tested = 1 ↔
      identity.rhs.toList.count tested = 1 := by
  have evaluated := valid
    (fun v => if v = tested then (1 : Fin 6) else (5 : Fin 6))
  rw [eval_multiplicityValue, eval_multiplicityValue] at evaluated
  constructor
  · intro leftOne
    have rightValue : multiplicityValue
        (identity.rhs.toList.count tested) = 1 := by
      rw [← evaluated, leftOne]
      rfl
    exact (multiplicityValue_eq_one_iff _).mp rightValue
  · intro rightOne
    have leftValue : multiplicityValue
        (identity.lhs.toList.count tested) = 1 := by
      rw [evaluated, rightOne]
      rfl
    exact (multiplicityValue_eq_one_iff _).mp leftValue

end SemigroupBasis.Examples.LeeL
