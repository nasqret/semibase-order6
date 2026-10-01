import SemigroupBasis.Nonfinite.B2One.OccurrenceOrder

namespace SemigroupBasis.Nonfinite.B2One

open SemigroupBasis

/-!
The explicit sufficient condition used by Perkins for the six-element
Brandt monoid.

The source deduction chooses the identity with `n = 4 * bound + 8` against
identities using at most `bound` variables. Since `extra + 1 = n` below, the
corresponding Lean obstruction is `perkinsIdentity (4 * bound + 7)`.

All finite-basis and derivation bookkeeping is proved in this module. The
remaining mathematical boundary is Sapir's semantic Condition (III): one
contextual bounded-variable rewrite preserves Perkins's occurrence order
while the current word remains in the identity class of the obstruction.
-/

def HasIdentity (G : Semigroup S) : Prop :=
  ∃ one : S, (∀ value, G.mul one value = value) ∧
    (∀ value, G.mul value one = value)

/-- A word is an isoterm when it cannot be one side of a nontrivial identity. -/
def Isoterm (G : Semigroup S) (word : Word Nat) : Prop :=
  ∀ other : Word Nat,
    (Identity.mk word other).SatisfiedBy G → other = word

def x : Word Nat := Word.singleton 0
def y : Word Nat := Word.singleton 1
def t : Word Nat := Word.singleton 2

def xyxy : Word Nat := ⟨0, [1, 0, 1]⟩
def xyyx : Word Nat := ⟨0, [1, 1, 0]⟩
def yxxy : Word Nat := ⟨1, [0, 0, 1]⟩
def xytyx : Word Nat := ⟨0, [1, 2, 1, 0]⟩
def xtyxy : Word Nat := ⟨0, [2, 1, 0, 1]⟩

/-- The nonempty block `y₁ ... yₙ`, with `n = extra + 1`. -/
def forwardY (extra : Nat) : Word Nat :=
  (List.range extra).foldl
    (fun current index => current ++ Word.singleton (index + 2))
    (Word.singleton 1)

/-- Perkins's left side
`x y₁ ... yₙ x yₙ ... y₁`, with `n = extra + 1`. -/
def perkinsLeft (extra : Nat) : Word Nat :=
  x ++ forwardY extra ++ x ++ (forwardY extra).reverse

/-- Perkins's right side
`x yₙ ... y₁ x y₁ ... yₙ`, with `n = extra + 1`. -/
def perkinsRight (extra : Nat) : Word Nat :=
  x ++ (forwardY extra).reverse ++ x ++ forwardY extra

def perkinsIdentity (extra : Nat) : Identity Nat :=
  ⟨perkinsLeft extra, perkinsRight extra⟩

theorem forwardY_toList (extra : Nat) :
    (forwardY extra).toList = 1 :: middleVariables extra := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      simp only [forwardY, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      rw [Word.toList_append]
      have ih' :
          (List.foldl
            (fun current index =>
              current ++ Word.singleton (index + 2))
            (Word.singleton 1) (List.range extra)).toList =
            1 :: middleVariables extra := by
        simpa only [forwardY] using ih
      rw [ih']
      simp [middleVariables, List.range_succ]

theorem perkinsLeft_toList (extra : Nat) :
    (perkinsLeft extra).toList =
      [0, 1] ++ middleVariables extra ++ [0] ++
        (middleVariables extra).reverse ++ [1] := by
  simp only [perkinsLeft, Word.toList_append, x, Word.toList_singleton,
    forwardY_toList, Word.toList_reverse]
  simp [List.reverse_cons, List.append_assoc]

theorem perkinsRight_toList (extra : Nat) :
    (perkinsRight extra).toList =
      [0] ++ (middleVariables extra).reverse ++ [1, 0, 1] ++
        middleVariables extra := by
  simp only [perkinsRight, Word.toList_append, x, Word.toList_singleton,
    forwardY_toList, Word.toList_reverse]
  simp [List.reverse_cons, List.append_assoc]

theorem perkinsLeft_has_occurrencePattern (extra : Nat) :
    OccurrencePattern extra (perkinsLeft extra).toList := by
  refine ⟨middleVariables extra, (middleVariables extra).reverse,
    List.Perm.refl _, List.reverse_perm _, ?_⟩
  exact perkinsLeft_toList extra

theorem perkinsRight_not_occurrencePattern
    (extra : Nat) (positive : 1 ≤ extra) :
    ¬OccurrencePattern extra (perkinsRight extra).toList := by
  intro pattern
  rcases pattern with
    ⟨firstMiddle, secondMiddle, firstPerm, _, shape⟩
  cases extra with
  | zero => omega
  | succ extra =>
      have firstNonempty : firstMiddle ≠ [] := by
        intro empty
        subst firstMiddle
        have targetNonempty :
            middleVariables (Nat.succ extra) ≠ [] := by
          simp [middleVariables, List.range_succ]
        exact targetNonempty firstPerm.symm.eq_nil
      rcases firstMiddle with _ | ⟨first, rest⟩
      · exact firstNonempty rfl
      · have secondLetter :
          extra + 2 = 1 := by
          have atIndex :=
            congrArg (fun letters => letters[1]?) shape
          rw [perkinsRight_toList] at atIndex
          simpa [middleVariables, List.range_succ,
            List.reverse_append, List.append_assoc] using atIndex
        omega

/-- The exact hypotheses of the simplified Perkins criterion.

The source states the identity family for `n > 1`; since `extra + 1 = n`,
the Lean bound is `1 ≤ extra`.
-/
structure PerkinsHypotheses (G : Semigroup S) : Prop where
  hasIdentity : HasIdentity G
  identityFamily :
    ∀ extra, 1 ≤ extra → (perkinsIdentity extra).SatisfiedBy G
  separatesFourLetterWords :
    ¬(Identity.mk xyxy xyyx).SatisfiedBy G
  xytyxIsoterm : Isoterm G xytyx
  xtyxyIsoterm : Isoterm G xtyxy

/-- The member used against identities whose variables have a cover of
length at most `bound`. It is Perkins's identity with `n = 4 * bound + 8`. -/
def obstruction (bound : Nat) : Identity Nat :=
  perkinsIdentity (4 * bound + 7)

/-- Every obstruction member is valid under Perkins's explicit identity
family hypothesis. -/
theorem obstruction_valid
    {G : Semigroup S}
    (hypotheses : PerkinsHypotheses G)
    (bound : Nat) :
    (obstruction bound).SatisfiedBy G := by
  apply hypotheses.identityFamily
  omega

/-- The exact derivational nonredundancy left by Perkins's combinatorial
argument.

For every variable bound, no sound collection of valid identities using at
most that many variables can derive the `n = 4 * bound + 8` member of the
Perkins sequence. This is strictly narrower than assuming that `G` is
nonfinitely based.
-/
def BoundedPerkinsUnderivability (G : Semigroup S) : Prop :=
  ∀ bound basis,
    Models G basis →
    BasisUsesAtMost basis bound →
    ¬Derives basis (obstruction bound).lhs (obstruction bound).rhs

/-- The false occurrence-only weakening of Perkins's one-step lemma.

This definition is retained only so `BoundaryCounterexample.lean` can prevent
the semantic-class hypothesis from being dropped again.
-/
def OccurrenceOnlyPerkinsOrderPreservation
    (G : Semigroup S) : Prop :=
  ∀ bound (identity : Identity Nat),
    identity.SatisfiedBy G →
    identity.UsesAtMost bound →
    ContextuallyPreservesOccurrencePattern (4 * bound + 7)
      identity.lhs identity.rhs

/-!
The occurrence pattern alone is not sufficient for the one-step lemma above.
The source proof also uses that the current word is identity-equivalent to the
original Perkins obstruction.  The following instance of Perkins's own
two-`y` identity is a counterexample to the statement without that semantic
hypothesis.
-/

private def counterexampleMiddle : Word Nat :=
  ⟨2, (List.range 18).map (fun index => index + 3)⟩

private def counterexampleSubstitution (letter : Nat) : Word Nat :=
  if letter = 0 then Word.singleton 0
  else if letter = 1 then Word.singleton 1
  else counterexampleMiddle

private theorem counterexampleMiddle_toList :
    counterexampleMiddle.toList = middleVariables 19 := by
  decide

private theorem perkinsIdentity_one_usesAtMost_three :
    (perkinsIdentity 1).UsesAtMost 3 := by
  refine ⟨[0, 1, 2], by decide, ?_, ?_⟩
  · intro letter member
    change letter ∈ (perkinsLeft 1).toList at member
    rw [perkinsLeft_toList] at member
    simp [middleVariables] at member ⊢
    omega
  · intro letter member
    change letter ∈ (perkinsRight 1).toList at member
    rw [perkinsRight_toList] at member
    simp [middleVariables] at member ⊢
    omega

private theorem counterexample_left_toList :
    ((perkinsIdentity 1).lhs.bind counterexampleSubstitution).toList =
      [0, 1] ++ middleVariables 19 ++ [0] ++
        middleVariables 19 ++ [1] := by
  simp [perkinsIdentity, perkinsLeft_toList, Word.toList_bind,
    counterexampleSubstitution, counterexampleMiddle_toList,
    middleVariables]

private theorem counterexample_right_toList :
    ((perkinsIdentity 1).rhs.bind counterexampleSubstitution).toList =
      [0] ++ middleVariables 19 ++ [1, 0, 1] ++
        middleVariables 19 := by
  simp [perkinsIdentity, perkinsRight_toList, Word.toList_bind,
    counterexampleSubstitution, counterexampleMiddle_toList,
    middleVariables]

private theorem counterexample_left_pattern :
    OccurrencePattern 19
      ((perkinsIdentity 1).lhs.bind counterexampleSubstitution).toList := by
  refine ⟨middleVariables 19, middleVariables 19,
    List.Perm.refl _, List.Perm.refl _, ?_⟩
  exact counterexample_left_toList

private theorem counterexample_right_not_pattern :
    ¬OccurrencePattern 19
      ((perkinsIdentity 1).rhs.bind counterexampleSubstitution).toList := by
  intro pattern
  rcases pattern with
    ⟨firstMiddle, secondMiddle, firstPerm, _, shape⟩
  have firstNonempty : firstMiddle ≠ [] := by
    intro empty
    subst firstMiddle
    have targetNonempty : middleVariables 19 ≠ [] := by
      simp [middleVariables]
    exact targetNonempty firstPerm.symm.eq_nil
  rcases firstMiddle with _ | ⟨first, rest⟩
  · exact firstNonempty rfl
  · have secondLetter : 2 = 1 := by
      have atIndex :=
        congrArg (fun letters => letters[1]?) shape
      rw [counterexample_right_toList] at atIndex
      simpa [middleVariables] using atIndex.symm
    omega

/-- Any semigroup satisfying the `n = 2` Perkins identity refutes the
occurrence-only preservation statement. -/
theorem not_occurrenceOnlyPerkinsOrderPreservation_of_perkinsIdentity_one
    {G : Semigroup S}
    (valid : (perkinsIdentity 1).SatisfiedBy G) :
    ¬OccurrenceOnlyPerkinsOrderPreservation G := by
  intro preserves
  have preserved :=
    preserves 3 (perkinsIdentity 1) valid
      perkinsIdentity_one_usesAtMost_three
      ([] : List Nat) ([] : List Nat) counterexampleSubstitution
      counterexample_left_pattern
  exact counterexample_right_not_pattern preserved

/-- Perkins's own hypotheses refute the occurrence-only preservation
statement, since they include the `n = 2` identity used above. -/
theorem PerkinsHypotheses.not_occurrenceOnlyPerkinsOrderPreservation
    {G : Semigroup S}
    (hypotheses : PerkinsHypotheses G) :
    ¬OccurrenceOnlyPerkinsOrderPreservation G :=
  not_occurrenceOnlyPerkinsOrderPreservation_of_perkinsIdentity_one
    (hypotheses.identityFamily 1 (by omega))

/-- A contextual substitution instance of a valid identity is valid. -/
theorem contextualInstance_satisfiedBy
    {G : Semigroup S} {identity : Identity Nat}
    (valid : identity.SatisfiedBy G)
    (pre post : List Nat) (substitution : Nat → Word Nat) :
    (Identity.mk
      (contextWord pre (identity.lhs.bind substitution) post)
      (contextWord pre (identity.rhs.bind substitution) post)).SatisfiedBy G := by
  intro valuation
  have middle :
      G.eval valuation (identity.lhs.bind substitution) =
        G.eval valuation (identity.rhs.bind substitution) := by
    simpa only [Semigroup.eval_bind] using
      valid (fun letter => G.eval valuation (substitution letter))
  cases pre with
  | nil =>
      cases post with
      | nil =>
          simpa [contextWord] using middle
      | cons postHead postTail =>
          change
            G.eval valuation
                (identity.lhs.bind substitution ++
                  Word.mk postHead postTail) =
              G.eval valuation
                (identity.rhs.bind substitution ++
                  Word.mk postHead postTail)
          rw [G.eval_append, G.eval_append]
          exact congrArg
            (fun value =>
              G.mul value
                (G.eval valuation (Word.mk postHead postTail)))
            middle
  | cons preHead preTail =>
      cases post with
      | nil =>
          simp only [contextWord, List.append_nil]
          change
            G.eval valuation
                (Word.mk preHead preTail ++
                  identity.lhs.bind substitution) =
              G.eval valuation
                (Word.mk preHead preTail ++
                  identity.rhs.bind substitution)
          rw [G.eval_append, G.eval_append]
          exact congrArg
            (fun value =>
              G.mul
                (G.eval valuation (Word.mk preHead preTail))
                value)
              middle
      | cons postHead postTail =>
          simp only [contextWord]
          change
            G.eval valuation
                ((Word.mk preHead preTail ++
                    identity.lhs.bind substitution) ++
                  Word.mk postHead postTail) =
              G.eval valuation
                ((Word.mk preHead preTail ++
                    identity.rhs.bind substitution) ++
                  Word.mk postHead postTail)
          simp only [G.eval_append]
          exact congrArg
            (fun value =>
              G.mul
                (G.mul
                  (G.eval valuation (Word.mk preHead preTail))
                  value)
                (G.eval valuation (Word.mk postHead postTail)))
            middle

private theorem satisfiedBy_trans
    {G : Semigroup S} {first second third : Word Nat}
    (firstSecond : (Identity.mk first second).SatisfiedBy G)
    (secondThird : (Identity.mk second third).SatisfiedBy G) :
    (Identity.mk first third).SatisfiedBy G := by
  intro valuation
  exact (firstSecond valuation).trans (secondThird valuation)

/-- Sapir's exact one-step invariant for Perkins's argument.

The current contextual word must both have the distinguished occurrence
pattern and lie in the identity class of the original obstruction left side.
This is Condition (III) in the reconstruction of Perkins's proof, specialized
to the occurrence maps used here.
-/
def BoundedPerkinsOccurrenceOrderPreservation
    (G : Semigroup S) : Prop :=
  ∀ bound (identity : Identity Nat),
    identity.SatisfiedBy G →
    identity.UsesAtMost bound →
    ∀ pre post substitution,
      let current :=
        contextWord pre (identity.lhs.bind substitution) post
      let next :=
        contextWord pre (identity.rhs.bind substitution) post
      (Identity.mk (obstruction bound).lhs current).SatisfiedBy G →
      OccurrencePattern (4 * bound + 7) current.toList →
      OccurrencePattern (4 * bound + 7) next.toList

private def swapIdentity (identity : Identity Nat) : Identity Nat :=
  ⟨identity.rhs, identity.lhs⟩

private theorem swapIdentity_satisfiedBy
    {G : Semigroup S} {identity : Identity Nat}
    (valid : identity.SatisfiedBy G) :
    (swapIdentity identity).SatisfiedBy G := by
  intro valuation
  exact (valid valuation).symm

private theorem swapIdentity_usesAtMost
    {identity : Identity Nat} {bound : Nat}
    (uses : identity.UsesAtMost bound) :
    (swapIdentity identity).UsesAtMost bound := by
  rcases uses with ⟨variables, lengthBound, leftUses, rightUses⟩
  exact ⟨variables, lengthBound, rightUses, leftUses⟩

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  rw [Word.toList_bind]
  induction word.toList with
  | nil =>
      cases word with
      | mk head tail =>
          simp [Word.toList] at *
  | cons head tail ih =>
      simp only [List.flatMap_cons, Word.toList_singleton,
        List.singleton_append]
      change List.flatMap (fun letter => [letter]) tail = tail at ih
      exact congrArg (List.cons head) ih

private def ContextuallySameOccurrencePatternInPerkinsClass
    (G : Semigroup S) (bound : Nat)
    (left right : Word Nat) : Prop :=
  ∀ pre post substitution,
    let leftContext :=
      contextWord pre (left.bind substitution) post
    let rightContext :=
      contextWord pre (right.bind substitution) post
    (Identity.mk (obstruction bound).lhs leftContext).SatisfiedBy G →
    (OccurrencePattern (4 * bound + 7) leftContext.toList ↔
      OccurrencePattern (4 * bound + 7) rightContext.toList)

private theorem Derives.contextuallySameOccurrencePatternInPerkinsClass
    {G : Semigroup S} {basis : List (Identity Nat)}
    {left right : Word Nat}
    (models : Models G basis)
    (bounded : BasisUsesAtMost basis bound)
    (preserves : BoundedPerkinsOccurrenceOrderPreservation G)
    (derivation : Derives basis left right) :
    ContextuallySameOccurrencePatternInPerkinsClass
      G bound left right := by
  induction derivation with
  | @fromBasis identity member =>
      simp only [ContextuallySameOccurrencePatternInPerkinsClass]
      intro pre post substitution anchorLeft
      have valid := models identity member
      have uses := bounded identity member
      have contextValid :=
        contextualInstance_satisfiedBy valid pre post substitution
      constructor
      · exact preserves bound identity valid uses
          pre post substitution anchorLeft
      · intro rightPattern
        have anchorRight := satisfiedBy_trans anchorLeft contextValid
        simpa [swapIdentity] using
          preserves bound (swapIdentity identity)
            (swapIdentity_satisfiedBy valid)
            (swapIdentity_usesAtMost uses)
            pre post substitution anchorRight rightPattern
  | refl word =>
      simp only [ContextuallySameOccurrencePatternInPerkinsClass]
      intro pre post substitution anchor
      trivial
  | @symm source target derivation ih =>
      simp only [ContextuallySameOccurrencePatternInPerkinsClass] at ih ⊢
      intro pre post substitution anchorRight
      have reverseValid :
          (Identity.mk target source).SatisfiedBy G := by
        intro valuation
        exact (Derives.sound models derivation valuation).symm
      have reverseContextValid :=
        contextualInstance_satisfiedBy reverseValid pre post substitution
      have anchorLeft :=
        satisfiedBy_trans anchorRight reverseContextValid
      exact (ih pre post substitution anchorLeft).symm
  | @trans source middle target first second ihFirst ihSecond =>
      simp only [ContextuallySameOccurrencePatternInPerkinsClass]
        at ihFirst ihSecond ⊢
      intro pre post substitution anchorLeft
      have firstValid :
          (Identity.mk source middle).SatisfiedBy G := by
        intro valuation
        exact Derives.sound models first valuation
      have firstContextValid :=
        contextualInstance_satisfiedBy firstValid pre post substitution
      have anchorMiddle :=
        satisfiedBy_trans anchorLeft firstContextValid
      exact
        (ihFirst pre post substitution anchorLeft).trans
          (ihSecond pre post substitution anchorMiddle)
  | @prepend p source target derivation ih =>
      simp only [ContextuallySameOccurrencePatternInPerkinsClass] at ih ⊢
      intro pre post substitution anchorLeft
      have leftEq :
          contextWord pre
              ((p ++ source).bind substitution) post =
            contextWord
              (pre ++ (p.bind substitution).toList)
              (source.bind substitution) post := by
        apply Word.toList_injective
        simp only [contextWord_toList, bind_append, Word.toList_append]
        simp only [List.append_assoc]
      have rightEq :
          contextWord pre
              ((p ++ target).bind substitution) post =
            contextWord
              (pre ++ (p.bind substitution).toList)
              (target.bind substitution) post := by
        apply Word.toList_injective
        simp only [contextWord_toList, bind_append, Word.toList_append]
        simp only [List.append_assoc]
      simpa [leftEq, rightEq] using
        ih (pre ++ (p.bind substitution).toList)
          post substitution
          (by simpa [leftEq] using anchorLeft)
  | @appendRight source target derivation suffix ih =>
      simp only [ContextuallySameOccurrencePatternInPerkinsClass] at ih ⊢
      intro pre post substitution anchorLeft
      have leftEq :
          contextWord pre
              ((source ++ suffix).bind substitution) post =
            contextWord pre (source.bind substitution)
              ((suffix.bind substitution).toList ++ post) := by
        apply Word.toList_injective
        simp only [contextWord_toList, bind_append, Word.toList_append]
        simp only [List.append_assoc]
      have rightEq :
          contextWord pre
              ((target ++ suffix).bind substitution) post =
            contextWord pre (target.bind substitution)
              ((suffix.bind substitution).toList ++ post) := by
        apply Word.toList_injective
        simp only [contextWord_toList, bind_append, Word.toList_append]
        simp only [List.append_assoc]
      simpa [leftEq, rightEq] using
        ih pre ((suffix.bind substitution).toList ++ post)
          substitution
          (by simpa [leftEq] using anchorLeft)
  | @subst source target derivation first ih =>
      simp only [ContextuallySameOccurrencePatternInPerkinsClass] at ih ⊢
      intro pre post second anchorLeft
      have leftEq :
          contextWord pre
              ((source.bind first).bind second) post =
            contextWord pre
              (source.bind
                (fun letter => (first letter).bind second)) post := by
        rw [bind_bind]
      have rightEq :
          contextWord pre
              ((target.bind first).bind second) post =
            contextWord pre
              (target.bind
                (fun letter => (first letter).bind second)) post := by
        rw [bind_bind]
      simpa [leftEq, rightEq] using
        ih pre post
          (fun letter => (first letter).bind second)
          (by simpa [leftEq] using anchorLeft)

/-- Sapir's semantic one-step occurrence lemma implies the exact bounded
underivability proposition.  All derivation induction is internal to Lean. -/
theorem boundedPerkinsUnderivability_of_occurrenceOrderPreservation
    {G : Semigroup S}
    (preserves : BoundedPerkinsOccurrenceOrderPreservation G) :
    BoundedPerkinsUnderivability G := by
  intro bound basis models bounded derivation
  have invariant :=
    Derives.contextuallySameOccurrencePatternInPerkinsClass
      models bounded preserves derivation
      ([] : List Nat) ([] : List Nat) Word.singleton
  have anchor :
      Identity.SatisfiedBy
        (Identity.mk (obstruction bound).lhs
          (contextWord []
            ((obstruction bound).lhs.bind Word.singleton) []))
        G := by
    intro valuation
    rw [contextWord_nil_nil, bind_singleton]
  have endpointInvariant :=
    invariant anchor
  have rightPattern :
      OccurrencePattern (4 * bound + 7)
        (obstruction bound).rhs.toList := by
    simpa only [contextWord_nil_nil, bind_singleton, obstruction,
      perkinsIdentity] using
      endpointInvariant.mp
        (by
          simpa only [contextWord_nil_nil, bind_singleton, obstruction,
            perkinsIdentity] using
            perkinsLeft_has_occurrencePattern (4 * bound + 7))
  exact
    perkinsRight_not_occurrencePattern (4 * bound + 7) (by omega)
      rightPattern

/-- The explicit Perkins sequence and its bounded derivational
nonredundancy imply nonfinite basability. -/
theorem nonfinitelyBased_of_perkins
    {G : Semigroup S}
    (hypotheses : PerkinsHypotheses G)
    (underivable : BoundedPerkinsUnderivability G) :
    NonfinitelyBased G := by
  apply nonfinitelyBased_of_variable_bound_obstructions obstruction
  · exact obstruction_valid hypotheses
  · exact underivable

end SemigroupBasis.Nonfinite.B2One
