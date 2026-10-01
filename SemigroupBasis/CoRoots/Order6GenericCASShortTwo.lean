import SemigroupBasis.Examples.ProjectionQuadraticThree
import SemigroupBasis.Generated.CatalogueOrder3

namespace SemigroupBasis.CoRoots.Order6GenericCASShortTwo

open SemigroupBasis
open SemigroupBasis.Examples

/-- The exact catalogue factor used by the two short-word generic-CAS roots. -/
abbrev shortFactor : Semigroup (Fin 3) :=
  SemigroupBasis.Generated.Catalogue.S3_4.table.semigroup

/-- Identify the generated catalogue table with the released
projection/quadratic model. -/
theorem shortFactorTable_eq_projectionQuadraticThree :
    SemigroupBasis.Generated.Catalogue.S3_4.table =
      projectionQuadraticThree := by
  unfold SemigroupBasis.Generated.Catalogue.S3_4.table
    SemigroupBasis.Generated.Catalogue.S3_4.mul
    projectionQuadraticThree projectionQuadraticThreeMul
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext left right
  decide +revert

def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private inductive ListDerives (basis : List (Identity Nat)) :
    List Nat → List Nat → Prop
  | empty : ListDerives basis [] []
  | words {leftHead rightHead : Nat} {leftTail rightTail : List Nat} :
      Derives basis
          (wordOfCons leftHead leftTail)
          (wordOfCons rightHead rightTail) →
        ListDerives basis
          (leftHead :: leftTail) (rightHead :: rightTail)

private theorem listDerives_of_perm
    {basis : List (Identity Nat)}
    (commutes : ∀ left right : Word Nat,
      Derives basis (left ++ right) (right ++ left))
    {source target : List Nat} (permutation : source.Perm target) :
    ListDerives basis source target := by
  induction permutation with
  | nil =>
      exact ListDerives.empty
  | cons head _ inductionHypothesis =>
      cases inductionHypothesis with
      | empty =>
          exact ListDerives.words (Derives.refl _)
      | words derivation =>
          exact ListDerives.words <| by
            simpa [wordOfCons, Word.singleton, Word.append] using
              Derives.prepend (Word.singleton head) derivation
  | swap first second suffix =>
      exact ListDerives.words <| by
        cases suffix with
        | nil =>
            simpa [wordOfCons, Word.singleton, Word.append] using
              commutes (Word.singleton second) (Word.singleton first)
        | cons next rest =>
            have swapped :=
              Derives.appendRight
                (commutes
                  (Word.singleton second) (Word.singleton first))
                (wordOfCons next rest)
            simpa [wordOfCons, Word.singleton, Word.append,
              Word.append_assoc] using swapped
  | trans _ _ firstProof secondProof =>
      cases firstProof with
      | empty =>
          cases secondProof
          exact ListDerives.empty
      | words firstDerivation =>
          cases secondProof with
          | words secondDerivation =>
              exact ListDerives.words
                (Derives.trans firstDerivation secondDerivation)

/-- Global commutativity derives every permutation of a nonempty word. -/
theorem derivesPermutation
    {basis : List (Identity Nat)}
    (commutes : ∀ left right : Word Nat,
      Derives basis (left ++ right) (right ++ left))
    (left right : Word Nat)
    (permutation : left.toList.Perm right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          cases listDerives_of_perm commutes permutation with
          | words derivation => exact derivation

private def projectionSeparator (selected : Nat) : Nat → Fin 3 :=
  fun letter => if letter = selected then 2 else 0

private def quadraticSeparator (selected : Nat) : Nat → Fin 3 :=
  fun letter => if letter = selected then 0 else 2

private theorem quadraticSeparator_eval (selected first second : Nat) :
    projectionQuadraticThree.semigroup.eval
        (quadraticSeparator selected) (wordOfCons first [second]) =
      if first = selected ∨ second = selected then (0 : Fin 3)
      else (1 : Fin 3) := by
  change
    projectionQuadraticThreeMul
        (quadraticSeparator selected first)
        (quadraticSeparator selected second) =
      if first = selected ∨ second = selected then 0 else 1
  by_cases firstSelected : first = selected <;>
    by_cases secondSelected : second = selected <;>
      simp [projectionQuadraticThreeMul, quadraticSeparator,
        firstSelected, secondSelected]

private theorem valid_singleton_eq {first second : Nat}
    (valid :
      (Identity.mk (Word.singleton first) (Word.singleton second)).SatisfiedBy
        projectionQuadraticThree.semigroup) :
    first = second := by
  have evaluated := valid (projectionSeparator first)
  change projectionSeparator first first =
    projectionSeparator first second at evaluated
  by_cases same : first = second
  · exact same
  · exfalso
    simp [projectionSeparator] at evaluated
    exact same evaluated.symm

private theorem valid_quadratic_support_iff
    {first second third fourth selected : Nat}
    (valid :
      (Identity.mk
        (wordOfCons first [second])
        (wordOfCons third [fourth])).SatisfiedBy
          projectionQuadraticThree.semigroup) :
    (first = selected ∨ second = selected) ↔
      (third = selected ∨ fourth = selected) := by
  have evaluated := valid (quadraticSeparator selected)
  rw [quadraticSeparator_eval, quadraticSeparator_eval] at evaluated
  constructor
  · intro leftSupport
    by_cases rightSupport : third = selected ∨ fourth = selected
    · exact rightSupport
    · exfalso
      simp [leftSupport, rightSupport] at evaluated
  · intro rightSupport
    by_cases leftSupport : first = selected ∨ second = selected
    · exact leftSupport
    · exfalso
      simp [leftSupport, rightSupport] at evaluated

private theorem valid_quadratic_perm
    {first second third fourth : Nat}
    (valid :
      (Identity.mk
        (wordOfCons first [second])
        (wordOfCons third [fourth])).SatisfiedBy
          projectionQuadraticThree.semigroup) :
    [first, second].Perm [third, fourth] := by
  have support (selected : Nat) :
      (first = selected ∨ second = selected) ↔
        (third = selected ∨ fourth = selected) :=
    valid_quadratic_support_iff valid
  have thirdSource : third = first ∨ third = second := by
    have occurrence := (support third).mpr (Or.inl rfl)
    exact occurrence.imp Eq.symm Eq.symm
  have fourthSource : fourth = first ∨ fourth = second := by
    have occurrence := (support fourth).mpr (Or.inr rfl)
    exact occurrence.imp Eq.symm Eq.symm
  rcases thirdSource with thirdFirst | thirdSecond
  · rcases fourthSource with fourthFirst | fourthSecond
    · subst third
      subst fourth
      by_cases same : first = second
      · subst second
        exact List.Perm.refl _
      · have missing := (support second).mp (Or.inr rfl)
        have contradiction : first = second := missing.elim id id
        exact False.elim (same contradiction)
    · subst third
      subst fourth
      exact List.Perm.refl _
  · rcases fourthSource with fourthFirst | fourthSecond
    · subst third
      subst fourth
      exact List.Perm.swap _ _ []
    · subst third
      subst fourth
      by_cases same : first = second
      · subst second
        exact List.Perm.refl _
      · have missing := (support first).mp (Or.inl rfl)
        have contradiction : second = first := missing.elim id id
        exact False.elim (same contradiction.symm)

private def lengthState (length : Nat) : Fin 3 :=
  if length = 1 then 2 else if length = 2 then 1 else 0

private theorem eval_constant_two (word : Word Nat) :
    projectionQuadraticThree.semigroup.eval
        (fun _ => (2 : Fin 3)) word =
      lengthState word.toList.length := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third suffix =>
              have evaluated :=
                projectionQuadraticEval_long
                  (fun _ => (2 : Fin 3)) head second third suffix
              simpa [lengthState, Word.toList] using evaluated

private theorem same_length_region
    {left right : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy
      projectionQuadraticThree.semigroup) :
    (left.toList.length = 1 ∧ right.toList.length = 1) ∨
      (left.toList.length = 2 ∧ right.toList.length = 2) ∨
      (3 ≤ left.toList.length ∧ 3 ≤ right.toList.length) := by
  have evaluated := valid (fun _ => (2 : Fin 3))
  rw [eval_constant_two, eval_constant_two] at evaluated
  have values := congrArg Fin.val evaluated
  have leftPositive : 0 < left.toList.length := by
    cases left
    simp [Word.toList]
  have rightPositive : 0 < right.toList.length := by
    cases right
    simp [Word.toList]
  by_cases leftOne : left.toList.length = 1
  · left
    refine ⟨leftOne, ?_⟩
    by_cases rightOne : right.toList.length = 1
    · exact rightOne
    · by_cases rightTwo : right.toList.length = 2
      · simp [lengthState, leftOne, rightOne, rightTwo] at values
      · have rightLong : 3 ≤ right.toList.length := by omega
        simp [lengthState, leftOne, rightOne, rightTwo] at values
  · by_cases leftTwo : left.toList.length = 2
    · right
      left
      refine ⟨leftTwo, ?_⟩
      by_cases rightOne : right.toList.length = 1
      · simp [lengthState, leftOne, leftTwo, rightOne] at values
      · by_cases rightTwo : right.toList.length = 2
        · exact rightTwo
        · have rightLong : 3 ≤ right.toList.length := by omega
          simp [lengthState, leftOne, leftTwo, rightOne, rightTwo] at values
    · right
      right
      have leftLong : 3 ≤ left.toList.length := by omega
      refine ⟨leftLong, ?_⟩
      by_cases rightOne : right.toList.length = 1
      · simp [lengthState, leftOne, leftTwo, rightOne] at values
      · by_cases rightTwo : right.toList.length = 2
        · simp [lengthState, leftOne, leftTwo, rightOne, rightTwo] at values
        · omega

private theorem singleton_word_eq
    {left right : Word Nat}
    (leftOne : left.toList.length = 1)
    (rightOne : right.toList.length = 1)
    (valid : (Identity.mk left right).SatisfiedBy
      projectionQuadraticThree.semigroup) :
    left = right := by
  cases left with
  | mk leftHead leftTail =>
      cases leftTail with
      | nil =>
          cases right with
          | mk rightHead rightTail =>
              cases rightTail with
              | nil =>
                  have heads : leftHead = rightHead :=
                    valid_singleton_eq valid
                  subst rightHead
                  rfl
              | cons next rest => simp [Word.toList] at rightOne
      | cons next rest => simp [Word.toList] at leftOne

private theorem quadratic_word_perm
    {left right : Word Nat}
    (leftTwo : left.toList.length = 2)
    (rightTwo : right.toList.length = 2)
    (valid : (Identity.mk left right).SatisfiedBy
      projectionQuadraticThree.semigroup) :
    left.toList.Perm right.toList := by
  cases left with
  | mk leftHead leftTail =>
      cases leftTail with
      | nil => simp [Word.toList] at leftTwo
      | cons leftSecond leftRest =>
          cases leftRest with
          | nil =>
              cases right with
              | mk rightHead rightTail =>
                  cases rightTail with
                  | nil => simp [Word.toList] at rightTwo
                  | cons rightSecond rightRest =>
                      cases rightRest with
                      | nil =>
                          simpa [wordOfCons, Word.toList] using
                            valid_quadratic_perm valid
                      | cons next rest => simp [Word.toList] at rightTwo
          | cons next rest => simp [Word.toList] at leftTwo

/-- `S3_4` keeps singleton words literal, keeps quadratic multisets literal,
and identifies every word of length at least three. -/
theorem classifyValidIdentity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy shortFactor) :
    identity.lhs = identity.rhs ∨
      (identity.lhs.toList.length = 2 ∧
        identity.rhs.toList.length = 2 ∧
        identity.lhs.toList.Perm identity.rhs.toList) ∨
      (3 ≤ identity.lhs.toList.length ∧
        3 ≤ identity.rhs.toList.length) := by
  have concreteValid :
      identity.SatisfiedBy projectionQuadraticThree.semigroup := by
    rw [← shortFactorTable_eq_projectionQuadraticThree]
    exact valid
  rcases same_length_region concreteValid with
    ⟨leftOne, rightOne⟩ | ⟨leftTwo, rightTwo⟩ |
      ⟨leftLong, rightLong⟩
  · exact Or.inl <|
      singleton_word_eq leftOne rightOne concreteValid
  · exact Or.inr <| Or.inl
      ⟨leftTwo, rightTwo,
        quadratic_word_perm leftTwo rightTwo concreteValid⟩
  · exact Or.inr <| Or.inr ⟨leftLong, rightLong⟩

end SemigroupBasis.CoRoots.Order6GenericCASShortTwo
