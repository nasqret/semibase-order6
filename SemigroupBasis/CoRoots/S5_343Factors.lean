import SemigroupBasis.CoRoots.S5_343Syntax
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.Examples.SimpleEndpointsFour
import SemigroupBasis.Generated.CatalogueOrder5Part03
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.TransferPower

namespace SemigroupBasis.CoRoots.S5_343Factors

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots

private def initialSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 3

private def finalSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 3

private theorem simpleInitial_of_valid
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          simpleEndpointsFour.semigroup) :
    ∀ z,
      (initial₁ = z ∧ z ∉ middle₁ ∧ final₁ ≠ z) ↔
        (initial₂ = z ∧ z ∉ middle₂ ∧ final₂ ≠ z) := by
  intro z
  have evaluated := valid (initialSeparator z)
  constructor
  · intro simple₁
    have lhsTwo :
        simpleEndpointsFour.semigroup.eval (initialSeparator z)
          (wordOfEndpoints initial₁ middle₁ final₁) = (2 : Fin 4) := by
      simpa [initialSeparator] using
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          z initial₁ middle₁ final₁).2 simple₁
    have rhsTwo := evaluated.symm.trans lhsTwo
    exact
      (simpleEndpointsEval_initialSeparator_eq_two_iff
        z initial₂ middle₂ final₂).1 <| by
          simpa [initialSeparator] using rhsTwo
  · intro simple₂
    have rhsTwo :
        simpleEndpointsFour.semigroup.eval (initialSeparator z)
          (wordOfEndpoints initial₂ middle₂ final₂) = (2 : Fin 4) := by
      simpa [initialSeparator] using
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          z initial₂ middle₂ final₂).2 simple₂
    have lhsTwo := evaluated.trans rhsTwo
    exact
      (simpleEndpointsEval_initialSeparator_eq_two_iff
        z initial₁ middle₁ final₁).1 <| by
          simpa [initialSeparator] using lhsTwo

private theorem simpleFinal_of_valid
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          simpleEndpointsFour.semigroup) :
    ∀ z,
      (final₁ = z ∧ z ∉ initial₁ :: middle₁) ↔
        (final₂ = z ∧ z ∉ initial₂ :: middle₂) := by
  intro z
  have evaluated := valid (finalSeparator z)
  constructor
  · intro simple₁
    have lhsOne :
        simpleEndpointsFour.semigroup.eval (finalSeparator z)
          (wordOfEndpoints initial₁ middle₁ final₁) = (1 : Fin 4) := by
      simpa [finalSeparator] using
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          z initial₁ middle₁ final₁).2 simple₁
    have rhsOne := evaluated.symm.trans lhsOne
    exact
      (simpleEndpointsEval_finalSeparator_eq_one_iff
        z initial₂ middle₂ final₂).1 <| by
          simpa [finalSeparator] using rhsOne
  · intro simple₂
    have rhsOne :
        simpleEndpointsFour.semigroup.eval (finalSeparator z)
          (wordOfEndpoints initial₂ middle₂ final₂) = (1 : Fin 4) := by
      simpa [finalSeparator] using
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          z initial₂ middle₂ final₂).2 simple₂
    have lhsOne := evaluated.trans rhsOne
    exact
      (simpleEndpointsEval_finalSeparator_eq_one_iff
        z initial₁ middle₁ final₁).1 <| by
          simpa [finalSeparator] using lhsOne

private def splitMiddleFinal (current : Nat) :
    List Nat → List Nat × Nat
  | [] => ([], current)
  | next :: rest =>
      let split := splitMiddleFinal next rest
      (current :: split.1, split.2)

private theorem splitMiddleFinal_reconstruct
    (current : Nat) (rest : List Nat) :
    (splitMiddleFinal current rest).1 ++
        [(splitMiddleFinal current rest).2] =
      current :: rest := by
  induction rest generalizing current with
  | nil =>
      rfl
  | cons next rest induction =>
      simp only [splitMiddleFinal]
      simpa using congrArg (List.cons current) (induction next)

private theorem wordOfEndpoints_splitMiddleFinal
    (initial current : Nat) (rest : List Nat) :
    wordOfEndpoints initial (splitMiddleFinal current rest).1
        (splitMiddleFinal current rest).2 =
      Word.mk initial (current :: rest) := by
  apply Word.toList_injective
  change
    initial ::
        ((splitMiddleFinal current rest).1 ++
          [(splitMiddleFinal current rest).2]) =
      initial :: current :: rest
  exact congrArg (List.cons initial)
    (splitMiddleFinal_reconstruct current rest)

private theorem singleton_iff_of_simpleEndpoints_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy simpleEndpointsFour.semigroup) :
    identity.lhs.tail = [] ↔ identity.rhs.tail = [] := by
  have evaluated := valid (fun _ => (1 : Fin 4))
  constructor
  · intro lhsSingleton
    have lhsOne :
        simpleEndpointsFour.semigroup.eval
            (fun _ => (1 : Fin 4)) identity.lhs = (1 : Fin 4) :=
      (simpleEndpointsSingletonSeparator identity.lhs).2 lhsSingleton
    have rhsOne := evaluated.symm.trans lhsOne
    exact
      (simpleEndpointsSingletonSeparator identity.rhs).1 rhsOne
  · intro rhsSingleton
    have rhsOne :
        simpleEndpointsFour.semigroup.eval
            (fun _ => (1 : Fin 4)) identity.rhs = (1 : Fin 4) :=
      (simpleEndpointsSingletonSeparator identity.rhs).2 rhsSingleton
    have lhsOne := evaluated.trans rhsOne
    exact
      (simpleEndpointsSingletonSeparator identity.lhs).1 lhsOne

private theorem final_wordOfEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) :
    (wordOfEndpoints initial middle final).final = final := by
  rw [wordOfEndpoints_eq, Word.final_append]
  induction middle with
  | nil =>
      rfl
  | cons next rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

private theorem simpleInitial_wordOfEndpoints_iff
    (initial : Nat) (middle : List Nat) (final z : Nat) :
    S5_107.SimpleInitial (wordOfEndpoints initial middle final) z ↔
      initial = z ∧ z ∉ middle ∧ final ≠ z := by
  change
    ((wordOfEndpoints initial middle final).toList.count z = 1 ∧
        initial = z) ↔
      initial = z ∧ z ∉ middle ∧ final ≠ z
  constructor
  · rintro ⟨countOne, initialEq⟩
    subst initial
    rw [toList_wordOfEndpoints] at countOne
    simp only [List.count_cons_self, List.count_append,
      List.count_singleton] at countOne
    have middleZero : middle.count z = 0 := by omega
    have finalNe : final ≠ z := by
      intro finalEq
      subst final
      simp at countOne
    exact
      ⟨rfl, List.count_eq_zero.mp middleZero, finalNe⟩
  · rintro ⟨initialEq, middleAbsent, finalNe⟩
    subst initial
    constructor
    · simp [toList_wordOfEndpoints,
        List.count_eq_zero.mpr middleAbsent,
        finalNe, Ne.symm finalNe]
    · rfl

private theorem simpleFinal_wordOfEndpoints_iff
    (initial : Nat) (middle : List Nat) (final z : Nat) :
    S5_107.SimpleFinal (wordOfEndpoints initial middle final) z ↔
      final = z ∧ z ∉ initial :: middle := by
  change
    ((wordOfEndpoints initial middle final).toList.count z = 1 ∧
        (wordOfEndpoints initial middle final).final = z) ↔
      final = z ∧ z ∉ initial :: middle
  rw [final_wordOfEndpoints]
  constructor
  · rintro ⟨countOne, finalEq⟩
    subst final
    rw [toList_wordOfEndpoints, List.count_append] at countOne
    have prefixZero : (initial :: middle).count z = 0 := by
      have countEquation :
          (initial :: middle).count z + 1 = 1 := by
        simpa using countOne
      omega
    exact ⟨rfl, List.count_eq_zero.mp prefixZero⟩
  · rintro ⟨finalEq, prefixAbsent⟩
    subst final
    constructor
    · rw [toList_wordOfEndpoints, List.count_append]
      simp [List.count_eq_zero.mpr prefixAbsent]
    · rfl

private theorem heads_eq_of_firstOccurrences
    (identity : Identity Nat)
    (firstOccurrences :
      firstOccurrenceSequence identity.lhs.toList =
        firstOccurrenceSequence identity.rhs.toList) :
    identity.lhs.head = identity.rhs.head := by
  cases identity with
  | mk lhs rhs =>
      cases lhs with
      | mk lhsHead lhsTail =>
          cases rhs with
          | mk rhsHead rhsTail =>
              simp only [Word.toList, firstOccurrenceSequence,
                List.cons.injEq] at firstOccurrences
              exact firstOccurrences.1

private theorem valid_simpleInitial_iff
    (identity : Identity Nat)
    (firstOccurrences :
      firstOccurrenceSequence identity.lhs.toList =
        firstOccurrenceSequence identity.rhs.toList)
    (valid :
      identity.SatisfiedBy simpleEndpointsFour.semigroup) :
    ∀ z,
      S5_107.SimpleInitial identity.lhs z ↔
        S5_107.SimpleInitial identity.rhs z := by
  intro z
  rcases identity with
    ⟨⟨lhsHead, lhsTail⟩, ⟨rhsHead, rhsTail⟩⟩
  cases lhsTail with
  | nil =>
      cases rhsTail with
      | nil =>
          have heads : lhsHead = rhsHead := by
            simp only [Word.toList, firstOccurrenceSequence,
              List.cons.injEq] at firstOccurrences
            exact firstOccurrences.1
          subst rhsHead
          exact Iff.rfl
      | cons rhsSecond rhsRest =>
          have impossible :
              rhsSecond :: rhsRest = [] :=
            (singleton_iff_of_simpleEndpoints_valid
              ⟨⟨lhsHead, []⟩, ⟨rhsHead, rhsSecond :: rhsRest⟩⟩
              valid).mp rfl
          simp at impossible
  | cons lhsSecond lhsRest =>
      cases rhsTail with
      | nil =>
          have impossible :
              lhsSecond :: lhsRest = [] :=
            (singleton_iff_of_simpleEndpoints_valid
              ⟨⟨lhsHead, lhsSecond :: lhsRest⟩, ⟨rhsHead, []⟩⟩
              valid).mpr rfl
          simp at impossible
      | cons rhsSecond rhsRest =>
          let lhsSplit := splitMiddleFinal lhsSecond lhsRest
          let rhsSplit := splitMiddleFinal rhsSecond rhsRest
          have lhsReconstruct :
              wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2 =
                Word.mk lhsHead (lhsSecond :: lhsRest) :=
            wordOfEndpoints_splitMiddleFinal
              lhsHead lhsSecond lhsRest
          have rhsReconstruct :
              wordOfEndpoints rhsHead rhsSplit.1 rhsSplit.2 =
                Word.mk rhsHead (rhsSecond :: rhsRest) :=
            wordOfEndpoints_splitMiddleFinal
              rhsHead rhsSecond rhsRest
          have endpointValid :
              (Identity.mk
                (wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2)
                (wordOfEndpoints rhsHead rhsSplit.1 rhsSplit.2)).SatisfiedBy
                  simpleEndpointsFour.semigroup := by
            rw [lhsReconstruct, rhsReconstruct]
            exact valid
          have endpointPreserved :=
            simpleInitial_of_valid
              lhsHead lhsSplit.1 lhsSplit.2
              rhsHead rhsSplit.1 rhsSplit.2 endpointValid z
          rw [← lhsReconstruct, ← rhsReconstruct]
          exact
            (simpleInitial_wordOfEndpoints_iff
              lhsHead lhsSplit.1 lhsSplit.2 z).trans <|
              endpointPreserved.trans <|
                (simpleInitial_wordOfEndpoints_iff
                  rhsHead rhsSplit.1 rhsSplit.2 z).symm

private theorem valid_simpleFinal_iff
    (identity : Identity Nat)
    (firstOccurrences :
      firstOccurrenceSequence identity.lhs.toList =
        firstOccurrenceSequence identity.rhs.toList)
    (valid :
      identity.SatisfiedBy simpleEndpointsFour.semigroup) :
    ∀ z,
      S5_107.SimpleFinal identity.lhs z ↔
        S5_107.SimpleFinal identity.rhs z := by
  intro z
  rcases identity with
    ⟨⟨lhsHead, lhsTail⟩, ⟨rhsHead, rhsTail⟩⟩
  cases lhsTail with
  | nil =>
      cases rhsTail with
      | nil =>
          have heads : lhsHead = rhsHead := by
            simp only [Word.toList, firstOccurrenceSequence,
              List.cons.injEq] at firstOccurrences
            exact firstOccurrences.1
          subst rhsHead
          exact Iff.rfl
      | cons rhsSecond rhsRest =>
          have impossible :
              rhsSecond :: rhsRest = [] :=
            (singleton_iff_of_simpleEndpoints_valid
              ⟨⟨lhsHead, []⟩, ⟨rhsHead, rhsSecond :: rhsRest⟩⟩
              valid).mp rfl
          simp at impossible
  | cons lhsSecond lhsRest =>
      cases rhsTail with
      | nil =>
          have impossible :
              lhsSecond :: lhsRest = [] :=
            (singleton_iff_of_simpleEndpoints_valid
              ⟨⟨lhsHead, lhsSecond :: lhsRest⟩, ⟨rhsHead, []⟩⟩
              valid).mpr rfl
          simp at impossible
      | cons rhsSecond rhsRest =>
          let lhsSplit := splitMiddleFinal lhsSecond lhsRest
          let rhsSplit := splitMiddleFinal rhsSecond rhsRest
          have lhsReconstruct :
              wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2 =
                Word.mk lhsHead (lhsSecond :: lhsRest) :=
            wordOfEndpoints_splitMiddleFinal
              lhsHead lhsSecond lhsRest
          have rhsReconstruct :
              wordOfEndpoints rhsHead rhsSplit.1 rhsSplit.2 =
                Word.mk rhsHead (rhsSecond :: rhsRest) :=
            wordOfEndpoints_splitMiddleFinal
              rhsHead rhsSecond rhsRest
          have endpointValid :
              (Identity.mk
                (wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2)
                (wordOfEndpoints rhsHead rhsSplit.1 rhsSplit.2)).SatisfiedBy
                  simpleEndpointsFour.semigroup := by
            rw [lhsReconstruct, rhsReconstruct]
            exact valid
          have endpointPreserved :=
            simpleFinal_of_valid
              lhsHead lhsSplit.1 lhsSplit.2
              rhsHead rhsSplit.1 rhsSplit.2 endpointValid z
          rw [← lhsReconstruct, ← rhsReconstruct]
          exact
            (simpleFinal_wordOfEndpoints_iff
              lhsHead lhsSplit.1 lhsSplit.2 z).trans <|
              endpointPreserved.trans <|
                (simpleFinal_wordOfEndpoints_iff
                  rhsHead rhsSplit.1 rhsSplit.2 z).symm

/-- The two exact factors recover the full endpoint-sequence signature. -/
theorem signature_of_factor_valid
    (identity : Identity Nat)
    (leftRegularBandValid :
      identity.SatisfiedBy leftRegularBandThree.semigroup)
    (simpleEndpointsValid :
      identity.SatisfiedBy simpleEndpointsFour.semigroup) :
    S5_343Syntax.SameEndpointSequenceSignature
      identity.lhs identity.rhs := by
  have firstOccurrences :=
    S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity leftRegularBandValid
  have heads :=
    heads_eq_of_firstOccurrences identity firstOccurrences
  have initials :=
    valid_simpleInitial_iff identity firstOccurrences
      simpleEndpointsValid
  have finals :=
    valid_simpleFinal_iff identity firstOccurrences
      simpleEndpointsValid
  refine ⟨firstOccurrences, ?_, ?_⟩
  · constructor
    · intro leftSimple
      have leftInitial :
          S5_107.SimpleInitial identity.lhs identity.lhs.head :=
        ⟨leftSimple, rfl⟩
      have rightInitial := (initials identity.lhs.head).mp leftInitial
      simpa [heads] using rightInitial.1
    · intro rightSimple
      have rightInitial :
          S5_107.SimpleInitial identity.rhs identity.lhs.head := by
        refine ⟨?_, heads.symm⟩
        simpa [heads] using rightSimple
      exact ((initials identity.lhs.head).mpr rightInitial).1
  · constructor
    · intro leftSimple
      have leftFinal :
          S5_107.SimpleFinal identity.lhs identity.lhs.final :=
        ⟨leftSimple, rfl⟩
      have rightFinal := (finals identity.lhs.final).mp leftFinal
      simpa [rightFinal.2] using rightFinal.1
    · intro rightSimple
      have rightFinal :
          S5_107.SimpleFinal identity.rhs identity.rhs.final :=
        ⟨rightSimple, rfl⟩
      have leftFinal := (finals identity.rhs.final).mpr rightFinal
      simpa [leftFinal.2] using leftFinal.1

namespace S5_343

/-- The exact order marker embedding `0 ↦ 0`, `1 ↦ 4`, `2 ↦ 3`. -/
def leftRegularBandEmbedding :
    Embedding leftRegularBandThree.semigroup
      Generated.Catalogue.S5_343.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨4, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The exact simple-endpoint quotient `[0, 1, 2, 0, 3]`. -/
def simpleEndpointsQuotient :
    SplitSurjection Generated.Catalogue.S5_343.table.semigroup
      simpleEndpointsFour.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨2, by decide⟩ else
          if a.val = 3 then ⟨0, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else
        if b.val = 2 then ⟨2, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- Zero-based form of the authoritative initial marker `3/default 5`. -/
def initialMarkerValuation (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 2 else 4

/-- Zero-based form of the authoritative final marker `2/default 5`. -/
def finalMarkerValuation (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 1 else 4

/-- Zero-based order marker `x ↦ 4`, `y ↦ 1`, default `5`. -/
def orderMarkerValuation (x y : Nat) : Nat → Fin 5 :=
  fun letter =>
    if letter = x then 3 else if letter = y then 0 else 4

theorem valid_leftRegularBandThree (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_343.table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  leftRegularBandEmbedding.pullback_identity identity valid

theorem valid_simpleEndpointsFour (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_343.table.semigroup) :
    identity.SatisfiedBy simpleEndpointsFour.semigroup :=
  simpleEndpointsQuotient.pushforwardIdentity identity valid

theorem valid_signature (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_343.table.semigroup) :
    S5_343Syntax.SameEndpointSequenceSignature
      identity.lhs identity.rhs :=
  signature_of_factor_valid identity
    (valid_leftRegularBandThree identity valid)
    (valid_simpleEndpointsFour identity valid)

end S5_343

namespace S5_592

/-- The exact order marker embedding `0 ↦ 0`, `1 ↦ 4`, `2 ↦ 2`. -/
def leftRegularBandEmbedding :
    Embedding leftRegularBandThree.semigroup
      Generated.Catalogue.S5_592.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨4, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

/-- The exact simple-endpoint quotient `[0, 1, 0, 2, 3]`. -/
def simpleEndpointsQuotient :
    SplitSurjection Generated.Catalogue.S5_592.table.semigroup
      simpleEndpointsFour.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else
      if a.val = 1 then ⟨1, by decide⟩ else
        if a.val = 2 then ⟨0, by decide⟩ else
          if a.val = 3 then ⟨2, by decide⟩ else ⟨3, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun b =>
    if b.val = 0 then ⟨0, by decide⟩ else
      if b.val = 1 then ⟨1, by decide⟩ else
        if b.val = 2 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  right_inverse := by
    intro b
    apply Fin.ext
    revert b
    decide

/-- Zero-based form of the authoritative initial marker `4/default 5`. -/
def initialMarkerValuation (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 3 else 4

/-- Zero-based form of the authoritative final marker `2/default 5`. -/
def finalMarkerValuation (tested : Nat) : Nat → Fin 5 :=
  fun letter => if letter = tested then 1 else 4

/-- Zero-based order marker `x ↦ 3`, `y ↦ 1`, default `5`. -/
def orderMarkerValuation (x y : Nat) : Nat → Fin 5 :=
  fun letter =>
    if letter = x then 2 else if letter = y then 0 else 4

theorem valid_leftRegularBandThree (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_592.table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  leftRegularBandEmbedding.pullback_identity identity valid

theorem valid_simpleEndpointsFour (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_592.table.semigroup) :
    identity.SatisfiedBy simpleEndpointsFour.semigroup :=
  simpleEndpointsQuotient.pushforwardIdentity identity valid

theorem valid_signature (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_592.table.semigroup) :
    S5_343Syntax.SameEndpointSequenceSignature
      identity.lhs identity.rhs :=
  signature_of_factor_valid identity
    (valid_leftRegularBandThree identity valid)
    (valid_simpleEndpointsFour identity valid)

end S5_592

end SemigroupBasis.CoRoots.S5_343Factors
