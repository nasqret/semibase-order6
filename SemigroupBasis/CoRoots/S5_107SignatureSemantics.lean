import SemigroupBasis.CoRoots.S5_107Syntax
import SemigroupBasis.CoRoots.S5_107Factors
import SemigroupBasis.CoRoots.S5_107AdjacencySemantics

namespace SemigroupBasis.CoRoots

open SemigroupBasis
open SemigroupBasis.Examples

/-- Split a nonempty list into all but its final entry and its final entry. -/
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
  | cons next rest ih =>
      simp only [splitMiddleFinal]
      simpa using congrArg (List.cons current) (ih next)

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

private theorem cappedMultiplicity_eq_of_min_count_eq
    (identity : Identity Nat)
    (counts :
      ∀ z,
        min (identity.lhs.toList.count z) 2 =
          min (identity.rhs.toList.count z) 2) :
    ∀ z,
      S5_107.cappedMultiplicity identity.lhs z =
        S5_107.cappedMultiplicity identity.rhs z := by
  intro z
  simpa [S5_107.cappedMultiplicity, Nat.min_comm] using counts z

private theorem simpleIn_iff_of_cappedMultiplicity_eq
    (identity : Identity Nat)
    (capped :
      ∀ z,
        S5_107.cappedMultiplicity identity.lhs z =
          S5_107.cappedMultiplicity identity.rhs z) :
    ∀ z,
      S5_107.SimpleIn identity.lhs z ↔
        S5_107.SimpleIn identity.rhs z := by
  intro z
  constructor
  · intro lhsSimple
    have lhsCapped :
        S5_107.cappedMultiplicity identity.lhs z = 1 :=
      (S5_107.cappedMultiplicity_eq_one_iff identity.lhs z).2
        lhsSimple
    have rhsCapped :
        S5_107.cappedMultiplicity identity.rhs z = 1 := by
      rw [← capped z]
      exact lhsCapped
    exact
      (S5_107.cappedMultiplicity_eq_one_iff identity.rhs z).1
        rhsCapped
  · intro rhsSimple
    have rhsCapped :
        S5_107.cappedMultiplicity identity.rhs z = 1 :=
      (S5_107.cappedMultiplicity_eq_one_iff identity.rhs z).2
        rhsSimple
    have lhsCapped :
        S5_107.cappedMultiplicity identity.lhs z = 1 := by
      rw [capped z]
      exact rhsCapped
    exact
      (S5_107.cappedMultiplicity_eq_one_iff identity.lhs z).1
        lhsCapped

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
    have rhsOne :
        simpleEndpointsFour.semigroup.eval
            (fun _ => (1 : Fin 4)) identity.rhs = (1 : Fin 4) :=
      evaluated.symm.trans lhsOne
    exact
      (simpleEndpointsSingletonSeparator identity.rhs).1 rhsOne
  · intro rhsSingleton
    have rhsOne :
        simpleEndpointsFour.semigroup.eval
            (fun _ => (1 : Fin 4)) identity.rhs = (1 : Fin 4) :=
      (simpleEndpointsSingletonSeparator identity.rhs).2 rhsSingleton
    have lhsOne :
        simpleEndpointsFour.semigroup.eval
            (fun _ => (1 : Fin 4)) identity.lhs = (1 : Fin 4) :=
      evaluated.trans rhsOne
    exact
      (simpleEndpointsSingletonSeparator identity.lhs).1 lhsOne

private theorem final_wordOfEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) :
    (wordOfEndpoints initial middle final).final = final := by
  rw [wordOfEndpoints_eq, Word.final_append]
  induction middle with
  | nil =>
      rfl
  | cons next rest ih =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact ih

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
    have middleZero : middle.count z = 0 := by
      omega
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

private theorem valid_simpleInitial_iff_of_callbacks
    (G : Semigroup (Fin 5))
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G)
    (simple :
      ∀ z,
        S5_107.SimpleIn identity.lhs z ↔
          S5_107.SimpleIn identity.rhs z)
    (singleton :
      identity.lhs.tail = [] ↔ identity.rhs.tail = [])
    (preserved :
      ∀ (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
        (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat),
        (Identity.mk
          (wordOfEndpoints initial₁ middle₁ final₁)
          (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy G →
        ∀ z,
          (initial₁ = z ∧ z ∉ middle₁ ∧ final₁ ≠ z) ↔
            (initial₂ = z ∧ z ∉ middle₂ ∧ final₂ ≠ z)) :
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
          have lhsSimple :
              S5_107.SimpleIn (Word.mk lhsHead []) lhsHead := by
            simp [S5_107.SimpleIn, Word.toList]
          have rhsSimple :
              S5_107.SimpleIn (Word.mk rhsHead []) lhsHead :=
            (simple lhsHead).mp lhsSimple
          have heads : lhsHead = rhsHead := by
            apply Decidable.byContradiction
            intro different
            simp [S5_107.SimpleIn, Word.toList,
              different, Ne.symm different] at rhsSimple
          subst rhsHead
          exact Iff.rfl
      | cons rhsSecond rhsRest =>
          have impossible :
              rhsSecond :: rhsRest = [] :=
            singleton.mp rfl
          simp at impossible
  | cons lhsSecond lhsRest =>
      cases rhsTail with
      | nil =>
          have impossible :
              lhsSecond :: lhsRest = [] :=
            singleton.mpr rfl
          simp at impossible
      | cons rhsSecond rhsRest =>
          let lhsSplit := splitMiddleFinal lhsSecond lhsRest
          let rhsSplit := splitMiddleFinal rhsSecond rhsRest
          have lhsReconstruct :
              wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2 =
                Word.mk lhsHead (lhsSecond :: lhsRest) := by
            exact
              wordOfEndpoints_splitMiddleFinal
                lhsHead lhsSecond lhsRest
          have rhsReconstruct :
              wordOfEndpoints rhsHead rhsSplit.1 rhsSplit.2 =
                Word.mk rhsHead (rhsSecond :: rhsRest) := by
            exact
              wordOfEndpoints_splitMiddleFinal
                rhsHead rhsSecond rhsRest
          have endpointValid :
              (Identity.mk
                (wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2)
                (wordOfEndpoints rhsHead rhsSplit.1 rhsSplit.2)).SatisfiedBy
                  G := by
            rw [lhsReconstruct, rhsReconstruct]
            exact valid
          have endpointPreserved :=
            preserved
              lhsHead lhsSplit.1 lhsSplit.2
              rhsHead rhsSplit.1 rhsSplit.2
              endpointValid z
          rw [← lhsReconstruct, ← rhsReconstruct]
          exact
            (simpleInitial_wordOfEndpoints_iff
              lhsHead lhsSplit.1 lhsSplit.2 z).trans <|
              endpointPreserved.trans <|
                (simpleInitial_wordOfEndpoints_iff
                  rhsHead rhsSplit.1 rhsSplit.2 z).symm

private theorem valid_simpleFinal_iff_of_callbacks
    (G : Semigroup (Fin 5))
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G)
    (simple :
      ∀ z,
        S5_107.SimpleIn identity.lhs z ↔
          S5_107.SimpleIn identity.rhs z)
    (singleton :
      identity.lhs.tail = [] ↔ identity.rhs.tail = [])
    (preserved :
      ∀ (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
        (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat),
        (Identity.mk
          (wordOfEndpoints initial₁ middle₁ final₁)
          (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy G →
        ∀ z,
          (final₁ = z ∧ z ∉ initial₁ :: middle₁) ↔
            (final₂ = z ∧ z ∉ initial₂ :: middle₂)) :
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
          have lhsSimple :
              S5_107.SimpleIn (Word.mk lhsHead []) lhsHead := by
            simp [S5_107.SimpleIn, Word.toList]
          have rhsSimple :
              S5_107.SimpleIn (Word.mk rhsHead []) lhsHead :=
            (simple lhsHead).mp lhsSimple
          have heads : lhsHead = rhsHead := by
            apply Decidable.byContradiction
            intro different
            simp [S5_107.SimpleIn, Word.toList,
              different, Ne.symm different] at rhsSimple
          subst rhsHead
          exact Iff.rfl
      | cons rhsSecond rhsRest =>
          have impossible :
              rhsSecond :: rhsRest = [] :=
            singleton.mp rfl
          simp at impossible
  | cons lhsSecond lhsRest =>
      cases rhsTail with
      | nil =>
          have impossible :
              lhsSecond :: lhsRest = [] :=
            singleton.mpr rfl
          simp at impossible
      | cons rhsSecond rhsRest =>
          let lhsSplit := splitMiddleFinal lhsSecond lhsRest
          let rhsSplit := splitMiddleFinal rhsSecond rhsRest
          have lhsReconstruct :
              wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2 =
                Word.mk lhsHead (lhsSecond :: lhsRest) := by
            exact
              wordOfEndpoints_splitMiddleFinal
                lhsHead lhsSecond lhsRest
          have rhsReconstruct :
              wordOfEndpoints rhsHead rhsSplit.1 rhsSplit.2 =
                Word.mk rhsHead (rhsSecond :: rhsRest) := by
            exact
              wordOfEndpoints_splitMiddleFinal
                rhsHead rhsSecond rhsRest
          have endpointValid :
              (Identity.mk
                (wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2)
                (wordOfEndpoints rhsHead rhsSplit.1 rhsSplit.2)).SatisfiedBy
                  G := by
            rw [lhsReconstruct, rhsReconstruct]
            exact valid
          have endpointPreserved :=
            preserved
              lhsHead lhsSplit.1 lhsSplit.2
              rhsHead rhsSplit.1 rhsSplit.2
              endpointValid z
          rw [← lhsReconstruct, ← rhsReconstruct]
          exact
            (simpleFinal_wordOfEndpoints_iff
              lhsHead lhsSplit.1 lhsSplit.2 z).trans <|
              endpointPreserved.trans <|
                (simpleFinal_wordOfEndpoints_iff
                  rhsHead rhsSplit.1 rhsSplit.2 z).symm

private theorem two_le_count_of_self_mem_adjacentPairsFrom
    (letter previous : Nat) :
    ∀ rest : List Nat,
      (letter, letter) ∈ Word.adjacentPairsFrom previous rest →
        2 ≤ (previous :: rest).count letter
  | [], member => by
      simp [Word.adjacentPairsFrom] at member
  | next :: rest, member => by
      simp only [Word.adjacentPairsFrom, List.mem_cons,
        Prod.mk.injEq] at member
      rcases member with endpoints | later
      · rcases endpoints with ⟨previousEq, nextEq⟩
        subst previous
        subst next
        simp
      · have lower :=
          two_le_count_of_self_mem_adjacentPairsFrom
            letter next rest later
        by_cases previousEq : previous = letter
        · subst previous
          rw [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne previousEq]
          exact lower

private theorem simpleAdjacent_ne
    {word : Word Nat} {source target : Nat}
    (adjacent : S5_107.SimpleAdjacent word source target) :
    source ≠ target := by
  intro equal
  subst target
  rcases adjacent with ⟨sourceSimple, _, edge⟩
  cases word with
  | mk head tail =>
      change (head :: tail).count source = 1 at sourceSimple
      change
        (source, source) ∈ Word.adjacentPairsFrom head tail at edge
      have repeated :=
        two_le_count_of_self_mem_adjacentPairsFrom
          source head tail edge
      omega

private theorem valid_sameSimpleAdjacencySignature_of_callbacks
    (G : Semigroup (Fin 5))
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G)
    (counts :
      ∀ z,
        min (identity.lhs.toList.count z) 2 =
          min (identity.rhs.toList.count z) 2)
    (simpleEndpointsValid :
      identity.SatisfiedBy simpleEndpointsFour.semigroup)
    (initialPreserved :
      ∀ (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
        (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat),
        (Identity.mk
          (wordOfEndpoints initial₁ middle₁ final₁)
          (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy G →
        ∀ z,
          (initial₁ = z ∧ z ∉ middle₁ ∧ final₁ ≠ z) ↔
            (initial₂ = z ∧ z ∉ middle₂ ∧ final₂ ≠ z))
    (finalPreserved :
      ∀ (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
        (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat),
        (Identity.mk
          (wordOfEndpoints initial₁ middle₁ final₁)
          (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy G →
        ∀ z,
          (final₁ = z ∧ z ∉ initial₁ :: middle₁) ↔
            (final₂ = z ∧ z ∉ initial₂ :: middle₂))
    (adjacencyPreserved :
      ∀ (e : Identity Nat),
        e.SatisfiedBy G →
        ∀ source target,
          source ≠ target →
          e.lhs.toList.count source = 1 →
          e.lhs.toList.count target = 1 →
          e.rhs.toList.count source = 1 →
          e.rhs.toList.count target = 1 →
          ((source, target) ∈ e.lhs.adjacentPairs ↔
            (source, target) ∈ e.rhs.adjacentPairs)) :
    S5_107.SameSimpleAdjacencySignature
      identity.lhs identity.rhs := by
  have capped :
      ∀ z,
        S5_107.cappedMultiplicity identity.lhs z =
          S5_107.cappedMultiplicity identity.rhs z :=
    cappedMultiplicity_eq_of_min_count_eq identity counts
  have simple :
      ∀ z,
        S5_107.SimpleIn identity.lhs z ↔
          S5_107.SimpleIn identity.rhs z :=
    simpleIn_iff_of_cappedMultiplicity_eq identity capped
  have singleton :
      identity.lhs.tail = [] ↔ identity.rhs.tail = [] :=
    singleton_iff_of_simpleEndpoints_valid
      identity simpleEndpointsValid
  refine
    { capped := capped
      initial :=
        valid_simpleInitial_iff_of_callbacks
          G identity valid simple singleton initialPreserved
      final :=
        valid_simpleFinal_iff_of_callbacks
          G identity valid simple singleton finalPreserved
      adjacent := ?_ }
  intro source target
  constructor
  · intro lhsAdjacent
    have different : source ≠ target :=
      simpleAdjacent_ne lhsAdjacent
    rcases lhsAdjacent with
      ⟨lhsSourceSimple, lhsTargetSimple, lhsEdge⟩
    have rhsSourceSimple :=
      (simple source).mp lhsSourceSimple
    have rhsTargetSimple :=
      (simple target).mp lhsTargetSimple
    have lhsSourceCount :
        identity.lhs.toList.count source = 1 := by
      simpa [S5_107.SimpleIn] using lhsSourceSimple
    have lhsTargetCount :
        identity.lhs.toList.count target = 1 := by
      simpa [S5_107.SimpleIn] using lhsTargetSimple
    have rhsSourceCount :
        identity.rhs.toList.count source = 1 := by
      simpa [S5_107.SimpleIn] using rhsSourceSimple
    have rhsTargetCount :
        identity.rhs.toList.count target = 1 := by
      simpa [S5_107.SimpleIn] using rhsTargetSimple
    exact
      ⟨rhsSourceSimple, rhsTargetSimple,
        (adjacencyPreserved identity valid source target different
          lhsSourceCount lhsTargetCount
          rhsSourceCount rhsTargetCount).mp lhsEdge⟩
  · intro rhsAdjacent
    have different : source ≠ target :=
      simpleAdjacent_ne rhsAdjacent
    rcases rhsAdjacent with
      ⟨rhsSourceSimple, rhsTargetSimple, rhsEdge⟩
    have lhsSourceSimple :=
      (simple source).mpr rhsSourceSimple
    have lhsTargetSimple :=
      (simple target).mpr rhsTargetSimple
    have lhsSourceCount :
        identity.lhs.toList.count source = 1 := by
      simpa [S5_107.SimpleIn] using lhsSourceSimple
    have lhsTargetCount :
        identity.lhs.toList.count target = 1 := by
      simpa [S5_107.SimpleIn] using lhsTargetSimple
    have rhsSourceCount :
        identity.rhs.toList.count source = 1 := by
      simpa [S5_107.SimpleIn] using rhsSourceSimple
    have rhsTargetCount :
        identity.rhs.toList.count target = 1 := by
      simpa [S5_107.SimpleIn] using rhsTargetSimple
    exact
      ⟨lhsSourceSimple, lhsTargetSimple,
        (adjacencyPreserved identity valid source target different
          lhsSourceCount lhsTargetCount
          rhsSourceCount rhsTargetCount).mpr rhsEdge⟩

namespace S5_107

/-- Every identity valid in the catalogue root `S5_107` preserves the full
capped-multiplicity, simple-endpoint, and directed-simple-adjacency
signature. -/
theorem valid_sameSimpleAdjacencySignature
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_107.table.semigroup) :
    SameSimpleAdjacencySignature e.lhs e.rhs :=
  valid_sameSimpleAdjacencySignature_of_callbacks
    Generated.Catalogue.S5_107.table.semigroup e valid
    (S5_107Factors.S5_107.valid_capped_count_eq e valid)
    (S5_107Factors.S5_107.valid_simpleEndpoints e valid)
    S5_107Factors.S5_107.valid_simpleInitial
    S5_107Factors.S5_107.valid_simpleFinal
    (fun identity identityValid source target different
        lhsSourceSimple lhsTargetSimple
        rhsSourceSimple rhsTargetSimple =>
      S5_107AdjacencySemantics.S5_107.valid_directedSimpleAdjacency_iff
        identity identityValid source target different
        lhsSourceSimple lhsTargetSimple
        rhsSourceSimple rhsTargetSimple)

end S5_107

namespace S5_108

/-- Every identity valid in the catalogue root `S5_108` preserves the full
simple-adjacency signature. -/
theorem valid_sameSimpleAdjacencySignature
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_108.table.semigroup) :
    S5_107.SameSimpleAdjacencySignature e.lhs e.rhs :=
  valid_sameSimpleAdjacencySignature_of_callbacks
    Generated.Catalogue.S5_108.table.semigroup e valid
    (S5_107Factors.S5_108.valid_capped_count_eq e valid)
    (S5_107Factors.S5_108.valid_simpleEndpoints e valid)
    S5_107Factors.S5_108.valid_simpleInitial
    S5_107Factors.S5_108.valid_simpleFinal
    (fun identity identityValid source target different
        lhsSourceSimple lhsTargetSimple
        rhsSourceSimple rhsTargetSimple =>
      S5_107AdjacencySemantics.S5_108.valid_directedSimpleAdjacency_iff
        identity identityValid source target different
        lhsSourceSimple lhsTargetSimple
        rhsSourceSimple rhsTargetSimple)

end S5_108

namespace S5_109

/-- Every identity valid in the catalogue root `S5_109` preserves the full
simple-adjacency signature. -/
theorem valid_sameSimpleAdjacencySignature
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_109.table.semigroup) :
    S5_107.SameSimpleAdjacencySignature e.lhs e.rhs :=
  valid_sameSimpleAdjacencySignature_of_callbacks
    Generated.Catalogue.S5_109.table.semigroup e valid
    (S5_107Factors.S5_109.valid_capped_count_eq e valid)
    (S5_107Factors.S5_109.valid_simpleEndpoints e valid)
    S5_107Factors.S5_109.valid_simpleInitial
    S5_107Factors.S5_109.valid_simpleFinal
    (fun identity identityValid source target different
        lhsSourceSimple lhsTargetSimple
        rhsSourceSimple rhsTargetSimple =>
      S5_107AdjacencySemantics.S5_109.valid_directedSimpleAdjacency_iff
        identity identityValid source target different
        lhsSourceSimple lhsTargetSimple
        rhsSourceSimple rhsTargetSimple)

end S5_109

end SemigroupBasis.CoRoots
