import SemigroupBasis.CoRoots.Order6SporadicSection27F9G1Canonical

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

/-! ## Witness-driven repairs for conditions (II) and (III) -/

/-- A literal condition-(II) witness, equipped with the rank decrease used by
the terminating normalizer. -/
structure CrossingWitness (markers source : List Nat) where
  earlier : Nat
  later : Nat
  pre : List Nat
  gapOne : List Nat
  gapTwo : List Nat
  gapThree : List Nat
  post : List Nat
  source_eq :
    source =
      pre ++ [earlier] ++ gapOne ++ [later] ++ gapTwo ++
        [earlier] ++ gapThree ++ [later] ++ post
  order : EarlierIn markers earlier later
  rank_lt : markers.idxOf earlier < markers.idxOf later

namespace CrossingWitness

def target {markers source : List Nat}
    (witness : CrossingWitness markers source) : List Nat :=
  witness.pre ++ [witness.earlier] ++ witness.gapOne ++
    [witness.later] ++ witness.gapTwo ++ [witness.earlier] ++
      witness.gapThree ++ [witness.earlier] ++ witness.post

theorem source_hasCrossing {markers source : List Nat}
    (witness : CrossingWitness markers source) :
    Has27Crossing markers source := by
  exact ⟨witness.earlier, witness.later, witness.pre,
    witness.gapOne, witness.gapTwo, witness.gapThree,
    witness.post, witness.order, witness.source_eq⟩

theorem derives {markers source : List Nat}
    (witness : CrossingWitness markers source) :
    ListDerives source witness.target := by
  generalize targetEq : witness.target = repaired
  rw [witness.source_eq]
  rw [← targetEq]
  simpa [target] using
    listDerivesDDisplayed witness.earlier witness.later
      witness.pre witness.gapOne witness.gapTwo
      witness.gapThree witness.post

end CrossingWitness

/-- A literal condition-(III) witness.  The middle occurrence pair is
adjacent in `source_eq`; this is intentionally not a nested-arc surrogate. -/
structure AdjacentWitness (markers source : List Nat) where
  earlier : Nat
  later : Nat
  pre : List Nat
  gapOne : List Nat
  gapTwo : List Nat
  post : List Nat
  source_eq :
    source =
      pre ++ [earlier] ++ gapOne ++ [earlier, later] ++
        gapTwo ++ [later] ++ post
  order : EarlierIn markers earlier later
  rank_lt : markers.idxOf earlier < markers.idxOf later

namespace AdjacentWitness

def target {markers source : List Nat}
    (witness : AdjacentWitness markers source) : List Nat :=
  witness.pre ++ [witness.earlier] ++ witness.gapOne ++
    [witness.earlier, witness.later] ++ witness.gapTwo ++
      [witness.earlier] ++ witness.post

theorem source_hasAdjacentPair {markers source : List Nat}
    (witness : AdjacentWitness markers source) :
    Has27AdjacentPair markers source := by
  exact ⟨witness.earlier, witness.later, witness.pre,
    witness.gapOne, witness.gapTwo, witness.post,
    witness.order, witness.source_eq⟩

theorem derives {markers source : List Nat}
    (witness : AdjacentWitness markers source) :
    ListDerives source witness.target := by
  generalize targetEq : witness.target = repaired
  rw [witness.source_eq]
  rw [← targetEq]
  simpa [target] using
    listDerivesEDisplayed witness.earlier witness.later
      witness.pre witness.gapOne witness.gapTwo witness.post

end AdjacentWitness

/-! ## A common termination measure -/

/-- Sum of first-occurrence ranks.  A D/E repair replaces only its final
later-ranked letter, so this measure strictly decreases. -/
def betaWeight (markers letters : List Nat) : Nat :=
  (letters.map fun letter => markers.idxOf letter).sum

private theorem listSum_append :
    ∀ left right : List Nat,
      (left ++ right).sum = left.sum + right.sum
  | [], right => by simp
  | head :: tail, right => by
      rw [List.cons_append, List.sum_cons, listSum_append tail right,
        List.sum_cons]
      omega

theorem betaWeight_replace_lt
    (markers prefixList suffix : List Nat) (earlier later : Nat)
    (rank_lt : markers.idxOf earlier < markers.idxOf later) :
    betaWeight markers (prefixList ++ [earlier] ++ suffix) <
      betaWeight markers (prefixList ++ [later] ++ suffix) := by
  simp only [betaWeight, List.map_append, List.map_cons, List.map_nil,
    listSum_append, List.sum_cons, List.sum_nil]
  omega

theorem CrossingWitness.weight_lt {markers source : List Nat}
    (witness : CrossingWitness markers source) :
    betaWeight markers witness.target < betaWeight markers source := by
  generalize targetEq : witness.target = repaired
  rw [witness.source_eq]
  rw [← targetEq]
  simpa [CrossingWitness.target, List.append_assoc] using
    betaWeight_replace_lt markers
      (witness.pre ++ [witness.earlier] ++ witness.gapOne ++
        [witness.later] ++ witness.gapTwo ++ [witness.earlier] ++
          witness.gapThree)
      witness.post witness.earlier witness.later witness.rank_lt

theorem AdjacentWitness.weight_lt {markers source : List Nat}
    (witness : AdjacentWitness markers source) :
    betaWeight markers witness.target < betaWeight markers source := by
  generalize targetEq : witness.target = repaired
  rw [witness.source_eq]
  rw [← targetEq]
  simpa [AdjacentWitness.target, List.append_assoc] using
    betaWeight_replace_lt markers
      (witness.pre ++ [witness.earlier] ++ witness.gapOne ++
        [witness.earlier, witness.later] ++ witness.gapTwo)
      witness.post witness.earlier witness.later witness.rank_lt

end SemigroupBasis.CoRoots.Order6SporadicSection27
