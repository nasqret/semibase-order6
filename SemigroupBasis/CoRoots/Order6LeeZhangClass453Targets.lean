import SemigroupBasis.CoRoots.Order6LeeZhangClass453Completeness
import SemigroupBasis.CoRoots.S5_107SignatureSemantics
import SemigroupBasis.CoRoots.S5_348Invariant
import SemigroupBasis.CoRoots.S5_381Invariant
import SemigroupBasis.Transfer

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

namespace SemigroupBasis.CoRoots.Order6LeeZhangClass453

open SemigroupBasis
open SemigroupBasis.Examples

private def select6 (index : Fin 6)
    (v0 v1 v2 v3 v4 v5 : Fin 6) : Fin 6 :=
  if index = 0 then v0
  else if index = 1 then v1
  else if index = 2 then v2
  else if index = 3 then v3
  else if index = 4 then v4
  else v5

private def map5
    (v0 v1 v2 v3 v4 : Fin 6) (value : Fin 5) : Fin 6 :=
  if value = 0 then v0
  else if value = 1 then v1
  else if value = 2 then v2
  else if value = 3 then v3
  else v4

private def reverseTable (source : FiniteTable) : FiniteTable where
  order := source.order
  mul := fun left right => source.mul right left
  assoc := by
    intro left middle right
    exact (source.assoc right middle left).symm

@[simp]
private theorem reverseTable_semigroup (source : FiniteTable) :
    (reverseTable source).semigroup = source.semigroup.opposite :=
  rfl

private def rowsOneBased (source : FiniteTable) : List (List Nat) :=
  List.ofFn fun left : Fin source.order =>
    List.ofFn fun right : Fin source.order =>
      (source.mul left right).val + 1

/-! ## Reversal of the simple-adjacency signature -/

private theorem adjacentPairs_reverse_iff
    (word : Word Nat) (source target : Nat) :
    (source, target) ∈ word.reverse.adjacentPairs ↔
      (target, source) ∈ word.adjacentPairs := by
  constructor
  · intro member
    obtain ⟨before, after, shape⟩ :=
      (S5_107.mem_adjacentPairs_iff_exists_split
        source target word.reverse).mp member
    apply (S5_107.mem_adjacentPairs_iff_exists_split
      target source word).mpr
    refine ⟨after.reverse, before.reverse, ?_⟩
    have reversed := congrArg List.reverse shape
    simpa [Word.toList_reverse, List.reverse_append] using reversed
  · intro member
    obtain ⟨before, after, shape⟩ :=
      (S5_107.mem_adjacentPairs_iff_exists_split
        target source word).mp member
    apply (S5_107.mem_adjacentPairs_iff_exists_split
      source target word.reverse).mpr
    refine ⟨after.reverse, before.reverse, ?_⟩
    rw [Word.toList_reverse, shape]
    simp [List.reverse_append]

private theorem reverseAux_head_eq_getLastD (head : Nat) :
    forall tail : List Nat,
      (Word.reverseAux head tail).head = tail.getLastD head
  | [] => rfl
  | next :: rest => by
      change
        (Word.reverseAux next rest).head =
          (next :: rest).getLastD head
      rw [List.getLastD_cons]
      exact reverseAux_head_eq_getLastD next rest

private theorem reverse_head_eq_final (word : Word Nat) :
    word.reverse.head = word.final := by
  cases word with
  | mk head tail => exact reverseAux_head_eq_getLastD head tail

private theorem reverse_final_eq_head (word : Word Nat) :
    word.reverse.final = word.head := by
  have reversed := reverse_head_eq_final word.reverse
  simpa using reversed.symm

private theorem simpleInitial_reverse_iff_simpleFinal
    (word : Word Nat) (letter : Nat) :
    S5_107.SimpleInitial word.reverse letter ↔
      S5_107.SimpleFinal word letter := by
  simp [S5_107.SimpleInitial, S5_107.SimpleFinal,
    S5_107.SimpleIn, reverse_head_eq_final]

private theorem simpleFinal_reverse_iff_simpleInitial
    (word : Word Nat) (letter : Nat) :
    S5_107.SimpleFinal word.reverse letter ↔
      S5_107.SimpleInitial word letter := by
  simp [S5_107.SimpleInitial, S5_107.SimpleFinal,
    S5_107.SimpleIn, reverse_final_eq_head]

private theorem simpleAdjacent_reverse_iff
    (word : Word Nat) (source target : Nat) :
    S5_107.SimpleAdjacent word.reverse source target ↔
      S5_107.SimpleAdjacent word target source := by
  unfold S5_107.SimpleAdjacent S5_107.SimpleIn
  rw [adjacentPairs_reverse_iff]
  simp only [Word.toList_reverse, List.count_reverse]
  constructor
  · rintro ⟨sourceSimple, targetSimple, edge⟩
    exact ⟨targetSimple, sourceSimple, edge⟩
  · rintro ⟨targetSimple, sourceSimple, edge⟩
    exact ⟨sourceSimple, targetSimple, edge⟩

/-- The simple-adjacency signature is self-dual after reversing both words.
This is the semantic bridge needed for the non-self-dual `S5_108` source. -/
theorem sameSimpleAdjacencySignature_of_reversed
    {left right : Word Nat}
    (same :
      S5_107.SameSimpleAdjacencySignature
        left.reverse right.reverse) :
    S5_107.SameSimpleAdjacencySignature left right := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro letter
    simpa [S5_107.cappedMultiplicity] using same.capped letter
  · intro letter
    simpa only [simpleFinal_reverse_iff_simpleInitial] using
      same.final letter
  · intro letter
    simpa only [simpleInitial_reverse_iff_simpleFinal] using
      same.initial letter
  · intro source target
    simpa only [simpleAdjacent_reverse_iff] using
      same.adjacent target source

private theorem firstGapOfS5_381Opposite
    {S : Type} {G : Semigroup S}
    (embedding :
      Embedding
        Generated.Catalogue.S5_381.table.semigroup.opposite G)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G) :
    SimpleSequenceFirstGap.SameSignature
      identity.lhs identity.rhs := by
  have oppositeValid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_381.table.semigroup.opposite :=
    embedding.pullback_identity identity valid
  have reversedValid :
      identity.reversed.SatisfiedBy
        Generated.Catalogue.S5_381.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed identity
      Generated.Catalogue.S5_381.table.semigroup).mp oppositeValid
  have dual :=
    S5_381FamilyInvariant.S5_381.valid_sameSignature
      identity.reversed reversedValid
  apply SimpleSequenceFirstGap.SameSignature.ofDual
  simpa [Identity.reversed] using dual

private theorem adjacencyOfS5_108Opposite
    {S : Type} {G : Semigroup S}
    (embedding :
      Embedding
        Generated.Catalogue.S5_108.table.semigroup.opposite G)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G) :
    S5_107.SameSimpleAdjacencySignature
      identity.lhs identity.rhs := by
  have oppositeValid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_108.table.semigroup.opposite :=
    embedding.pullback_identity identity valid
  have reversedValid :
      identity.reversed.SatisfiedBy
        Generated.Catalogue.S5_108.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed identity
      Generated.Catalogue.S5_108.table.semigroup).mp oppositeValid
  have reversedSignature :=
    SemigroupBasis.CoRoots.S5_108.valid_sameSimpleAdjacencySignature
      identity.reversed reversedValid
  apply sameSimpleAdjacencySignature_of_reversed
  simpa [Identity.reversed] using reversedSignature

/-! ## `S6_3806` -/

namespace S6_3806

/-- Authenticated packet orientation. -/
def packetMul (left right : Fin 6) : Fin 6 :=
  select6 left
    (select6 right 0 0 0 0 0 0)
    (select6 right 0 0 0 0 1 1)
    (select6 right 0 0 0 1 0 0)
    (select6 right 0 0 0 0 3 3)
    (select6 right 0 0 0 0 4 4)
    (select6 right 0 1 2 0 4 5)

def packetTable : FiniteTable where
  order := 6
  mul := packetMul
  assoc := by decide

def packetTableRowsOneBased : List (List Nat) :=
  rowsOneBased packetTable

theorem packetTable_certificate :
    packetTableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2, 2],
       [1, 1, 1, 2, 1, 1], [1, 1, 1, 1, 4, 4],
       [1, 1, 1, 1, 5, 5], [1, 2, 3, 1, 5, 6]] := by
  decide

/-- Exact direct Smallsemi orientation. -/
def table : FiniteTable := reverseTable packetTable

theorem table_mul_eq_packet_opposite (left right : Fin 6) :
    table.mul left right = packetTable.mul right left := rfl

def tableRowsOneBased : List (List Nat) := rowsOneBased table

theorem table_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 2],
       [1, 1, 1, 1, 1, 3], [1, 1, 2, 1, 1, 1],
       [1, 2, 1, 4, 5, 5], [1, 2, 1, 4, 5, 6]] := by
  decide

def firstGapEmbedding :
    Embedding Generated.Catalogue.S5_348.table.semigroup
      packetTable.semigroup where
  toFun := map5 0 2 1 4 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def adjacencyEmbedding :
    Embedding Generated.Catalogue.S5_107.table.semigroup
      packetTable.semigroup where
  toFun := map5 0 1 3 2 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem packetModels : Models packetTable.semigroup basis :=
  modelsOfFiniteChecks packetTable (by decide)

private theorem validFirstGap
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy packetTable.semigroup) :
    SimpleSequenceFirstGap.SameSignature
      identity.lhs identity.rhs :=
  S5_348FamilyInvariant.S5_348.valid_sameSignature identity
    (firstGapEmbedding.pullback_identity identity valid)

private theorem validAdjacency
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy packetTable.semigroup) :
    S5_107.SameSimpleAdjacencySignature
      identity.lhs identity.rhs :=
  SemigroupBasis.CoRoots.S5_107.valid_sameSimpleAdjacencySignature
    identity (adjacencyEmbedding.pullback_identity identity valid)

theorem packetBasisFor : BasisFor packetTable.semigroup basis :=
  basisCompleteOfSignatures packetTable.semigroup packetModels
    validFirstGap validAdjacency

/-- Unconditional endpoint for direct Smallsemi `S6_3806`. -/
theorem basisFor : BasisFor table.semigroup oppositeBasis := by
  change BasisFor packetTable.semigroup.opposite (reversedBasis basis)
  exact packetBasisFor.oppositeReversed

end S6_3806

/-! ## `S6_3809` -/

namespace S6_3809

def packetMul (left right : Fin 6) : Fin 6 :=
  select6 left
    (select6 right 0 0 0 0 0 0)
    (select6 right 0 0 0 0 1 1)
    (select6 right 0 0 0 1 1 1)
    (select6 right 0 0 0 0 3 3)
    (select6 right 0 0 0 0 4 4)
    (select6 right 0 1 2 0 4 5)

def packetTable : FiniteTable where
  order := 6
  mul := packetMul
  assoc := by decide

def packetTableRowsOneBased : List (List Nat) :=
  rowsOneBased packetTable

theorem packetTable_certificate :
    packetTableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2, 2],
       [1, 1, 1, 2, 2, 2], [1, 1, 1, 1, 4, 4],
       [1, 1, 1, 1, 5, 5], [1, 2, 3, 1, 5, 6]] := by
  decide

def table : FiniteTable := reverseTable packetTable

theorem table_mul_eq_packet_opposite (left right : Fin 6) :
    table.mul left right = packetTable.mul right left := rfl

def tableRowsOneBased : List (List Nat) := rowsOneBased table

theorem table_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 2],
       [1, 1, 1, 1, 1, 3], [1, 1, 2, 1, 1, 1],
       [1, 2, 2, 4, 5, 5], [1, 2, 2, 4, 5, 6]] := by
  decide

def firstGapEmbedding :
    Embedding Generated.Catalogue.S5_381.table.semigroup.opposite
      packetTable.semigroup where
  toFun := map5 0 1 2 4 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def adjacencyEmbedding :
    Embedding Generated.Catalogue.S5_108.table.semigroup.opposite
      packetTable.semigroup where
  toFun := map5 0 1 2 3 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem packetModels : Models packetTable.semigroup basis :=
  modelsOfFiniteChecks packetTable (by decide)

private theorem validFirstGap
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy packetTable.semigroup) :
    SimpleSequenceFirstGap.SameSignature
      identity.lhs identity.rhs :=
  firstGapOfS5_381Opposite firstGapEmbedding identity valid

private theorem validAdjacency
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy packetTable.semigroup) :
    S5_107.SameSimpleAdjacencySignature
      identity.lhs identity.rhs :=
  adjacencyOfS5_108Opposite adjacencyEmbedding identity valid

theorem packetBasisFor : BasisFor packetTable.semigroup basis :=
  basisCompleteOfSignatures packetTable.semigroup packetModels
    validFirstGap validAdjacency

/-- Unconditional endpoint for direct Smallsemi `S6_3809`. -/
theorem basisFor : BasisFor table.semigroup oppositeBasis := by
  change BasisFor packetTable.semigroup.opposite (reversedBasis basis)
  exact packetBasisFor.oppositeReversed

end S6_3809

/-! ## `S6_3819` -/

namespace S6_3819

def packetMul (left right : Fin 6) : Fin 6 :=
  select6 left
    (select6 right 0 0 0 0 0 0)
    (select6 right 0 0 0 0 1 1)
    (select6 right 0 0 0 1 0 0)
    (select6 right 0 0 0 0 3 3)
    (select6 right 0 0 0 0 4 4)
    (select6 right 0 1 2 1 4 5)

def packetTable : FiniteTable where
  order := 6
  mul := packetMul
  assoc := by decide

def packetTableRowsOneBased : List (List Nat) :=
  rowsOneBased packetTable

theorem packetTable_certificate :
    packetTableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2, 2],
       [1, 1, 1, 2, 1, 1], [1, 1, 1, 1, 4, 4],
       [1, 1, 1, 1, 5, 5], [1, 2, 3, 2, 5, 6]] := by
  decide

def table : FiniteTable := reverseTable packetTable

theorem table_mul_eq_packet_opposite (left right : Fin 6) :
    table.mul left right = packetTable.mul right left := rfl

def tableRowsOneBased : List (List Nat) := rowsOneBased table

theorem table_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 2],
       [1, 1, 1, 1, 1, 3], [1, 1, 2, 1, 1, 2],
       [1, 2, 1, 4, 5, 5], [1, 2, 1, 4, 5, 6]] := by
  decide

def firstGapEmbedding :
    Embedding Generated.Catalogue.S5_348.table.semigroup
      packetTable.semigroup where
  toFun := map5 0 2 1 4 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def adjacencyEmbedding :
    Embedding Generated.Catalogue.S5_108.table.semigroup
      packetTable.semigroup where
  toFun := map5 0 1 3 2 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem packetModels : Models packetTable.semigroup basis :=
  modelsOfFiniteChecks packetTable (by decide)

private theorem validFirstGap
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy packetTable.semigroup) :
    SimpleSequenceFirstGap.SameSignature
      identity.lhs identity.rhs :=
  S5_348FamilyInvariant.S5_348.valid_sameSignature identity
    (firstGapEmbedding.pullback_identity identity valid)

private theorem validAdjacency
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy packetTable.semigroup) :
    S5_107.SameSimpleAdjacencySignature
      identity.lhs identity.rhs :=
  SemigroupBasis.CoRoots.S5_108.valid_sameSimpleAdjacencySignature
    identity (adjacencyEmbedding.pullback_identity identity valid)

theorem packetBasisFor : BasisFor packetTable.semigroup basis :=
  basisCompleteOfSignatures packetTable.semigroup packetModels
    validFirstGap validAdjacency

/-- Unconditional endpoint for direct Smallsemi `S6_3819`. -/
theorem basisFor : BasisFor table.semigroup oppositeBasis := by
  change BasisFor packetTable.semigroup.opposite (reversedBasis basis)
  exact packetBasisFor.oppositeReversed

end S6_3819

/-! ## `S6_3822` -/

namespace S6_3822

def packetMul (left right : Fin 6) : Fin 6 :=
  select6 left
    (select6 right 0 0 0 0 0 0)
    (select6 right 0 0 0 0 1 1)
    (select6 right 0 0 0 1 1 1)
    (select6 right 0 0 0 0 3 3)
    (select6 right 0 0 0 0 4 4)
    (select6 right 0 1 2 1 4 5)

def packetTable : FiniteTable where
  order := 6
  mul := packetMul
  assoc := by decide

def packetTableRowsOneBased : List (List Nat) :=
  rowsOneBased packetTable

theorem packetTable_certificate :
    packetTableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2, 2],
       [1, 1, 1, 2, 2, 2], [1, 1, 1, 1, 4, 4],
       [1, 1, 1, 1, 5, 5], [1, 2, 3, 2, 5, 6]] := by
  decide

def table : FiniteTable := reverseTable packetTable

theorem table_mul_eq_packet_opposite (left right : Fin 6) :
    table.mul left right = packetTable.mul right left := rfl

def tableRowsOneBased : List (List Nat) := rowsOneBased table

theorem table_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 2],
       [1, 1, 1, 1, 1, 3], [1, 1, 2, 1, 1, 2],
       [1, 2, 2, 4, 5, 5], [1, 2, 2, 4, 5, 6]] := by
  decide

def firstGapEmbedding :
    Embedding Generated.Catalogue.S5_381.table.semigroup.opposite
      packetTable.semigroup where
  toFun := map5 0 1 2 4 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def adjacencyEmbedding :
    Embedding Generated.Catalogue.S5_109.table.semigroup
      packetTable.semigroup where
  toFun := map5 0 1 3 2 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem packetModels : Models packetTable.semigroup basis :=
  modelsOfFiniteChecks packetTable (by decide)

private theorem validFirstGap
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy packetTable.semigroup) :
    SimpleSequenceFirstGap.SameSignature
      identity.lhs identity.rhs :=
  firstGapOfS5_381Opposite firstGapEmbedding identity valid

private theorem validAdjacency
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy packetTable.semigroup) :
    S5_107.SameSimpleAdjacencySignature
      identity.lhs identity.rhs :=
  SemigroupBasis.CoRoots.S5_109.valid_sameSimpleAdjacencySignature
    identity (adjacencyEmbedding.pullback_identity identity valid)

theorem packetBasisFor : BasisFor packetTable.semigroup basis :=
  basisCompleteOfSignatures packetTable.semigroup packetModels
    validFirstGap validAdjacency

/-- Unconditional endpoint for direct Smallsemi `S6_3822`. -/
theorem basisFor : BasisFor table.semigroup oppositeBasis := by
  change BasisFor packetTable.semigroup.opposite (reversedBasis basis)
  exact packetBasisFor.oppositeReversed

end S6_3822

end SemigroupBasis.CoRoots.Order6LeeZhangClass453
