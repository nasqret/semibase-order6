import SemigroupBasis.CoRoots.Order6LeeLiCondition9
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

namespace SemigroupBasis.CoRoots.Order6LeeLiCondition9Roots

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6LeeLiCondition9

/-!
Exact catalogue bindings for the ten Condition 9 roots.  Every public `table`
below has the stored six-element multiplication.  The transposed tables are
kept as explicit proof witnesses where the normal-form argument needs the
opposite orientation.  The two basis lists are actual Lean terms; hashes and
Smallsemi indices are inventory metadata only.
-/

private def select6 (index : Fin 6)
    (v0 v1 v2 v3 v4 v5 : Fin 6) : Fin 6 :=
  if index = 0 then v0
  else if index = 1 then v1
  else if index = 2 then v2
  else if index = 3 then v3
  else if index = 4 then v4
  else v5

private def map3 (v0 v1 v2 : Fin 6) (value : Fin 3) : Fin 6 :=
  if value = 0 then v0 else if value = 1 then v1 else v2

private def map4 (v0 v1 v2 v3 : Fin 6) (value : Fin 4) : Fin 6 :=
  if value = 0 then v0
  else if value = 1 then v1
  else if value = 2 then v2
  else v3

private def reverseTable (T : FiniteTable) : FiniteTable where
  order := T.order
  mul := fun left right => T.mul right left
  assoc := by
    intro left middle right
    exact (T.assoc right middle left).symm

@[simp]
private theorem reverseTable_semigroup (T : FiniteTable) :
    (reverseTable T).semigroup = T.semigroup.opposite := rfl

/-! ## Direct-basis roots -/

namespace S6_9937

def mul (a b : Fin 6) : Fin 6 :=
  select6 a
    (select6 b 0 0 0 0 0 0)
    (select6 b 0 0 0 0 1 1)
    (select6 b 2 2 2 2 2 2)
    (select6 b 2 2 2 2 3 3)
    (select6 b 0 1 2 3 4 5)
    (select6 b 2 3 0 1 5 4)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- Bytewise multiplication binding to the original source table. -/
theorem mul_eq_source (a b : Fin 6) :
    table.mul a b = leeLiCondition9Table.mul a b := by
  change mul a b = leeLiCondition9Mul a b
  revert a b
  decide

private def toSourceEmbedding :
    Embedding table.semigroup.opposite leeLiCondition9Semigroup where
  toFun := id
  map_mul := by
    intro left right
    exact mul_eq_source right left
  injective := by
    exact Function.injective_id

private def fromSourceEmbedding :
    Embedding leeLiCondition9Semigroup table.semigroup.opposite where
  toFun := id
  map_mul := by
    intro left right
    exact (mul_eq_source right left).symm
  injective := by
    exact Function.injective_id

private theorem models :
    Models table.semigroup.opposite leeLiCondition9Basis := by
  intro identity member
  exact toSourceEmbedding.pullback_identity identity
    (leeLiCondition9Models identity member)

theorem representative_basis :
    BasisFor table.semigroup.opposite leeLiCondition9Basis :=
  leeLiCondition9BasisFor.inheritAlongEmbedding
    fromSourceEmbedding models

end S6_9937

namespace S6_10837

def mul (a b : Fin 6) : Fin 6 :=
  select6 a
    (select6 b 0 0 0 0 0 0)
    (select6 b 0 0 0 0 0 1)
    (select6 b 0 0 2 3 4 0)
    (select6 b 4 4 3 2 0 4)
    (select6 b 4 4 4 4 4 4)
    (select6 b 0 1 0 0 0 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

private theorem models :
    Models table.semigroup leeLiCondition9ReversedBasis :=
  modelsLeeLiCondition9ReversedBasisOfCheck table (by decide)

private def affineEmbedding :
    Embedding affineParityFour.semigroup.opposite
      table.semigroup where
  toFun := map4 2 3 0 4
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def cappedEmbedding :
    Embedding commutativeExponentThree.semigroup
      table.semigroup where
  toFun := map3 0 1 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def semanticWitness : SemanticWitness table.semigroup where
  models := models
  affineConsequence := fun identity valid =>
    affineEmbedding.pullback_identity identity valid
  cappedConsequence := fun identity valid =>
    cappedEmbedding.pullback_identity identity valid

private theorem stored_reversed_basis :
    BasisFor table.semigroup leeLiCondition9ReversedBasis :=
  reversedBasisForOfSemanticWitness semanticWitness

theorem representative_basis :
    BasisFor table.semigroup.opposite leeLiCondition9Basis := by
  simpa only [leeLiCondition9Basis] using
    stored_reversed_basis.oppositeReversed

end S6_10837

namespace S6_10842

def mul (a b : Fin 6) : Fin 6 :=
  select6 a
    (select6 b 0 0 0 0 0 0)
    (select6 b 0 0 0 0 0 1)
    (select6 b 0 0 2 3 4 2)
    (select6 b 4 4 3 2 0 3)
    (select6 b 4 4 4 4 4 4)
    (select6 b 0 1 2 3 4 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

private theorem models :
    Models table.semigroup leeLiCondition9ReversedBasis :=
  modelsLeeLiCondition9ReversedBasisOfCheck table (by decide)

private def affineEmbedding :
    Embedding affineParityFour.semigroup.opposite
      table.semigroup where
  toFun := map4 2 3 0 4
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def cappedEmbedding :
    Embedding commutativeExponentThree.semigroup
      table.semigroup where
  toFun := map3 0 1 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def semanticWitness : SemanticWitness table.semigroup where
  models := models
  affineConsequence := fun identity valid =>
    affineEmbedding.pullback_identity identity valid
  cappedConsequence := fun identity valid =>
    cappedEmbedding.pullback_identity identity valid

private theorem stored_reversed_basis :
    BasisFor table.semigroup leeLiCondition9ReversedBasis :=
  reversedBasisForOfSemanticWitness semanticWitness

theorem representative_basis :
    BasisFor table.semigroup.opposite leeLiCondition9Basis := by
  simpa only [leeLiCondition9Basis] using
    stored_reversed_basis.oppositeReversed

end S6_10842

namespace S6_11396

def mul (a b : Fin 6) : Fin 6 :=
  select6 a
    (select6 b 0 0 0 0 0 0)
    (select6 b 0 0 1 1 0 0)
    (select6 b 0 1 2 3 4 5)
    (select6 b 0 1 3 2 5 4)
    (select6 b 4 4 4 4 4 4)
    (select6 b 5 5 5 5 5 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

private theorem models :
    Models table.semigroup leeLiCondition9ReversedBasis :=
  modelsLeeLiCondition9ReversedBasisOfCheck table (by decide)

private def affineEmbedding :
    Embedding affineParityFour.semigroup.opposite
      table.semigroup where
  toFun := map4 2 3 4 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def cappedEmbedding :
    Embedding commutativeExponentThree.semigroup
      table.semigroup where
  toFun := map3 0 1 2
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def semanticWitness : SemanticWitness table.semigroup where
  models := models
  affineConsequence := fun identity valid =>
    affineEmbedding.pullback_identity identity valid
  cappedConsequence := fun identity valid =>
    cappedEmbedding.pullback_identity identity valid

private theorem stored_reversed_basis :
    BasisFor table.semigroup leeLiCondition9ReversedBasis :=
  reversedBasisForOfSemanticWitness semanticWitness

theorem representative_basis :
    BasisFor table.semigroup.opposite leeLiCondition9Basis := by
  simpa only [leeLiCondition9Basis] using
    stored_reversed_basis.oppositeReversed

end S6_11396

namespace S6_11459

def mul (a b : Fin 6) : Fin 6 :=
  select6 a
    (select6 b 0 0 0 0 0 0)
    (select6 b 0 0 1 1 0 1)
    (select6 b 0 0 2 3 4 2)
    (select6 b 4 4 3 2 0 3)
    (select6 b 4 4 4 4 4 4)
    (select6 b 0 1 2 3 4 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

private theorem models :
    Models table.semigroup leeLiCondition9ReversedBasis :=
  modelsLeeLiCondition9ReversedBasisOfCheck table (by decide)

private def affineEmbedding :
    Embedding affineParityFour.semigroup.opposite
      table.semigroup where
  toFun := map4 2 3 0 4
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def cappedEmbedding :
    Embedding commutativeExponentThree.semigroup
      table.semigroup where
  toFun := map3 0 1 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def semanticWitness : SemanticWitness table.semigroup where
  models := models
  affineConsequence := fun identity valid =>
    affineEmbedding.pullback_identity identity valid
  cappedConsequence := fun identity valid =>
    cappedEmbedding.pullback_identity identity valid

private theorem stored_reversed_basis :
    BasisFor table.semigroup leeLiCondition9ReversedBasis :=
  reversedBasisForOfSemanticWitness semanticWitness

theorem representative_basis :
    BasisFor table.semigroup.opposite leeLiCondition9Basis := by
  simpa only [leeLiCondition9Basis] using
    stored_reversed_basis.oppositeReversed

end S6_11459

/-! ## Reversed-basis roots -/

namespace S6_8924

def mul (a b : Fin 6) : Fin 6 :=
  select6 a
    (select6 b 0 0 2 0 4 5)
    (select6 b 0 0 2 1 4 5)
    (select6 b 2 2 0 2 4 5)
    (select6 b 0 1 2 3 4 5)
    (select6 b 4 4 5 4 4 5)
    (select6 b 5 5 4 5 4 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

private theorem models :
    Models table.semigroup.opposite leeLiCondition9ReversedBasis := by
  simpa only [reverseTable_semigroup] using
    modelsLeeLiCondition9ReversedBasisOfCheck
      (reverseTable table) (by decide)

private def affineEmbedding :
    Embedding affineParityFour.semigroup.opposite
      table.semigroup.opposite where
  toFun := map4 0 2 4 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def cappedEmbedding :
    Embedding commutativeExponentThree.semigroup
      table.semigroup.opposite where
  toFun := map3 0 1 3
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def semanticWitness : SemanticWitness table.semigroup.opposite where
  models := models
  affineConsequence := fun identity valid =>
    affineEmbedding.pullback_identity identity valid
  cappedConsequence := fun identity valid =>
    cappedEmbedding.pullback_identity identity valid

theorem representative_basis :
    BasisFor table.semigroup.opposite leeLiCondition9ReversedBasis :=
  reversedBasisForOfSemanticWitness semanticWitness

end S6_8924

namespace S6_9065

def mul (a b : Fin 6) : Fin 6 :=
  select6 a
    (select6 b 0 1 1 0 4 5)
    (select6 b 1 0 0 1 4 5)
    (select6 b 1 0 0 2 4 5)
    (select6 b 0 1 2 3 4 5)
    (select6 b 4 5 5 4 4 5)
    (select6 b 5 4 4 5 4 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

private theorem models :
    Models table.semigroup.opposite leeLiCondition9ReversedBasis := by
  simpa only [reverseTable_semigroup] using
    modelsLeeLiCondition9ReversedBasisOfCheck
      (reverseTable table) (by decide)

private def affineEmbedding :
    Embedding affineParityFour.semigroup.opposite
      table.semigroup.opposite where
  toFun := map4 0 1 4 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def cappedQuotientMap (value : Fin 6) : Fin 3 :=
  if value = 2 then 1
  else if value = 3 then 2
  else 0

private def cappedQuotientPreimage (value : Fin 3) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 2
  else 3

private def cappedQuotient :
    SplitSurjection table.semigroup.opposite
      commutativeExponentThree.semigroup where
  toFun := cappedQuotientMap
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := cappedQuotientPreimage
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

private def semanticWitness : SemanticWitness table.semigroup.opposite where
  models := models
  affineConsequence := fun identity valid =>
    affineEmbedding.pullback_identity identity valid
  cappedConsequence := fun identity valid =>
    cappedQuotient.pushforwardIdentity identity valid

theorem representative_basis :
    BasisFor table.semigroup.opposite leeLiCondition9ReversedBasis :=
  reversedBasisForOfSemanticWitness semanticWitness

end S6_9065

namespace S6_11385

def mul (a b : Fin 6) : Fin 6 :=
  select6 a
    (select6 b 0 0 0 0 0 0)
    (select6 b 0 0 1 1 0 0)
    (select6 b 0 1 2 3 4 5)
    (select6 b 0 1 3 2 4 5)
    (select6 b 0 0 4 5 4 5)
    (select6 b 0 0 5 4 4 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

private theorem models :
    Models table.semigroup.opposite leeLiCondition9ReversedBasis := by
  simpa only [reverseTable_semigroup] using
    modelsLeeLiCondition9ReversedBasisOfCheck
      (reverseTable table) (by decide)

private def affineEmbedding :
    Embedding affineParityFour.semigroup.opposite
      table.semigroup.opposite where
  toFun := map4 2 3 4 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def cappedEmbedding :
    Embedding commutativeExponentThree.semigroup
      table.semigroup.opposite where
  toFun := map3 0 1 2
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def semanticWitness : SemanticWitness table.semigroup.opposite where
  models := models
  affineConsequence := fun identity valid =>
    affineEmbedding.pullback_identity identity valid
  cappedConsequence := fun identity valid =>
    cappedEmbedding.pullback_identity identity valid

theorem representative_basis :
    BasisFor table.semigroup.opposite leeLiCondition9ReversedBasis :=
  reversedBasisForOfSemanticWitness semanticWitness

end S6_11385

namespace S6_11392

def mul (a b : Fin 6) : Fin 6 :=
  select6 a
    (select6 b 0 0 0 0 0 0)
    (select6 b 0 0 1 1 0 0)
    (select6 b 0 1 2 3 4 5)
    (select6 b 0 1 3 2 4 5)
    (select6 b 0 1 4 5 4 5)
    (select6 b 0 1 5 4 4 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

private theorem models :
    Models table.semigroup.opposite leeLiCondition9ReversedBasis := by
  simpa only [reverseTable_semigroup] using
    modelsLeeLiCondition9ReversedBasisOfCheck
      (reverseTable table) (by decide)

private def affineEmbedding :
    Embedding affineParityFour.semigroup.opposite
      table.semigroup.opposite where
  toFun := map4 2 3 4 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def cappedEmbedding :
    Embedding commutativeExponentThree.semigroup
      table.semigroup.opposite where
  toFun := map3 0 1 2
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def semanticWitness : SemanticWitness table.semigroup.opposite where
  models := models
  affineConsequence := fun identity valid =>
    affineEmbedding.pullback_identity identity valid
  cappedConsequence := fun identity valid =>
    cappedEmbedding.pullback_identity identity valid

theorem representative_basis :
    BasisFor table.semigroup.opposite leeLiCondition9ReversedBasis :=
  reversedBasisForOfSemanticWitness semanticWitness

end S6_11392

namespace S6_11598

def mul (a b : Fin 6) : Fin 6 :=
  select6 a
    (select6 b 0 0 0 0 0 0)
    (select6 b 0 0 1 1 1 1)
    (select6 b 0 1 2 3 4 5)
    (select6 b 0 1 3 2 4 5)
    (select6 b 0 1 4 5 4 5)
    (select6 b 0 1 5 4 4 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

private theorem models :
    Models table.semigroup.opposite leeLiCondition9ReversedBasis := by
  simpa only [reverseTable_semigroup] using
    modelsLeeLiCondition9ReversedBasisOfCheck
      (reverseTable table) (by decide)

private def affineEmbedding :
    Embedding affineParityFour.semigroup.opposite
      table.semigroup.opposite where
  toFun := map4 2 3 4 5
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def cappedEmbedding :
    Embedding commutativeExponentThree.semigroup
      table.semigroup.opposite where
  toFun := map3 0 1 2
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private def semanticWitness : SemanticWitness table.semigroup.opposite where
  models := models
  affineConsequence := fun identity valid =>
    affineEmbedding.pullback_identity identity valid
  cappedConsequence := fun identity valid =>
    cappedEmbedding.pullback_identity identity valid

theorem representative_basis :
    BasisFor table.semigroup.opposite leeLiCondition9ReversedBasis :=
  reversedBasisForOfSemanticWitness semanticWitness

end S6_11598

/-! ## Exact proof-carrying root inventory -/

structure CatalogueRootBinding where
  smallsemiIndex : Nat
  table : FiniteTable
  basis : List (Identity Nat)
  complete : BasisFor table.semigroup.opposite basis

def catalogueRootInventory : List CatalogueRootBinding :=
  [{ smallsemiIndex := 9937
     table := S6_9937.table
     basis := leeLiCondition9Basis
     complete := S6_9937.representative_basis },
   { smallsemiIndex := 10837
     table := S6_10837.table
     basis := leeLiCondition9Basis
     complete := S6_10837.representative_basis },
   { smallsemiIndex := 10842
     table := S6_10842.table
     basis := leeLiCondition9Basis
     complete := S6_10842.representative_basis },
   { smallsemiIndex := 11396
     table := S6_11396.table
     basis := leeLiCondition9Basis
     complete := S6_11396.representative_basis },
   { smallsemiIndex := 11459
     table := S6_11459.table
     basis := leeLiCondition9Basis
     complete := S6_11459.representative_basis },
   { smallsemiIndex := 8924
     table := S6_8924.table
     basis := leeLiCondition9ReversedBasis
     complete := S6_8924.representative_basis },
   { smallsemiIndex := 9065
     table := S6_9065.table
     basis := leeLiCondition9ReversedBasis
     complete := S6_9065.representative_basis },
   { smallsemiIndex := 11385
     table := S6_11385.table
     basis := leeLiCondition9ReversedBasis
     complete := S6_11385.representative_basis },
   { smallsemiIndex := 11392
     table := S6_11392.table
     basis := leeLiCondition9ReversedBasis
     complete := S6_11392.representative_basis },
   { smallsemiIndex := 11598
     table := S6_11598.table
     basis := leeLiCondition9ReversedBasis
     complete := S6_11598.representative_basis }]

theorem catalogueRootInventory_indices :
    catalogueRootInventory.map CatalogueRootBinding.smallsemiIndex =
      [9937, 10837, 10842, 11396, 11459,
        8924, 9065, 11385, 11392, 11598] := rfl

end SemigroupBasis.CoRoots.Order6LeeLiCondition9Roots
