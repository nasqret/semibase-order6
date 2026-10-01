import SemigroupBasis.CoRoots.Order6Sunday.FordOnlyExactFinite

/-! The two literal finite power embeddings requested by S2 in
`s2-msg0490-fordonly-fixed-transfers-request-20260831`.
Only multiplication preservation and joint injectivity on the six-element
carriers are proved here. The imported laws and tables are unchanged. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.FordOnlyExactTransfers

open SemigroupBasis

private def coordinate5563 (i : Fin 3) (a : Fin 6) : Fin 6 :=
  if i = 0 then
    if a = 4 then 4 else if a = 5 then 5 else 0
  else if i = 1 then
    if a = 2 then 2 else if a = 5 then 5 else 0
  else
    if a = 1 then 1 else if a = 3 then 3 else 0

private def hom5563 (i : Fin 3) :
    Hom L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup
      FordOnlyExactFinite.S6_5563.table.semigroup where
  toFun := coordinate5563 i
  map_mul := by decide +revert

/-- The three requested coordinate maps jointly embed the literal source. -/
def powerEmbedding5563 :
    Embedding L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup
      (FordOnlyExactFinite.S6_5563.table.semigroup.pi (Fin 3)) :=
  Embedding.ofSeparatingHoms hom5563 (by decide)

private def coordinate9657 (i : Fin 3) (a : Fin 6) : Fin 6 :=
  if i = 0 then
    if a = 4 then 5 else if a = 5 then 0 else 3
  else if i = 1 then
    if a = 2 then 4 else if a = 5 then 0 else 3
  else
    if a = 1 then 1 else if a = 3 then 2 else 0

private def hom9657 (i : Fin 3) :
    Hom L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup
      FordOnlyExactFinite.S6_9657.table.semigroup where
  toFun := coordinate9657 i
  map_mul := by decide +revert

/-- The three requested coordinate maps jointly embed the literal source. -/
def powerEmbedding9657 :
    Embedding L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup
      (FordOnlyExactFinite.S6_9657.table.semigroup.pi (Fin 3)) :=
  Embedding.ofSeparatingHoms hom9657 (by decide)

end SemigroupBasis.CoRoots.Order6Sunday.FordOnlyExactTransfers
