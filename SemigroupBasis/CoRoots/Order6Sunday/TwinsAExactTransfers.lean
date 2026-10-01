import SemigroupBasis.CoRoots.Order6Sunday.TwinTwoLawFinite

/-! Literal family-A transfers for msg0511, using the established FORDONLY
Hom/Embedding interface. The finite anchor is S6_14814: it embeds in powers
of S6_11915 and S6_14833. The final map goes from S6_11915 to S6_14852;
the existing S6_11915-to-S6_14689/S6_14851 maps are reused unchanged.
All tables and the exact two-law list remain imported, not reconstructed. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.TwinsAExactTransfers

open SemigroupBasis

private def coordinate11915 (i : Fin 2) (a : Fin 6) : Fin 6 :=
  if i = 0 then
    if a = 0 then 0 else if a = 1 then 1 else
    if a = 2 then 4 else if a = 3 then 4 else 5
  else
    if a = 3 then 2 else if a = 5 then 2 else 0

private def hom11915 (i : Fin 2) :
    Hom LateFinite.SigmaF137a.S6_14814.table.semigroup
      LateFinite.SigmaF137c.S6_11915.table.semigroup where
  toFun := coordinate11915 i
  map_mul := by decide +revert

/-- The literal S6_14814 embeds into two copies of the literal S6_11915. -/
def powerEmbedding11915 :
    Embedding LateFinite.SigmaF137a.S6_14814.table.semigroup
      (LateFinite.SigmaF137c.S6_11915.table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms hom11915 (by decide)

private def coordinate14833 (i : Fin 2) (a : Fin 6) : Fin 6 :=
  if i = 0 then
    if a = 0 then 0 else if a = 1 then 1 else
    if a = 2 then 2 else if a = 4 then 2 else 3
  else
    if a = 0 then 0 else if a = 1 then 1 else
    if a = 2 then 4 else if a = 3 then 4 else 5

private def hom14833 (i : Fin 2) :
    Hom LateFinite.SigmaF137a.S6_14814.table.semigroup
      LateFinite.SigmaF137b.S6_14833.table.semigroup where
  toFun := coordinate14833 i
  map_mul := by decide +revert

/-- The literal S6_14814 embeds into two copies of the literal S6_14833. -/
def powerEmbedding14833 :
    Embedding LateFinite.SigmaF137a.S6_14814.table.semigroup
      (LateFinite.SigmaF137b.S6_14833.table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms hom14833 (by decide)

private def coordinate14852 (i : Fin 2) (a : Fin 6) : Fin 6 :=
  if i = 0 then
    if a = 4 then 4 else if a = 5 then 5 else
    if a = 1 then 1 else if a = 3 then 1 else 0
  else
    if a = 4 then 4 else if a = 5 then 5 else
    if a = 2 then 3 else if a = 3 then 3 else 2

private def hom14852 (i : Fin 2) :
    Hom LateFinite.SigmaF137c.S6_11915.table.semigroup
      LateFinite.SigmaF137c.S6_14852.table.semigroup where
  toFun := coordinate14852 i
  map_mul := by decide +revert

/-- The literal S6_11915 embeds into two copies of the literal S6_14852. -/
def powerEmbedding14852 :
    Embedding LateFinite.SigmaF137c.S6_11915.table.semigroup
      (LateFinite.SigmaF137c.S6_14852.table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms hom14852 (by decide)

end SemigroupBasis.CoRoots.Order6Sunday.TwinsAExactTransfers
