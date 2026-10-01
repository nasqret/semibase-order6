import SemigroupBasis.CoRoots.Order6Sunday.TwinTwoLawFinite

/-! Literal family-B transfers for msg0511. Only multiplication preservation
and joint injectivity on the imported six-element carriers are proved.
The anchor is S6_11897; all tables and exact two-law lists are unchanged. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.TwinsBExactTransfers

open SemigroupBasis

private def coordinate14651 (i : Fin 2) (a : Fin 6) : Fin 6 :=
  if i = 0 then
    if a = 4 then 3 else if a = 5 then 4 else
    if a = 1 then 1 else if a = 3 then 1 else 0
  else
    if a = 4 then 3 else if a = 5 then 4 else
    if a = 2 then 5 else if a = 3 then 5 else 2

private def hom14651 (i : Fin 2) :
    Hom LateFinite.Sigma086fa.S6_11897.table.semigroup
      LateFinite.Sigma086fb.S6_14651.table.semigroup where
  toFun := coordinate14651 i
  map_mul := by decide +revert

/-- The literal S6_11897 embeds into two copies of the literal S6_14651. -/
def powerEmbedding14651 :
    Embedding LateFinite.Sigma086fa.S6_11897.table.semigroup
      (LateFinite.Sigma086fb.S6_14651.table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms hom14651 (by decide)

private def coordinate14680 (i : Fin 2) (a : Fin 6) : Fin 6 :=
  if i = 0 then
    if a = 4 then 2 else if a = 5 then 3 else
    if a = 1 then 1 else if a = 3 then 1 else 0
  else
    if a = 4 then 2 else if a = 5 then 3 else
    if a = 2 then 5 else if a = 3 then 5 else 4

private def hom14680 (i : Fin 2) :
    Hom LateFinite.Sigma086fa.S6_11897.table.semigroup
      LateFinite.Sigma086fc.S6_14680.table.semigroup where
  toFun := coordinate14680 i
  map_mul := by decide +revert

/-- The literal S6_11897 embeds into two copies of the literal S6_14680. -/
def powerEmbedding14680 :
    Embedding LateFinite.Sigma086fa.S6_11897.table.semigroup
      (LateFinite.Sigma086fc.S6_14680.table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms hom14680 (by decide)

private def coordinate14762 (i : Fin 2) (a : Fin 6) : Fin 6 :=
  if i = 0 then
    if a = 4 then 3 else if a = 5 then 4 else
    if a = 2 then 5 else if a = 3 then 5 else 2
  else
    if a = 1 then 1 else if a = 3 then 1 else 0

private def hom14762 (i : Fin 2) :
    Hom LateFinite.Sigma086fa.S6_11897.table.semigroup
      LateFinite.Sigma086fc.S6_14762.table.semigroup where
  toFun := coordinate14762 i
  map_mul := by decide +revert

/-- The literal S6_11897 embeds into two copies of the literal S6_14762. -/
def powerEmbedding14762 :
    Embedding LateFinite.Sigma086fa.S6_11897.table.semigroup
      (LateFinite.Sigma086fc.S6_14762.table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms hom14762 (by decide)

private def coordinate14780 (i : Fin 3) (a : Fin 6) : Fin 6 :=
  if i = 0 then
    if a = 4 then 0 else if a = 5 then 0 else
    if a = 2 then 5 else if a = 3 then 5 else 2
  else if i = 1 then
    if a = 1 then 1 else if a = 3 then 1 else 0
  else
    if a = 4 then 3 else if a = 5 then 4 else 2

private def hom14780 (i : Fin 3) :
    Hom LateFinite.Sigma086fa.S6_11897.table.semigroup
      LateFinite.Sigma086fc.S6_14780.table.semigroup where
  toFun := coordinate14780 i
  map_mul := by decide +revert

/-- The literal S6_11897 embeds into three copies of the literal S6_14780. -/
def powerEmbedding14780 :
    Embedding LateFinite.Sigma086fa.S6_11897.table.semigroup
      (LateFinite.Sigma086fc.S6_14780.table.semigroup.pi (Fin 3)) :=
  Embedding.ofSeparatingHoms hom14780 (by decide)

end SemigroupBasis.CoRoots.Order6Sunday.TwinsBExactTransfers
