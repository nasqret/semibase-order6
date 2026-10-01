import SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4Syntax
import SemigroupBasis.Transfer

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4

open SemigroupBasis

/-!
# Lee--Zhang Proposition 20.7 / E4: exact finite targets

This module binds the published E4 table, catalogue representative S6_5661,
and the audited nontrivial relabelling between them.  Its `Models` theorems
are finite-table soundness certificates only; no completeness claim occurs in
this file.
-/

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

private def rowsOneBased (source : FiniteTable) : List (List Nat) :=
  List.ofFn fun left : Fin source.order =>
    List.ofFn fun right : Fin source.order =>
      (source.mul left right).val + 1

/-! ## Frozen table and map provenance -/

def publishedTableSourceRecordPath : String :=
  "l6d-work/s6_5661-route/source/published_sporadic_tables_source.json"

def publishedTableSourceRecordSHA256 : String :=
  "aa02e738e124b2496ea0fe85811881678a4c49d140a3263c6bedceddd1462467"

def publishedMapSourceRecordPath : String :=
  "l6d-work/s6_5661-route/source/published_sporadic_catalogue_map.json"

def publishedMapSourceRecordSHA256 : String :=
  "dc2d24b9736ef125b79864fa556ed1774eac47bcb6fa7a5785f7295db2f650ee"

def catalogueSourceRecordPath : String :=
  "l6d-work/s6_5661-route/source/catalogue6.json"

def catalogueSourceRecordSHA256 : String :=
  "944f356c42b8e703988f5684cd81b650f99cc0ccd1ef1d7fc6e900f2c95f287c"

def publishedTableRecordSemanticSHA256 : String :=
  "9ec384f85f8f4baf3394776280ebc9c88dbf5333710c6ee3ff206f8ca1b407bb"

def publishedMapRecordSemanticSHA256 : String :=
  "be3d6e9693d55c8f274c7436f0c53443cf85ae66a18cdc43c1c7f2eb40c05624"

/-! ## Published E4 table -/

/-- Exact zero-based multiplication of published table E4.  Its compact
one-based rows are `111111/111113/111133/111344/123455/123466`. -/
def publishedMul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 2 right else
      if left = 2 then row6 0 0 0 0 2 2 right else
        if left = 3 then row6 0 0 0 2 3 3 right else
          if left = 4 then row6 0 1 2 3 4 4 right else
            row6 0 1 2 3 5 5 right

def publishedTable : FiniteTable where
  order := 6
  mul := publishedMul
  assoc := by decide

def publishedTableRowsCompact : List String :=
  ["111111", "111113", "111133", "111344", "123455", "123466"]

def publishedTableRowsOneBased : List (List Nat) :=
  rowsOneBased publishedTable

theorem publishedTableRowsOneBased_certificate :
    publishedTableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 3],
        [1, 1, 1, 1, 3, 3], [1, 1, 1, 3, 4, 4],
        [1, 2, 3, 4, 5, 5], [1, 2, 3, 4, 6, 6]] := by
  decide

def publishedTableSemanticSHA256 : String :=
  "009b5e5302a0a1b091d5fb4fa352f0c9c1df788c348de719b32f3da1b5fd359c"

/-! ## Catalogue S6_5661 table -/

def catalogueID : String := "S6_5661"

/-- Exact zero-based multiplication of catalogue representative S6_5661.
Its compact one-based rows are
`111111/111122/111112/111244/123455/123466`. -/
def catalogueMul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 1 1 right else
      if left = 2 then row6 0 0 0 0 0 1 right else
        if left = 3 then row6 0 0 0 1 3 3 right else
          if left = 4 then row6 0 1 2 3 4 4 right else
            row6 0 1 2 3 5 5 right

def catalogueTable : FiniteTable where
  order := 6
  mul := catalogueMul
  assoc := by decide

def catalogueTableRowsCompact : List String :=
  ["111111", "111122", "111112", "111244", "123455", "123466"]

def catalogueTableRowsOneBased : List (List Nat) :=
  rowsOneBased catalogueTable

theorem catalogueTableRowsOneBased_certificate :
    catalogueTableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2, 2],
        [1, 1, 1, 1, 1, 2], [1, 1, 1, 2, 4, 4],
        [1, 2, 3, 4, 5, 5], [1, 2, 3, 4, 6, 6]] := by
  decide

def catalogueTableSemanticSHA256 : String :=
  "dcb1d70a7c386d3e5ae0aaeb5db654d5554f544cc26eacb01f2164d09d128660"

/-! ## Published-to-catalogue relabelling -/

/-- The audited zero-based relabelling `[0,2,1,3,4,5]`, equivalently the
one-based source map `[1,3,2,4,5,6]`. -/
def publishedToCatalogueRelabel (value : Fin 6) : Fin 6 :=
  if value = 0 then 0 else
    if value = 1 then 2 else
      if value = 2 then 1 else
        if value = 3 then 3 else
          if value = 4 then 4 else 5

def publishedToCatalogueMapZeroBased : List Nat :=
  List.ofFn fun value : Fin 6 =>
    (publishedToCatalogueRelabel value).val

theorem publishedToCatalogueMapZeroBased_certificate :
    publishedToCatalogueMapZeroBased = [0, 2, 1, 3, 4, 5] := by
  decide

def publishedToCatalogueMapOneBased : List Nat :=
  List.ofFn fun value : Fin 6 =>
    (publishedToCatalogueRelabel value).val + 1

theorem publishedToCatalogueMapOneBased_certificate :
    publishedToCatalogueMapOneBased = [1, 3, 2, 4, 5, 6] := by
  decide

theorem publishedToCatalogue_mul_certificate
    (left right : Fin 6) :
    publishedToCatalogueRelabel (publishedMul left right) =
      catalogueMul (publishedToCatalogueRelabel left)
        (publishedToCatalogueRelabel right) := by
  apply Fin.ext
  revert left right
  decide

/-- The exact 36-entry table transport certified by the frozen source map. -/
def publishedToCatalogueEmbedding :
    Embedding publishedTable.semigroup catalogueTable.semigroup where
  toFun := publishedToCatalogueRelabel
  map_mul := publishedToCatalogue_mul_certificate
  injective := by
    intro left right
    revert left right
    decide

/-! ## Exact finite soundness

The original eight-slot fused decisions evaluate all 6^8 valuations for
every literal law.  The certificate statements below are unchanged, but
their proofs use a semantic factorization.  A doubled-letter block cannot
evaluate to E4 element 1; after three such blocks, the two right factors
commute.  This reduces every eight-variable (20.6f) law to closed checks on
at most three elements.  The remaining literal laws use at most five
actual variables.  No assignment domain or displayed law is weakened.
-/

private theorem publishedMul_assoc (a b c : Fin 6) :
    publishedMul (publishedMul a b) c =
      publishedMul a (publishedMul b c) :=
  publishedTable.assoc a b c

set_option maxHeartbeats 0 in
private theorem publishedSquare_ne_one (x : Fin 6) :
    publishedMul x x ≠ 1 := by
  revert x
  decide

set_option maxHeartbeats 0 in
private theorem publishedSandwich_ne_one (x h : Fin 6) :
    publishedMul (publishedMul x h) x ≠ 1 := by
  revert x h
  decide

set_option maxHeartbeats 0 in
private theorem publishedLeft_ne_one (a q : Fin 6) (hq : q ≠ 1) :
    publishedMul a q ≠ 1 := by
  revert a q
  decide

set_option maxHeartbeats 0 in
private theorem publishedStable_right_commute
    (p q r : Fin 6) (hp : p ≠ 1) (hq : q ≠ 1) (hr : r ≠ 1) :
    publishedMul (publishedMul p q) r =
      publishedMul (publishedMul p r) q := by
  revert p q r
  decide

set_option maxHeartbeats 0 in
private theorem publishedPrefixSquare_ne_one (a y : Fin 6) :
    publishedMul (publishedMul a y) y ≠ 1 := by
  revert a y
  decide

set_option maxHeartbeats 0 in
private theorem publishedPrefixSandwich_ne_one (a y b : Fin 6) :
    publishedMul (publishedMul (publishedMul a y) b) y ≠ 1 := by
  revert a y b
  decide

/-- Perform the representation-boundary rewrite while the operation is
abstract.  In particular, do not normalize long concrete-table products
with the simplifier's definitional-equality matcher. -/
private theorem identity_sound_of_three_blocks
    {S : Type} (G : Semigroup S) (identity : Identity Nat)
    (p q r : Word Nat)
    (leftShape : identity.lhs = (p ++ q) ++ r)
    (rightShape : identity.rhs = (p ++ r) ++ q)
    (commutes : ∀ valuation : Nat → S,
      G.mul (G.mul (G.eval valuation p) (G.eval valuation q))
          (G.eval valuation r) =
        G.mul (G.mul (G.eval valuation p) (G.eval valuation r))
          (G.eval valuation q)) :
    identity.SatisfiedBy G := by
  intro valuation
  rw [leftShape, rightShape]
  simpa only [Semigroup.eval_append] using commutes valuation

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HABCD :
    law20_6f_HABCD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HABCD (w 0 [2, 0]) (w 3 [1, 4, 1]) (w 5 [6, 7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 4, 1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 7, 6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedPrefixSandwich_ne_one (valuation 3) (valuation 1) (valuation 4))
    (publishedPrefixSandwich_ne_one (valuation 5) (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HABC :
    law20_6f_HABC.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HABC (w 0 [2, 0]) (w 3 [1, 4, 1]) (w 5 [6, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 4, 1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedPrefixSandwich_ne_one (valuation 3) (valuation 1) (valuation 4))
    (publishedPrefixSquare_ne_one (valuation 5) (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HABD :
    law20_6f_HABD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HABD (w 0 [2, 0]) (w 3 [1, 4, 1]) (w 6 [7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 4, 1]))
    (publishedTable.semigroup.eval valuation (w 6 [7, 6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedPrefixSandwich_ne_one (valuation 3) (valuation 1) (valuation 4))
    (publishedSandwich_ne_one (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HAB :
    law20_6f_HAB.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HAB (w 0 [2, 0]) (w 3 [1, 4, 1]) (w 6 [6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 4, 1]))
    (publishedTable.semigroup.eval valuation (w 6 [6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedPrefixSandwich_ne_one (valuation 3) (valuation 1) (valuation 4))
    (publishedSquare_ne_one (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HACD :
    law20_6f_HACD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HACD (w 0 [2, 0]) (w 3 [1, 1]) (w 5 [6, 7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 7, 6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedPrefixSquare_ne_one (valuation 3) (valuation 1))
    (publishedPrefixSandwich_ne_one (valuation 5) (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HAC :
    law20_6f_HAC.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HAC (w 0 [2, 0]) (w 3 [1, 1]) (w 5 [6, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedPrefixSquare_ne_one (valuation 3) (valuation 1))
    (publishedPrefixSquare_ne_one (valuation 5) (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HAD :
    law20_6f_HAD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HAD (w 0 [2, 0]) (w 3 [1, 1]) (w 6 [7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 1]))
    (publishedTable.semigroup.eval valuation (w 6 [7, 6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedPrefixSquare_ne_one (valuation 3) (valuation 1))
    (publishedSandwich_ne_one (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HA :
    law20_6f_HA.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HA (w 0 [2, 0]) (w 3 [1, 1]) (w 6 [6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 1]))
    (publishedTable.semigroup.eval valuation (w 6 [6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedPrefixSquare_ne_one (valuation 3) (valuation 1))
    (publishedSquare_ne_one (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6b_HK :
    law20_6b_HK.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v2 v3 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v0) v3) v0) =
        (publishedMul (publishedMul (publishedMul (publishedMul v0 v3) v0) v2) v0) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 2) (valuation 3)

set_option maxHeartbeats 0 in
private theorem published_law20_6a_HK :
    law20_6a_HK.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v2 v3 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v0) v3) v0) v0) =
        (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v0) v3) v0) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 2) (valuation 3)

set_option maxHeartbeats 0 in
private theorem published_law20_6c_HKT :
    law20_6c_HKT.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v2 v3 v4 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v0) v3) v1) v4) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v0) v4) v1) v3) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 2) (valuation 3) (valuation 4)

set_option maxHeartbeats 0 in
private theorem published_law20_6c_HK :
    law20_6c_HK.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v2 v3 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v0) v3) v1) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v0) v1) v3) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 2) (valuation 3)

set_option maxHeartbeats 0 in
private theorem published_law20_6b_H :
    law20_6b_H.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v2 : Fin 6),
      (publishedMul (publishedMul (publishedMul v0 v2) v0) v0) =
        (publishedMul (publishedMul (publishedMul v0 v0) v2) v0) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 2)

set_option maxHeartbeats 0 in
private theorem published_law20_6a_H :
    law20_6a_H.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v2 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v0) v0) v0) =
        (publishedMul (publishedMul (publishedMul v0 v2) v0) v0) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 2)

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HBCD :
    law20_6f_HBCD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HBCD (w 0 [2, 0]) (w 1 [4, 1]) (w 5 [6, 7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 1 [4, 1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 7, 6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedSandwich_ne_one (valuation 1) (valuation 4))
    (publishedPrefixSandwich_ne_one (valuation 5) (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HBC :
    law20_6f_HBC.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HBC (w 0 [2, 0]) (w 1 [4, 1]) (w 5 [6, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 1 [4, 1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedSandwich_ne_one (valuation 1) (valuation 4))
    (publishedPrefixSquare_ne_one (valuation 5) (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HBD :
    law20_6f_HBD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HBD (w 0 [2, 0]) (w 1 [4, 1]) (w 6 [7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 1 [4, 1]))
    (publishedTable.semigroup.eval valuation (w 6 [7, 6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedSandwich_ne_one (valuation 1) (valuation 4))
    (publishedSandwich_ne_one (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HB :
    law20_6f_HB.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HB (w 0 [2, 0]) (w 1 [4, 1]) (w 6 [6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 1 [4, 1]))
    (publishedTable.semigroup.eval valuation (w 6 [6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedSandwich_ne_one (valuation 1) (valuation 4))
    (publishedSquare_ne_one (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6c_HT :
    law20_6c_HT.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v2 v4 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v0) v1) v4) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v0) v4) v1) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 2) (valuation 4)

set_option maxHeartbeats 0 in
private theorem published_law20_6c_H :
    law20_6c_H.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v2 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v0) v1) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v0) v1) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 2)

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HCD :
    law20_6f_HCD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HCD (w 0 [2, 0]) (w 1 [1]) (w 5 [6, 7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 1 [1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 7, 6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedSquare_ne_one (valuation 1))
    (publishedPrefixSandwich_ne_one (valuation 5) (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HC :
    law20_6f_HC.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HC (w 0 [2, 0]) (w 1 [1]) (w 5 [6, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 1 [1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedSquare_ne_one (valuation 1))
    (publishedPrefixSquare_ne_one (valuation 5) (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_HD :
    law20_6f_HD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_HD (w 0 [2, 0]) (w 1 [1]) (w 6 [7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 1 [1]))
    (publishedTable.semigroup.eval valuation (w 6 [7, 6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedSquare_ne_one (valuation 1))
    (publishedSandwich_ne_one (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_H :
    law20_6f_H.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_H (w 0 [2, 0]) (w 1 [1]) (w 6 [6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [2, 0]))
    (publishedTable.semigroup.eval valuation (w 1 [1]))
    (publishedTable.semigroup.eval valuation (w 6 [6]))
    (publishedSandwich_ne_one (valuation 0) (valuation 2))
    (publishedSquare_ne_one (valuation 1))
    (publishedSquare_ne_one (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6d_HKT :
    law20_6d_HKT.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v2 v3 v4 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v1) v3) v0) v4) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v3) v0) v2) v1) v4) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 2) (valuation 3) (valuation 4)

set_option maxHeartbeats 0 in
private theorem published_law20_6d_HK :
    law20_6d_HK.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v2 v3 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v1) v3) v0) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v3) v0) v2) v1) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 2) (valuation 3)

set_option maxHeartbeats 0 in
private theorem published_law20_6e_HKT :
    law20_6e_HKT.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v2 v3 v4 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v1) v3) v1) v4) v0) =
        (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v4) v0) v2) v1) v3) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 2) (valuation 3) (valuation 4)

set_option maxHeartbeats 0 in
private theorem published_law20_6e_HK :
    law20_6e_HK.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v2 v3 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v1) v3) v1) v0) =
        (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v0) v2) v1) v3) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 2) (valuation 3)

set_option maxHeartbeats 0 in
private theorem published_law20_6d_HT :
    law20_6d_HT.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v2 v4 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v1) v0) v4) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v0) v2) v1) v4) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 2) (valuation 4)

set_option maxHeartbeats 0 in
private theorem published_law20_6d_H :
    law20_6d_H.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v2 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v1) v0) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul v0 v0) v2) v1) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 2)

set_option maxHeartbeats 0 in
private theorem published_law20_6e_HT :
    law20_6e_HT.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v2 v4 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v1) v1) v4) v0) =
        (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v4) v0) v2) v1) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 2) (valuation 4)

set_option maxHeartbeats 0 in
private theorem published_law20_6e_H :
    law20_6e_H.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v2 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul v0 v2) v1) v1) v0) =
        (publishedMul (publishedMul (publishedMul (publishedMul v0 v0) v2) v1) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 2)

set_option maxHeartbeats 0 in
private theorem published_law20_6f_ABCD :
    law20_6f_ABCD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_ABCD (w 0 [0]) (w 3 [1, 4, 1]) (w 5 [6, 7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 4, 1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 7, 6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedPrefixSandwich_ne_one (valuation 3) (valuation 1) (valuation 4))
    (publishedPrefixSandwich_ne_one (valuation 5) (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_ABC :
    law20_6f_ABC.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_ABC (w 0 [0]) (w 3 [1, 4, 1]) (w 5 [6, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 4, 1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedPrefixSandwich_ne_one (valuation 3) (valuation 1) (valuation 4))
    (publishedPrefixSquare_ne_one (valuation 5) (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_ABD :
    law20_6f_ABD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_ABD (w 0 [0]) (w 3 [1, 4, 1]) (w 6 [7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 4, 1]))
    (publishedTable.semigroup.eval valuation (w 6 [7, 6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedPrefixSandwich_ne_one (valuation 3) (valuation 1) (valuation 4))
    (publishedSandwich_ne_one (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_AB :
    law20_6f_AB.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_AB (w 0 [0]) (w 3 [1, 4, 1]) (w 6 [6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 4, 1]))
    (publishedTable.semigroup.eval valuation (w 6 [6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedPrefixSandwich_ne_one (valuation 3) (valuation 1) (valuation 4))
    (publishedSquare_ne_one (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_ACD :
    law20_6f_ACD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_ACD (w 0 [0]) (w 3 [1, 1]) (w 5 [6, 7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 7, 6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedPrefixSquare_ne_one (valuation 3) (valuation 1))
    (publishedPrefixSandwich_ne_one (valuation 5) (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_AC :
    law20_6f_AC.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_AC (w 0 [0]) (w 3 [1, 1]) (w 5 [6, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedPrefixSquare_ne_one (valuation 3) (valuation 1))
    (publishedPrefixSquare_ne_one (valuation 5) (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_AD :
    law20_6f_AD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_AD (w 0 [0]) (w 3 [1, 1]) (w 6 [7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 1]))
    (publishedTable.semigroup.eval valuation (w 6 [7, 6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedPrefixSquare_ne_one (valuation 3) (valuation 1))
    (publishedSandwich_ne_one (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_A :
    law20_6f_A.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_A (w 0 [0]) (w 3 [1, 1]) (w 6 [6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 3 [1, 1]))
    (publishedTable.semigroup.eval valuation (w 6 [6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedPrefixSquare_ne_one (valuation 3) (valuation 1))
    (publishedSquare_ne_one (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6b_K :
    law20_6b_K.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v3 : Fin 6),
      (publishedMul (publishedMul (publishedMul v0 v0) v3) v0) =
        (publishedMul (publishedMul (publishedMul v0 v3) v0) v0) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 3)

set_option maxHeartbeats 0 in
private theorem published_law20_6a_K :
    law20_6a_K.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v3 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul v0 v0) v3) v0) v0) =
        (publishedMul (publishedMul (publishedMul v0 v0) v3) v0) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 3)

set_option maxHeartbeats 0 in
private theorem published_law20_6c_KT :
    law20_6c_KT.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v3 v4 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v0) v3) v1) v4) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v0) v4) v1) v3) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 3) (valuation 4)

set_option maxHeartbeats 0 in
private theorem published_law20_6c_K :
    law20_6c_K.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v3 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul v0 v0) v3) v1) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul v0 v0) v1) v3) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 3)

set_option maxHeartbeats 0 in
private theorem published_law20_6b_empty :
    law20_6b_empty.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 : Fin 6),
      (publishedMul (publishedMul v0 v0) v0) =
        (publishedMul (publishedMul v0 v0) v0) := by
    decide
  intro valuation
  exact checked (valuation 0)

set_option maxHeartbeats 0 in
private theorem published_law20_6a_empty :
    law20_6a_empty.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 : Fin 6),
      (publishedMul (publishedMul (publishedMul v0 v0) v0) v0) =
        (publishedMul (publishedMul v0 v0) v0) := by
    decide
  intro valuation
  exact checked (valuation 0)

set_option maxHeartbeats 0 in
private theorem published_law20_6f_BCD :
    law20_6f_BCD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_BCD (w 0 [0]) (w 1 [4, 1]) (w 5 [6, 7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 1 [4, 1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 7, 6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedSandwich_ne_one (valuation 1) (valuation 4))
    (publishedPrefixSandwich_ne_one (valuation 5) (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_BC :
    law20_6f_BC.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_BC (w 0 [0]) (w 1 [4, 1]) (w 5 [6, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 1 [4, 1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedSandwich_ne_one (valuation 1) (valuation 4))
    (publishedPrefixSquare_ne_one (valuation 5) (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_BD :
    law20_6f_BD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_BD (w 0 [0]) (w 1 [4, 1]) (w 6 [7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 1 [4, 1]))
    (publishedTable.semigroup.eval valuation (w 6 [7, 6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedSandwich_ne_one (valuation 1) (valuation 4))
    (publishedSandwich_ne_one (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_B :
    law20_6f_B.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_B (w 0 [0]) (w 1 [4, 1]) (w 6 [6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 1 [4, 1]))
    (publishedTable.semigroup.eval valuation (w 6 [6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedSandwich_ne_one (valuation 1) (valuation 4))
    (publishedSquare_ne_one (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6c_T :
    law20_6c_T.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v4 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul v0 v0) v1) v4) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul v0 v0) v4) v1) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 4)

set_option maxHeartbeats 0 in
private theorem published_law20_6c_empty :
    law20_6c_empty.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 : Fin 6),
      (publishedMul (publishedMul (publishedMul v0 v0) v1) v1) =
        (publishedMul (publishedMul (publishedMul v0 v0) v1) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1)

set_option maxHeartbeats 0 in
private theorem published_law20_6f_CD :
    law20_6f_CD.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_CD (w 0 [0]) (w 1 [1]) (w 5 [6, 7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 1 [1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 7, 6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedSquare_ne_one (valuation 1))
    (publishedPrefixSandwich_ne_one (valuation 5) (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_C :
    law20_6f_C.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_C (w 0 [0]) (w 1 [1]) (w 5 [6, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 1 [1]))
    (publishedTable.semigroup.eval valuation (w 5 [6, 6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedSquare_ne_one (valuation 1))
    (publishedPrefixSquare_ne_one (valuation 5) (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_D :
    law20_6f_D.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_D (w 0 [0]) (w 1 [1]) (w 6 [7, 6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 1 [1]))
    (publishedTable.semigroup.eval valuation (w 6 [7, 6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedSquare_ne_one (valuation 1))
    (publishedSandwich_ne_one (valuation 6) (valuation 7))

set_option maxHeartbeats 0 in
private theorem published_law20_6f_empty :
    law20_6f_empty.SatisfiedBy publishedTable.semigroup := by
  refine identity_sound_of_three_blocks publishedTable.semigroup
    law20_6f_empty (w 0 [0]) (w 1 [1]) (w 6 [6])
    rfl rfl ?_
  intro valuation
  exact publishedStable_right_commute
    (publishedTable.semigroup.eval valuation (w 0 [0]))
    (publishedTable.semigroup.eval valuation (w 1 [1]))
    (publishedTable.semigroup.eval valuation (w 6 [6]))
    (publishedSquare_ne_one (valuation 0))
    (publishedSquare_ne_one (valuation 1))
    (publishedSquare_ne_one (valuation 6))

set_option maxHeartbeats 0 in
private theorem published_law20_6d_KT :
    law20_6d_KT.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v3 v4 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v1) v3) v0) v4) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v3) v0) v1) v4) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 3) (valuation 4)

set_option maxHeartbeats 0 in
private theorem published_law20_6d_K :
    law20_6d_K.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v3 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul v0 v1) v3) v0) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul v0 v3) v0) v1) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 3)

set_option maxHeartbeats 0 in
private theorem published_law20_6e_KT :
    law20_6e_KT.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v3 v4 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v1) v3) v1) v4) v0) =
        (publishedMul (publishedMul (publishedMul (publishedMul (publishedMul v0 v4) v0) v1) v3) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 3) (valuation 4)

set_option maxHeartbeats 0 in
private theorem published_law20_6e_K :
    law20_6e_K.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v3 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul v0 v1) v3) v1) v0) =
        (publishedMul (publishedMul (publishedMul (publishedMul v0 v0) v1) v3) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 3)

set_option maxHeartbeats 0 in
private theorem published_law20_6d_T :
    law20_6d_T.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v4 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul v0 v1) v0) v4) v1) =
        (publishedMul (publishedMul (publishedMul (publishedMul v0 v0) v1) v4) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 4)

set_option maxHeartbeats 0 in
private theorem published_law20_6d_empty :
    law20_6d_empty.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 : Fin 6),
      (publishedMul (publishedMul (publishedMul v0 v1) v0) v1) =
        (publishedMul (publishedMul (publishedMul v0 v0) v1) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1)

set_option maxHeartbeats 0 in
private theorem published_law20_6e_T :
    law20_6e_T.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 v4 : Fin 6),
      (publishedMul (publishedMul (publishedMul (publishedMul v0 v1) v1) v4) v0) =
        (publishedMul (publishedMul (publishedMul (publishedMul v0 v4) v0) v1) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1) (valuation 4)

set_option maxHeartbeats 0 in
private theorem published_law20_6e_empty :
    law20_6e_empty.SatisfiedBy publishedTable.semigroup := by
  have checked : ∀ (v0 v1 : Fin 6),
      (publishedMul (publishedMul (publishedMul v0 v1) v1) v0) =
        (publishedMul (publishedMul (publishedMul v0 v0) v1) v1) := by
    decide
  intro valuation
  exact checked (valuation 0) (valuation 1)

private theorem publishedModelsDirect : Models publishedTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact published_law20_6f_HABCD
  · exact published_law20_6f_HABC
  · exact published_law20_6f_HABD
  · exact published_law20_6f_HAB
  · exact published_law20_6f_HACD
  · exact published_law20_6f_HAC
  · exact published_law20_6f_HAD
  · exact published_law20_6f_HA
  · exact published_law20_6b_HK
  · exact published_law20_6a_HK
  · exact published_law20_6c_HKT
  · exact published_law20_6c_HK
  · exact published_law20_6b_H
  · exact published_law20_6a_H
  · exact published_law20_6f_HBCD
  · exact published_law20_6f_HBC
  · exact published_law20_6f_HBD
  · exact published_law20_6f_HB
  · exact published_law20_6c_HT
  · exact published_law20_6c_H
  · exact published_law20_6f_HCD
  · exact published_law20_6f_HC
  · exact published_law20_6f_HD
  · exact published_law20_6f_H
  · exact published_law20_6d_HKT
  · exact published_law20_6d_HK
  · exact published_law20_6e_HKT
  · exact published_law20_6e_HK
  · exact published_law20_6d_HT
  · exact published_law20_6d_H
  · exact published_law20_6e_HT
  · exact published_law20_6e_H
  · exact published_law20_6f_ABCD
  · exact published_law20_6f_ABC
  · exact published_law20_6f_ABD
  · exact published_law20_6f_AB
  · exact published_law20_6f_ACD
  · exact published_law20_6f_AC
  · exact published_law20_6f_AD
  · exact published_law20_6f_A
  · exact published_law20_6b_K
  · exact published_law20_6a_K
  · exact published_law20_6c_KT
  · exact published_law20_6c_K
  · exact published_law20_6b_empty
  · exact published_law20_6a_empty
  · exact published_law20_6f_BCD
  · exact published_law20_6f_BC
  · exact published_law20_6f_BD
  · exact published_law20_6f_B
  · exact published_law20_6c_T
  · exact published_law20_6c_empty
  · exact published_law20_6f_CD
  · exact published_law20_6f_C
  · exact published_law20_6f_D
  · exact published_law20_6f_empty
  · exact published_law20_6d_KT
  · exact published_law20_6d_K
  · exact published_law20_6e_KT
  · exact published_law20_6e_K
  · exact published_law20_6d_T
  · exact published_law20_6d_empty
  · exact published_law20_6e_T
  · exact published_law20_6e_empty

private theorem fusedAssignmentsOfAll {variables carrier : Nat}
    (predicate : (Fin variables → Fin carrier) → Bool)
    (valid : ∀ valuation, predicate valuation = true) :
    FiniteTable.checkAssignmentsFused variables carrier predicate = true := by
  induction variables with
  | zero =>
      exact valid _
  | succ variables ih =>
      change (List.finRange carrier).all (fun head =>
        FiniteTable.checkAssignmentsFused variables carrier
          (fun tail => predicate (Fin.cases head tail))) = true
      apply List.all_eq_true.mpr
      intro head _
      exact ih (fun tail => predicate (Fin.cases head tail))
        (fun tail => valid (Fin.cases head tail))

private theorem fusedCheckOfSatisfied
    (candidate : FiniteTable) (identity : Identity (Fin variables))
    (valid : identity.SatisfiedBy candidate.semigroup) :
    candidate.checkIdentityFused identity = true := by
  apply fusedAssignmentsOfAll
  intro valuation
  simp only [decide_eq_true_eq]
  exact valid valuation

private theorem fusedShardOfModels
    (candidate : FiniteTable) (shard : List (Identity Nat))
    (included : ∀ identity, identity ∈ shard → identity ∈ basis)
    (models : Models candidate.semigroup basis) :
    (shard.map (fun identity => identity.map toFinEight)).all
      candidate.checkIdentityFused = true := by
  apply List.all_eq_true.mpr
  intro finiteIdentity finiteMember
  obtain ⟨identity, sourceMember, rfl⟩ := List.mem_map.mp finiteMember
  exact fusedCheckOfSatisfied candidate (identity.map toFinEight)
    (identity.satisfiedBy_map toFinEight candidate.semigroup
      (models identity (included identity sourceMember)))

private def catalogueToPublishedEmbedding :
    Embedding catalogueTable.semigroup publishedTable.semigroup where
  toFun := publishedToCatalogueRelabel
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := publishedToCatalogueEmbedding.injective

private theorem catalogueModelsDirect : Models catalogueTable.semigroup basis := by
  intro identity member
  exact catalogueToPublishedEmbedding.pullback_identity identity
    (publishedModelsDirect identity member)

theorem publishedCheckShard01 :
    finiteBasisShard01.all publishedTable.checkIdentityFused = true := by
  apply fusedShardOfModels publishedTable basisShard01 ?_ publishedModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inl member

theorem publishedCheckShard02 :
    finiteBasisShard02.all publishedTable.checkIdentityFused = true := by
  apply fusedShardOfModels publishedTable basisShard02 ?_ publishedModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inl member)

theorem publishedCheckShard03 :
    finiteBasisShard03.all publishedTable.checkIdentityFused = true := by
  apply fusedShardOfModels publishedTable basisShard03 ?_ publishedModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inl member))

theorem publishedCheckShard04 :
    finiteBasisShard04.all publishedTable.checkIdentityFused = true := by
  apply fusedShardOfModels publishedTable basisShard04 ?_ publishedModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inr (Or.inl member)))

theorem publishedCheckShard05 :
    finiteBasisShard05.all publishedTable.checkIdentityFused = true := by
  apply fusedShardOfModels publishedTable basisShard05 ?_ publishedModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl member))))

theorem publishedCheckShard06 :
    finiteBasisShard06.all publishedTable.checkIdentityFused = true := by
  apply fusedShardOfModels publishedTable basisShard06 ?_ publishedModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl member)))))

theorem publishedCheckShard07 :
    finiteBasisShard07.all publishedTable.checkIdentityFused = true := by
  apply fusedShardOfModels publishedTable basisShard07 ?_ publishedModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl member))))))

theorem publishedCheckShard08 :
    finiteBasisShard08.all publishedTable.checkIdentityFused = true := by
  apply fusedShardOfModels publishedTable basisShard08 ?_ publishedModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (member)))))))

theorem publishedModels : Models publishedTable.semigroup basis :=
  models_of_sharded_fused_checks publishedTable
    publishedCheckShard01 publishedCheckShard02 publishedCheckShard03
    publishedCheckShard04 publishedCheckShard05 publishedCheckShard06
    publishedCheckShard07 publishedCheckShard08

theorem catalogueCheckShard01 :
    finiteBasisShard01.all catalogueTable.checkIdentityFused = true := by
  apply fusedShardOfModels catalogueTable basisShard01 ?_ catalogueModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inl member

theorem catalogueCheckShard02 :
    finiteBasisShard02.all catalogueTable.checkIdentityFused = true := by
  apply fusedShardOfModels catalogueTable basisShard02 ?_ catalogueModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inl member)

theorem catalogueCheckShard03 :
    finiteBasisShard03.all catalogueTable.checkIdentityFused = true := by
  apply fusedShardOfModels catalogueTable basisShard03 ?_ catalogueModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inl member))

theorem catalogueCheckShard04 :
    finiteBasisShard04.all catalogueTable.checkIdentityFused = true := by
  apply fusedShardOfModels catalogueTable basisShard04 ?_ catalogueModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inr (Or.inl member)))

theorem catalogueCheckShard05 :
    finiteBasisShard05.all catalogueTable.checkIdentityFused = true := by
  apply fusedShardOfModels catalogueTable basisShard05 ?_ catalogueModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl member))))

theorem catalogueCheckShard06 :
    finiteBasisShard06.all catalogueTable.checkIdentityFused = true := by
  apply fusedShardOfModels catalogueTable basisShard06 ?_ catalogueModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl member)))))

theorem catalogueCheckShard07 :
    finiteBasisShard07.all catalogueTable.checkIdentityFused = true := by
  apply fusedShardOfModels catalogueTable basisShard07 ?_ catalogueModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl member))))))

theorem catalogueCheckShard08 :
    finiteBasisShard08.all catalogueTable.checkIdentityFused = true := by
  apply fusedShardOfModels catalogueTable basisShard08 ?_ catalogueModelsDirect
  intro identity member
  simp only [basis_eq_shards, List.mem_append, or_assoc]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (member)))))))

theorem catalogueModels : Models catalogueTable.semigroup basis :=
  models_of_sharded_fused_checks catalogueTable
    catalogueCheckShard01 catalogueCheckShard02 catalogueCheckShard03
    catalogueCheckShard04 catalogueCheckShard05 catalogueCheckShard06
    catalogueCheckShard07 catalogueCheckShard08

theorem publishedOppositeModels :
    Models publishedTable.semigroup.opposite oppositeBasis :=
  publishedModels.oppositeReversed

theorem catalogueOppositeModels :
    Models catalogueTable.semigroup.opposite oppositeBasis :=
  catalogueModels.oppositeReversed

end SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4
