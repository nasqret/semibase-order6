import SemigroupBasis.CoRoots.Order6D2D4SuffixTraceSyntax

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6D2D4SuffixTrace

open SemigroupBasis

/-!
# D2 / D4 suffix-trace spine: exact Step-1 targets

This module binds the published D2 and D4 tables to the frozen `B31` syntax.
Its two `Models` endpoints are finite-table soundness certificates only.
No descriptor-preservation, canonicalization, or completeness result is
asserted here.
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

/-! ## Published D2 / catalogue S6_6432 -/

def d2ClassID : String := "S6_6432"
def d2PublishedLabel : String := "D2"

/-- Exact zero-based multiplication for D2 / S6_6432.  Its compact
one-based rows are `111111/111112/111121/123444/123445/123446`. -/
def d2Mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 1 right else
      if left = 2 then row6 0 0 0 0 1 0 right else
        if left = 3 then row6 0 1 2 3 3 3 right else
          if left = 4 then row6 0 1 2 3 3 4 right else
            row6 0 1 2 3 3 5 right

def d2Table : FiniteTable where
  order := 6
  mul := d2Mul
  assoc := by decide

def d2RowsCompact : List String :=
  ["111111", "111112", "111121", "123444", "123445", "123446"]

def d2RowsOneBased : List (List Nat) := rowsOneBased d2Table

theorem d2RowsOneBased_certificate :
    d2RowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 2],
        [1, 1, 1, 1, 2, 1], [1, 2, 3, 4, 4, 4],
        [1, 2, 3, 4, 4, 5], [1, 2, 3, 4, 4, 6]] := by
  decide

/-! ## Published D4 / catalogue S6_6439 -/

def d4ClassID : String := "S6_6439"
def d4PublishedLabel : String := "D4"

/-- Exact zero-based multiplication for D4 / S6_6439.  Its compact
one-based rows are `111111/111112/111122/123444/123445/123446`. -/
def d4Mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 1 right else
      if left = 2 then row6 0 0 0 0 1 1 right else
        if left = 3 then row6 0 1 2 3 3 3 right else
          if left = 4 then row6 0 1 2 3 3 4 right else
            row6 0 1 2 3 3 5 right

def d4Table : FiniteTable where
  order := 6
  mul := d4Mul
  assoc := by decide

def d4RowsCompact : List String :=
  ["111111", "111112", "111122", "123444", "123445", "123446"]

def d4RowsOneBased : List (List Nat) := rowsOneBased d4Table

theorem d4RowsOneBased_certificate :
    d4RowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 2],
        [1, 1, 1, 1, 2, 2], [1, 2, 3, 4, 4, 4],
        [1, 2, 3, 4, 4, 5], [1, 2, 3, 4, 4, 6]] := by
  decide
end SemigroupBasis.CoRoots.Order6D2D4SuffixTrace
