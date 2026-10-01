import SemigroupBasis.Examples.NormalBandFourSyntax
import SemigroupBasis.Examples.RectangularBandFourSyntax
import SemigroupBasis.Examples.LeftRegularBandThree
import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.CoRoots.Order6FennemoreR3Band

open SemigroupBasis

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- The exact zero-based Smallsemi table `S6_15646`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 1 0 1 4 5 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 0 1 2 3 4 5 right else
          if left = 4 then row6 0 1 5 4 4 5 right else
            row6 5 5 5 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 =>
      (table.semigroup.mul left right).val + 1

theorem tableOneBased_certificate :
    tableOneBased =
      [[1, 1, 1, 1, 1, 1],
       [1, 2, 1, 2, 5, 6],
       [3, 3, 3, 3, 3, 3],
       [1, 2, 3, 4, 5, 6],
       [1, 2, 6, 5, 5, 6],
       [6, 6, 6, 6, 6, 6]] := by
  decide

def x : Word Nat := Word.singleton 0
def xx : Word Nat := ⟨0, [0]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xyzxzyz : Word Nat := ⟨0, [1, 2, 0, 2, 1, 2]⟩

def idempotenceLaw : Identity Nat := ⟨x, xx⟩
def r3Law : Identity Nat := ⟨xyz, xyzxzyz⟩

/-- The Fennemore `R3 = S3` band basis, in the orientation attached to
`S6_15646`: `x = xx`, `xyz = xyzxzyz`. -/
def basis : List (Identity Nat) := [idempotenceLaw, r3Law]

def finiteIdempotenceLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0]⟩⟩

def finiteR3Law : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 2, 0, 2, 1, 2]⟩⟩

theorem finiteIdempotenceLaw_map :
    finiteIdempotenceLaw.map Fin.val = idempotenceLaw := rfl

theorem finiteR3Law_map :
    finiteR3Law.map Fin.val = r3Law := rfl

set_option maxRecDepth 100000 in
theorem basis_models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← finiteIdempotenceLaw_map]
    exact table.checkIdentityNat_sound finiteIdempotenceLaw (by decide)
  · rw [← finiteR3Law_map]
    exact table.checkIdentityNat_sound finiteR3Law (by decide)

end SemigroupBasis.CoRoots.Order6FennemoreR3Band
