import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier

open SemigroupBasis

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- The exact zero-based Smallsemi table `S6_14897`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 2 3 4 5 right else
    if left = 1 then row6 1 0 3 2 5 4 right else
      if left = 2 then row6 2 4 2 2 4 4 right else
        if left = 3 then row6 3 5 3 3 5 5 right else
          if left = 4 then row6 4 2 2 2 4 4 right else
            row6 5 3 3 3 5 5 right

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
      [[1, 2, 3, 4, 5, 6],
       [2, 1, 4, 3, 6, 5],
       [3, 5, 3, 3, 5, 5],
       [4, 6, 4, 4, 6, 6],
       [5, 3, 3, 3, 5, 5],
       [6, 4, 4, 4, 6, 6]] := by
  decide

def x : Word Nat := Word.singleton 0
def xxx : Word Nat := ⟨0, [0, 0]⟩

def powerLaw : Identity Nat := ⟨x, xxx⟩

/-- The recorded one-identity candidate `x = xxx`. -/
def basis : List (Identity Nat) := [powerLaw]

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem basis_models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  rw [← finitePowerLaw_map]
  exact table.checkIdentityNat_sound finitePowerLaw (by decide)

end SemigroupBasis.CoRoots.Order6S6_14897InvolutoryBarrier
