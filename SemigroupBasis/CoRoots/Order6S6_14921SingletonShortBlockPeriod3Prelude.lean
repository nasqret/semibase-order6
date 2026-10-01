import SemigroupBasis.CoRoots.S5_530Normalization
import SemigroupBasis.Examples.CommutativePeriodThreeFromTwo
import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.CoRoots.Order6S6_14921SingletonShortBlockPeriod3

open SemigroupBasis

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- The exact zero-based Smallsemi table `S6_14921`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 1 1 1 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 0 0 2 3 4 5 right else
          if left = 4 then row6 0 0 2 4 5 3 right else
            row6 0 0 2 5 3 4 right

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
       [1, 1, 1, 2, 2, 2],
       [3, 3, 3, 3, 3, 3],
       [1, 1, 3, 4, 5, 6],
       [1, 1, 3, 5, 6, 4],
       [1, 1, 3, 6, 4, 5]] := by
  decide

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxxx : Word Nat := w 0 [0, 0, 0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def xy : Word Nat := w 0 [1]
def xyyyy : Word Nat := w 0 [1, 1, 1, 1]

def powerLaw : Identity Nat := ⟨xx, xxxxx⟩
def gatherLaw : Identity Nat := ⟨xxy, xyx⟩
def tailLaw : Identity Nat := ⟨xy, xyyyy⟩

/-- The exact accepted basis in catalogue orientation. -/
def basis : List (Identity Nat) :=
  [powerLaw, gatherLaw, tailLaw]

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def finiteTailLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1, 1, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = gatherLaw := rfl

theorem finiteTailLaw_map :
    finiteTailLaw.map Fin.val = tailLaw := rfl

theorem basis_models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact table.checkIdentityNat_sound finiteGatherLaw (by decide)
  · rw [← finiteTailLaw_map]
    exact table.checkIdentityNat_sound finiteTailLaw (by decide)

end SemigroupBasis.CoRoots.Order6S6_14921SingletonShortBlockPeriod3
