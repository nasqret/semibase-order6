import SemigroupBasis.CoRoots.S5_530Normalization
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.Order6S6_5654SelectiveCubeTraceV2

open SemigroupBasis

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- The exact zero-based Smallsemi table `S6_5654`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 1 right else
      if left = 2 then row6 0 0 0 1 2 2 right else
        if left = 3 then row6 0 0 0 1 2 3 right else
          if left = 4 then row6 0 1 2 3 4 4 right else
            row6 0 1 2 3 4 5 right

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
       [1, 1, 1, 1, 1, 2],
       [1, 1, 1, 2, 3, 3],
       [1, 1, 1, 2, 3, 4],
       [1, 2, 3, 4, 5, 5],
       [1, 2, 3, 4, 5, 6]] := by
  decide

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xxxyyy : Word Nat := w 0 [0, 0, 1, 1, 1]
def xxyyyx : Word Nat := w 0 [0, 1, 1, 1, 0]

def powerLaw : Identity Nat := ⟨xxx, xxxx⟩
def rightGatherLaw : Identity Nat := ⟨xyx, yxx⟩
def cubeTraceLaw : Identity Nat := ⟨xxxyyy, xxyyyx⟩

/-- The certified selective cube-trace basis in catalogue orientation. -/
def basis : List (Identity Nat) :=
  [powerLaw, rightGatherLaw, cubeTraceLaw]

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteRightGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteCubeTraceLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1, 1, 1]⟩, ⟨0, [0, 1, 1, 1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem finiteRightGatherLaw_map :
    finiteRightGatherLaw.map Fin.val = rightGatherLaw := rfl

theorem finiteCubeTraceLaw_map :
    finiteCubeTraceLaw.map Fin.val = cubeTraceLaw := rfl

theorem basis_models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteRightGatherLaw_map]
    exact table.checkIdentityNat_sound finiteRightGatherLaw (by decide)
  · rw [← finiteCubeTraceLaw_map]
    exact table.checkIdentityNat_sound finiteCubeTraceLaw (by decide)

end SemigroupBasis.CoRoots.Order6S6_5654SelectiveCubeTraceV2
