import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.CoRoots.Order6S6_14934FinalSortedPeriod3

open SemigroupBasis

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- The exact zero-based Smallsemi table `S6_14934`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 4 5 right else
    if left = 1 then row6 0 0 0 0 4 5 right else
      if left = 2 then row6 0 1 2 3 4 5 right else
        if left = 3 then row6 0 1 2 3 4 5 right else
          if left = 4 then row6 4 4 4 4 5 0 right else
            row6 5 5 5 5 0 4 right

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
      [[1, 1, 1, 1, 5, 6],
       [1, 1, 1, 1, 5, 6],
       [1, 2, 3, 4, 5, 6],
       [1, 2, 3, 4, 5, 6],
       [5, 5, 5, 5, 6, 1],
       [6, 6, 6, 6, 1, 5]] := by
  decide

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxxx : Word Nat := w 0 [0, 0, 0, 0]
def xxxxy : Word Nat := w 0 [0, 0, 0, 1]
def xy : Word Nat := w 0 [1]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xyz : Word Nat := w 0 [1, 2]
def yxz : Word Nat := w 1 [0, 2]

def powerLaw : Identity Nat := ⟨xx, xxxxx⟩
def tailPeriodLaw : Identity Nat := ⟨xxxxy, xy⟩
def gatherLaw : Identity Nat := ⟨xyx, yxx⟩
def prefixSwapLaw : Identity Nat := ⟨xyz, yxz⟩

/-- The exact accepted basis in catalogue orientation. -/
def basis : List (Identity Nat) :=
  [powerLaw, tailPeriodLaw, gatherLaw, prefixSwapLaw]

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0, 0]⟩⟩

def finiteTailPeriodLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 0, 1]⟩, ⟨0, [1]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finitePrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem finiteTailPeriodLaw_map :
    finiteTailPeriodLaw.map Fin.val = tailPeriodLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = gatherLaw := rfl

theorem finitePrefixSwapLaw_map :
    finitePrefixSwapLaw.map Fin.val = prefixSwapLaw := rfl

theorem basis_models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteTailPeriodLaw_map]
    exact table.checkIdentityNat_sound finiteTailPeriodLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact table.checkIdentityNat_sound finiteGatherLaw (by decide)
  · rw [← finitePrefixSwapLaw_map]
    exact table.checkIdentityNat_sound finitePrefixSwapLaw (by decide)

end SemigroupBasis.CoRoots.Order6S6_14934FinalSortedPeriod3
