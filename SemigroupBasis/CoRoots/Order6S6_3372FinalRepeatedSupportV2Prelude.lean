import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.CoRoots.Order6S6_3372FinalRepeatedSupportV2

open SemigroupBasis

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- The exact zero-based Smallsemi table `S6_3372`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 0 0 right else
        if left = 3 then row6 0 0 1 0 0 0 right else
          if left = 4 then row6 0 1 0 3 4 5 right else
            row6 0 1 1 3 4 5 right

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
       [1, 1, 1, 1, 1, 1],
       [1, 1, 1, 1, 1, 1],
       [1, 1, 2, 1, 1, 1],
       [1, 2, 1, 4, 5, 6],
       [1, 2, 2, 4, 5, 6]] := by
  decide

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyz : Word Nat := w 0 [1, 2]
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyx : Word Nat := w 0 [1, 0]
def xyyx : Word Nat := w 0 [1, 1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def eraseSquareLaw : Identity Nat := ⟨xxyz, xyz⟩
def repeatFinalLaw : Identity Nat := ⟨xyx, xyyx⟩
def gatherFinalLaw : Identity Nat := ⟨xyx, yxx⟩
def guardedSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩

/-- The exact accepted basis in catalogue orientation. -/
def basis : List (Identity Nat) :=
  [powerLaw, eraseSquareLaw, repeatFinalLaw, gatherFinalLaw, guardedSwapLaw]

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteEraseSquareLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def finiteRepeatFinalLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteGatherFinalLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteGuardedSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem finiteEraseSquareLaw_map :
    finiteEraseSquareLaw.map Fin.val = eraseSquareLaw := rfl

theorem finiteRepeatFinalLaw_map :
    finiteRepeatFinalLaw.map Fin.val = repeatFinalLaw := rfl

theorem finiteGatherFinalLaw_map :
    finiteGatherFinalLaw.map Fin.val = gatherFinalLaw := rfl

theorem finiteGuardedSwapLaw_map :
    finiteGuardedSwapLaw.map Fin.val = guardedSwapLaw := rfl

theorem basis_models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteEraseSquareLaw_map]
    exact table.checkIdentityNat_sound finiteEraseSquareLaw (by
      set_option maxRecDepth 10000 in
        decide)
  · rw [← finiteRepeatFinalLaw_map]
    exact table.checkIdentityNat_sound finiteRepeatFinalLaw (by decide)
  · rw [← finiteGatherFinalLaw_map]
    exact table.checkIdentityNat_sound finiteGatherFinalLaw (by decide)
  · rw [← finiteGuardedSwapLaw_map]
    exact table.checkIdentityNat_sound finiteGuardedSwapLaw (by
      set_option maxRecDepth 10000 in
        decide)

end SemigroupBasis.CoRoots.Order6S6_3372FinalRepeatedSupportV2
