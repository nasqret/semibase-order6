import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_215

open SemigroupBasis

def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xy : Word Nat := w 0 [1]
def yx : Word Nat := w 1 [0]
def xxy : Word Nat := w 0 [0, 1]
def xyy : Word Nat := w 0 [1, 1]
def xyzt : Word Nat := w 0 [1, 2, 3]
def xxyzt : Word Nat := w 0 [0, 1, 2, 3]

def commutativityLaw : Identity Nat := ⟨xy, yx⟩
def transferLaw : Identity Nat := ⟨xxy, xyy⟩

/-- The two-law basis candidate recorded for `S5_215` and inherited by
`S5_221` in the authoritative lower-order ledger. -/
def basis : List (Identity Nat) :=
  [commutativityLaw, transferLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

/-- A valid family identity that the recorded two-law candidate cannot
derive. It is the first square-free obstruction to the proposed
support-and-truncated-degree normal form. -/
def squarefreeInsertionLaw : Identity Nat :=
  ⟨xyzt, xxyzt⟩

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def finiteTransferLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 1]⟩⟩

def finiteSquarefreeInsertionLaw : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 3]⟩, ⟨0, [0, 1, 2, 3]⟩⟩

/-- The repaired candidate obtained by adjoining the first square-free
obstruction to the recorded two-law list. -/
def correctedBasis : List (Identity Nat) :=
  [commutativityLaw, transferLaw, squarefreeInsertionLaw]

def correctedOppositeBasis : List (Identity Nat) :=
  reversedBasis correctedBasis

theorem finiteCommutativityLaw_map :
    finiteCommutativityLaw.map Fin.val = commutativityLaw := rfl

theorem finiteTransferLaw_map :
    finiteTransferLaw.map Fin.val = transferLaw := rfl

theorem finiteSquarefreeInsertionLaw_map :
    finiteSquarefreeInsertionLaw.map Fin.val =
      squarefreeInsertionLaw := rfl

/-- Lift exhaustive checks of all three repaired laws to natural-number
variables. -/
theorem correctedModels_of_finite_checks
    (table : FiniteTable)
    (commutativityChecked :
      table.checkIdentity finiteCommutativityLaw = true)
    (transferChecked :
      table.checkIdentity finiteTransferLaw = true)
    (squarefreeInsertionChecked :
      table.checkIdentity finiteSquarefreeInsertionLaw = true) :
    Models table.semigroup correctedBasis := by
  intro identity member
  simp only [correctedBasis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [← finiteCommutativityLaw_map]
    exact table.checkIdentityNat_sound finiteCommutativityLaw
      commutativityChecked
  · rw [← finiteTransferLaw_map]
    exact table.checkIdentityNat_sound finiteTransferLaw transferChecked
  · rw [← finiteSquarefreeInsertionLaw_map]
    exact table.checkIdentityNat_sound finiteSquarefreeInsertionLaw
      squarefreeInsertionChecked

/-- Lift exhaustive checks of the two finite-variable laws to the
repository's natural-number variable type. -/
theorem models_of_finite_checks
    (table : FiniteTable)
    (commutativityChecked :
      table.checkIdentity finiteCommutativityLaw = true)
    (transferChecked :
      table.checkIdentity finiteTransferLaw = true) :
    Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← finiteCommutativityLaw_map]
    exact table.checkIdentityNat_sound finiteCommutativityLaw
      commutativityChecked
  · rw [← finiteTransferLaw_map]
    exact table.checkIdentityNat_sound finiteTransferLaw transferChecked

/-- Lift the exhaustive four-variable obstruction check. -/
theorem squarefreeInsertion_valid_of_check
    (table : FiniteTable)
    (checked :
      table.checkIdentity finiteSquarefreeInsertionLaw = true) :
    squarefreeInsertionLaw.SatisfiedBy table.semigroup := by
  rw [← finiteSquarefreeInsertionLaw_map]
  exact table.checkIdentityNat_sound finiteSquarefreeInsertionLaw checked

/-- Multiplication on nonempty subsets of a four-element set, represented
by bit masks `1` through `15`, with `0` as an absorbing collision element.
Disjoint supports multiply to their union; overlapping supports multiply
to zero. -/
def squareFreeSupportMul (a b : Fin 16) : Fin 16 :=
  if a = 0 then 0
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 3
    else if b = 3 then 0 else if b = 4 then 5 else if b = 5 then 0
    else if b = 6 then 7 else if b = 7 then 0 else if b = 8 then 9
    else if b = 9 then 0 else if b = 10 then 11 else if b = 11 then 0
    else if b = 12 then 13 else if b = 13 then 0
    else if b = 14 then 15 else 0
  else if a = 2 then
    if b = 0 then 0 else if b = 1 then 3 else if b = 2 then 0
    else if b = 3 then 0 else if b = 4 then 6 else if b = 5 then 7
    else if b = 6 then 0 else if b = 7 then 0 else if b = 8 then 10
    else if b = 9 then 11 else if b = 10 then 0 else if b = 11 then 0
    else if b = 12 then 14 else if b = 13 then 15 else 0
  else if a = 3 then
    if b = 4 then 7 else if b = 8 then 11 else if b = 12 then 15 else 0
  else if a = 4 then
    if b = 0 then 0 else if b = 1 then 5 else if b = 2 then 6
    else if b = 3 then 7 else if b = 4 then 0 else if b = 5 then 0
    else if b = 6 then 0 else if b = 7 then 0 else if b = 8 then 12
    else if b = 9 then 13 else if b = 10 then 14 else if b = 11 then 15
    else 0
  else if a = 5 then
    if b = 2 then 7 else if b = 8 then 13 else if b = 10 then 15 else 0
  else if a = 6 then
    if b = 1 then 7 else if b = 8 then 14 else if b = 9 then 15 else 0
  else if a = 7 then
    if b = 8 then 15 else 0
  else if a = 8 then
    if b = 0 then 0 else if b = 1 then 9 else if b = 2 then 10
    else if b = 3 then 11 else if b = 4 then 12 else if b = 5 then 13
    else if b = 6 then 14 else if b = 7 then 15 else 0
  else if a = 9 then
    if b = 2 then 11 else if b = 4 then 13 else if b = 6 then 15 else 0
  else if a = 10 then
    if b = 1 then 11 else if b = 4 then 14 else if b = 5 then 15 else 0
  else if a = 11 then
    if b = 4 then 15 else 0
  else if a = 12 then
    if b = 1 then 13 else if b = 2 then 14 else if b = 3 then 15 else 0
  else if a = 13 then
    if b = 2 then 15 else 0
  else if a = 14 then
    if b = 1 then 15 else 0
  else 0

def squareFreeSupportTable : FiniteTable where
  order := 16
  mul := squareFreeSupportMul
  assoc := by decide

theorem squareFreeSupportModels :
    Models squareFreeSupportTable.semigroup basis :=
  models_of_finite_checks squareFreeSupportTable (by decide) (by decide)

def squareFreeValuation : Nat → Fin 16
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | _ => 1

theorem squareFreeSupportLeftValue :
    squareFreeSupportTable.semigroup.eval squareFreeValuation xyzt =
      (⟨15, by decide⟩ : Fin 16) := by
  decide

theorem squareFreeSupportRightValue :
    squareFreeSupportTable.semigroup.eval squareFreeValuation xxyzt =
      (⟨0, by decide⟩ : Fin 16) := by
  decide

theorem squareFreeSupportSeparates :
    squareFreeSupportTable.semigroup.eval squareFreeValuation xyzt ≠
      squareFreeSupportTable.semigroup.eval squareFreeValuation xxyzt := by
  decide

/-- The square-free insertion identity is not derivable from the recorded
two laws. This is an unconditional source-level obstruction theorem. -/
theorem squarefreeInsertion_not_derivable :
    ¬ Derives basis squarefreeInsertionLaw.lhs
      squarefreeInsertionLaw.rhs := by
  intro derived
  exact squareFreeSupportSeparates
    (derived.sound squareFreeSupportModels squareFreeValuation)

/-- Any semigroup validating the square-free insertion identity cannot
have the recorded two-law list as a complete basis. -/
theorem not_basisFor_of_squarefreeInsertion
    {S : Type u} (G : Semigroup S)
    (valid : squarefreeInsertionLaw.SatisfiedBy G) :
    ¬ BasisFor G basis := by
  intro complete
  exact squarefreeInsertion_not_derivable
    (complete.2 squarefreeInsertionLaw valid)

theorem reversedSquarefreeInsertion_not_derivable :
    ¬ Derives oppositeBasis squarefreeInsertionLaw.reversed.lhs
      squarefreeInsertionLaw.reversed.rhs := by
  intro derived
  apply squarefreeInsertion_not_derivable
  simpa [oppositeBasis, Identity.reversed] using derived.reverse

theorem not_oppositeBasisFor_of_squarefreeInsertion
    {S : Type u} (G : Semigroup S)
    (valid : squarefreeInsertionLaw.SatisfiedBy G) :
    ¬ BasisFor G.opposite oppositeBasis := by
  intro complete
  have reversedValid :
      squarefreeInsertionLaw.reversed.SatisfiedBy G.opposite :=
    (Identity.satisfiedBy_opposite_iff_reversed
      squarefreeInsertionLaw.reversed G).mpr (by simpa using valid)
  exact reversedSquarefreeInsertion_not_derivable
    (complete.2 squarefreeInsertionLaw.reversed reversedValid)

end SemigroupBasis.CoRoots.S5_215
