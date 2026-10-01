import SemigroupBasis.Examples.CommutativeParityThree
import SemigroupBasis.Examples.ConnectedComponentFourFinal
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_442

open SemigroupBasis
open SemigroupBasis.Examples

def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xxyxx : Word Nat := w 0 [0, 1, 0, 0]
def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
def xyxyy : Word Nat := w 0 [1, 0, 1, 1]
def xyyxy : Word Nat := w 0 [1, 1, 0, 1]
def xyyyx : Word Nat := w 0 [1, 1, 1, 0]
def yxxyy : Word Nat := w 1 [0, 0, 1, 1]
def yxyxy : Word Nat := w 1 [0, 1, 0, 1]
def yxyyx : Word Nat := w 1 [0, 1, 1, 0]
def yyxxy : Word Nat := w 1 [1, 0, 0, 1]
def yyxyx : Word Nat := w 1 [1, 0, 1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def yxyy : Word Nat := w 1 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xxyzx : Word Nat := w 0 [0, 1, 2, 0]
def yxyzy : Word Nat := w 1 [0, 1, 2, 1]
def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def yxxzy : Word Nat := w 1 [0, 0, 2, 1]

def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def xyxXXXYXLaw : Identity Nat := ⟨xyx, xxxyx⟩
def xyxXXYXXLaw : Identity Nat := ⟨xyx, xxyxx⟩
def xyxXYXXXLaw : Identity Nat := ⟨xyx, xyxxx⟩
def xyxXYXYYLaw : Identity Nat := ⟨xyx, xyxyy⟩
def xyxXYYXYLaw : Identity Nat := ⟨xyx, xyyxy⟩
def xyxXYYYXLaw : Identity Nat := ⟨xyx, xyyyx⟩
def xyxYXXYYLaw : Identity Nat := ⟨xyx, yxxyy⟩
def xyxYXYXYLaw : Identity Nat := ⟨xyx, yxyxy⟩
def xyxYXYYXLaw : Identity Nat := ⟨xyx, yxyyx⟩
def xyxYYXXYLaw : Identity Nat := ⟨xyx, yyxxy⟩
def xyxYYXYXLaw : Identity Nat := ⟨xyx, yyxyx⟩
def xxyxXYXXLaw : Identity Nat := ⟨xxyx, xyxx⟩
def xxyxYXYYLaw : Identity Nat := ⟨xxyx, yxyy⟩
def xyxyXYYXLaw : Identity Nat := ⟨xyxy, xyyx⟩
def xyxyYXXYLaw : Identity Nat := ⟨xyxy, yxxy⟩
def xyzxXZYXLaw : Identity Nat := ⟨xyzx, xzyx⟩
def xxyzxYXYZYLaw : Identity Nat := ⟨xxyzx, yxyzy⟩
def xyxzyXYYZXLaw : Identity Nat := ⟨xyxzy, xyyzx⟩
def xyxzyYXXZYLaw : Identity Nat := ⟨xyxzy, yxxzy⟩

/-- The exact ordered 20-law basis recorded for `S5_442` and `S5_613`. -/
def basis : List (Identity Nat) :=
  [powerLaw,
    xyxXXXYXLaw, xyxXXYXXLaw, xyxXYXXXLaw, xyxXYXYYLaw,
    xyxXYYXYLaw, xyxXYYYXLaw, xyxYXXYYLaw, xyxYXYXYLaw,
    xyxYXYYXLaw, xyxYYXXYLaw, xyxYYXYXLaw, xxyxXYXXLaw,
    xxyxYXYYLaw, xyxyXYYXLaw, xyxyYXXYLaw, xyzxXZYXLaw,
    xxyzxYXYZYLaw, xyxzyXYYZXLaw, xyxzyYXXZYLaw]

/-- The explicit opposite orientation used for the non-self-dual endpoint. -/
def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

theorem basis_length : basis.length = 20 := by
  decide

theorem oppositeBasis_length : oppositeBasis.length = 20 := by
  decide

def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinThree).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

theorem models_of_finite_checks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

private theorem connectedComponentFour_finiteBasis_checked :
    finiteBasis.all connectedComponentFour.checkIdentity = true := by
  decide

theorem basis_models_connectedComponentFour :
    Models connectedComponentFour.semigroup basis :=
  models_of_finite_checks connectedComponentFour
    connectedComponentFour_finiteBasis_checked

private theorem cyclicTwo_finiteBasis_checked :
    finiteBasis.all cyclicTwo.checkIdentity = true := by
  decide

theorem basis_models_cyclicTwo :
    Models cyclicTwo.semigroup basis :=
  models_of_finite_checks cyclicTwo cyclicTwo_finiteBasis_checked

private theorem parityZeroThree_finiteBasis_checked :
    finiteBasis.all parityZeroThree.checkIdentity = true := by
  decide

theorem basis_models_parityZeroThree :
    Models parityZeroThree.semigroup basis :=
  models_of_finite_checks parityZeroThree
    parityZeroThree_finiteBasis_checked

end SemigroupBasis.CoRoots.S5_442
