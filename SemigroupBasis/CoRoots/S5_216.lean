import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_216

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def xyy : Word Nat := w 0 [1, 1]
def xyz : Word Nat := w 0 [1, 2]
def xzy : Word Nat := w 0 [2, 1]
def xyzt : Word Nat := w 0 [1, 2, 3]
def xxxx : Word Nat := w 0 [0, 0, 0]

def firstRepeatMiddleLaw : Identity Nat := ⟨xxy, xyx⟩
def firstRepeatTailLaw : Identity Nat := ⟨xxy, xyy⟩
def tailCommutationLaw : Identity Nat := ⟨xyz, xzy⟩
def longToHeadFourthLaw : Identity Nat := ⟨xyzt, xxxx⟩

/-- The exact ordered four-law basis recorded for catalogue class `S5_216`.
No unrestricted normal-form or completeness theorem is asserted here. -/
def basis : List (Identity Nat) :=
  [firstRepeatMiddleLaw, firstRepeatTailLaw, tailCommutationLaw,
    longToHeadFourthLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

/- Definitions for the planned head/content/length proof. The left-zero
factor records the head, while the `C_{4,1}` factor records capped length and
the short-word support information. The length-three derivational branch is
deliberately not asserted by this source. -/
namespace DirectCompletenessArchitecture

inductive LengthState where
  | one
  | two
  | three
  | long
deriving DecidableEq, Repr

/-- Length one, two, three, or at least four. -/
def lengthState (word : Word Nat) : LengthState :=
  match word.tail.length with
  | 0 => .one
  | 1 => .two
  | 2 => .three
  | _ => .long

def SameSupport (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

def IsLengthThree (word : Word Nat) : Prop :=
  lengthState word = .three

def IsLong (word : Word Nat) : Prop :=
  lengthState word = .long

/-- The semantic signature suggested by the two finite separating factors.
The structure only names the future proof interface; no theorem says that the
basis derives all pairs carrying this signature. -/
structure SameHeadContentLengthSignature
    (left right : Word Nat) : Prop where
  head : left.head = right.head
  state : lengthState left = lengthState right
  lengthOne :
    lengthState left = .one → left.toList = right.toList
  lengthTwo :
    lengthState left = .two → left.toList = right.toList
  lengthThreeSupport :
    lengthState left = .three → SameSupport left right

end DirectCompletenessArchitecture

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Exhaustive checks on the four displayed variables imply the corresponding
`Models` theorem over natural-number variables. -/
theorem models_of_finite_checks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

abbrev table : FiniteTable :=
  Generated.Catalogue.S5_216.table

set_option maxRecDepth 100000 in
/-- The generated catalogue representative satisfies the four recorded laws. -/
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/-- The opposite representative satisfies the literal reversed laws. -/
theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

private def instantiateFourWords
    (u v z t : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

private theorem basisFirstRepeatMiddle :
    Derives basis xxy xyx :=
  Derives.fromBasis (e := firstRepeatMiddleLaw) <| by simp [basis]

private theorem basisFirstRepeatTail :
    Derives basis xxy xyy :=
  Derives.fromBasis (e := firstRepeatTailLaw) <| by simp [basis]

private theorem basisTailCommutation :
    Derives basis xyz xzy :=
  Derives.fromBasis (e := tailCommutationLaw) <| by simp [basis]

private theorem basisLongToHeadFourth :
    Derives basis xyzt xxxx :=
  Derives.fromBasis (e := longToHeadFourthLaw) <| by simp [basis]

/-- Direct block substitution in `xxy = xyx`. -/
theorem derivesFirstRepeatToMiddle (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v) ((u ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisFirstRepeatMiddle
      (instantiateFourWords u v v v)
  simpa [firstRepeatMiddleLaw, xxy, xyx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in `xxy = xyy`. -/
theorem derivesFirstRepeatToTail (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v) ((u ++ v) ++ v) := by
  have substituted :=
    Derives.subst basisFirstRepeatTail
      (instantiateFourWords u v v v)
  simpa [firstRepeatTailLaw, xxy, xyy, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Direct block substitution in `xyz = xzy`. -/
theorem derivesTailSwap (u v z : Word Nat) :
    Derives basis ((u ++ v) ++ z) ((u ++ z) ++ v) := by
  have substituted :=
    Derives.subst basisTailCommutation
      (instantiateFourWords u v z z)
  simpa [tailCommutationLaw, xyz, xzy, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- One substitution in `xyzt = xxxx` collapses four nonempty blocks to four
copies of the first block. Taking `u` to be the singleton head and `t` to be
the remaining nonempty suffix is the planned long-word normalization step. -/
theorem derivesLongToHeadFourth (u v z t : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ t)
      (((u ++ u) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisLongToHeadFourth
      (instantiateFourWords u v z t)
  simpa [longToHeadFourthLaw, xyzt, xxxx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

end SemigroupBasis.CoRoots.S5_216
