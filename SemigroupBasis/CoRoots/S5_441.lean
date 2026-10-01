import SemigroupBasis.Examples.CommutativeParityThree
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.Examples.UniqueSeparatorFour
import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis
open SemigroupBasis.Examples

def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xxyxx : Word Nat := w 0 [0, 1, 0, 0]
def xxyyy : Word Nat := w 0 [0, 1, 1, 1]
def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
def xyxyy : Word Nat := w 0 [1, 0, 1, 1]
def xyyxy : Word Nat := w 0 [1, 1, 0, 1]
def xyyyx : Word Nat := w 0 [1, 1, 1, 0]
def yxxyy : Word Nat := w 1 [0, 0, 1, 1]
def yxyxy : Word Nat := w 1 [0, 1, 0, 1]
def yxyyx : Word Nat := w 1 [0, 1, 1, 0]
def yyxxy : Word Nat := w 1 [1, 0, 0, 1]
def yyxyx : Word Nat := w 1 [1, 0, 1, 0]
def yyyxx : Word Nat := w 1 [1, 1, 0, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def yxyy : Word Nat := w 1 [0, 1, 1]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xxyzx : Word Nat := w 0 [0, 1, 2, 0]
def yxyzy : Word Nat := w 1 [0, 1, 2, 1]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xzxyy : Word Nat := w 0 [2, 0, 1, 1]
def yxxzy : Word Nat := w 1 [0, 0, 2, 1]

def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def xyxXXXYXLaw : Identity Nat := ⟨xyx, xxxyx⟩
def xyxXXYXXLaw : Identity Nat := ⟨xyx, xxyxx⟩
def xyxXXYYYLaw : Identity Nat := ⟨xyx, xxyyy⟩
def xyxXYXXXLaw : Identity Nat := ⟨xyx, xyxxx⟩
def xyxXYXYYLaw : Identity Nat := ⟨xyx, xyxyy⟩
def xyxXYYXYLaw : Identity Nat := ⟨xyx, xyyxy⟩
def xyxXYYYXLaw : Identity Nat := ⟨xyx, xyyyx⟩
def xyxYXXYYLaw : Identity Nat := ⟨xyx, yxxyy⟩
def xyxYXYXYLaw : Identity Nat := ⟨xyx, yxyxy⟩
def xyxYXYYXLaw : Identity Nat := ⟨xyx, yxyyx⟩
def xyxYYXXYLaw : Identity Nat := ⟨xyx, yyxxy⟩
def xyxYYXYXLaw : Identity Nat := ⟨xyx, yyxyx⟩
def xyxYYYXXLaw : Identity Nat := ⟨xyx, yyyxx⟩
def xxyxXYXXLaw : Identity Nat := ⟨xxyx, xyxx⟩
def xxyxYXYYLaw : Identity Nat := ⟨xxyx, yxyy⟩
def xxyyXYXYLaw : Identity Nat := ⟨xxyy, xyxy⟩
def xxyyXYYXLaw : Identity Nat := ⟨xxyy, xyyx⟩
def xxyyYXXYLaw : Identity Nat := ⟨xxyy, yxxy⟩
def xyzxXZYXLaw : Identity Nat := ⟨xyzx, xzyx⟩
def xxyzxYXYZYLaw : Identity Nat := ⟨xxyzx, yxyzy⟩
def xxyzyXYXZYLaw : Identity Nat := ⟨xxyzy, xyxzy⟩
def xxyzyXYYZXLaw : Identity Nat := ⟨xxyzy, xyyzx⟩
def xxyzyXZXYYLaw : Identity Nat := ⟨xxyzy, xzxyy⟩
def xxyzyYXXZYLaw : Identity Nat := ⟨xxyzy, yxxzy⟩

/-- The common ordered 25-identity basis of `S5_441`, `S5_464`, and
`S5_612`. -/
def basis : List (Identity Nat) :=
  [powerLaw,
    xyxXXXYXLaw, xyxXXYXXLaw, xyxXXYYYLaw, xyxXYXXXLaw,
    xyxXYXYYLaw, xyxXYYXYLaw, xyxXYYYXLaw, xyxYXXYYLaw,
    xyxYXYXYLaw, xyxYXYYXLaw, xyxYYXXYLaw, xyxYYXYXLaw,
    xyxYYYXXLaw, xxyxXYXXLaw, xxyxYXYYLaw, xxyyXYXYLaw,
    xxyyXYYXLaw, xxyyYXXYLaw, xyzxXZYXLaw,
    xxyzxYXYZYLaw, xxyzyXYXZYLaw, xxyzyXYYZXLaw,
    xxyzyXZXYYLaw, xxyzyYXXZYLaw]

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

private theorem uniqueSeparatorFour_finiteBasis_checked :
    finiteBasis.all uniqueSeparatorFour.checkIdentity = true := by
  decide

theorem basis_models_uniqueSeparatorFour :
    Models uniqueSeparatorFour.semigroup basis :=
  models_of_finite_checks uniqueSeparatorFour
    uniqueSeparatorFour_finiteBasis_checked

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

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem bind_append (u v : Word Nat) (sigma : Nat → Word Nat) :
    (u ++ v).bind sigma = u.bind sigma ++ v.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (tau sigma : Nat → Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun x => (tau x).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Add or remove two copies of an arbitrary nonempty block between matching
nonempty envelope blocks. -/
theorem derivesEnvelopePower (envelope block : Word Nat) :
    Derives basis
      ((envelope ++ block) ++ envelope)
      ((((envelope ++ block) ++ block) ++ block) ++ envelope) := by
  have base :
      Derives basis xyx xyyyx :=
    Derives.fromBasis (e := xyxXYYYXLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords envelope block block)
  simpa [xyxXYYYXLaw, xyx, xyyyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Add or remove a parity-neutral pair of the left envelope block. -/
theorem derivesLeftEnvelopePower (envelope middle : Word Nat) :
    Derives basis
      ((envelope ++ middle) ++ envelope)
      ((((envelope ++ envelope) ++ envelope) ++ middle) ++ envelope) := by
  have base :
      Derives basis xyx xxxyx :=
    Derives.fromBasis (e := xyxXXXYXLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords envelope middle middle)
  simpa [xyxXXXYXLaw, xyx, xxxyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Add or remove a parity-neutral pair of the right envelope block. -/
theorem derivesRightEnvelopePower (envelope middle : Word Nat) :
    Derives basis
      ((envelope ++ middle) ++ envelope)
      ((((envelope ++ middle) ++ envelope) ++ envelope) ++ envelope) := by
  have base :
      Derives basis xyx xyxxx :=
    Derives.fromBasis (e := xyxXYXXXLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords envelope middle middle)
  simpa [xyxXYXXXLaw, xyx, xyxxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesXYYXY (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((x ++ y) ++ y) ++ x) ++ y) := by
  have base :
      Derives basis xyx xyyxy :=
    Derives.fromBasis (e := xyxXYYXYLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xyxXYYXYLaw, xyx, xyyxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesYXYXY (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((y ++ x) ++ y) ++ x) ++ y) := by
  have base :
      Derives basis xyx yxyxy :=
    Derives.fromBasis (e := xyxYXYXYLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xyxYXYXYLaw, xyx, yxyxy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Arbitrary adjacent nonempty blocks may be transposed between matching
nonempty envelope blocks. -/
theorem derivesInteriorSwap
    (envelope left right : Word Nat) :
    Derives basis
      (((envelope ++ left) ++ right) ++ envelope)
      (((envelope ++ right) ++ left) ++ envelope) := by
  have base :
      Derives basis xyzx xzyx :=
    Derives.fromBasis (e := xyzxXZYXLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords envelope left right)
  simpa [xyzxXZYXLaw, xyzx, xzyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Four adjacent copies of a nonempty block may be contracted to two, and
vice versa, in arbitrary outer contexts. -/
theorem derivesBlockSquarePower (block : Word Nat) :
    Derives basis
      (block ++ block)
      (((block ++ block) ++ block) ++ block) := by
  have base :
      Derives basis xx xxxx :=
    Derives.fromBasis (e := powerLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords block block block)
  simpa [powerLaw, xx, xxxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Replay a derivation under a substitution. This small public wrapper keeps
later normalization modules independent of the private substitution helper. -/
theorem derivesSubstitution
    {left right : Word Nat}
    (derivation : Derives basis left right)
    (sigma : Nat → Word Nat) :
    Derives basis (left.bind sigma) (right.bind sigma) :=
  Derives.subst derivation sigma

end SemigroupBasis.CoRoots.S5_441
