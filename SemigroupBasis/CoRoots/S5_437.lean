import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_437

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xy : Word Nat := w 0 [1]
def xxxy : Word Nat := w 0 [0, 0, 1]
def xyx : Word Nat := w 0 [1, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xxyxx : Word Nat := w 0 [0, 1, 0, 0]
def xxyyy : Word Nat := w 0 [0, 1, 1, 1]
def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
def xyxyy : Word Nat := w 0 [1, 0, 1, 1]
def xyyxy : Word Nat := w 0 [1, 1, 0, 1]
def xyy : Word Nat := w 0 [1, 1]
def xxyxy : Word Nat := w 0 [0, 1, 0, 1]
def xxyyx : Word Nat := w 0 [0, 1, 1, 0]
def xyxxy : Word Nat := w 0 [1, 0, 0, 1]
def xyxyx : Word Nat := w 0 [1, 0, 1, 0]
def xyyxx : Word Nat := w 0 [1, 1, 0, 0]
def xyz : Word Nat := w 0 [1, 2]
def xxyxz : Word Nat := w 0 [0, 1, 0, 2]
def xyxxz : Word Nat := w 0 [1, 0, 0, 2]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xyyy : Word Nat := w 0 [1, 1, 1]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyxz : Word Nat := w 0 [1, 0, 2]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyy : Word Nat := w 0 [2, 1, 1]
def xxyzx : Word Nat := w 0 [0, 1, 2, 0]
def xyyzy : Word Nat := w 0 [1, 1, 2, 1]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xxyzz : Word Nat := w 0 [0, 1, 2, 2]
def xxyyzzy : Word Nat := w 0 [0, 1, 1, 2, 2, 1]
def xxxyzzx : Word Nat := w 0 [0, 0, 1, 2, 2, 0]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xzxyx : Word Nat := w 0 [2, 0, 1, 0]

def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def prefixParityLaw : Identity Nat := ⟨xy, xxxy⟩
def xyxXXYXXLaw : Identity Nat := ⟨xyx, xxyxx⟩
def xyxXXYYYLaw : Identity Nat := ⟨xyx, xxyyy⟩
def xyxXYXXXLaw : Identity Nat := ⟨xyx, xyxxx⟩
def xyxXYXYYLaw : Identity Nat := ⟨xyx, xyxyy⟩
def xyxXYYXYLaw : Identity Nat := ⟨xyx, xyyxy⟩
def xyyXXYXYLaw : Identity Nat := ⟨xyy, xxyxy⟩
def xyyXXYYXLaw : Identity Nat := ⟨xyy, xxyyx⟩
def xyyXYXXYLaw : Identity Nat := ⟨xyy, xyxxy⟩
def xyyXYXYXLaw : Identity Nat := ⟨xyy, xyxyx⟩
def xyyXYYXXLaw : Identity Nat := ⟨xyy, xyyxx⟩
def xyzXXYXZLaw : Identity Nat := ⟨xyz, xxyxz⟩
def xyzXYXXZLaw : Identity Nat := ⟨xyz, xyxxz⟩
def xxyxXYXXLaw : Identity Nat := ⟨xxyx, xyxx⟩
def xxyxXYYYLaw : Identity Nat := ⟨xxyx, xyyy⟩
def xxyyXYXYLaw : Identity Nat := ⟨xxyy, xyxy⟩
def xxyyXYYXLaw : Identity Nat := ⟨xxyy, xyyx⟩
def xxyzXYXZLaw : Identity Nat := ⟨xxyz, xyxz⟩
def xyzxXZYXLaw : Identity Nat := ⟨xyzx, xzyx⟩
def xyzyXZYYLaw : Identity Nat := ⟨xyzy, xzyy⟩
def xxyzxXYYZYLaw : Identity Nat := ⟨xxyzx, xyyzy⟩
def xxyzyXYYZXLaw : Identity Nat := ⟨xxyzy, xyyzx⟩

/-- The common ordered 23-identity basis candidate for
`S5_437`, `S5_460`, and `S5_575`. -/
def basis : List (Identity Nat) :=
  [powerLaw, prefixParityLaw, xyxXXYXXLaw, xyxXXYYYLaw,
    xyxXYXXXLaw, xyxXYXYYLaw, xyxXYYXYLaw, xyyXXYXYLaw,
    xyyXXYYXLaw, xyyXYXXYLaw, xyyXYXYXLaw, xyyXYYXXLaw,
    xyzXXYXZLaw, xyzXYXXZLaw, xxyxXYXXLaw, xxyxXYYYLaw,
    xxyyXYXYLaw, xxyyXYYXLaw, xxyzXYXZLaw, xyzxXZYXLaw,
    xyzyXZYYLaw, xxyzxXYYZYLaw, xxyzyXYYZXLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun e => e.map toFinThree

private theorem basis_roundTrip_checked :
    basis.all (fun e =>
      decide ((e.map toFinThree).map Fin.val = e)) = true := by
  decide

private theorem basis_roundTrip
    (e : Identity Nat) (member : e ∈ basis) :
    (e.map toFinThree).map Fin.val = e := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) e member

theorem models_of_finite_checks
    (T : FiniteTable)
    (checked : finiteBasis.all T.checkIdentity = true) :
    Models T.semigroup basis := by
  intro e member
  have finiteMember : e.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨e, member, rfl⟩
  have finiteValid :=
    T.checkIdentityNat_sound (e.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip e member] at finiteValid
  exact finiteValid

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisPower :
    Derives basis xx xxxx :=
  Derives.fromBasis (e := powerLaw) <| by
    simp [basis]

private theorem basisPrefixParity :
    Derives basis xy xxxy :=
  Derives.fromBasis (e := prefixParityLaw) <| by
    simp [basis]

private theorem basisEndpointTransfer :
    Derives basis xxyx xyxx :=
  Derives.fromBasis (e := xxyxXYXXLaw) <| by
    simp [basis]

private theorem basisTripleSuffixExpansion :
    Derives basis xyz xyxxz :=
  Derives.fromBasis (e := xyzXYXXZLaw) <| by
    simp [basis]

private theorem basisTailRotation :
    Derives basis xyzy xzyy :=
  Derives.fromBasis (e := xyzyXZYYLaw) <| by
    simp [basis]

private theorem basisFinalSwitch :
    Derives basis xxyy xyyx :=
  Derives.fromBasis (e := xxyyXYYXLaw) <| by
    simp [basis]

/-- The first Lee-system law `x^4 = x^2`. -/
theorem derivesLeePower :
    Derives basis xxxx xx :=
  Derives.symm basisPower

/-- The second Lee-system law `x^3 y x = x y x`. -/
theorem derivesLeeLeftContraction :
    Derives basis xxxyx xyx := by
  have expanded :=
    Derives.appendRight basisPrefixParity (Word.singleton 0)
  exact Derives.symm <| by
    simpa [xy, xxxy, xyx, xxxyx, w, Word.singleton, Word.append,
      Word.append_assoc] using expanded

/-- The third Lee-system law `x^2 y x = x y x^2`. -/
theorem derivesLeeEndpointTransfer :
    Derives basis xxyx xyxx :=
  basisEndpointTransfer

/-- First step of the fourth Lee-system derivation:
`xxyzz = xxyyzzy`. -/
private theorem derivesXxyzzXxyyzzy :
    Derives basis xxyzz xxyyzzy := by
  have base :
      Derives basis xyy xxyyx :=
    Derives.fromBasis (e := xyyXXYYXLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base
      (instantiateThreeWords
        (Word.singleton 1) (Word.singleton 2) (Word.singleton 2))
  have contextual :=
    Derives.prepend xx substituted
  simpa [xyyXXYYXLaw, xyy, xxyyx, xxyzz, xxyyzzy, xx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using contextual

/-- Second step of the fourth Lee-system derivation:
`xxyyzzy = xxxyzzx`. -/
private theorem derivesXxyyzzyXxxyzzx :
    Derives basis xxyyzzy xxxyzzx := by
  have base :
      Derives basis xyyzy xxyzx :=
    Derives.symm <|
      Derives.fromBasis (e := xxyzxXYYZYLaw) <| by
        simp [basis]
  have substituted :=
    Derives.subst base
      (instantiateThreeWords
        (Word.singleton 0) (Word.singleton 1) (w 2 [2]))
  have contextual :=
    Derives.prepend (Word.singleton 0) substituted
  simpa [xxyzxXYYZYLaw, xxyzx, xyyzy, xxyyzzy, xxxyzzx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using contextual

/-- Third step of the fourth Lee-system derivation:
`xxxyzzx = xyzzx`. -/
private theorem derivesXxxyzzxXyzzx :
    Derives basis xxxyzzx xyzzx := by
  have contextual :=
    Derives.appendRight
      (Derives.symm basisPrefixParity) (w 2 [2, 0])
  simpa [xy, xxxy, xxxyzzx, xyzzx, w, Word.singleton,
    Word.append, Word.append_assoc] using contextual

/-- The fourth Lee-system law `x^2 y z^2 = x y z^2 x`. -/
theorem derivesLeeSquareMove :
    Derives basis xxyzz xyzzx :=
  Derives.trans derivesXxyzzXxyyzzy <|
    Derives.trans derivesXxyyzzyXxxyzzx derivesXxxyzzxXyzzx

/-- First step of the fifth Lee-system derivation:
`xyxzx = xxyzx`. -/
private theorem derivesXyxzxXxyzx :
    Derives basis xyxzx xxyzx := by
  have base :
      Derives basis xyxz xxyz :=
    Derives.symm <|
      Derives.fromBasis (e := xxyzXYXZLaw) <| by
        simp [basis]
  have contextual :=
    Derives.appendRight base (Word.singleton 0)
  simpa [xxyzXYXZLaw, xxyz, xyxz, xyxzx, xxyzx, w,
    Word.singleton, Word.append, Word.append_assoc] using contextual

/-- Second step of the fifth Lee-system derivation:
`xxyzx = xzxyx`. -/
private theorem derivesXxyzxXzxyx :
    Derives basis xxyzx xzxyx := by
  have base :
      Derives basis xyzx xzyx :=
    Derives.fromBasis (e := xyzxXZYXLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base
      (instantiateThreeWords
        (Word.singleton 0) (w 0 [1]) (Word.singleton 2))
  simpa [xyzxXZYXLaw, xyzx, xzyx, xxyzx, xzxyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The fifth Lee-system law `xyxzx = xzxyx`. -/
theorem derivesLeeBlockSwap :
    Derives basis xyxzx xzxyx :=
  Derives.trans derivesXyxzxXxyzx derivesXxyzxXzxyx

/-- Lee's identity system `(8)`, in the order used by the normal-form proof. -/
def leeSystemEight : List (Identity Nat) :=
  [⟨xxxx, xx⟩, ⟨xxxyx, xyx⟩, ⟨xxyx, xyxx⟩,
    ⟨xxyzz, xyzzx⟩, ⟨xyxzx, xzxyx⟩]

theorem leeSystemEightAxiomsDerive
    (e : Identity Nat) (member : e ∈ leeSystemEight) :
    Derives basis e.lhs e.rhs := by
  simp only [leeSystemEight, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact derivesLeePower
  · exact derivesLeeLeftContraction
  · exact derivesLeeEndpointTransfer
  · exact derivesLeeSquareMove
  · exact derivesLeeBlockSwap

/-- Add two copies of a nonempty prefix block. -/
theorem derivesPrefixPairExpansion (u v : Word Nat) :
    Derives basis
      (u ++ v) (((u ++ u) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisPrefixParity
      (instantiateThreeWords u v v)
  simpa [xy, xxxy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Remove two copies of a nonempty prefix block. -/
theorem derivesPrefixPairContraction (u v : Word Nat) :
    Derives basis
      (((u ++ u) ++ u) ++ v) (u ++ v) :=
  Derives.symm (derivesPrefixPairExpansion u v)

/-- Add two copies of an arbitrary nonempty block. -/
theorem derivesTwoToFour (u : Word Nat) :
    Derives basis
      (u ++ u) (((u ++ u) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower
      (instantiateThreeWords u u u)
  simpa [xx, xxxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Remove two copies from a fourth power. -/
theorem derivesFourToTwo (u : Word Nat) :
    Derives basis
      (((u ++ u) ++ u) ++ u) (u ++ u) :=
  Derives.symm (derivesTwoToFour u)

/-- Move one copy of a repeated endpoint from the left to the right. -/
theorem derivesEndpointTransfer (u v : Word Nat) :
    Derives basis
      (((u ++ u) ++ v) ++ u)
      ((u ++ v) ++ (u ++ u)) := by
  have substituted :=
    Derives.subst basisEndpointTransfer
      (instantiateThreeWords u v v)
  simpa [xxyx, xyxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Arbitrary adjacent nonempty blocks may be transposed while nonempty
prefix and suffix contexts remain fixed. The three steps are
`PABQ = PAB³Q = PBAB²Q = PBAQ`. -/
theorem derivesInteriorSwap
    (leftContext left right rightContext : Word Nat) :
    Derives basis
      (((leftContext ++ left) ++ right) ++ rightContext)
      (((leftContext ++ right) ++ left) ++ rightContext) := by
  have expandRight :=
    Derives.prepend (leftContext ++ left)
      (derivesPrefixPairExpansion right rightContext)
  have rotateCore :=
    Derives.subst (Derives.symm basisTailRotation)
      (instantiateThreeWords leftContext right left)
  have rotate :=
    Derives.appendRight rotateCore (right ++ rightContext)
  have contractCore :=
    Derives.subst (Derives.symm basisTripleSuffixExpansion)
      (instantiateThreeWords right left rightContext)
  have contract :=
    Derives.prepend leftContext contractCore
  exact Derives.trans
    (by simpa [Word.append_assoc] using expandRight) <|
      Derives.trans
        (by simpa [xyzy, xzyy, w, instantiateThreeWords,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using rotate)
        (by simpa [xyz, xyxxz, w, instantiateThreeWords,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using contract)

/-- Add two copies of an arbitrary nonempty block strictly between fixed
nonempty contexts. -/
theorem derivesInteriorPower
    (leftContext block rightContext : Word Nat) :
    Derives basis
      ((leftContext ++ block) ++ rightContext)
      ((leftContext ++ ((block ++ block) ++ block)) ++ rightContext) := by
  have expanded :=
    Derives.prepend leftContext
      (derivesPrefixPairExpansion block rightContext)
  simpa [Word.append_assoc] using expanded

/-- Change a terminal square from `y²` to a terminal `x`, retaining the
same multiplicities: `x²y² = xy²x`. -/
theorem derivesFinalSwitchPattern (x y : Word Nat) :
    Derives basis
      ((x ++ x) ++ (y ++ y))
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisFinalSwitch
      (instantiateThreeWords x y y)
  simpa [xxyy, xyyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

end SemigroupBasis.CoRoots.S5_437
