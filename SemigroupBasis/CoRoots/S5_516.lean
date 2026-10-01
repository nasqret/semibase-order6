import SemigroupBasis.CoRoots.S5_196
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_516

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def yxy : Word Nat := w 1 [0, 1]
def xxxy : Word Nat := w 0 [0, 0, 1]
def xyy : Word Nat := w 0 [1, 1]
def xyyy : Word Nat := w 0 [1, 1, 1]
def xyz : Word Nat := w 0 [1, 2]
def xzy : Word Nat := w 0 [2, 1]
def xyyz : Word Nat := w 0 [1, 1, 2]

def powerLaw : Identity Nat := ⟨xxx, xxxx⟩
def gatherLaw : Identity Nat := ⟨xxy, xyx⟩
def initialSwitchLaw : Identity Nat := ⟨xxy, yxy⟩
def prefixPowerLaw : Identity Nat := ⟨xxy, xxxy⟩
def suffixPowerLaw : Identity Nat := ⟨xyy, xyyy⟩
def suffixCommutationLaw : Identity Nat := ⟨xyz, xzy⟩
def middleDuplicationLaw : Identity Nat := ⟨xyz, xyyz⟩

/-- The exact authoritative seven-law basis for `S5_516`. -/
def basis : List (Identity Nat) :=
  [powerLaw, gatherLaw, initialSwitchLaw, prefixPowerLaw,
    suffixPowerLaw, suffixCommutationLaw, middleDuplicationLaw]

def yxx : Word Nat := w 1 [0, 0]
def yxxx : Word Nat := w 1 [0, 0, 0]
def yyx : Word Nat := w 1 [1, 0]
def yyyx : Word Nat := w 1 [1, 1, 0]
def zyx : Word Nat := w 2 [1, 0]
def yzx : Word Nat := w 1 [2, 0]
def zyyx : Word Nat := w 2 [1, 1, 0]

/-- The literal reverse-word transform of the authoritative basis. -/
def expectedOppositeBasis : List (Identity Nat) :=
  [⟨xxx, xxxx⟩, ⟨yxx, xyx⟩, ⟨yxx, yxy⟩,
    ⟨yxx, yxxx⟩, ⟨yyx, yyyx⟩, ⟨zyx, yzx⟩,
    ⟨zyx, zyyx⟩]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

theorem oppositeBasis_eq_expected :
    oppositeBasis = expectedOppositeBasis := by
  rfl

def xyxx : Word Nat := w 0 [1, 0, 0]
def zxy : Word Nat := w 2 [0, 1]
def zyxx : Word Nat := w 2 [1, 0, 0]

def initialMarkerPowerLaw : Identity Nat := ⟨xxx, xxxx⟩
def initialMarkerSuffixPowerLaw : Identity Nat := ⟨yxx, yxxx⟩
def initialMarkerCopyLaw : Identity Nat := ⟨xyx, yyx⟩
def initialMarkerGatherLaw : Identity Nat := ⟨xyx, xxy⟩
def initialMarkerFinalDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def initialMarkerSuffixCommutationLaw : Identity Nat := ⟨zyx, zxy⟩
def initialMarkerLastDuplicationLaw : Identity Nat := ⟨zyx, zyxx⟩

/-- A literal presentation of the reversed `S5_196` basis. It has the
same initial-uniqueness word problem as the authoritative `S5_516`
basis, but its laws are arranged for direct dual reuse. -/
def initialMarkerBasis : List (Identity Nat) :=
  [initialMarkerPowerLaw, initialMarkerSuffixPowerLaw,
    initialMarkerCopyLaw, initialMarkerGatherLaw,
    initialMarkerFinalDuplicationLaw,
    initialMarkerSuffixCommutationLaw,
    initialMarkerLastDuplicationLaw]

theorem initialMarkerBasis_eq_reversedS5_196 :
    initialMarkerBasis =
      reversedBasis SemigroupBasis.CoRoots.S5_196.basis := by
  calc
    initialMarkerBasis =
        SemigroupBasis.CoRoots.S5_196.expectedReversedBasis := by
      rfl
    _ = reversedBasis SemigroupBasis.CoRoots.S5_196.basis :=
      SemigroupBasis.CoRoots.S5_196.reversedBasis_eq_expected.symm

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
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

/-- Finite checks on the variables `0,1,2` suffice for all seven displayed
laws. -/
theorem models_of_finite_checks
    (table : FiniteTable)
    (checks : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checks) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

theorem derivesPower (u : Word Nat) :
    Derives basis
      ((u ++ u) ++ u)
      (((u ++ u) ++ u) ++ u) := by
  have base : Derives basis xxx xxxx :=
    Derives.fromBasis (e := powerLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u u u)
  simpa [powerLaw, xxx, xxxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesGather (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ v)
      ((u ++ v) ++ u) := by
  have base : Derives basis xxy xyx :=
    Derives.fromBasis (e := gatherLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [gatherLaw, xxy, xyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesInitialSwitch (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ v)
      ((v ++ u) ++ v) := by
  have base : Derives basis xxy yxy :=
    Derives.fromBasis (e := initialSwitchLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [initialSwitchLaw, xxy, yxy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesPrefixPower (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ v)
      (((u ++ u) ++ u) ++ v) := by
  have base : Derives basis xxy xxxy :=
    Derives.fromBasis (e := prefixPowerLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [prefixPowerLaw, xxy, xxxy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesSuffixPower (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ v)
      (((u ++ v) ++ v) ++ v) := by
  have base : Derives basis xyy xyyy :=
    Derives.fromBasis (e := suffixPowerLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [suffixPowerLaw, xyy, xyyy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Swap two nonempty blocks in the suffix after a fixed nonempty block. -/
theorem derivesSuffixSwap (u v z : Word Nat) :
    Derives basis
      ((u ++ v) ++ z)
      ((u ++ z) ++ v) := by
  have base : Derives basis xyz xzy :=
    Derives.fromBasis (e := suffixCommutationLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [suffixCommutationLaw, xyz, xzy, w,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesMiddleDuplication (u v z : Word Nat) :
    Derives basis
      ((u ++ v) ++ z)
      (((u ++ v) ++ v) ++ z) := by
  have base : Derives basis xyz xyyz :=
    Derives.fromBasis (e := middleDuplicationLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [middleDuplicationLaw, xyz, xyyz, w,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem initialMarkerDerivesPower (u : Word Nat) :
    Derives initialMarkerBasis
      ((u ++ u) ++ u)
      (((u ++ u) ++ u) ++ u) := by
  have base : Derives initialMarkerBasis xxx xxxx :=
    Derives.fromBasis (e := initialMarkerPowerLaw) <| by
      simp [initialMarkerBasis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u u u)
  simpa [initialMarkerPowerLaw, xxx, xxxx, w,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem initialMarkerDerivesSuffixPower (u v : Word Nat) :
    Derives initialMarkerBasis
      ((u ++ v) ++ v)
      (((u ++ v) ++ v) ++ v) := by
  have base : Derives initialMarkerBasis yxx yxxx :=
    Derives.fromBasis (e := initialMarkerSuffixPowerLaw) <| by
      simp [initialMarkerBasis]
  have substituted :=
    Derives.subst base (instantiateThreeWords v u u)
  simpa [initialMarkerSuffixPowerLaw, yxx, yxxx, w,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem initialMarkerDerivesCopy (u v : Word Nat) :
    Derives initialMarkerBasis
      ((u ++ v) ++ u)
      ((v ++ v) ++ u) := by
  have base : Derives initialMarkerBasis xyx yyx :=
    Derives.fromBasis (e := initialMarkerCopyLaw) <| by
      simp [initialMarkerBasis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [initialMarkerCopyLaw, xyx, yyx, w,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem initialMarkerDerivesGather (u v : Word Nat) :
    Derives initialMarkerBasis
      ((u ++ v) ++ u)
      ((u ++ u) ++ v) := by
  have base : Derives initialMarkerBasis xyx xxy :=
    Derives.fromBasis (e := initialMarkerGatherLaw) <| by
      simp [initialMarkerBasis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [initialMarkerGatherLaw, xyx, xxy, w,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem initialMarkerDerivesFinalDuplication (u v : Word Nat) :
    Derives initialMarkerBasis
      ((u ++ v) ++ u)
      (((u ++ v) ++ u) ++ u) := by
  have base : Derives initialMarkerBasis xyx xyxx :=
    Derives.fromBasis
      (e := initialMarkerFinalDuplicationLaw) <| by
        simp [initialMarkerBasis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [initialMarkerFinalDuplicationLaw, xyx, xyxx, w,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem initialMarkerDerivesSuffixSwap (u v z : Word Nat) :
    Derives initialMarkerBasis
      ((u ++ v) ++ z)
      ((u ++ z) ++ v) := by
  have base : Derives initialMarkerBasis zyx zxy :=
    Derives.fromBasis
      (e := initialMarkerSuffixCommutationLaw) <| by
        simp [initialMarkerBasis]
  have substituted :=
    Derives.subst base (instantiateThreeWords z v u)
  simpa [initialMarkerSuffixCommutationLaw, zyx, zxy, w,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem initialMarkerDerivesLastDuplication (u v z : Word Nat) :
    Derives initialMarkerBasis
      ((u ++ v) ++ z)
      (((u ++ v) ++ z) ++ z) := by
  have base : Derives initialMarkerBasis zyx zyxx :=
    Derives.fromBasis
      (e := initialMarkerLastDuplicationLaw) <| by
        simp [initialMarkerBasis]
  have substituted :=
    Derives.subst base (instantiateThreeWords z v u)
  simpa [initialMarkerLastDuplicationLaw, zyx, zyxx, w,
    instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Derive the one nonprimitive reversed-terminal law from the
authoritative basis. -/
theorem derivesInitialMarkerFinalDuplicationLaw :
    Derives basis xyx xyxx := by
  let x := Word.singleton 0
  let y := Word.singleton 1
  have gatherBack := (derivesGather x y).symm
  have insert := derivesPrefixPower x y
  have commute := derivesSuffixSwap x (x ++ x) y
  apply Derives.trans
  · simpa [x, y, xyx, xxy, w, Word.append_assoc] using gatherBack
  · apply Derives.trans
    · simpa [x, y, xxy, xxxy, w, Word.append_assoc] using insert
    · simpa [x, y, xxxy, xyxx, w, Word.append_assoc] using commute

/-- Derive final duplication after a two-block suffix by swapping,
duplicating the middle block, and swapping back. -/
theorem derivesInitialMarkerLastDuplicationLaw :
    Derives basis zyx zyxx := by
  let x := Word.singleton 0
  let y := Word.singleton 1
  let z := Word.singleton 2
  have first := derivesSuffixSwap z y x
  have duplicate := derivesMiddleDuplication z x y
  have last := derivesSuffixSwap z (x ++ x) y
  apply Derives.trans
  · simpa [x, y, z, zyx, zxy, w, Word.append_assoc] using first
  · apply Derives.trans
    · simpa [x, y, z, zxy, w, Word.append_assoc] using duplicate
    · simpa [x, y, z, zyxx, w, Word.append_assoc] using last

/-- Every axiom of the reversed `S5_196` presentation is derivable from
the authoritative `S5_516` basis. -/
theorem initialMarkerAxiomsDeriveBasis
    (identity : Identity Nat) (member : identity ∈ initialMarkerBasis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [initialMarkerBasis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [initialMarkerPowerLaw, xxx, xxxx, w,
      Word.append_assoc] using
        derivesPower (Word.singleton 0)
  · simpa [initialMarkerSuffixPowerLaw, yxx, yxxx, w,
      Word.append_assoc] using
        derivesSuffixPower (Word.singleton 1) (Word.singleton 0)
  · simpa [initialMarkerCopyLaw, xyx, yyx, w,
      Word.append_assoc] using
        (derivesInitialSwitch
          (Word.singleton 1) (Word.singleton 0)).symm
  · simpa [initialMarkerGatherLaw, xyx, xxy, w,
      Word.append_assoc] using
        (derivesGather
          (Word.singleton 0) (Word.singleton 1)).symm
  · exact derivesInitialMarkerFinalDuplicationLaw
  · simpa [initialMarkerSuffixCommutationLaw, zyx, zxy, w,
      Word.append_assoc] using
        derivesSuffixSwap
          (Word.singleton 2) (Word.singleton 1)
          (Word.singleton 0)
  · exact derivesInitialMarkerLastDuplicationLaw

/-- Derive `xxy = xxxy` from the reversed terminal-marker laws. -/
theorem initialMarkerDerivesPrefixPowerLaw :
    Derives initialMarkerBasis xxy xxxy := by
  let x := Word.singleton 0
  let y := Word.singleton 1
  have gather := (initialMarkerDerivesGather x y).symm
  have duplicate := initialMarkerDerivesFinalDuplication x y
  have commute := initialMarkerDerivesSuffixSwap x y (x ++ x)
  apply Derives.trans
  · simpa [x, y, xxy, xyx, w, Word.append_assoc] using gather
  · apply Derives.trans
    · simpa [x, y, xyx, xyxx, w, Word.append_assoc] using duplicate
    · simpa [x, y, xyxx, xxxy, w, Word.append_assoc] using commute

/-- Derive `xyz = xyyz` by moving the target block to the end,
duplicating it, and restoring suffix order. -/
theorem initialMarkerDerivesMiddleDuplicationLaw :
    Derives initialMarkerBasis xyz xyyz := by
  let x := Word.singleton 0
  let y := Word.singleton 1
  let z := Word.singleton 2
  have first := initialMarkerDerivesSuffixSwap x y z
  have duplicate := initialMarkerDerivesLastDuplication x z y
  have last := initialMarkerDerivesSuffixSwap x z (y ++ y)
  apply Derives.trans
  · simpa [x, y, z, xyz, xzy, w, Word.append_assoc] using first
  · apply Derives.trans
    · simpa [x, y, z, xzy, w, Word.append_assoc] using duplicate
    · simpa [x, y, z, xyyz, w, Word.append_assoc] using last

/-- Every authoritative `S5_516` axiom is derivable from the literal
reversed `S5_196` presentation. -/
theorem basisAxiomsDeriveInitialMarker
    (identity : Identity Nat) (member : identity ∈ basis) :
    Derives initialMarkerBasis identity.lhs identity.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [powerLaw, xxx, xxxx, w, Word.append_assoc] using
      initialMarkerDerivesPower (Word.singleton 0)
  · simpa [gatherLaw, xxy, xyx, w, Word.append_assoc] using
      (initialMarkerDerivesGather
        (Word.singleton 0) (Word.singleton 1)).symm
  · simpa [initialSwitchLaw, xxy, yxy, w,
      Word.append_assoc] using
        (initialMarkerDerivesCopy
          (Word.singleton 1) (Word.singleton 0)).symm
  · exact initialMarkerDerivesPrefixPowerLaw
  · simpa [suffixPowerLaw, xyy, xyyy, w,
      Word.append_assoc] using
        initialMarkerDerivesSuffixPower
          (Word.singleton 0) (Word.singleton 1)
  · simpa [suffixCommutationLaw, xyz, xzy, w,
      Word.append_assoc] using
        initialMarkerDerivesSuffixSwap
          (Word.singleton 0) (Word.singleton 1)
          (Word.singleton 2)
  · exact initialMarkerDerivesMiddleDuplicationLaw

theorem derivesInitialMarkerOfBasis
    {left right : Word Nat} (derivation : Derives basis left right) :
    Derives initialMarkerBasis left right :=
  derivation.transport basisAxiomsDeriveInitialMarker

theorem derivesBasisOfInitialMarker
    {left right : Word Nat}
    (derivation : Derives initialMarkerBasis left right) :
    Derives basis left right :=
  derivation.transport initialMarkerAxiomsDeriveBasis

end SemigroupBasis.CoRoots.S5_516
