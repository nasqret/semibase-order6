import SemigroupBasis.CoRoots.S5_793Normalization

namespace SemigroupBasis.CoRoots.S5_381

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyy : Word Nat := w 0 [2, 1, 1]
def xyxzz : Word Nat := w 0 [1, 0, 2, 2]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def rightDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def squareInterleaveLaw : Identity Nat := ⟨xxyy, xyxy⟩
def squareFinalSwitchLaw : Identity Nat := ⟨xxyy, xyyx⟩
def squareInitialSwitchLaw : Identity Nat := ⟨xxyy, yxxy⟩
def interiorInsertionLaw : Identity Nat := ⟨xyzx, xyxzx⟩
def prefixedGatherLaw : Identity Nat := ⟨xyzy, xzyy⟩

/-- The exact common basis recorded for `S5_381` and `S5_610`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftDuplicationLaw, rightDuplicationLaw,
    squareInterleaveLaw, squareFinalSwitchLaw, squareInitialSwitchLaw,
    interiorInsertionLaw, prefixedGatherLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

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

/-- Turn the finite three-variable checks for the displayed laws into a
`Models` theorem over the repository's standard `Nat` variables. -/
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

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisPower :
    Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) <| by
    simp [basis]

private theorem basisLeftDuplication :
    Derives basis xyx xxyx :=
  Derives.fromBasis (e := leftDuplicationLaw) <| by
    simp [basis]

private theorem basisRightDuplication :
    Derives basis xyx xyxx :=
  Derives.fromBasis (e := rightDuplicationLaw) <| by
    simp [basis]

private theorem basisSquareInterleave :
    Derives basis xxyy xyxy :=
  Derives.fromBasis (e := squareInterleaveLaw) <| by
    simp [basis]

private theorem basisSquareFinalSwitch :
    Derives basis xxyy xyyx :=
  Derives.fromBasis (e := squareFinalSwitchLaw) <| by
    simp [basis]

private theorem basisSquareInitialSwitch :
    Derives basis xxyy yxxy :=
  Derives.fromBasis (e := squareInitialSwitchLaw) <| by
    simp [basis]

private theorem basisInteriorInsertion :
    Derives basis xyzx xyxzx :=
  Derives.fromBasis (e := interiorInsertionLaw) <| by
    simp [basis]

private theorem basisPrefixedGather :
    Derives basis xyzy xzyy :=
  Derives.fromBasis (e := prefixedGatherLaw) <| by
    simp [basis]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateThreeWords u u u)
  simpa [xx, xxx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesLeftDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisLeftDuplication
      (instantiateThreeWords u v v)
  simpa [xyx, xxyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesRightDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightDuplication
      (instantiateThreeWords u v v)
  simpa [xyx, xyxx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareInterleave (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisSquareInterleave
      (instantiateThreeWords u v v)
  simpa [xxyy, xyxy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareFinalSwitch (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSquareFinalSwitch
      (instantiateThreeWords u v v)
  simpa [xxyy, xyyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareInitialSwitch (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      (((v ++ u) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisSquareInitialSwitch
      (instantiateThreeWords u v v)
  simpa [xxyy, yxxy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesInteriorInsertion (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u)
      ((((u ++ v) ++ u) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisInteriorInsertion
      (instantiateThreeWords u v z)
  simpa [xyzx, xyxzx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesPrefixedGather
    (pre u middle : Word Nat) :
    Derives basis (((pre ++ u) ++ middle) ++ u)
      (((pre ++ middle) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPrefixedGather
      (instantiateThreeWords pre u middle)
  simpa [xyzy, xzyy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesThirdOccurrenceDeletion
    (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) := by
  exact Derives.symm <| by
    simpa [Word.append_assoc] using
      derivesInteriorInsertion u v z

theorem derivesPrefixedSquareCommutation
    (pre u v : Word Nat) :
    Derives basis
      (pre ++ ((u ++ u) ++ (v ++ v)))
      (pre ++ ((v ++ v) ++ (u ++ u))) := by
  have first :=
    Derives.prepend pre (derivesSquareFinalSwitch u v)
  have second :=
    derivesPrefixedGather pre u (v ++ v)
  exact first.trans <| by
    simpa [Word.append_assoc] using second

/-- The S5_793 head-square rotation follows from right duplication,
the square-final switch, and interior-insertion contraction. -/
theorem derivesHeadAcrossSquare
    (head middle square : Word Nat) :
    Derives basis
      ((((head ++ middle) ++ head) ++ square) ++ square)
      ((((head ++ middle) ++ square) ++ square) ++ head) := by
  have duplicate :=
    Derives.appendRight
      (derivesRightDuplication head middle)
      (square ++ square)
  have rotate :=
    Derives.prepend (head ++ middle)
      (derivesSquareFinalSwitch head square)
  have contract :=
    (derivesInteriorInsertion head middle (square ++ square)).symm
  simp only [Word.append_assoc] at duplicate rotate contract
  simpa only [Word.append_assoc] using
    duplicate.trans (rotate.trans contract)

/-- The complete S5_793 basis is derivable from the exact S5_381 basis. -/
theorem s5_793AxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_793.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_793.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [SemigroupBasis.CoRoots.S5_793.powerLaw,
      SemigroupBasis.CoRoots.S5_793.xx,
      SemigroupBasis.CoRoots.S5_793.xxx, powerLaw, xx, xxx, w] using
      basisPower
  · simpa [SemigroupBasis.CoRoots.S5_793.leftDuplicationLaw,
      SemigroupBasis.CoRoots.S5_793.xyx,
      SemigroupBasis.CoRoots.S5_793.xxyx,
      leftDuplicationLaw, xyx, xxyx, w] using basisLeftDuplication
  · simpa [SemigroupBasis.CoRoots.S5_793.rightDuplicationLaw,
      SemigroupBasis.CoRoots.S5_793.xyx,
      SemigroupBasis.CoRoots.S5_793.xyxx,
      rightDuplicationLaw, xyx, xyxx, w] using basisRightDuplication
  · simpa [SemigroupBasis.CoRoots.S5_793.squareInterleaveLaw,
      SemigroupBasis.CoRoots.S5_793.xxyy,
      SemigroupBasis.CoRoots.S5_793.xyxy,
      squareInterleaveLaw, xxyy, xyxy, w] using basisSquareInterleave
  · simpa [SemigroupBasis.CoRoots.S5_793.squareFinalSwitchLaw,
      SemigroupBasis.CoRoots.S5_793.xxyy,
      SemigroupBasis.CoRoots.S5_793.xyyx,
      squareFinalSwitchLaw, xxyy, xyyx, w] using basisSquareFinalSwitch
  · simpa [SemigroupBasis.CoRoots.S5_793.interiorInsertionLaw,
      SemigroupBasis.CoRoots.S5_793.xyzx,
      SemigroupBasis.CoRoots.S5_793.xyxzx,
      interiorInsertionLaw, xyzx, xyxzx, w] using basisInteriorInsertion
  · simpa [SemigroupBasis.CoRoots.S5_793.prefixedGatherLaw,
      SemigroupBasis.CoRoots.S5_793.xyzy,
      SemigroupBasis.CoRoots.S5_793.xzyy,
      prefixedGatherLaw, xyzy, xzyy, w] using basisPrefixedGather
  · simpa [SemigroupBasis.CoRoots.S5_793.headSquareRotationLaw,
      SemigroupBasis.CoRoots.S5_793.xyxzz,
      SemigroupBasis.CoRoots.S5_793.xyzzx,
      xyxzz, xyzzx, w,
      Word.singleton, Word.append] using
      derivesHeadAcrossSquare
        (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)

theorem transportS5_793Derivation
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_793.basis left right) :
    Derives basis left right :=
  derivation.transport s5_793AxiomDerives

/-- Initial-marker switch when both intervening words are nonempty:
`y U y V x² = x U y² V x`. -/
theorem derivesInitialSwitchBoth
    (old new first second : Word Nat) :
    Derives basis
      ((((old ++ first) ++ old) ++ second) ++ (new ++ new))
      ((((new ++ first) ++ (old ++ old)) ++ second) ++ new) := by
  let middle := (((old ++ first) ++ old) ++ second)
  let newMiddle := (((old ++ old) ++ first) ++ old) ++ second
  have stepOne :=
    Derives.appendRight
      (derivesLeftDuplication old first)
      (second ++ (new ++ new))
  have stepTwo :=
    (derivesPrefixedGather old new middle).symm
  have stepThree :=
    Derives.prepend old
      (derivesLeftDuplication new middle)
  have stepFour :=
    Derives.appendRight
      (derivesSquareInitialSwitch new old).symm
      (((first ++ old) ++ second) ++ new)
  have stepFive :=
    (derivesLeftDuplication new newMiddle).symm
  have stepSix :=
    Derives.appendRight
      (Derives.prepend new
        (derivesLeftDuplication old first).symm)
      (second ++ new)
  have stepSeven :=
    Derives.appendRight
      (derivesPrefixedGather new old first)
      (second ++ new)
  simp only [middle, newMiddle, Word.append_assoc] at stepOne stepTwo stepThree stepFour stepFive stepSix stepSeven
  simpa only [Word.append_assoc] using
    stepOne.trans
      (stepTwo.trans
        (stepThree.trans
          (stepFour.trans
            (stepFive.trans
              (stepSix.trans stepSeven)))))

/-- Initial-marker switch with an empty first interior:
`y² V x² = x y² V x`. -/
theorem derivesInitialSwitchFirstEmpty
    (old new second : Word Nat) :
    Derives basis
      (((old ++ old) ++ second) ++ (new ++ new))
      ((((new ++ old) ++ old) ++ second) ++ new) := by
  let middle := (old ++ old) ++ second
  have stepOne :=
    (derivesPrefixedGather old new (old ++ second)).symm
  have stepTwo :=
    Derives.prepend old
      (derivesLeftDuplication new (old ++ second))
  have stepThree :=
    Derives.appendRight
      (derivesSquareInitialSwitch new old).symm
      (second ++ new)
  have stepFour :=
    (derivesLeftDuplication new middle).symm
  simp only [middle, Word.append_assoc] at stepOne stepTwo stepThree stepFour
  simpa only [Word.append_assoc] using
    stepOne.trans (stepTwo.trans (stepThree.trans stepFour))

/-- Initial-marker switch with an empty second interior:
`y U y x² = x U y² x`. -/
theorem derivesInitialSwitchSecondEmpty
    (old new first : Word Nat) :
    Derives basis
      (((old ++ first) ++ old) ++ (new ++ new))
      (((new ++ first) ++ (old ++ old)) ++ new) := by
  let middle := (old ++ first) ++ old
  let newMiddle := ((old ++ old) ++ first) ++ old
  have stepOne :=
    Derives.appendRight
      (derivesLeftDuplication old first)
      (new ++ new)
  have stepTwo :=
    (derivesPrefixedGather old new middle).symm
  have stepThree :=
    Derives.prepend old
      (derivesLeftDuplication new middle)
  have stepFour :=
    Derives.appendRight
      (derivesSquareInitialSwitch new old).symm
      ((first ++ old) ++ new)
  have stepFive :=
    (derivesLeftDuplication new newMiddle).symm
  have stepSix :=
    Derives.appendRight
      (Derives.prepend new
        (derivesLeftDuplication old first).symm)
      new
  have stepSeven :=
    Derives.appendRight
      (derivesPrefixedGather new old first)
      new
  simp only [middle, newMiddle, Word.append_assoc] at stepOne stepTwo stepThree stepFour stepFive stepSix stepSeven
  simpa only [Word.append_assoc] using
    stepOne.trans
      (stepTwo.trans
        (stepThree.trans
          (stepFour.trans
            (stepFive.trans
              (stepSix.trans stepSeven)))))

/-- Initial-marker switch with both interiors empty:
`y²x² = xy²x`. -/
theorem derivesInitialSwitchBothEmpty
    (old new : Word Nat) :
    Derives basis ((old ++ old) ++ (new ++ new))
      (((new ++ old) ++ old) ++ new) :=
  derivesSquareInitialSwitch old new

end SemigroupBasis.CoRoots.S5_381
