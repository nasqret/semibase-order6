import SemigroupBasis.CoRoots.S5_381

namespace SemigroupBasis.CoRoots.S5_348

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
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyxz : Word Nat := w 0 [1, 0, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def rightDuplicationLaw : Identity Nat := ⟨xyx, xyxx⟩
def squareInterleaveLaw : Identity Nat := ⟨xxyy, xyxy⟩
def squareFinalSwitchLaw : Identity Nat := ⟨xxyy, xyyx⟩
def squareInitialSwitchLaw : Identity Nat := ⟨xxyy, yxxy⟩
def firstGapGatherLaw : Identity Nat := ⟨xxyz, xyxz⟩

/-- The exact common basis recorded for `S5_348` and `S5_354`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftDuplicationLaw, rightDuplicationLaw,
    squareInterleaveLaw, squareFinalSwitchLaw,
    squareInitialSwitchLaw, firstGapGatherLaw]

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

/-- Turn finite three-variable checks for the displayed laws into a
`Models` theorem over the standard `Nat` variable type. -/
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

private theorem basisFirstGapGather :
    Derives basis xxyz xyxz :=
  Derives.fromBasis (e := firstGapGatherLaw) <| by
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

/-- Gather the second copy of `u` next to its first occurrence:
`u² v z = u v u z`. -/
theorem derivesFirstGapGather (u v z : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ z)
      (((u ++ v) ++ u) ++ z) := by
  have substituted :=
    Derives.subst basisFirstGapGather
      (instantiateThreeWords u v z)
  simpa [xxyz, xyxz, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Delete the middle copy in `u v u z u = u v z u`. -/
theorem derivesThirdOccurrenceDeletion
    (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) := by
  have gather :=
    Derives.appendRight (derivesFirstGapGather u v z).symm u
  have contract :=
    (derivesLeftDuplication u (v ++ z)).symm
  exact gather.trans <| by
    simpa [Word.append_assoc] using contract

/-- Square blocks commute without changing the surrounding first-gap
data. -/
theorem derivesSquareBlockCommutation (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      ((v ++ v) ++ (u ++ u)) := by
  exact (derivesSquareFinalSwitch u v).trans <|
    (derivesSquareInitialSwitch v u).symm

private def yyxx : Word Nat := w 1 [1, 0, 0]
private def yxyx : Word Nat := w 1 [0, 1, 0]
private def xzyx : Word Nat := w 0 [2, 1, 0]
private def xzxyx : Word Nat := w 0 [2, 0, 1, 0]
private def yzyx : Word Nat := w 1 [2, 1, 0]
private def yyzx : Word Nat := w 1 [1, 2, 0]

private def reversedSquareInterleaveLaw : Identity Nat :=
  ⟨yyxx, yxyx⟩

private def reversedSquareFinalSwitchLaw : Identity Nat :=
  ⟨yyxx, xyyx⟩

private def reversedSquareInitialSwitchLaw : Identity Nat :=
  ⟨yyxx, yxxy⟩

private def reversedInteriorInsertionLaw : Identity Nat :=
  ⟨xzyx, xzxyx⟩

private def reversedPrefixedGatherLaw : Identity Nat :=
  ⟨yzyx, yyzx⟩

private def reversedS5_381BridgeBasis : List (Identity Nat) :=
  [powerLaw, rightDuplicationLaw, leftDuplicationLaw,
    reversedSquareInterleaveLaw, reversedSquareFinalSwitchLaw,
    reversedSquareInitialSwitchLaw, reversedInteriorInsertionLaw,
    reversedPrefixedGatherLaw]

private theorem reversedS5_381Basis_eq_bridge :
    reversedBasis SemigroupBasis.CoRoots.S5_381.basis =
      reversedS5_381BridgeBasis := by
  decide

/-- Every axiom of the reversed `S5_381` basis follows from the exact
seven-law `S5_348` basis. The only non-basis bridge is the derived
third-occurrence deletion. -/
theorem reversedS5_381AxiomDerives
    (identity : Identity Nat)
    (member :
      identity ∈ reversedBasis SemigroupBasis.CoRoots.S5_381.basis) :
    Derives basis identity.lhs identity.rhs := by
  rw [reversedS5_381Basis_eq_bridge] at member
  simp only [reversedS5_381BridgeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact basisPower
  · exact basisRightDuplication
  · exact basisLeftDuplication
  · simpa [reversedSquareInterleaveLaw, yyxx, yxyx, w,
      Word.singleton, Word.append] using
      derivesSquareInterleave (Word.singleton 1) (Word.singleton 0)
  · simpa [reversedSquareFinalSwitchLaw, yyxx, xyyx, w,
      Word.singleton, Word.append] using
      derivesSquareInitialSwitch (Word.singleton 1) (Word.singleton 0)
  · simpa [reversedSquareInitialSwitchLaw, yyxx, yxxy, w,
      Word.singleton, Word.append] using
      derivesSquareFinalSwitch (Word.singleton 1) (Word.singleton 0)
  · simpa [reversedInteriorInsertionLaw, xzyx, xzxyx, w,
      Word.singleton, Word.append] using
      (derivesThirdOccurrenceDeletion
        (Word.singleton 0) (Word.singleton 2) (Word.singleton 1)).symm
  · simpa [reversedPrefixedGatherLaw, yzyx, yyzx, w,
      Word.singleton, Word.append] using
      (derivesFirstGapGather
        (Word.singleton 1) (Word.singleton 2) (Word.singleton 0)).symm

theorem transportReversedS5_381Derivation
    {left right : Word Nat}
    (derivation :
      Derives (reversedBasis SemigroupBasis.CoRoots.S5_381.basis)
        left right) :
    Derives basis left right :=
  derivation.transport reversedS5_381AxiomDerives

/-- Move a repeated terminal marker before a square block:
`x² y z y = y x² z y`. -/
theorem derivesTerminalMarkerFront
    (square marker middle : Word Nat) :
    Derives basis
      ((((square ++ square) ++ marker) ++ middle) ++ marker)
      ((((marker ++ square) ++ square) ++ middle) ++ marker) := by
  have reversed :=
    (SemigroupBasis.CoRoots.S5_381.derivesHeadAcrossSquare
      marker.reverse middle.reverse square.reverse).reverse
  exact transportReversedS5_381Derivation <| by
    simpa [Word.append_assoc] using reversed

/-- Terminal-marker switch with both intervening words nonempty:
`x² U y V y = x U y² V x`. -/
theorem derivesTerminalSwitchBoth
    (new old first second : Word Nat) :
    Derives basis
      (((((new ++ new) ++ first) ++ old) ++ second) ++ old)
      (((((new ++ first) ++ old) ++ old) ++ second) ++ new) := by
  have reversed :=
    (SemigroupBasis.CoRoots.S5_381.derivesInitialSwitchBoth
      old.reverse new.reverse second.reverse first.reverse).reverse
  exact transportReversedS5_381Derivation <| by
    simpa [Word.append_assoc] using reversed

/-- Terminal-marker switch with an empty first interior:
`x² y V y = x y² V x`. -/
theorem derivesTerminalSwitchFirstEmpty
    (new old second : Word Nat) :
    Derives basis
      ((((new ++ new) ++ old) ++ second) ++ old)
      ((((new ++ old) ++ old) ++ second) ++ new) := by
  have reversed :=
    (SemigroupBasis.CoRoots.S5_381.derivesInitialSwitchSecondEmpty
      old.reverse new.reverse second.reverse).reverse
  exact transportReversedS5_381Derivation <| by
    simpa [Word.append_assoc] using reversed

/-- Terminal-marker switch with an empty second interior:
`x² U y² = x U y² x`. -/
theorem derivesTerminalSwitchSecondEmpty
    (new old first : Word Nat) :
    Derives basis
      ((((new ++ new) ++ first) ++ old) ++ old)
      ((((new ++ first) ++ old) ++ old) ++ new) := by
  have reversed :=
    (SemigroupBasis.CoRoots.S5_381.derivesInitialSwitchFirstEmpty
      old.reverse new.reverse first.reverse).reverse
  exact transportReversedS5_381Derivation <| by
    simpa [Word.append_assoc] using reversed

/-- Terminal-marker switch with both interiors empty:
`x²y² = xy²x`. -/
theorem derivesTerminalSwitchBothEmpty
    (new old : Word Nat) :
    Derives basis ((new ++ new) ++ (old ++ old))
      (((new ++ old) ++ old) ++ new) := by
  have reversed :=
    (SemigroupBasis.CoRoots.S5_381.derivesInitialSwitchBothEmpty
      old.reverse new.reverse).reverse
  exact transportReversedS5_381Derivation <| by
    simpa [Word.append_assoc] using reversed

end SemigroupBasis.CoRoots.S5_348
