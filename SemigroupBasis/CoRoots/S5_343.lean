import SemigroupBasis.CoRoots.S5_345
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_343

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyz : Word Nat := w 0 [1, 2]
def xyyz : Word Nat := w 0 [1, 1, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def endpointSquareLaw : Identity Nat := ⟨xyx, xxyy⟩
def interiorDuplicationLaw : Identity Nat := ⟨xyz, xyyz⟩

/-- The exact basis `xx = xxx`, `xyx = xxyy`, `xyz = xyyz`. -/
def basis : List (Identity Nat) :=
  [powerLaw, endpointSquareLaw, interiorDuplicationLaw]

def yyxx : Word Nat := w 1 [1, 0, 0]
def zyx : Word Nat := w 2 [1, 0]
def zyyx : Word Nat := w 2 [1, 1, 0]

/-- The literal reverse-word orientation used for opposite semigroups. -/
def expectedReversedBasis : List (Identity Nat) :=
  [⟨xx, xxx⟩, ⟨xyx, yyxx⟩, ⟨zyx, zyyx⟩]

theorem reversedBasis_eq_expected :
    reversedBasis basis = expectedReversedBasis := by
  rfl

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem powerLaw_mem : powerLaw ∈ basis := by
  simp [basis]

private theorem endpointSquareLaw_mem : endpointSquareLaw ∈ basis := by
  simp [basis]

private theorem interiorDuplicationLaw_mem :
    interiorDuplicationLaw ∈ basis := by
  simp [basis]

/-- Expand a square of a nonempty block to a cube. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis xx xxx :=
    Derives.fromBasis (e := powerLaw) powerLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Contract a cube of a nonempty block to a square. -/
theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

/-- Replace repeated endpoints by adjacent squares. -/
theorem derivesEndpointSquares (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ u) ++ (v ++ v)) := by
  have base : Derives basis xyx xxyy :=
    Derives.fromBasis (e := endpointSquareLaw)
      endpointSquareLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [endpointSquareLaw, xyx, xxyy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Duplicate a nonempty block between nonempty left and right contexts. -/
theorem derivesInteriorDuplication (u v z : Word Nat) :
    Derives basis ((u ++ v) ++ z) (((u ++ v) ++ v) ++ z) := by
  have base : Derives basis xyz xyyz :=
    Derives.fromBasis (e := interiorDuplicationLaw)
      interiorDuplicationLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [interiorDuplicationLaw, xyz, xyyz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The authoritative consequence `PaQaR = PaQR`. -/
theorem derivesInteriorRepeatDeletion
    (p a q r : Word Nat) :
    Derives basis
      ((((p ++ a) ++ q) ++ a) ++ r)
      (((p ++ a) ++ q) ++ r) := by
  have square :=
    Derives.appendRight
      (Derives.prepend p (derivesEndpointSquares a q)) r
  have contractA :=
    (derivesInteriorDuplication p a ((q ++ q) ++ r)).symm
  have contractQ :=
    (derivesInteriorDuplication (p ++ a) q r).symm
  exact Derives.trans
    (by simpa [Word.append_assoc] using square)
    (Derives.trans
      (by simpa [Word.append_assoc] using contractA)
      (by simpa [Word.append_assoc] using contractQ))

/-- The authoritative consequence `xAxB = x^2AB`. -/
theorem derivesHeadRepeatGathering
    (x middle after : Word Nat) :
    Derives basis
      (((x ++ middle) ++ x) ++ after)
      (((x ++ x) ++ middle) ++ after) := by
  have square :=
    Derives.appendRight (derivesEndpointSquares x middle) after
  have contractMiddle :=
    (derivesInteriorDuplication (x ++ x) middle after).symm
  exact Derives.trans
    (by simpa [Word.append_assoc] using square)
    (by simpa [Word.append_assoc] using contractMiddle)

/-- The authoritative consequence `PaQa = PaQ^2`. -/
theorem derivesRepeatedFinalSwitch
    (p a q : Word Nat) :
    Derives basis
      (((p ++ a) ++ q) ++ a)
      ((p ++ a) ++ (q ++ q)) := by
  have square := Derives.prepend p (derivesEndpointSquares a q)
  have contractA :=
    (derivesInteriorDuplication p a (q ++ q)).symm
  exact Derives.trans
    (by simpa [Word.append_assoc] using square)
    (by simpa [Word.append_assoc] using contractA)

/-- The authoritative consequence `xAxBx = xABx`. -/
theorem derivesThirdHeadDeletion
    (x left right : Word Nat) :
    Derives basis
      ((((x ++ left) ++ x) ++ right) ++ x)
      (((x ++ left) ++ right) ++ x) := by
  let core := (left ++ left) ++ right
  have stepOne :=
    Derives.appendRight
      (derivesEndpointSquares x left) (right ++ x)
  have stepTwo :=
    Derives.prepend x (derivesEndpointSquares x core)
  have stepThree :=
    Derives.appendRight (derivesPowerContraction x) (core ++ core)
  have stepFour := (derivesEndpointSquares x core).symm
  have stepFive :=
    (derivesInteriorDuplication x left (right ++ x)).symm
  exact Derives.trans
    (by simpa [core, Word.append_assoc] using stepOne)
    (Derives.trans
      (by simpa [core, Word.append_assoc] using stepTwo)
      (Derives.trans
        (by simpa [core, Word.append_assoc] using stepThree)
        (Derives.trans
          (by simpa [core, Word.append_assoc] using stepFour)
          (by simpa [core, Word.append_assoc] using stepFive))))

/-- The authoritative consequence `x^2yzy = xyzx`. -/
theorem derivesBothEndpointSwitch
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      (((x ++ y) ++ z) ++ x) := by
  have stepOne :=
    Derives.prepend (x ++ x) (derivesEndpointSquares y z)
  have stepTwo :=
    Derives.prepend (((x ++ x) ++ (y ++ y)))
      (derivesPowerExpansion z)
  have stepThree :=
    Derives.appendRight
      (Derives.prepend (x ++ x) (derivesEndpointSquares y z).symm) z
  have stepFour :=
    (derivesEndpointSquares x (y ++ z)).symm
  exact Derives.trans
    (by simpa [Word.append_assoc] using stepOne)
    (Derives.trans
      (by simpa [Word.append_assoc] using stepTwo)
      (Derives.trans
        (by simpa [Word.append_assoc] using stepThree)
        (by simpa [Word.append_assoc] using stepFour)))

/-- Recover `xyx = xxyx`, the left endpoint law used by `S5_345`. -/
theorem derivesLeftEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have stepOne := derivesEndpointSquares u v
  have stepTwo :=
    Derives.appendRight (derivesPowerExpansion u) (v ++ v)
  have stepThree :=
    Derives.prepend u (derivesEndpointSquares u v).symm
  exact Derives.trans
    (by simpa [Word.append_assoc] using stepOne)
    (Derives.trans
      (by simpa [Word.append_assoc] using stepTwo)
      (by simpa [Word.append_assoc] using stepThree))

/-- Recover `xyx = xyxx`, the right endpoint law used by `S5_345`. -/
theorem derivesRightEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have stepOne := derivesEndpointSquares u v
  have stepTwo := (derivesHeadRepeatGathering u v v).symm
  have stepThree := derivesRepeatedFinalSwitch u v u
  exact Derives.trans
    (by simpa [Word.append_assoc] using stepOne)
    (Derives.trans
      (by simpa [Word.append_assoc] using stepTwo)
      (by simpa [Word.append_assoc] using stepThree))

/-- Recover `xxyy = xyxy`. -/
theorem derivesSquareInterleave (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ u) ++ v) := by
  simpa [Word.append_assoc] using
    (derivesHeadRepeatGathering u v v).symm

/-- Recover `xxyy = xyyx`. -/
theorem derivesSquareFinalSwitch (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ v) ++ u) := by
  have stepOne := (derivesEndpointSquares u v).symm
  have stepTwo := derivesInteriorDuplication u v u
  exact Derives.trans
    (by simpa [Word.append_assoc] using stepOne)
    (by simpa [Word.append_assoc] using stepTwo)

/-- Recover `xxyz = xyxz`. -/
theorem derivesDoubledInitialMove
    (u v z : Word Nat) :
    Derives basis
      (((u ++ u) ++ v) ++ z)
      (((u ++ v) ++ u) ++ z) := by
  have stepOne :=
    derivesInteriorDuplication (u ++ u) v z
  have stepTwo :=
    Derives.appendRight
      (Derives.prepend (u ++ u) (derivesPowerExpansion v)) z
  have stepThree :=
    Derives.appendRight (derivesEndpointSquares u v).symm (v ++ z)
  have stepFour := derivesInteriorRepeatDeletion u v u z
  exact Derives.trans
    (by simpa [Word.append_assoc] using stepOne)
    (Derives.trans
      (by simpa [Word.append_assoc] using stepTwo)
      (Derives.trans
        (by simpa [Word.append_assoc] using stepThree)
        (by simpa [Word.append_assoc] using stepFour)))

/-- Recover `xxyzy = xyyzx`. -/
theorem derivesOpenTerminalSwitch
    (u v z : Word Nat) :
    Derives basis
      ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ v) ++ z) ++ u) := by
  have stepOne := derivesBothEndpointSwitch u v z
  have stepTwo := derivesInteriorDuplication u v (z ++ u)
  exact Derives.trans
    (by simpa [Word.append_assoc] using stepOne)
    (by simpa [Word.append_assoc] using stepTwo)

private theorem derivesMarkerToClosed
    (u v z : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ u)
      (((u ++ u) ++ v) ++ (z ++ z)) := by
  have stepOne := derivesEndpointSquares u (v ++ z)
  have stepTwo :=
    Derives.appendRight
      (Derives.prepend (u ++ u) (derivesEndpointSquares v z)) z
  have stepThree :=
    Derives.prepend (((u ++ u) ++ (v ++ v)))
      (derivesPowerContraction z)
  have stepFour :=
    (derivesInteriorDuplication (u ++ u) v (z ++ z)).symm
  exact Derives.trans
    (by simpa [Word.append_assoc] using stepOne)
    (Derives.trans
      (by simpa [Word.append_assoc] using stepTwo)
      (Derives.trans
        (by simpa [Word.append_assoc] using stepThree)
        (by simpa [Word.append_assoc] using stepFour)))

/-- Recover `xxyzz = xyzzx`. -/
theorem derivesClosedTerminalSwitch
    (u v z : Word Nat) :
    Derives basis
      (((u ++ u) ++ v) ++ (z ++ z))
      ((((u ++ v) ++ z) ++ z) ++ u) := by
  have stepOne := (derivesMarkerToClosed u v z).symm
  have stepTwo := derivesInteriorDuplication (u ++ v) z u
  exact Derives.trans
    (by simpa [Word.append_assoc] using stepOne)
    (by simpa [Word.append_assoc] using stepTwo)

/-- Every axiom of the `S5_345` normalizer follows from the three-law basis. -/
theorem s5_345AxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ S5_345.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [S5_345.basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact derivesPowerExpansion (Word.singleton 0)
  · exact derivesLeftEndpointExpansion
      (Word.singleton 0) (Word.singleton 1)
  · exact derivesRightEndpointExpansion
      (Word.singleton 0) (Word.singleton 1)
  · exact derivesSquareInterleave
      (Word.singleton 0) (Word.singleton 1)
  · exact derivesSquareFinalSwitch
      (Word.singleton 0) (Word.singleton 1)
  · exact derivesDoubledInitialMove
      (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)
  · exact derivesOpenTerminalSwitch
      (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)
  · exact derivesClosedTerminalSwitch
      (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem basisRoundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinThree).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basisRoundTripChecked) identity member

/-- A finite table models the exact basis after its finite images check. -/
theorem modelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basisRoundTrip identity member] at finiteValid
  exact finiteValid

end SemigroupBasis.CoRoots.S5_343
