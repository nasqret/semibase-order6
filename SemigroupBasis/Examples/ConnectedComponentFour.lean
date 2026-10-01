import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for the catalogue table
`[[1,1,1,1],[1,1,1,2],[1,2,3,2],[1,1,1,4]]`. -/
def connectedComponentFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 1 then (if b = 3 then 1 else 0) else
      if a = 2 then
        if b = 0 then 0 else if b = 1 then 1 else
          if b = 2 then 2 else 1
      else
        if b = 3 then 3 else 0

/-- The root catalogue representative `S4_70`. -/
def connectedComponentFour : FiniteTable where
  order := 4
  mul := connectedComponentFourMul
  assoc := by decide

def connectedComponentXX : Word Nat := ⟨0, [0]⟩
def connectedComponentXXX : Word Nat := ⟨0, [0, 0]⟩
def connectedComponentXYX : Word Nat := ⟨0, [1, 0]⟩
def connectedComponentXXYX : Word Nat := ⟨0, [0, 1, 0]⟩
def connectedComponentXYYX : Word Nat := ⟨0, [1, 1, 0]⟩
def connectedComponentXYXX : Word Nat := ⟨0, [1, 0, 0]⟩
def connectedComponentXYXY : Word Nat := ⟨0, [1, 0, 1]⟩
def connectedComponentYXY : Word Nat := ⟨1, [0, 1]⟩

def connectedComponentPowerLaw : Identity Nat :=
  ⟨connectedComponentXX, connectedComponentXXX⟩

def connectedComponentLeftDuplicationLaw : Identity Nat :=
  ⟨connectedComponentXYX, connectedComponentXXYX⟩

def connectedComponentMiddleDuplicationLaw : Identity Nat :=
  ⟨connectedComponentXYX, connectedComponentXYYX⟩

def connectedComponentRightDuplicationLaw : Identity Nat :=
  ⟨connectedComponentXYX, connectedComponentXYXX⟩

def connectedComponentAlternatingLaw : Identity Nat :=
  ⟨connectedComponentXYX, connectedComponentXYXY⟩

def connectedComponentRotationLaw : Identity Nat :=
  ⟨connectedComponentXYX, connectedComponentYXY⟩

/-- The exact six-law basis
`xx = xxx`, `xyx = xxyx`, `xyx = xyyx`, `xyx = xyxx`,
`xyx = xyxy`, `xyx = yxy`. -/
def connectedComponentFourBasis : List (Identity Nat) :=
  [connectedComponentPowerLaw, connectedComponentLeftDuplicationLaw,
    connectedComponentMiddleDuplicationLaw,
    connectedComponentRightDuplicationLaw,
    connectedComponentAlternatingLaw, connectedComponentRotationLaw]

private def connectedComponentInstantiateTwo
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem connectedComponentDerivesPowerExpansion (u : Word Nat) :
    Derives connectedComponentFourBasis
      (u ++ u) ((u ++ u) ++ u) := by
  have hbase :
      Derives connectedComponentFourBasis
        connectedComponentXX connectedComponentXXX :=
    Derives.fromBasis (e := connectedComponentPowerLaw) <|
      List.Mem.head _
  have h :=
    Derives.subst hbase (connectedComponentInstantiateTwo u u)
  simpa [connectedComponentFourBasis, connectedComponentPowerLaw,
    connectedComponentXX, connectedComponentXXX,
    connectedComponentInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem connectedComponentDerivesLeftDuplication
    (u v : Word Nat) :
    Derives connectedComponentFourBasis
      ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have hbase :
      Derives connectedComponentFourBasis
        connectedComponentXYX connectedComponentXXYX :=
    Derives.fromBasis (e := connectedComponentLeftDuplicationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (connectedComponentInstantiateTwo u v)
  simpa [connectedComponentFourBasis,
    connectedComponentLeftDuplicationLaw,
    connectedComponentXYX, connectedComponentXXYX,
    connectedComponentInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem connectedComponentDerivesMiddleDuplication
    (u v : Word Nat) :
    Derives connectedComponentFourBasis
      ((u ++ v) ++ u) (((u ++ v) ++ v) ++ u) := by
  have hbase :
      Derives connectedComponentFourBasis
        connectedComponentXYX connectedComponentXYYX :=
    Derives.fromBasis (e := connectedComponentMiddleDuplicationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (connectedComponentInstantiateTwo u v)
  simpa [connectedComponentFourBasis,
    connectedComponentMiddleDuplicationLaw,
    connectedComponentXYX, connectedComponentXYYX,
    connectedComponentInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem connectedComponentDerivesRightDuplication
    (u v : Word Nat) :
    Derives connectedComponentFourBasis
      ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have hbase :
      Derives connectedComponentFourBasis
        connectedComponentXYX connectedComponentXYXX :=
    Derives.fromBasis (e := connectedComponentRightDuplicationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (connectedComponentInstantiateTwo u v)
  simpa [connectedComponentFourBasis,
    connectedComponentRightDuplicationLaw,
    connectedComponentXYX, connectedComponentXYXX,
    connectedComponentInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem connectedComponentDerivesAlternating
    (u v : Word Nat) :
    Derives connectedComponentFourBasis
      ((u ++ v) ++ u) (((u ++ v) ++ u) ++ v) := by
  have hbase :
      Derives connectedComponentFourBasis
        connectedComponentXYX connectedComponentXYXY :=
    Derives.fromBasis (e := connectedComponentAlternatingLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (connectedComponentInstantiateTwo u v)
  simpa [connectedComponentFourBasis,
    connectedComponentAlternatingLaw,
    connectedComponentXYX, connectedComponentXYXY,
    connectedComponentInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem connectedComponentDerivesRotation
    (u v : Word Nat) :
    Derives connectedComponentFourBasis
      ((u ++ v) ++ u) ((v ++ u) ++ v) := by
  have hbase :
      Derives connectedComponentFourBasis
        connectedComponentXYX connectedComponentYXY :=
    Derives.fromBasis (e := connectedComponentRotationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (connectedComponentInstantiateTwo u v)
  simpa [connectedComponentFourBasis, connectedComponentRotationLaw,
    connectedComponentXYX, connectedComponentYXY,
    connectedComponentInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

/-- Interchange two arbitrary nonempty blocks inside matching endpoints:
`uvwu = uwvu`. -/
theorem connectedComponentDerivesInteriorSwap
    (u v w : Word Nat) :
    Derives connectedComponentFourBasis
      (((u ++ v) ++ w) ++ u)
      (((u ++ w) ++ v) ++ u) := by
  have first :=
    connectedComponentDerivesMiddleDuplication u (v ++ w)
  have second :=
    Derives.appendRight
      (Derives.prepend (u ++ v)
        (connectedComponentDerivesMiddleDuplication w v))
      u
  have third :=
    Derives.appendRight
      (Derives.prepend u
        (connectedComponentDerivesRotation v w))
      ((v ++ w) ++ u)
  have fourth :=
    Derives.appendRight
      (Derives.prepend (u ++ w)
        (Derives.symm
          (connectedComponentDerivesAlternating v w)))
      u
  have fifth :=
    Derives.symm <|
      connectedComponentDerivesMiddleDuplication u (w ++ v)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third) <|
        Derives.trans
          (by simpa [Word.append_assoc] using fourth)
          (by simpa [Word.append_assoc] using fifth)

/-- Delete a middle occurrence from three separated occurrences:
`uvuwu = uvwu`. -/
theorem connectedComponentDerivesThirdOccurrenceDeletion
    (u v w : Word Nat) :
    Derives connectedComponentFourBasis
      ((((u ++ v) ++ u) ++ w) ++ u)
      (((u ++ v) ++ w) ++ u) := by
  have first :=
    connectedComponentDerivesInteriorSwap u v (u ++ w)
  have second :=
    Derives.symm <|
      connectedComponentDerivesLeftDuplication u (w ++ v)
  have third :=
    connectedComponentDerivesInteriorSwap u w v
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second)
      (by simpa [Word.append_assoc] using third)

/-- Delete one doubled interior block when nonempty blocks occur on both
sides: `uazzbu = uazbu`. -/
theorem connectedComponentDerivesInteriorContraction
    (u a z b : Word Nat) :
    Derives connectedComponentFourBasis
      (((((u ++ a) ++ z) ++ z) ++ b) ++ u)
      ((((u ++ a) ++ z) ++ b) ++ u) := by
  have first :=
    connectedComponentDerivesMiddleDuplication u
      (((a ++ z) ++ z) ++ b)
  have second :=
    Derives.appendRight
      (Derives.prepend (u ++ a)
        (Derives.symm <|
          connectedComponentDerivesLeftDuplication z (b ++ a)))
      ((z ++ b) ++ u)
  have third :=
    Derives.appendRight
      (Derives.prepend (u ++ a)
        (Derives.symm <|
          connectedComponentDerivesRightDuplication z (b ++ a)))
      (b ++ u)
  have fourth :=
    Derives.symm <|
      connectedComponentDerivesMiddleDuplication u
        ((a ++ z) ++ b)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third)
        (by simpa [Word.append_assoc] using fourth)

/-- Left-boundary case of interior contraction: `uzzbu = uzbu`. -/
theorem connectedComponentDerivesLeftInteriorContraction
    (u z b : Word Nat) :
    Derives connectedComponentFourBasis
      ((((u ++ z) ++ z) ++ b) ++ u)
      (((u ++ z) ++ b) ++ u) := by
  have first :=
    connectedComponentDerivesMiddleDuplication u ((z ++ z) ++ b)
  have second :=
    Derives.appendRight
      (Derives.prepend u
        (Derives.symm <|
          connectedComponentDerivesLeftDuplication z b))
      ((z ++ b) ++ u)
  have third :=
    Derives.appendRight
      (Derives.prepend (u ++ z)
        (Derives.symm <|
          connectedComponentDerivesMiddleDuplication b z))
      u
  have fourth :=
    Derives.symm <|
      connectedComponentDerivesMiddleDuplication u (z ++ b)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third)
        (by simpa [Word.append_assoc] using fourth)

/-- Right-boundary case of interior contraction: `uazzu = uazu`. -/
theorem connectedComponentDerivesRightInteriorContraction
    (u a z : Word Nat) :
    Derives connectedComponentFourBasis
      ((((u ++ a) ++ z) ++ z) ++ u)
      (((u ++ a) ++ z) ++ u) := by
  have first :=
    connectedComponentDerivesMiddleDuplication u ((a ++ z) ++ z)
  have second :=
    Derives.appendRight
      (Derives.prepend (u ++ a)
        (Derives.symm <|
          connectedComponentDerivesLeftDuplication z a))
      (z ++ u)
  have third :=
    Derives.appendRight
      (Derives.prepend (u ++ a)
        (Derives.symm <|
          connectedComponentDerivesRightDuplication z a))
      u
  have fourth :=
    Derives.symm <|
      connectedComponentDerivesMiddleDuplication u (a ++ z)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third)
        (by simpa [Word.append_assoc] using fourth)

/-- Both-boundaries case of interior contraction: `uzzu = uzu`. -/
theorem connectedComponentDerivesMiddleContraction
    (u z : Word Nat) :
    Derives connectedComponentFourBasis
      (((u ++ z) ++ z) ++ u)
      ((u ++ z) ++ u) :=
  Derives.symm (connectedComponentDerivesMiddleDuplication u z)

/-- The first documented short crossing chain:
`xyxzy = xyyzx`. -/
theorem connectedComponentDerivesShortCrossingToLeft
    (x y z : Word Nat) :
    Derives connectedComponentFourBasis
      ((((x ++ y) ++ x) ++ z) ++ y)
      ((((x ++ y) ++ y) ++ z) ++ x) := by
  have first :=
    Derives.appendRight
      (connectedComponentDerivesLeftDuplication x y)
      (z ++ y)
  have second :=
    Derives.prepend (x ++ x)
      (connectedComponentDerivesInteriorSwap y x z)
  have third :=
    Derives.appendRight
      (connectedComponentDerivesInteriorSwap x (x ++ y) z)
      y
  have fourthCore :
      Derives connectedComponentFourBasis
        (((x ++ y) ++ x) ++ y)
        (((x ++ y) ++ y) ++ x) :=
    Derives.trans
      (Derives.symm <|
        connectedComponentDerivesAlternating x y)
      (connectedComponentDerivesMiddleDuplication x y)
  have fourth :=
    Derives.prepend (x ++ z) fourthCore
  have fifth :=
    connectedComponentDerivesInteriorSwap x z ((x ++ y) ++ y)
  have sixth :=
    Derives.symm <|
      connectedComponentDerivesLeftDuplication x ((y ++ y) ++ z)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third) <|
        Derives.trans
          (by simpa [Word.append_assoc] using fourth) <|
          Derives.trans
            (by simpa [Word.append_assoc] using fifth)
            (by simpa [Word.append_assoc] using sixth)

/-- The second documented short crossing chain:
`xyxzy = yxxzy`. -/
theorem connectedComponentDerivesShortCrossingToRight
    (x y z : Word Nat) :
    Derives connectedComponentFourBasis
      ((((x ++ y) ++ x) ++ z) ++ y)
      ((((y ++ x) ++ x) ++ z) ++ y) := by
  have first :=
    Derives.appendRight
      (connectedComponentDerivesMiddleDuplication x y)
      (z ++ y)
  have secondCore :
      Derives connectedComponentFourBasis
        (((x ++ y) ++ y) ++ x)
        (((y ++ x) ++ y) ++ x) :=
    Derives.trans
      (Derives.symm <|
        connectedComponentDerivesMiddleDuplication x y) <|
    Derives.trans
      (connectedComponentDerivesRotation x y)
      (connectedComponentDerivesAlternating y x)
  have second :=
    Derives.appendRight secondCore (z ++ y)
  have third :=
    connectedComponentDerivesInteriorSwap y x ((y ++ x) ++ z)
  have fourth :=
    Derives.symm <|
      connectedComponentDerivesLeftDuplication y ((x ++ z) ++ x)
  have fifth :=
    connectedComponentDerivesInteriorSwap y (x ++ z) x
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third) <|
        Derives.trans
          (by simpa [Word.append_assoc] using fourth)
          (by simpa [Word.append_assoc] using fifth)

/-- Switch matching endpoints across a nonempty interior:
`xyyzx = yxxzy`. -/
theorem connectedComponentDerivesEndpointSwitch
    (x y z : Word Nat) :
    Derives connectedComponentFourBasis
      ((((x ++ y) ++ y) ++ z) ++ x)
      ((((y ++ x) ++ x) ++ z) ++ y) :=
  Derives.trans
    (Derives.symm <|
      connectedComponentDerivesShortCrossingToLeft x y z)
    (connectedComponentDerivesShortCrossingToRight x y z)

/-- Empty-interior endpoint switch: `xyyx = yxxy`. -/
theorem connectedComponentDerivesShortEndpointSwitch
    (x y : Word Nat) :
    Derives connectedComponentFourBasis
      (((x ++ y) ++ y) ++ x)
      (((y ++ x) ++ x) ++ y) :=
  Derives.trans
    (Derives.symm <|
      connectedComponentDerivesMiddleDuplication x y) <|
  Derives.trans
    (connectedComponentDerivesRotation x y)
    (connectedComponentDerivesMiddleDuplication y x)

/-- Absorb the shortest crossing pair: `xyxzy = xyzx`. -/
theorem connectedComponentDerivesShortCrossing
    (x y z : Word Nat) :
    Derives connectedComponentFourBasis
      ((((x ++ y) ++ x) ++ z) ++ y)
      (((x ++ y) ++ z) ++ x) :=
  Derives.trans
    (connectedComponentDerivesShortCrossingToLeft x y z)
    (connectedComponentDerivesLeftInteriorContraction x y z)

/-- Absorb a crossing pair while preserving the order of both nonempty
fillers: `xyzxuy = xyzux`. -/
theorem connectedComponentDerivesCrossing
    (x y z u : Word Nat) :
    Derives connectedComponentFourBasis
      (((((x ++ y) ++ z) ++ x) ++ u) ++ y)
      ((((x ++ y) ++ z) ++ u) ++ x) := by
  have first :=
    Derives.appendRight
      (Derives.symm <|
        connectedComponentDerivesThirdOccurrenceDeletion x y z)
      (u ++ y)
  have second :=
    connectedComponentDerivesShortCrossing x y ((z ++ x) ++ u)
  have third :=
    connectedComponentDerivesThirdOccurrenceDeletion x (y ++ z) u
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second)
      (by simpa [Word.append_assoc] using third)

private theorem connectedComponentMul_power (a : Fin 4) :
    connectedComponentFourMul a a =
      connectedComponentFourMul
        (connectedComponentFourMul a a) a := by
  decide +revert

private theorem connectedComponentMul_leftDuplication
    (a b : Fin 4) :
    connectedComponentFourMul (connectedComponentFourMul a b) a =
      connectedComponentFourMul
        (connectedComponentFourMul
          (connectedComponentFourMul a a) b) a := by
  decide +revert

private theorem connectedComponentMul_middleDuplication
    (a b : Fin 4) :
    connectedComponentFourMul (connectedComponentFourMul a b) a =
      connectedComponentFourMul
        (connectedComponentFourMul
          (connectedComponentFourMul a b) b) a := by
  decide +revert

private theorem connectedComponentMul_rightDuplication
    (a b : Fin 4) :
    connectedComponentFourMul (connectedComponentFourMul a b) a =
      connectedComponentFourMul
        (connectedComponentFourMul
          (connectedComponentFourMul a b) a) a := by
  decide +revert

private theorem connectedComponentMul_alternating
    (a b : Fin 4) :
    connectedComponentFourMul (connectedComponentFourMul a b) a =
      connectedComponentFourMul
        (connectedComponentFourMul
          (connectedComponentFourMul a b) a) b := by
  decide +revert

private theorem connectedComponentMul_rotation
    (a b : Fin 4) :
    connectedComponentFourMul (connectedComponentFourMul a b) a =
      connectedComponentFourMul
        (connectedComponentFourMul b a) b := by
  decide +revert

theorem connectedComponentFourBasis_models :
    Models connectedComponentFour.semigroup
      connectedComponentFourBasis := by
  intro e he
  simp only [connectedComponentFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · intro valuation
    exact connectedComponentMul_power (valuation 0)
  · intro valuation
    exact connectedComponentMul_leftDuplication
      (valuation 0) (valuation 1)
  · intro valuation
    exact connectedComponentMul_middleDuplication
      (valuation 0) (valuation 1)
  · intro valuation
    exact connectedComponentMul_rightDuplication
      (valuation 0) (valuation 1)
  · intro valuation
    exact connectedComponentMul_alternating
      (valuation 0) (valuation 1)
  · intro valuation
    exact connectedComponentMul_rotation
      (valuation 0) (valuation 1)

end SemigroupBasis.Examples
