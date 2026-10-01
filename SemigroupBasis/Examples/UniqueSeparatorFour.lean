import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for the catalogue table
`[[1,1,1,1],[1,1,1,2],[1,2,3,1],[1,1,1,4]]`. -/
def uniqueSeparatorFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 1 then (if b = 3 then 1 else 0) else
      if a = 2 then
        if b = 0 then 0 else if b = 1 then 1 else
          if b = 2 then 2 else 0
      else
        if b = 3 then 3 else 0

/-- The root catalogue representative `S4_69`. -/
def uniqueSeparatorFour : FiniteTable where
  order := 4
  mul := uniqueSeparatorFourMul
  assoc := by decide

def uniqueSeparatorXX : Word Nat := ⟨0, [0]⟩
def uniqueSeparatorXXX : Word Nat := ⟨0, [0, 0]⟩
def uniqueSeparatorXYX : Word Nat := ⟨0, [1, 0]⟩
def uniqueSeparatorXXYX : Word Nat := ⟨0, [0, 1, 0]⟩
def uniqueSeparatorXYYX : Word Nat := ⟨0, [1, 1, 0]⟩
def uniqueSeparatorXYXX : Word Nat := ⟨0, [1, 0, 0]⟩
def uniqueSeparatorXYXY : Word Nat := ⟨0, [1, 0, 1]⟩
def uniqueSeparatorXXYY : Word Nat := ⟨0, [0, 1, 1]⟩
def uniqueSeparatorYXY : Word Nat := ⟨1, [0, 1]⟩

def uniqueSeparatorPowerLaw : Identity Nat :=
  ⟨uniqueSeparatorXX, uniqueSeparatorXXX⟩

def uniqueSeparatorLeftDuplicationLaw : Identity Nat :=
  ⟨uniqueSeparatorXYX, uniqueSeparatorXXYX⟩

def uniqueSeparatorMiddleDuplicationLaw : Identity Nat :=
  ⟨uniqueSeparatorXYX, uniqueSeparatorXYYX⟩

def uniqueSeparatorRightDuplicationLaw : Identity Nat :=
  ⟨uniqueSeparatorXYX, uniqueSeparatorXYXX⟩

def uniqueSeparatorAlternatingLaw : Identity Nat :=
  ⟨uniqueSeparatorXYX, uniqueSeparatorXYXY⟩

def uniqueSeparatorSquaresLaw : Identity Nat :=
  ⟨uniqueSeparatorXYX, uniqueSeparatorXXYY⟩

def uniqueSeparatorRotationLaw : Identity Nat :=
  ⟨uniqueSeparatorXYX, uniqueSeparatorYXY⟩

/-- The exact seven-law basis
`xx = xxx`, `xyx = xxyx`, `xyx = xyyx`, `xyx = xyxx`,
`xyx = xyxy`, `xyx = xxyy`, `xyx = yxy`. -/
def uniqueSeparatorFourBasis : List (Identity Nat) :=
  [uniqueSeparatorPowerLaw, uniqueSeparatorLeftDuplicationLaw,
    uniqueSeparatorMiddleDuplicationLaw, uniqueSeparatorRightDuplicationLaw,
    uniqueSeparatorAlternatingLaw, uniqueSeparatorSquaresLaw,
    uniqueSeparatorRotationLaw]

private def uniqueSeparatorInstantiateTwo
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem uniqueSeparatorDerivesPowerExpansion (u : Word Nat) :
    Derives uniqueSeparatorFourBasis
      (u ++ u) ((u ++ u) ++ u) := by
  have hbase :
      Derives uniqueSeparatorFourBasis
        uniqueSeparatorXX uniqueSeparatorXXX :=
    Derives.fromBasis (e := uniqueSeparatorPowerLaw) <|
      List.Mem.head _
  have h :=
    Derives.subst hbase (uniqueSeparatorInstantiateTwo u u)
  simpa [uniqueSeparatorFourBasis, uniqueSeparatorPowerLaw,
    uniqueSeparatorXX, uniqueSeparatorXXX,
    uniqueSeparatorInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem uniqueSeparatorDerivesLeftDuplication (u v : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have hbase :
      Derives uniqueSeparatorFourBasis
        uniqueSeparatorXYX uniqueSeparatorXXYX :=
    Derives.fromBasis (e := uniqueSeparatorLeftDuplicationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (uniqueSeparatorInstantiateTwo u v)
  simpa [uniqueSeparatorFourBasis, uniqueSeparatorLeftDuplicationLaw,
    uniqueSeparatorXYX, uniqueSeparatorXXYX,
    uniqueSeparatorInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem uniqueSeparatorDerivesMiddleDuplication (u v : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((u ++ v) ++ u) (((u ++ v) ++ v) ++ u) := by
  have hbase :
      Derives uniqueSeparatorFourBasis
        uniqueSeparatorXYX uniqueSeparatorXYYX :=
    Derives.fromBasis (e := uniqueSeparatorMiddleDuplicationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (uniqueSeparatorInstantiateTwo u v)
  simpa [uniqueSeparatorFourBasis, uniqueSeparatorMiddleDuplicationLaw,
    uniqueSeparatorXYX, uniqueSeparatorXYYX,
    uniqueSeparatorInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem uniqueSeparatorDerivesRightDuplication (u v : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have hbase :
      Derives uniqueSeparatorFourBasis
        uniqueSeparatorXYX uniqueSeparatorXYXX :=
    Derives.fromBasis (e := uniqueSeparatorRightDuplicationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (uniqueSeparatorInstantiateTwo u v)
  simpa [uniqueSeparatorFourBasis, uniqueSeparatorRightDuplicationLaw,
    uniqueSeparatorXYX, uniqueSeparatorXYXX,
    uniqueSeparatorInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem uniqueSeparatorDerivesAlternating (u v : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((u ++ v) ++ u) (((u ++ v) ++ u) ++ v) := by
  have hbase :
      Derives uniqueSeparatorFourBasis
        uniqueSeparatorXYX uniqueSeparatorXYXY :=
    Derives.fromBasis (e := uniqueSeparatorAlternatingLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (uniqueSeparatorInstantiateTwo u v)
  simpa [uniqueSeparatorFourBasis, uniqueSeparatorAlternatingLaw,
    uniqueSeparatorXYX, uniqueSeparatorXYXY,
    uniqueSeparatorInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem uniqueSeparatorDerivesSquares (u v : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((u ++ v) ++ u) ((u ++ u) ++ (v ++ v)) := by
  have hbase :
      Derives uniqueSeparatorFourBasis
        uniqueSeparatorXYX uniqueSeparatorXXYY :=
    Derives.fromBasis (e := uniqueSeparatorSquaresLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (uniqueSeparatorInstantiateTwo u v)
  simpa [uniqueSeparatorFourBasis, uniqueSeparatorSquaresLaw,
    uniqueSeparatorXYX, uniqueSeparatorXXYY,
    uniqueSeparatorInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem uniqueSeparatorDerivesRotation (u v : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((u ++ v) ++ u) ((v ++ u) ++ v) := by
  have hbase :
      Derives uniqueSeparatorFourBasis
        uniqueSeparatorXYX uniqueSeparatorYXY :=
    Derives.fromBasis (e := uniqueSeparatorRotationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h :=
    Derives.subst hbase (uniqueSeparatorInstantiateTwo u v)
  simpa [uniqueSeparatorFourBasis, uniqueSeparatorRotationLaw,
    uniqueSeparatorXYX, uniqueSeparatorYXY,
    uniqueSeparatorInstantiateTwo, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

/-- Arbitrary nonempty blocks may be interchanged inside matching endpoints:
`uvwu = uwvu`. This is Edmunds' interior-commutation law from `L₈`. -/
theorem uniqueSeparatorDerivesInteriorSwap (u v w : Word Nat) :
    Derives uniqueSeparatorFourBasis
      (((u ++ v) ++ w) ++ u)
      (((u ++ w) ++ v) ++ u) := by
  have first :=
    uniqueSeparatorDerivesMiddleDuplication u (v ++ w)
  have second :=
    Derives.appendRight
      (Derives.prepend (u ++ v)
        (uniqueSeparatorDerivesMiddleDuplication w v))
      u
  have third :=
    Derives.appendRight
      (Derives.prepend u
        (uniqueSeparatorDerivesRotation v w))
      ((v ++ w) ++ u)
  have fourth :=
    Derives.appendRight
      (Derives.prepend (u ++ w)
        (Derives.symm
          (uniqueSeparatorDerivesAlternating v w)))
      u
  have fifth :=
    Derives.symm <|
      uniqueSeparatorDerivesMiddleDuplication u (w ++ v)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third) <|
        Derives.trans
          (by simpa [Word.append_assoc] using fourth)
          (by simpa [Word.append_assoc] using fifth)

/-- Products of two square blocks commute. -/
theorem uniqueSeparatorDerivesSquareCommutation (u v : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((u ++ u) ++ (v ++ v))
      ((v ++ v) ++ (u ++ u)) := by
  exact Derives.trans
    (Derives.symm (uniqueSeparatorDerivesSquares u v)) <|
    Derives.trans
      (uniqueSeparatorDerivesRotation u v)
      (uniqueSeparatorDerivesSquares v u)

/-- Delete a middle occurrence from three separated occurrences:
`uvuwu = uvwu`. This is the first law of Edmunds' `L₃`. -/
theorem uniqueSeparatorDerivesThirdOccurrenceDeletion
    (u v w : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((((u ++ v) ++ u) ++ w) ++ u)
      (((u ++ v) ++ w) ++ u) := by
  have first :=
    uniqueSeparatorDerivesInteriorSwap u v (u ++ w)
  have second :=
    Derives.symm <|
      uniqueSeparatorDerivesLeftDuplication u (w ++ v)
  have third :=
    uniqueSeparatorDerivesInteriorSwap u w v
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second)
      (by simpa [Word.append_assoc] using third)

/-- Delete one doubled interior block when nonempty blocks occur on both
sides: `uazzbu = uazbu`. -/
theorem uniqueSeparatorDerivesInteriorContraction
    (u a z b : Word Nat) :
    Derives uniqueSeparatorFourBasis
      (((((u ++ a) ++ z) ++ z) ++ b) ++ u)
      ((((u ++ a) ++ z) ++ b) ++ u) := by
  have first :=
    uniqueSeparatorDerivesMiddleDuplication u
      (((a ++ z) ++ z) ++ b)
  have second :=
    Derives.appendRight
      (Derives.prepend (u ++ a)
        (Derives.symm <|
          uniqueSeparatorDerivesLeftDuplication z (b ++ a)))
      ((z ++ b) ++ u)
  have third :=
    Derives.appendRight
      (Derives.prepend (u ++ a)
        (Derives.symm <|
          uniqueSeparatorDerivesRightDuplication z (b ++ a)))
      (b ++ u)
  have fourth :=
    Derives.symm <|
      uniqueSeparatorDerivesMiddleDuplication u
        ((a ++ z) ++ b)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third)
        (by simpa [Word.append_assoc] using fourth)

/-- Left-boundary case of interior contraction: `uzzbu = uzbu`. -/
theorem uniqueSeparatorDerivesLeftInteriorContraction
    (u z b : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((((u ++ z) ++ z) ++ b) ++ u)
      (((u ++ z) ++ b) ++ u) := by
  have first :=
    uniqueSeparatorDerivesMiddleDuplication u ((z ++ z) ++ b)
  have second :=
    Derives.appendRight
      (Derives.prepend u
        (Derives.symm <|
          uniqueSeparatorDerivesLeftDuplication z b))
      ((z ++ b) ++ u)
  have third :=
    Derives.appendRight
      (Derives.prepend (u ++ z)
        (Derives.symm <|
          uniqueSeparatorDerivesMiddleDuplication b z))
      u
  have fourth :=
    Derives.symm <|
      uniqueSeparatorDerivesMiddleDuplication u (z ++ b)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third)
        (by simpa [Word.append_assoc] using fourth)

/-- Right-boundary case of interior contraction: `uazzu = uazu`. -/
theorem uniqueSeparatorDerivesRightInteriorContraction
    (u a z : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((((u ++ a) ++ z) ++ z) ++ u)
      (((u ++ a) ++ z) ++ u) := by
  have first :=
    uniqueSeparatorDerivesMiddleDuplication u ((a ++ z) ++ z)
  have second :=
    Derives.appendRight
      (Derives.prepend (u ++ a)
        (Derives.symm <|
          uniqueSeparatorDerivesLeftDuplication z a))
      (z ++ u)
  have third :=
    Derives.appendRight
      (Derives.prepend (u ++ a)
        (Derives.symm <|
          uniqueSeparatorDerivesRightDuplication z a))
      u
  have fourth :=
    Derives.symm <|
      uniqueSeparatorDerivesMiddleDuplication u (a ++ z)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third)
        (by simpa [Word.append_assoc] using fourth)

/-- Both-boundaries case of interior contraction: `uzzu = uzu`. -/
theorem uniqueSeparatorDerivesMiddleContraction
    (u z : Word Nat) :
    Derives uniqueSeparatorFourBasis
      (((u ++ z) ++ z) ++ u)
      ((u ++ z) ++ u) :=
  Derives.symm (uniqueSeparatorDerivesMiddleDuplication u z)

/-- Merge the shortest crossing pair: `uvuzv = uvzu`. -/
theorem uniqueSeparatorDerivesShortCrossingAbsorption
    (u v z : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((((u ++ v) ++ u) ++ z) ++ v)
      (((u ++ v) ++ z) ++ u) := by
  have first :=
    Derives.appendRight
      (uniqueSeparatorDerivesSquares u v)
      (z ++ v)
  have second :=
    Derives.prepend ((u ++ u) ++ v)
      (uniqueSeparatorDerivesRotation v z)
  have third :=
    Derives.symm <|
      uniqueSeparatorDerivesSquares u (v ++ z)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second)
      (by simpa [Word.append_assoc] using third)

/-- Delete the second occurrence of a repeated block nested inside matching
outer endpoints: `uvzwzqu = uvzwqu`. -/
theorem uniqueSeparatorDerivesNestedRepeatDeletion
    (u v z w q : Word Nat) :
    Derives uniqueSeparatorFourBasis
      (((((((u ++ v) ++ z) ++ w) ++ z) ++ q) ++ u))
      (((((u ++ v) ++ z) ++ w) ++ q) ++ u) := by
  have first :=
    uniqueSeparatorDerivesInteriorSwap u v
      (((z ++ w) ++ z) ++ q)
  have second :=
    Derives.appendRight
      (Derives.prepend u
        (uniqueSeparatorDerivesLeftDuplication z w))
      (((q ++ v) ++ u))
  have third :=
    Derives.appendRight
      (Derives.prepend (u ++ z)
        (uniqueSeparatorDerivesRotation z w))
      (((q ++ v) ++ u))
  have fourth :=
    uniqueSeparatorDerivesLeftDuplication u
      ((((((z ++ w) ++ z) ++ w) ++ q) ++ v))
  have fifth :=
    Derives.appendRight
      (Derives.symm <|
        uniqueSeparatorDerivesSquares u (z ++ w))
      (((q ++ v) ++ u))
  have sixth :=
    uniqueSeparatorDerivesInteriorSwap u (z ++ w)
      (((u ++ q) ++ v))
  have seventh :=
    Derives.symm <|
      uniqueSeparatorDerivesLeftDuplication u
        (((q ++ v) ++ (z ++ w)))
  have eighth :=
    uniqueSeparatorDerivesInteriorSwap u q
      (((v ++ z) ++ w))
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third) <|
        Derives.trans
          (by simpa [Word.append_assoc] using fourth) <|
          Derives.trans
            (by simpa [Word.append_assoc] using fifth) <|
            Derives.trans
              (by simpa [Word.append_assoc] using sixth) <|
              Derives.trans
                (by simpa [Word.append_assoc] using seventh)
                (by simpa [Word.append_assoc] using eighth)

/-- Merge two crossing repeated intervals while retaining the first endpoint:
`uvzwuqz = uvzwqu`. -/
theorem uniqueSeparatorDerivesCrossingAbsorption
    (u v z w q : Word Nat) :
    Derives uniqueSeparatorFourBasis
      (((((((u ++ v) ++ z) ++ w) ++ u) ++ q) ++ z))
      (((((u ++ v) ++ z) ++ w) ++ q) ++ u) := by
  have firstCore :=
    uniqueSeparatorDerivesInteriorSwap z w (u ++ q)
  have first :=
    Derives.prepend (u ++ v) firstCore
  have second :=
    Derives.appendRight
      (uniqueSeparatorDerivesSquares u (v ++ z))
      (((q ++ w) ++ z))
  have thirdCore :=
    uniqueSeparatorDerivesInteriorSwap z q w
  have third :=
    Derives.prepend ((((u ++ u) ++ v) ++ z) ++ v) thirdCore
  have fourth :=
    Derives.prepend ((((u ++ u) ++ v) ++ z) ++ v)
      (uniqueSeparatorDerivesRotation z (w ++ q))
  have fifthCore :=
    uniqueSeparatorDerivesInteriorSwap z v (w ++ q)
  have fifth :=
    Derives.appendRight
      (Derives.prepend ((u ++ u) ++ v) fifthCore)
      (w ++ q)
  have sixth :=
    Derives.symm <|
      uniqueSeparatorDerivesSquares u
        (((v ++ z) ++ w) ++ q)
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

/-- The first (long-context) law in Edmunds' `L₆`. -/
theorem uniqueSeparatorDerivesL6Long
    (u v w q : Word Nat) :
    Derives uniqueSeparatorFourBasis
      (((((u ++ v) ++ w) ++ u) ++ q) ++ v)
      (((((v ++ u) ++ w) ++ u) ++ q) ++ v) := by
  have first :=
    Derives.prepend u <|
      uniqueSeparatorDerivesRotation v ((w ++ u) ++ q)
  have second :=
    Derives.appendRight
      (Derives.prepend u <|
        uniqueSeparatorDerivesMiddleDuplication w ((u ++ q) ++ v))
      (u ++ q)
  have third :=
    Derives.appendRight
      (Derives.prepend (u ++ w) <|
        Derives.symm <|
          uniqueSeparatorDerivesAlternating u (q ++ v))
      ((w ++ u) ++ q)
  have fourth :=
    uniqueSeparatorDerivesRotation (((u ++ w) ++ u) ++ q) v
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third)
        (by simpa [Word.append_assoc] using fourth)

/-- The second (shorter-context) law in Edmunds' `L₆`. -/
theorem uniqueSeparatorDerivesL6Medium
    (u v w : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((((u ++ v) ++ w) ++ u) ++ v)
      ((((v ++ u) ++ w) ++ u) ++ v) := by
  have first :=
    Derives.prepend u <|
      uniqueSeparatorDerivesRotation v (w ++ u)
  have second :=
    Derives.appendRight
      (Derives.prepend u <|
        uniqueSeparatorDerivesMiddleDuplication w (u ++ v))
      u
  have third :=
    Derives.appendRight
      (Derives.prepend (u ++ w) <|
        Derives.symm <|
          uniqueSeparatorDerivesAlternating u v)
      (w ++ u)
  have fourth :=
    uniqueSeparatorDerivesRotation ((u ++ w) ++ u) v
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third)
        (by simpa [Word.append_assoc] using fourth)

/-- The third law in Edmunds' `L₆`. -/
theorem uniqueSeparatorDerivesL6Short
    (u v w : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((((u ++ v) ++ u) ++ w) ++ v)
      ((((v ++ u) ++ u) ++ w) ++ v) := by
  have first :=
    Derives.appendRight
      (uniqueSeparatorDerivesRotation u v)
      (w ++ v)
  have second :=
    Derives.appendRight
      (uniqueSeparatorDerivesSquares v u)
      (w ++ v)
  have third :=
    Derives.symm <|
      uniqueSeparatorDerivesLeftDuplication v ((u ++ u) ++ w)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second)
      (by simpa [Word.append_assoc] using third)

/-- The fourth law in Edmunds' `L₆`. -/
theorem uniqueSeparatorDerivesL6Square
    (u v : Word Nat) :
    Derives uniqueSeparatorFourBasis
      (((u ++ v) ++ u) ++ v)
      (((v ++ u) ++ u) ++ v) := by
  have first :=
    Derives.prepend u <|
      uniqueSeparatorDerivesRotation v u
  have second :=
    uniqueSeparatorDerivesRightDuplication u (u ++ v)
  have third :=
    uniqueSeparatorDerivesRotation (u ++ u) v
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second)
      (by simpa [Word.append_assoc] using third)

/-- The first (long-context) law in Edmunds' `L₇`. -/
theorem uniqueSeparatorDerivesL7Long
    (u v w q : Word Nat) :
    Derives uniqueSeparatorFourBasis
      (((((u ++ v) ++ w) ++ u) ++ q) ++ w)
      (((((u ++ v) ++ u) ++ w) ++ q) ++ w) := by
  have first :=
    Derives.appendRight
      (uniqueSeparatorDerivesSquares u (v ++ w))
      (q ++ w)
  have second :=
    Derives.appendRight
      (Derives.prepend (u ++ u) <|
        uniqueSeparatorDerivesSquares v w)
      ((w ++ q) ++ w)
  have third :=
    Derives.appendRight
      (Derives.prepend ((u ++ u) ++ (v ++ v)) <|
        Derives.symm <|
          uniqueSeparatorDerivesPowerExpansion w)
      (q ++ w)
  have fourth :=
    Derives.prepend ((u ++ u) ++ (v ++ v)) <|
      Derives.symm <|
        uniqueSeparatorDerivesLeftDuplication w q
  have fifth :=
    Derives.appendRight
      (Derives.symm <|
        uniqueSeparatorDerivesSquares u v)
      ((w ++ q) ++ w)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third) <|
        Derives.trans
          (by simpa [Word.append_assoc] using fourth)
          (by simpa [Word.append_assoc] using fifth)

/-- The second law in Edmunds' `L₇`. -/
theorem uniqueSeparatorDerivesL7Medium
    (u v w : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((((u ++ v) ++ w) ++ u) ++ w)
      ((((u ++ v) ++ u) ++ w) ++ w) := by
  have first :=
    Derives.prepend (u ++ v) <|
      uniqueSeparatorDerivesRotation w u
  have second :=
    Derives.prepend (u ++ v) <|
      uniqueSeparatorDerivesSquares u w
  have third :=
    Derives.appendRight
      (Derives.symm <|
        uniqueSeparatorDerivesRightDuplication u v)
      (w ++ w)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second)
      (by simpa [Word.append_assoc] using third)

/-- The third law in Edmunds' `L₇`. -/
theorem uniqueSeparatorDerivesL7Short
    (u v w : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((((u ++ v) ++ u) ++ w) ++ v)
      ((((u ++ u) ++ v) ++ w) ++ v) := by
  have first :=
    Derives.appendRight
      (uniqueSeparatorDerivesSquares u v)
      (w ++ v)
  have second :=
    Derives.prepend (u ++ u) <|
      Derives.symm <|
        uniqueSeparatorDerivesLeftDuplication v w
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using second)

/-- The fourth law in Edmunds' `L₇`. -/
theorem uniqueSeparatorDerivesL7Square
    (u v : Word Nat) :
    Derives uniqueSeparatorFourBasis
      (((u ++ v) ++ u) ++ v)
      ((u ++ u) ++ (v ++ v)) :=
  Derives.trans
    (Derives.symm <|
      uniqueSeparatorDerivesAlternating u v)
    (uniqueSeparatorDerivesSquares u v)

/-- The first (long-context) law in Edmunds' `L₈`. -/
theorem uniqueSeparatorDerivesL8Long
    (u v w q : Word Nat) :
    Derives uniqueSeparatorFourBasis
      (((((u ++ v) ++ w) ++ q) ++ u) ++ w)
      (((((u ++ v) ++ w) ++ q) ++ w) ++ u) := by
  have first :=
    Derives.appendRight
      (uniqueSeparatorDerivesRotation u ((v ++ w) ++ q))
      w
  have second :=
    Derives.appendRight
      (Derives.prepend v <|
        uniqueSeparatorDerivesLeftDuplication
          (w ++ q) (u ++ v))
      w
  have third :=
    Derives.appendRight
      (Derives.prepend v <|
        Derives.symm <|
          uniqueSeparatorDerivesAlternating w q)
      ((((u ++ v) ++ w) ++ q) ++ w)
  have fourth :=
    uniqueSeparatorDerivesRotation
      ((((v ++ w) ++ q) ++ w)) u
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second) <|
      Derives.trans
        (by simpa [Word.append_assoc] using third)
        (by simpa [Word.append_assoc] using fourth)

/-- The second law in Edmunds' `L₈`. -/
theorem uniqueSeparatorDerivesL8Medium
    (u v w : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((((u ++ v) ++ w) ++ u) ++ w)
      ((((u ++ v) ++ w) ++ w) ++ u) := by
  have first :=
    Derives.prepend (u ++ v) <|
      uniqueSeparatorDerivesSquares w u
  have second :=
    Derives.symm <|
      uniqueSeparatorDerivesRightDuplication u
        ((v ++ w) ++ w)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using second)

/-- The third law in Edmunds' `L₈`. -/
theorem uniqueSeparatorDerivesL8Short
    (u v w : Word Nat) :
    Derives uniqueSeparatorFourBasis
      ((((u ++ v) ++ w) ++ u) ++ v)
      ((((u ++ v) ++ w) ++ v) ++ u) := by
  have first :=
    Derives.appendRight
      (uniqueSeparatorDerivesSquares u (v ++ w))
      v
  have second :=
    Derives.prepend (((u ++ u) ++ v) ++ w) <|
      uniqueSeparatorDerivesLeftDuplication v w
  have third :=
    Derives.symm <|
      uniqueSeparatorDerivesSquares u ((v ++ w) ++ v)
  exact Derives.trans
    (by simpa [Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [Word.append_assoc] using second)
      (by simpa [Word.append_assoc] using third)

/-- The fourth law in Edmunds' `L₈`. -/
theorem uniqueSeparatorDerivesL8Square
    (u v : Word Nat) :
    Derives uniqueSeparatorFourBasis
      (((u ++ v) ++ u) ++ v)
      (((u ++ v) ++ v) ++ u) :=
  Derives.trans
    (Derives.symm <|
      uniqueSeparatorDerivesAlternating u v)
    (uniqueSeparatorDerivesMiddleDuplication u v)

private theorem uniqueSeparatorMul_power (a : Fin 4) :
    uniqueSeparatorFourMul a a =
      uniqueSeparatorFourMul (uniqueSeparatorFourMul a a) a := by
  decide +revert

private theorem uniqueSeparatorMul_leftDuplication (a b : Fin 4) :
    uniqueSeparatorFourMul (uniqueSeparatorFourMul a b) a =
      uniqueSeparatorFourMul
        (uniqueSeparatorFourMul (uniqueSeparatorFourMul a a) b) a := by
  decide +revert

private theorem uniqueSeparatorMul_middleDuplication (a b : Fin 4) :
    uniqueSeparatorFourMul (uniqueSeparatorFourMul a b) a =
      uniqueSeparatorFourMul
        (uniqueSeparatorFourMul
          (uniqueSeparatorFourMul a b) b) a := by
  decide +revert

private theorem uniqueSeparatorMul_rightDuplication (a b : Fin 4) :
    uniqueSeparatorFourMul (uniqueSeparatorFourMul a b) a =
      uniqueSeparatorFourMul
        (uniqueSeparatorFourMul
          (uniqueSeparatorFourMul a b) a) a := by
  decide +revert

private theorem uniqueSeparatorMul_alternating (a b : Fin 4) :
    uniqueSeparatorFourMul (uniqueSeparatorFourMul a b) a =
      uniqueSeparatorFourMul
        (uniqueSeparatorFourMul
          (uniqueSeparatorFourMul a b) a) b := by
  decide +revert

private theorem uniqueSeparatorMul_squares (a b : Fin 4) :
    uniqueSeparatorFourMul (uniqueSeparatorFourMul a b) a =
      uniqueSeparatorFourMul
        (uniqueSeparatorFourMul
          (uniqueSeparatorFourMul a a) b) b := by
  decide +revert

private theorem uniqueSeparatorMul_rotation (a b : Fin 4) :
    uniqueSeparatorFourMul (uniqueSeparatorFourMul a b) a =
      uniqueSeparatorFourMul (uniqueSeparatorFourMul b a) b := by
  decide +revert

theorem uniqueSeparatorFourBasis_models :
    Models uniqueSeparatorFour.semigroup uniqueSeparatorFourBasis := by
  intro e he
  simp only [uniqueSeparatorFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro valuation
    exact uniqueSeparatorMul_power (valuation 0)
  · intro valuation
    exact uniqueSeparatorMul_leftDuplication
      (valuation 0) (valuation 1)
  · intro valuation
    exact uniqueSeparatorMul_middleDuplication
      (valuation 0) (valuation 1)
  · intro valuation
    exact uniqueSeparatorMul_rightDuplication
      (valuation 0) (valuation 1)
  · intro valuation
    exact uniqueSeparatorMul_alternating
      (valuation 0) (valuation 1)
  · intro valuation
    exact uniqueSeparatorMul_squares (valuation 0) (valuation 1)
  · intro valuation
    exact uniqueSeparatorMul_rotation
      (valuation 0) (valuation 1)

end SemigroupBasis.Examples
