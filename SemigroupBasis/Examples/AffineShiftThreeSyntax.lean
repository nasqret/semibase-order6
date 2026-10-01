import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

def affineShiftThreeX : Word Nat := Word.singleton 0
def affineShiftThreeXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def affineShiftThreeXY : Word Nat := ⟨0, [1]⟩
def affineShiftThreeXYXXX : Word Nat := ⟨0, [1, 0, 0, 0]⟩
def affineShiftThreeXYYX : Word Nat := ⟨0, [1, 1, 0]⟩
def affineShiftThreeXYXY : Word Nat := ⟨0, [1, 0, 1]⟩
def affineShiftThreeXYYYX : Word Nat := ⟨0, [1, 1, 1, 0]⟩
def affineShiftThreeXYXYY : Word Nat := ⟨0, [1, 0, 1, 1]⟩
def affineShiftThreeXYZYX : Word Nat := ⟨0, [1, 2, 1, 0]⟩
def affineShiftThreeXYZXY : Word Nat := ⟨0, [1, 2, 0, 1]⟩
def affineShiftThreeXYZZX : Word Nat := ⟨0, [1, 2, 2, 0]⟩
def affineShiftThreeXYZXZ : Word Nat := ⟨0, [1, 2, 0, 2]⟩

def affineShiftThreePowerLaw : Identity Nat :=
  ⟨affineShiftThreeX, affineShiftThreeXXXX⟩

def affineShiftThreeGuardedTripleLaw : Identity Nat :=
  ⟨affineShiftThreeXYXXX, affineShiftThreeXY⟩

def affineShiftThreeBinaryResidueOneLaw : Identity Nat :=
  ⟨affineShiftThreeXYYX, affineShiftThreeXYXY⟩

def affineShiftThreeBinaryResidueTwoLaw : Identity Nat :=
  ⟨affineShiftThreeXYYYX, affineShiftThreeXYXYY⟩

def affineShiftThreeTernaryResidueOneLaw : Identity Nat :=
  ⟨affineShiftThreeXYZYX, affineShiftThreeXYZXY⟩

def affineShiftThreeTernaryResidueTwoLaw : Identity Nat :=
  ⟨affineShiftThreeXYZZX, affineShiftThreeXYZXZ⟩

/-- The exact stored-orientation six-law basis recorded for `S6_15903`.
It is the modulus-three analogue of the affine-parity syntax. -/
def affineShiftThreeBasis : List (Identity Nat) :=
  [affineShiftThreePowerLaw, affineShiftThreeGuardedTripleLaw,
    affineShiftThreeBinaryResidueOneLaw,
    affineShiftThreeBinaryResidueTwoLaw,
    affineShiftThreeTernaryResidueOneLaw,
    affineShiftThreeTernaryResidueTwoLaw]

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Substitute an arbitrary nonempty block into `x = x^4`. -/
theorem affineShiftThreeDerivesPowerExpansion (u : Word Nat) :
    Derives affineShiftThreeBasis u (((u ++ u) ++ u) ++ u) := by
  have base :
      Derives affineShiftThreeBasis
        affineShiftThreeX affineShiftThreeXXXX :=
    Derives.fromBasis (e := affineShiftThreePowerLaw) <|
      List.Mem.head _
  have derived := Derives.subst base (instantiateThreeWords u u u)
  simpa [affineShiftThreeBasis, affineShiftThreePowerLaw,
    affineShiftThreeX, affineShiftThreeXXXX, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using derived

theorem affineShiftThreeDerivesPowerContraction (u : Word Nat) :
    Derives affineShiftThreeBasis (((u ++ u) ++ u) ++ u) u :=
  (affineShiftThreeDerivesPowerExpansion u).symm

/-- Delete a triple copy after a nonempty guard. -/
theorem affineShiftThreeDerivesGuardedTriple
    (u v : Word Nat) :
    Derives affineShiftThreeBasis
      ((((u ++ v) ++ u) ++ u) ++ u) (u ++ v) := by
  have base :
      Derives affineShiftThreeBasis
        affineShiftThreeXYXXX affineShiftThreeXY :=
    Derives.fromBasis (e := affineShiftThreeGuardedTripleLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have derived := Derives.subst base (instantiateThreeWords u v v)
  simpa [affineShiftThreeBasis, affineShiftThreeGuardedTripleLaw,
    affineShiftThreeXYXXX, affineShiftThreeXY, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using derived

/-- The first binary residue move with arbitrary nonempty blocks. -/
theorem affineShiftThreeDerivesBinaryResidueOne
    (u v : Word Nat) :
    Derives affineShiftThreeBasis
      (((u ++ v) ++ v) ++ u) (((u ++ v) ++ u) ++ v) := by
  have base :
      Derives affineShiftThreeBasis
        affineShiftThreeXYYX affineShiftThreeXYXY :=
    Derives.fromBasis (e := affineShiftThreeBinaryResidueOneLaw) <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have derived := Derives.subst base (instantiateThreeWords u v v)
  simpa [affineShiftThreeBasis, affineShiftThreeBinaryResidueOneLaw,
    affineShiftThreeXYYX, affineShiftThreeXYXY, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using derived

/-- The second binary residue move with arbitrary nonempty blocks. -/
theorem affineShiftThreeDerivesBinaryResidueTwo
    (u v : Word Nat) :
    Derives affineShiftThreeBasis
      ((((u ++ v) ++ v) ++ v) ++ u)
      ((((u ++ v) ++ u) ++ v) ++ v) := by
  have base :
      Derives affineShiftThreeBasis
        affineShiftThreeXYYYX affineShiftThreeXYXYY :=
    Derives.fromBasis (e := affineShiftThreeBinaryResidueTwoLaw) <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.head _
  have derived := Derives.subst base (instantiateThreeWords u v v)
  simpa [affineShiftThreeBasis, affineShiftThreeBinaryResidueTwoLaw,
    affineShiftThreeXYYYX, affineShiftThreeXYXYY, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using derived

/-- The first ternary guarded residue move with arbitrary nonempty blocks. -/
theorem affineShiftThreeDerivesTernaryResidueOne
    (u v w : Word Nat) :
    Derives affineShiftThreeBasis
      ((((u ++ v) ++ w) ++ v) ++ u)
      ((((u ++ v) ++ w) ++ u) ++ v) := by
  have base :
      Derives affineShiftThreeBasis
        affineShiftThreeXYZYX affineShiftThreeXYZXY :=
    Derives.fromBasis (e := affineShiftThreeTernaryResidueOneLaw) <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have derived := Derives.subst base (instantiateThreeWords u v w)
  simpa [affineShiftThreeBasis, affineShiftThreeTernaryResidueOneLaw,
    affineShiftThreeXYZYX, affineShiftThreeXYZXY, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using derived

/-- The second ternary guarded residue move with arbitrary nonempty blocks. -/
theorem affineShiftThreeDerivesTernaryResidueTwo
    (u v w : Word Nat) :
    Derives affineShiftThreeBasis
      ((((u ++ v) ++ w) ++ w) ++ u)
      ((((u ++ v) ++ w) ++ u) ++ w) := by
  have base :
      Derives affineShiftThreeBasis
        affineShiftThreeXYZZX affineShiftThreeXYZXZ :=
    Derives.fromBasis (e := affineShiftThreeTernaryResidueTwoLaw) <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have derived := Derives.subst base (instantiateThreeWords u v w)
  simpa [affineShiftThreeBasis, affineShiftThreeTernaryResidueTwoLaw,
    affineShiftThreeXYZZX, affineShiftThreeXYZXZ, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using derived

/-- Swap the displayed later copies of `second` and `first` once both have
already occurred, with nonempty gaps between the displayed witnesses. The
three-step certificate expands the later `second`, applies the ternary-two
law, and deletes the resulting guarded triple. -/
theorem affineShiftThreeDerivesGuardedSwap
    (first firstGap second secondGap : Word Nat) :
    Derives affineShiftThreeBasis
      (((((first ++ firstGap) ++ second) ++ secondGap) ++ second) ++ first)
      (((((first ++ firstGap) ++ second) ++ secondGap) ++ first) ++ second) := by
  let stem := ((first ++ firstGap) ++ second) ++ secondGap
  have expanded :=
    Derives.appendRight
      (Derives.prepend stem
        (affineShiftThreeDerivesPowerExpansion second)) first
  let middle :=
    (((firstGap ++ second) ++ secondGap) ++ second) ++ second
  have moved :=
    affineShiftThreeDerivesTernaryResidueTwo first middle second
  have contracted :=
    Derives.appendRight
      (Derives.prepend (first ++ firstGap)
        (affineShiftThreeDerivesGuardedTriple second secondGap))
      (first ++ second)
  simp only [stem, middle, Word.append_assoc] at expanded moved contracted ⊢
  exact expanded.trans (moved.trans contracted)

end SemigroupBasis.Examples
