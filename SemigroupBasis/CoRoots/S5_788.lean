import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_788

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxz : Word Nat := w 0 [1, 0, 2]
def xyxyyxz : Word Nat := w 0 [1, 0, 1, 1, 0, 2]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xyzxx : Word Nat := w 0 [1, 2, 0, 0]
def xyzxz : Word Nat := w 0 [1, 2, 0, 2]
def xxyzyyz : Word Nat := w 0 [0, 1, 2, 1, 1, 2]
def xyxxyzy : Word Nat := w 0 [1, 0, 0, 1, 2, 1]
def xyxxyzz : Word Nat := w 0 [1, 0, 0, 1, 2, 2]
def xyxyxzx : Word Nat := w 0 [1, 0, 1, 0, 2, 0]
def xyxyxzy : Word Nat := w 0 [1, 0, 1, 0, 2, 1]
def xyxyyzx : Word Nat := w 0 [1, 0, 1, 1, 2, 0]
def xyxyzyx : Word Nat := w 0 [1, 0, 1, 2, 1, 0]
def xyxzyxz : Word Nat := w 0 [1, 0, 2, 1, 0, 2]
def xyxzzxy : Word Nat := w 0 [1, 0, 2, 2, 0, 1]
def xyxzzyx : Word Nat := w 0 [1, 0, 2, 2, 1, 0]
def xyyxzzx : Word Nat := w 0 [1, 1, 0, 2, 2, 0]
def xyzxyzx : Word Nat := w 0 [1, 2, 0, 1, 2, 0]
def xyzyyxz : Word Nat := w 0 [1, 2, 1, 1, 0, 2]
def xyzyyzx : Word Nat := w 0 [1, 2, 1, 1, 2, 0]
def xyzyzxy : Word Nat := w 0 [1, 2, 1, 2, 0, 1]
def xyzyzyx : Word Nat := w 0 [1, 2, 1, 2, 1, 0]
def xyzyzzx : Word Nat := w 0 [1, 2, 1, 2, 2, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xyzyzzy : Word Nat := w 0 [1, 2, 1, 2, 2, 1]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def squaresLaw : Identity Nat := ⟨xyx, xxyy⟩
def intervalExpansionLaw : Identity Nat := ⟨xyxz, xyxyyxz⟩
def rightXExpansionLaw : Identity Nat := ⟨xyzx, xyzxx⟩
def rightZExpansionLaw : Identity Nat := ⟨xyzx, xyzxz⟩
def separatorExpansionLaw : Identity Nat := ⟨xyzx, xxyzyyz⟩
def leftNestedExpansionLaw : Identity Nat := ⟨xyzx, xyxxyzy⟩
def leftNestedZExpansionLaw : Identity Nat := ⟨xyzx, xyxxyzz⟩
def alternatingCrossingLaw : Identity Nat := ⟨xyzx, xyxyxzx⟩
def alternatingCrossingYLaw : Identity Nat := ⟨xyzx, xyxyxzy⟩
def alternatingSquareLaw : Identity Nat := ⟨xyzx, xyxyyzx⟩
def alternatingTurnLaw : Identity Nat := ⟨xyzx, xyxyzyx⟩
def thirdOccurrenceLaw : Identity Nat := ⟨xyzx, xyxzyxz⟩
def doubledZTurnLaw : Identity Nat := ⟨xyzx, xyxzzxy⟩
def doubledZReturnLaw : Identity Nat := ⟨xyzx, xyxzzyx⟩
def doubledYAndZLaw : Identity Nat := ⟨xyzx, xyyxzzx⟩
def repeatedBlockLaw : Identity Nat := ⟨xyzx, xyzxyzx⟩
def delayedYExpansionLaw : Identity Nat := ⟨xyzx, xyzyyxz⟩
def delayedYReturnLaw : Identity Nat := ⟨xyzx, xyzyyzx⟩
def delayedCrossingLaw : Identity Nat := ⟨xyzx, xyzyzxy⟩
def delayedTurnLaw : Identity Nat := ⟨xyzx, xyzyzyx⟩
def delayedSquareLaw : Identity Nat := ⟨xyzx, xyzyzzx⟩
def terminalInitialLaw : Identity Nat := ⟨xyzy, xyzyzzy⟩

/-- The common 24-law candidate basis for `S5_788`, `S5_805`, and
`S5_811`, in the authoritative separator/initial order. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftDuplicationLaw, squaresLaw, intervalExpansionLaw,
    rightXExpansionLaw, rightZExpansionLaw, separatorExpansionLaw,
    leftNestedExpansionLaw, leftNestedZExpansionLaw,
    alternatingCrossingLaw, alternatingCrossingYLaw,
    alternatingSquareLaw, alternatingTurnLaw, thirdOccurrenceLaw,
    doubledZTurnLaw, doubledZReturnLaw, doubledYAndZLaw,
    repeatedBlockLaw, delayedYExpansionLaw, delayedYReturnLaw,
    delayedCrossingLaw, delayedTurnLaw, delayedSquareLaw,
    terminalInitialLaw]

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

/-- Reduce a finite model check on the three variables occurring in the
candidate basis to a `Models` theorem over `Nat` variables. -/
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

private def instantiateFiveWords
    (a b c d e : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | n + 5 => Word.singleton (n + 5)

private theorem basisPower :
    Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) <| by
    simp [basis]

private theorem basisLeftDuplication :
    Derives basis xyx xxyx :=
  Derives.fromBasis (e := leftDuplicationLaw) <| by
    simp [basis]

private theorem basisSquares :
    Derives basis xyx xxyy :=
  Derives.fromBasis (e := squaresLaw) <| by
    simp [basis]

private theorem basisRightZExpansion :
    Derives basis xyzx xyzxz :=
  Derives.fromBasis (e := rightZExpansionLaw) <| by
    simp [basis]

private theorem basisSeparatorExpansion :
    Derives basis xyzx xxyzyyz :=
  Derives.fromBasis (e := separatorExpansionLaw) <| by
    simp [basis]

private theorem basisAlternatingCrossing :
    Derives basis xyzx xyxyxzx :=
  Derives.fromBasis (e := alternatingCrossingLaw) <| by
    simp [basis]

private theorem basisThirdOccurrence :
    Derives basis xyzx xyxzyxz :=
  Derives.fromBasis (e := thirdOccurrenceLaw) <| by
    simp [basis]

private theorem basisRepeatedBlock :
    Derives basis xyzx xyzxyzx :=
  Derives.fromBasis (e := repeatedBlockLaw) <| by
    simp [basis]

private theorem basisDelayedSquare :
    Derives basis xyzx xyzyzzx :=
  Derives.fromBasis (e := delayedSquareLaw) <| by
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

theorem derivesSquares (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ u) ++ (v ++ v)) := by
  have substituted :=
    Derives.subst basisSquares (instantiateThreeWords u v v)
  simpa [xyx, xxyy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesRightZExpansion (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u)
      ((((u ++ v) ++ z) ++ u) ++ z) := by
  have substituted :=
    Derives.subst basisRightZExpansion
      (instantiateThreeWords u v z)
  simpa [xyzx, xyzxz, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Put a substituted basis step inside a concrete list context. This is
used only to replay the advertised finite derivation chains. -/
theorem derivesConcreteContext
    {source target patternLeft patternRight : Word Nat}
    (patternDerivation :
      Derives basis patternLeft patternRight)
    (u v z : Word Nat) (ctxPrefix ctxSuffix : List Nat)
    (sourceShape :
      source.toList =
        ctxPrefix ++
          (patternLeft.bind (instantiateThreeWords u v z)).toList ++
          ctxSuffix)
    (targetShape :
      target.toList =
        ctxPrefix ++
          (patternRight.bind (instantiateThreeWords u v z)).toList ++
          ctxSuffix) :
    Derives basis source target := by
  have contextual :
      S5_107.ListDerives basis
        (ctxPrefix ++
          (patternLeft.bind (instantiateThreeWords u v z)).toList ++
          ctxSuffix)
        (ctxPrefix ++
          (patternRight.bind (instantiateThreeWords u v z)).toList ++
          ctxSuffix) :=
    (S5_107.ListDerives.ofWord
      (Derives.subst patternDerivation
        (instantiateThreeWords u v z))).context ctxPrefix ctxSuffix
  rw [← sourceShape, ← targetShape] at contextual
  cases source with
  | mk sourceHead sourceTail =>
      cases target with
      | mk targetHead targetTail =>
          exact S5_107.ListDerives.toWord contextual

private def xWord : Word Nat := w 0 []
private def yWord : Word Nat := w 1 []
private def zWord : Word Nat := w 2 []
private def uWord : Word Nat := w 3 []
private def vWord : Word Nat := w 4 []

private def yyWord : Word Nat := w 1 [1]
private def yzWord : Word Nat := w 1 [2]
private def yxzWord : Word Nat := w 1 [0, 2]
private def yzzWord : Word Nat := w 1 [2, 2]
private def yzzuWord : Word Nat := w 1 [2, 2, 3]
private def yzuWord : Word Nat := w 1 [2, 3]
private def yzuyzuvWord : Word Nat := w 1 [2, 3, 1, 2, 3, 4]
private def yzyzuuvWord : Word Nat := w 1 [2, 1, 2, 3, 3, 4]
private def yzxuWord : Word Nat := w 1 [2, 0, 3]
private def yzuzuxWord : Word Nat := w 1 [2, 3, 2, 3, 0]
private def uvWord : Word Nat := w 3 [4]
private def vxWord : Word Nat := w 4 [0]
private def zuWord : Word Nat := w 2 [3]
private def zuvWord : Word Nat := w 2 [3, 4]
private def uvxWord : Word Nat := w 3 [4, 0]

def xyyx : Word Nat := w 0 [1, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xyzuzvx : Word Nat := w 0 [1, 2, 3, 2, 4, 0]
def xyzuvx : Word Nat := w 0 [1, 2, 3, 4, 0]
def xyzuxvz : Word Nat := w 0 [1, 2, 3, 0, 4, 2]

/-- The advertised chain `xyx = xxyy = xxyyy = xxyyyy = xyyx`. -/
theorem derivesMiddleDoubling :
    Derives basis xyx xyyx := by
  have stepOne :
      Derives basis xyx xxyy :=
    derivesConcreteContext basisSquares xWord yWord zWord [] []
      (by decide) (by decide)
  have stepTwo :
      Derives basis xxyy (w 0 [0, 1, 1, 1]) :=
    derivesConcreteContext basisPower yWord yWord zWord [0, 0] []
      (by decide) (by decide)
  have stepThree :
      Derives basis (w 0 [0, 1, 1, 1])
        (w 0 [0, 1, 1, 1, 1]) :=
    derivesConcreteContext basisPower yWord yWord zWord [0, 0] [1]
      (by decide) (by decide)
  have stepFour :
      Derives basis (w 0 [0, 1, 1, 1, 1]) xyyx :=
    derivesConcreteContext (Derives.symm basisSquares)
      xWord yyWord zWord [] [] (by decide) (by decide)
  exact stepOne.trans (stepTwo.trans (stepThree.trans stepFour))

/-- The advertised chain `xyx = xxyx = xxyxyyx = xyxx`. -/
theorem derivesRightDoubling :
    Derives basis xyx xyxx := by
  have stepOne :
      Derives basis xyx xxyx :=
    derivesConcreteContext basisLeftDuplication
      xWord yWord zWord [] [] (by decide) (by decide)
  have stepTwo :
      Derives basis xxyx (w 0 [0, 1, 0, 1, 1, 0]) :=
    derivesConcreteContext basisDelayedSquare
      xWord xWord yWord [] [] (by decide) (by decide)
  have stepThree :
      Derives basis (w 0 [0, 1, 0, 1, 1, 0]) xyxx :=
    derivesConcreteContext (Derives.symm basisSeparatorExpansion)
      xWord yWord xWord [] [] (by decide) (by decide)
  exact stepOne.trans (stepTwo.trans stepThree)

/-- The advertised chain `xyx = xxyx = xxyxy = xyxy`. -/
theorem derivesAlternatingExtension :
    Derives basis xyx xyxy := by
  have stepOne :
      Derives basis xyx xxyx :=
    derivesConcreteContext basisLeftDuplication
      xWord yWord zWord [] [] (by decide) (by decide)
  have stepTwo :
      Derives basis xxyx (w 0 [0, 1, 0, 1]) :=
    derivesConcreteContext basisRightZExpansion
      xWord xWord yWord [] [] (by decide) (by decide)
  have stepThree :
      Derives basis (w 0 [0, 1, 0, 1]) xyxy :=
    derivesConcreteContext (Derives.symm basisLeftDuplication)
      xWord yWord zWord [] [1] (by decide) (by decide)
  exact stepOne.trans (stepTwo.trans stepThree)

/-- The advertised chain
`xyxzx = xxyxzyxz = xxyzx = xyzx`. -/
theorem derivesThirdOccurrenceDeletion :
    Derives basis xyxzx xyzx := by
  have stepOne :
      Derives basis xyxzx (w 0 [0, 1, 0, 2, 1, 0, 2]) :=
    derivesConcreteContext basisSquares
      xWord yxzWord zWord [] [] (by decide) (by decide)
  have stepTwo :
      Derives basis (w 0 [0, 1, 0, 2, 1, 0, 2])
        (w 0 [0, 1, 2, 0]) :=
    derivesConcreteContext (Derives.symm basisThirdOccurrence)
      xWord yWord zWord [0] [] (by decide) (by decide)
  have stepThree :
      Derives basis (w 0 [0, 1, 2, 0]) xyzx :=
    derivesConcreteContext (Derives.symm basisLeftDuplication)
      xWord yzWord zWord [] [] (by decide) (by decide)
  exact stepOne.trans (stepTwo.trans stepThree)

/-- The advertised seven-step nested-repeat deletion chain. -/
theorem derivesNestedRepeatDeletion :
    Derives basis xyzuzvx xyzuvx := by
  have stepOne :
      Derives basis xyzuzvx (w 0 [1, 2, 2, 3, 3, 4, 0]) :=
    derivesConcreteContext basisSquares
      zWord uWord xWord [0, 1] [4, 0] (by decide) (by decide)
  have stepTwo :
      Derives basis (w 0 [1, 2, 2, 3, 3, 4, 0])
        (w 0 [1, 2, 2, 3, 3, 4, 0, 3, 4]) :=
    derivesConcreteContext basisRightZExpansion
      xWord yzzuWord uvWord [] [] (by decide) (by decide)
  have stepThree :
      Derives basis (w 0 [1, 2, 2, 3, 3, 4, 0, 3, 4])
        (w 0 [1, 2, 2, 3, 4, 0, 3, 4]) :=
    derivesConcreteContext (Derives.symm basisLeftDuplication)
      uWord vxWord zWord [0, 1, 2, 2] [4]
      (by decide) (by decide)
  have stepFour :
      Derives basis (w 0 [1, 2, 2, 3, 4, 0, 3, 4])
        (w 0 [1, 2, 2, 3, 4, 0]) :=
    derivesConcreteContext (Derives.symm basisRightZExpansion)
      xWord yzzWord uvWord [] [] (by decide) (by decide)
  have stepFive :
      Derives basis (w 0 [1, 2, 2, 3, 4, 0])
        (w 0 [1, 2, 2, 3, 4, 0, 2, 3, 4]) :=
    derivesConcreteContext basisRightZExpansion
      xWord yzWord zuvWord [] [] (by decide) (by decide)
  have stepSix :
      Derives basis (w 0 [1, 2, 2, 3, 4, 0, 2, 3, 4])
        (w 0 [1, 2, 3, 4, 0, 2, 3, 4]) :=
    derivesConcreteContext (Derives.symm basisLeftDuplication)
      zWord uvxWord xWord [0, 1] [3, 4] (by decide) (by decide)
  have stepSeven :
      Derives basis (w 0 [1, 2, 3, 4, 0, 2, 3, 4]) xyzuvx :=
    derivesConcreteContext (Derives.symm basisRightZExpansion)
      xWord yWord zuvWord [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <|
    stepFour.trans <| stepFive.trans <| stepSix.trans stepSeven

/-- The advertised twenty-step general crossing-absorption chain. -/
theorem derivesGeneralCrossingAbsorption :
    Derives basis xyzuxvz xyzuvx := by
  have stepOne :
      Derives basis xyzuxvz (w 0 [1, 2, 3, 0, 3, 4, 2]) :=
    derivesConcreteContext basisRightZExpansion
      xWord yzWord uWord [] [4, 2] (by decide) (by decide)
  have stepTwo :
      Derives basis (w 0 [1, 2, 3, 0, 3, 4, 2])
        (w 0 [1, 2, 3, 0, 3, 4, 2, 3, 4]) :=
    derivesConcreteContext basisRightZExpansion
      zWord (w 3 [0]) uvWord [0, 1] [] (by decide) (by decide)
  have stepThree :
      Derives basis (w 0 [1, 2, 3, 0, 3, 4, 2, 3, 4])
        (w 0 [1, 2, 3, 0, 4, 2, 3, 4]) :=
    derivesConcreteContext (Derives.symm basisRightZExpansion)
      xWord yzWord uWord [] [4, 2, 3, 4] (by decide) (by decide)
  have stepFour :
      Derives basis (w 0 [1, 2, 3, 0, 4, 2, 3, 4])
        (w 0 [1, 2, 3, 0, 4, 2, 3]) :=
    derivesConcreteContext (Derives.symm basisRightZExpansion)
      zuWord xWord vWord [0, 1] [] (by decide) (by decide)
  have stepFive :
      Derives basis (w 0 [1, 2, 3, 0, 4, 2, 3])
        (w 0 [1, 2, 3, 2, 3, 0, 4, 0, 4]) :=
    derivesConcreteContext basisSquares
      zuWord (w 0 [4]) yWord [0, 1] [] (by decide) (by decide)
  have stepSix :
      Derives basis (w 0 [1, 2, 3, 2, 3, 0, 4, 0, 4])
        (w 0 [1, 2, 3, 2, 3, 0, 4, 0]) :=
    derivesConcreteContext (Derives.symm basisRightZExpansion)
      xWord yzuzuxWord vWord [] [] (by decide) (by decide)
  have stepSeven :
      Derives basis (w 0 [1, 2, 3, 2, 3, 0, 4, 0])
        (w 0 [1, 2, 3, 2, 3, 0, 0, 4, 0]) :=
    derivesConcreteContext basisLeftDuplication
      xWord vWord yWord [0, 1, 2, 3, 2, 3] []
      (by decide) (by decide)
  have stepEight :
      Derives basis (w 0 [1, 2, 3, 2, 3, 0, 0, 4, 0])
        (w 0 [1, 2, 3, 0, 2, 3, 4, 0]) :=
    derivesConcreteContext (Derives.symm basisSquares)
      zuWord xWord yWord [0, 1] [4, 0] (by decide) (by decide)
  have stepNine :
      Derives basis (w 0 [1, 2, 3, 0, 2, 3, 4, 0])
        (w 0 [1, 2, 3, 0, 4, 0]) :=
    derivesConcreteContext (Derives.symm basisRightZExpansion)
      xWord yWord zuWord [] [4, 0] (by decide) (by decide)
  have stepTen :
      Derives basis (w 0 [1, 2, 3, 0, 4, 0])
        (w 0 [0, 1, 2, 3, 1, 2, 3, 4, 0]) :=
    derivesConcreteContext basisSquares
      xWord yzuWord zWord [] [4, 0] (by decide) (by decide)
  have stepEleven :
      Derives basis (w 0 [0, 1, 2, 3, 1, 2, 3, 4, 0])
        (w 0 [1, 2, 3, 1, 2, 3, 4, 0]) :=
    derivesConcreteContext (Derives.symm basisLeftDuplication)
      xWord yzuyzuvWord zWord [] [] (by decide) (by decide)
  have stepTwelve :
      Derives basis (w 0 [1, 2, 3, 1, 2, 3, 4, 0])
        (w 0 [1, 2, 1, 2, 3, 3, 3, 4, 0]) :=
    derivesConcreteContext basisSquares
      yzWord uWord xWord [0] [3, 4, 0] (by decide) (by decide)
  have stepThirteen :
      Derives basis (w 0 [1, 2, 1, 2, 3, 3, 3, 4, 0])
        (w 0 [1, 2, 1, 2, 3, 3, 4, 0]) :=
    derivesConcreteContext (Derives.symm basisPower)
      uWord yWord zWord [0, 1, 2, 1, 2] [4, 0]
      (by decide) (by decide)
  have stepFourteen :
      Derives basis (w 0 [1, 2, 1, 2, 3, 3, 4, 0])
        (w 0 [0, 1, 2, 1, 2, 3, 3, 4, 0]) :=
    derivesConcreteContext basisLeftDuplication
      xWord yzyzuuvWord zWord [] [] (by decide) (by decide)
  have stepFifteen :
      Derives basis (w 0 [0, 1, 2, 1, 2, 3, 3, 4, 0])
        (w 0 [1, 2, 0, 3, 3, 4, 0]) :=
    derivesConcreteContext (Derives.symm basisSquares)
      xWord yzWord zWord [] [3, 3, 4, 0] (by decide) (by decide)
  have stepSixteen :
      Derives basis (w 0 [1, 2, 0, 3, 3, 4, 0])
        (w 0 [1, 2, 0, 3, 3, 4, 0, 3, 4]) :=
    derivesConcreteContext basisRightZExpansion
      xWord yzxuWord uvWord [] [] (by decide) (by decide)
  have stepSeventeen :
      Derives basis (w 0 [1, 2, 0, 3, 3, 4, 0, 3, 4])
        (w 0 [1, 2, 0, 3, 4, 0, 3, 4]) :=
    derivesConcreteContext (Derives.symm basisLeftDuplication)
      uWord vxWord zWord [0, 1, 2, 0] [4]
      (by decide) (by decide)
  have stepEighteen :
      Derives basis (w 0 [1, 2, 0, 3, 4, 0, 3, 4])
        (w 0 [1, 2, 0, 3, 4, 0]) :=
    derivesConcreteContext (Derives.symm basisRightZExpansion)
      xWord (w 1 [2, 0]) uvWord [] [] (by decide) (by decide)
  have stepNineteen :
      Derives basis (w 0 [1, 2, 0, 3, 4, 0])
        (w 0 [1, 2, 0, 1, 2, 0, 3, 4, 0]) :=
    derivesConcreteContext basisRepeatedBlock
      xWord yWord zWord [] [3, 4, 0] (by decide) (by decide)
  have stepTwenty :
      Derives basis (w 0 [1, 2, 0, 1, 2, 0, 3, 4, 0]) xyzuvx :=
    derivesConcreteContext (Derives.symm basisAlternatingCrossing)
      xWord yzWord uvWord [] [] (by decide) (by decide)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans <|
    stepFour.trans <| stepFive.trans <| stepSix.trans <|
    stepSeven.trans <| stepEight.trans <| stepNine.trans <|
    stepTen.trans <| stepEleven.trans <| stepTwelve.trans <|
    stepThirteen.trans <| stepFourteen.trans <| stepFifteen.trans <|
    stepSixteen.trans <| stepSeventeen.trans <| stepEighteen.trans <|
    stepNineteen.trans stepTwenty

/-- The derived middle-doubling law under arbitrary nonempty-word
substitution. -/
theorem derivesMiddleDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst derivesMiddleDoubling
      (instantiateThreeWords u v v)
  simpa [xyx, xyyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The derived right-doubling law under arbitrary nonempty-word
substitution. -/
theorem derivesRightDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst derivesRightDoubling
      (instantiateThreeWords u v v)
  simpa [xyx, xyxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The derived alternating-extension law under arbitrary nonempty-word
substitution. -/
theorem derivesAlternating (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ v) := by
  have substituted :=
    Derives.subst derivesAlternatingExtension
      (instantiateThreeWords u v v)
  simpa [xyx, xyxy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Delete the middle of three occurrences under arbitrary nonempty-word
substitution. -/
theorem derivesThirdOccurrence
    (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) := by
  have substituted :=
    Derives.subst derivesThirdOccurrenceDeletion
      (instantiateThreeWords u v z)
  simpa [xyxzx, xyzx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Delete a nested repeated interval when all three displayed filler
blocks are nonempty. -/
theorem derivesNestedRepeat
    (outer leftGap repeated middleGap rightGap : Word Nat) :
    Derives basis
      ((((((outer ++ leftGap) ++ repeated) ++ middleGap) ++
        repeated) ++ rightGap) ++ outer)
      (((((outer ++ leftGap) ++ repeated) ++ middleGap) ++
        rightGap) ++ outer) := by
  have substituted :=
    Derives.subst derivesNestedRepeatDeletion
      (instantiateFiveWords
        outer leftGap repeated middleGap rightGap)
  simpa [xyzuzvx, xyzuvx, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Absorb a crossing repeated interval when all three displayed filler
blocks are nonempty. -/
theorem derivesCrossingRepeat
    (outer leftGap crossing middleGap rightGap : Word Nat) :
    Derives basis
      ((((((outer ++ leftGap) ++ crossing) ++ middleGap) ++
        outer) ++ rightGap) ++ crossing)
      (((((outer ++ leftGap) ++ crossing) ++ middleGap) ++
        rightGap) ++ outer) := by
  have substituted :=
    Derives.subst derivesGeneralCrossingAbsorption
      (instantiateFiveWords
        outer leftGap crossing middleGap rightGap)
  simpa [xyzuxvz, xyzuvx, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

end SemigroupBasis.CoRoots.S5_788
