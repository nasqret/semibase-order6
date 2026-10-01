import SemigroupBasis.FiniteTable

/-!
# The direct Lee--Zhang basis for `S6_9727`: normalization

Every word of length at least three is reduced to its first three letters.
If the third letter repeats the second one, it is replaced by the first.
Thus a long word is represented by its ordered first pair and one normalized
third coordinate.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhangS6_9727

open SemigroupBasis

def xxx : Word Nat := ⟨0, [0, 0]⟩
def xxxx : Word Nat := ⟨0, [0, 0, 0]⟩
def xxxy : Word Nat := ⟨0, [0, 0, 1]⟩
def xxy : Word Nat := ⟨0, [0, 1]⟩
def xxyx : Word Nat := ⟨0, [0, 1, 0]⟩
def xxyy : Word Nat := ⟨0, [0, 1, 1]⟩
def xxyz : Word Nat := ⟨0, [0, 1, 2]⟩
def xyx : Word Nat := ⟨0, [1, 0]⟩
def xyxx : Word Nat := ⟨0, [1, 0, 0]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xyzx : Word Nat := ⟨0, [1, 2, 0]⟩

def powerLaw : Identity Nat := ⟨xxx, xxxx⟩
def powerTailLaw : Identity Nat := ⟨xxx, xxxy⟩
def doubleFirstReturnLaw : Identity Nat := ⟨xxy, xxyx⟩
def doubleFirstRepeatLaw : Identity Nat := ⟨xxy, xxyy⟩
def doubleFirstForgetLaw : Identity Nat := ⟨xxy, xxyz⟩
def returnPowerLaw : Identity Nat := ⟨xyx, xyxx⟩
def returnCollapseLaw : Identity Nat := ⟨xyx, xyy⟩
def tailDeleteLaw : Identity Nat := ⟨xyz, xyzx⟩

/-- The corrected eight-law Lee--Zhang system recorded for `S6_9727`. -/
def basis : List (Identity Nat) :=
  [powerLaw, powerTailLaw, doubleFirstReturnLaw,
    doubleFirstRepeatLaw, doubleFirstForgetLaw, returnPowerLaw,
    returnCollapseLaw, tailDeleteLaw]

def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def wordOfTwo (first second : Nat) (rest : List Nat) : Word Nat :=
  ⟨first, second :: rest⟩

private def instantiateFour
    (x y z u : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => u
  | n + 4 => Word.singleton (n + 4)

private theorem basisDoubleFirstForget :
    Derives basis xxy xxyz := by
  exact Derives.fromBasis (e := doubleFirstForgetLaw) (by
    simp [basis])

private theorem basisReturnCollapse :
    Derives basis xyx xyy := by
  exact Derives.fromBasis (e := returnCollapseLaw) (by
    simp [basis])

private theorem basisTailDelete :
    Derives basis xyz xyzx := by
  exact Derives.fromBasis (e := tailDeleteLaw) (by
    simp [basis])

/-- An arbitrary three-block word can acquire a copy of its first block. -/
theorem derivesAppendFirst
    (x y z : Word Nat) :
    Derives basis ((x ++ y) ++ z) (((x ++ y) ++ z) ++ x) := by
  have substituted :=
    Derives.subst basisTailDelete (instantiateFour x y z z)
  simpa [tailDeleteLaw, xyz, xyzx, instantiateFour,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- An arbitrary `XXY` block can acquire a nonempty fourth block. -/
theorem derivesAppendAfterDoubleFirst
    (x y z : Word Nat) :
    Derives basis ((x ++ x) ++ y) (((x ++ x) ++ y) ++ z) := by
  have substituted :=
    Derives.subst basisDoubleFirstForget (instantiateFour x y z z)
  simpa [doubleFirstForgetLaw, xxy, xxyz, instantiateFour,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- A repeated third block may be replaced by the first block. -/
theorem derivesRepeatedThirdToFirst
    (x y : Word Nat) :
    Derives basis ((x ++ y) ++ y) ((x ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisReturnCollapse (instantiateFour x y y y)
  simpa [returnCollapseLaw, xyx, xyy, instantiateFour,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.symm substituted

/-- The five-step deletion calculation
`XYZU = XYZXU = XYZXXYU = XYZXXY = XYZX = XYZ`.

The variables here denote arbitrary nonempty words, so one use removes the
entire suffix after the third block. -/
theorem derivesDeleteFourth
    (x y z u : Word Nat) :
    Derives basis (((x ++ y) ++ z) ++ u) ((x ++ y) ++ z) := by
  have first :=
    Derives.appendRight (derivesAppendFirst x y z) u
  have second :=
    Derives.appendRight (derivesAppendFirst (x ++ y) z x) u
  have third :=
    Derives.prepend ((x ++ y) ++ z) <|
      Derives.symm (derivesAppendAfterDoubleFirst x y u)
  have fourth :=
    Derives.symm (derivesAppendFirst (x ++ y) z x)
  have fifth :=
    Derives.symm (derivesAppendFirst x y z)
  simp only [Word.append_assoc] at first second third fourth fifth ⊢
  exact first.trans <| second.trans <| third.trans <| fourth.trans fifth

/-- Every word with at least four letters contracts to its first three. -/
theorem derivesLongToThree
    (first second third fourth : Nat) (more : List Nat) :
    Derives basis
      (wordOfTwo first second (third :: fourth :: more))
      (wordOfTwo first second [third]) := by
  have deletion :=
    derivesDeleteFourth
      (Word.singleton first)
      (Word.singleton second)
      (Word.singleton third)
      (wordOfCons fourth more)
  simpa [wordOfCons, wordOfTwo, Word.singleton, Word.append,
    Word.append_assoc] using deletion

/-- The third coordinate identifies a repetition of the second letter with
the first letter. -/
def normalizeThird (first second third : Nat) : Nat :=
  if third = second then first else third

inductive Signature where
  | singleton (first : Nat)
  | pair (first second : Nat)
  | long (first second third : Nat)
deriving DecidableEq, Repr

def Signature.word : Signature → Word Nat
  | .singleton first => Word.singleton first
  | .pair first second => wordOfTwo first second []
  | .long first second third => wordOfTwo first second [third]

def signature : Word Nat → Signature
  | ⟨first, []⟩ => .singleton first
  | ⟨first, second :: []⟩ => .pair first second
  | ⟨first, second :: third :: _⟩ =>
      .long first second (normalizeThird first second third)

def normalWord (word : Word Nat) : Word Nat :=
  (signature word).word

/-- Every word derives to its explicit three-coordinate normal form. -/
theorem derivesNormal (word : Word Nat) :
    Derives basis word (normalWord word) := by
  cases word with
  | mk first tail =>
      cases tail with
      | nil =>
          exact Derives.refl _
      | cons second rest =>
          cases rest with
          | nil =>
              exact Derives.refl _
          | cons third more =>
              have shortened :
                  Derives basis
                    (wordOfTwo first second (third :: more))
                    (wordOfTwo first second [third]) := by
                cases more with
                | nil => exact Derives.refl _
                | cons fourth extra =>
                    exact derivesLongToThree first second third fourth extra
              by_cases repeated : third = second
              · subst third
                have collapsed :=
                  derivesRepeatedThirdToFirst
                    (Word.singleton first) (Word.singleton second)
                simpa [normalWord, signature, Signature.word,
                  normalizeThird, wordOfTwo, Word.singleton, Word.append,
                  Word.append_assoc] using shortened.trans collapsed
              · simpa [normalWord, signature, Signature.word,
                  normalizeThird, repeated, wordOfTwo] using shortened

theorem normalWord_eq_of_signature_eq
    {left right : Word Nat}
    (equal : signature left = signature right) :
    normalWord left = normalWord right :=
  congrArg Signature.word equal

theorem derivesOfSignatureEq
    {left right : Word Nat}
    (equal : signature left = signature right) :
    Derives basis left right := by
  have normalEqual := normalWord_eq_of_signature_eq equal
  exact Derives.trans (derivesNormal left) <| by
    rw [normalEqual]
    exact Derives.symm (derivesNormal right)

theorem basis_complete_of_signature
    (T : FiniteTable)
    (modelsT : Models T.semigroup basis)
    (separates :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy T.semigroup →
          signature identity.lhs = signature identity.rhs) :
    BasisFor T.semigroup basis := by
  refine ⟨modelsT, ?_⟩
  intro identity valid
  exact derivesOfSignatureEq (separates identity valid)

end SemigroupBasis.CoRoots.Order6LeeZhangS6_9727
