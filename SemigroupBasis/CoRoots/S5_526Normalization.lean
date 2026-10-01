import SemigroupBasis.FiniteTable

namespace SemigroupBasis.CoRoots.S5_526

open SemigroupBasis

def xxx : Word Nat := ⟨0, [0, 0]⟩
def xxy : Word Nat := ⟨0, [0, 1]⟩
def xyx : Word Nat := ⟨0, [1, 0]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩

def firstRepeatLaw : Identity Nat := ⟨xxx, xxy⟩
def secondRepeatLaw : Identity Nat := ⟨xyx, xyy⟩
def firstPairLaw : Identity Nat := ⟨xyx, xyz⟩

/-- The exact catalogue basis `xxx = xxy`, `xyx = xyy`, `xyx = xyz`. -/
def basis : List (Identity Nat) :=
  [firstRepeatLaw, secondRepeatLaw, firstPairLaw]

def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def wordOfTwo (first second : Nat) (rest : List Nat) : Word Nat :=
  ⟨first, second :: rest⟩

private def instantiateThree
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Every word of length at least three contracts to its first letter,
second letter, and first letter. -/
theorem derivesLongToFirstPairReturn
    (first second third : Nat) (rest : List Nat) :
    Derives basis
      (wordOfTwo first second (third :: rest))
      (wordOfTwo first second [first]) := by
  have base : Derives basis xyz xyx :=
    Derives.symm <|
      Derives.fromBasis (e := firstPairLaw) <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have instantiated :=
    Derives.subst base
      (instantiateThree
        (Word.singleton first)
        (Word.singleton second)
        (wordOfCons third rest))
  simpa [basis, firstPairLaw, xyz, xyx, instantiateThree,
    wordOfCons, wordOfTwo, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

/-- The unrestricted normal-form signature. Singleton and quadratic words
remain literal; every longer word keeps only its first ordered pair. -/
inductive FirstPairSignature where
  | singleton (first : Nat)
  | pair (first second : Nat)
  | long (first second : Nat)
deriving DecidableEq, Repr

def FirstPairSignature.word : FirstPairSignature → Word Nat
  | .singleton first => Word.singleton first
  | .pair first second => wordOfTwo first second []
  | .long first second => wordOfTwo first second [first]

def signature : Word Nat → FirstPairSignature
  | ⟨first, []⟩ => .singleton first
  | ⟨first, second :: []⟩ => .pair first second
  | ⟨first, second :: third :: rest⟩ => .long first second

def normalWord (word : Word Nat) : Word Nat :=
  (signature word).word

/-- Every nonempty word derives to its explicit first-pair normal form. -/
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
              simpa [normalWord, signature, FirstPairSignature.word,
                wordOfTwo] using
                  derivesLongToFirstPairReturn first second third more

theorem normalWord_eq_of_signature_eq
    {left right : Word Nat}
    (equal : signature left = signature right) :
    normalWord left = normalWord right :=
  congrArg FirstPairSignature.word equal

/-- Equal first-pair signatures are sufficient for unrestricted
derivability from the exact three-law basis. -/
theorem derivesOfSignatureEq
    {left right : Word Nat}
    (equal : signature left = signature right) :
    Derives basis left right := by
  have normalEqual :=
    normalWord_eq_of_signature_eq equal
  exact Derives.trans (derivesNormal left) <| by
    rw [normalEqual]
    exact Derives.symm (derivesNormal right)

/-- Generic completeness theorem for the S5_526 normalizer. A concrete
semigroup only has to model the basis and separate the three signature
constructors with their stored variables. -/
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

end SemigroupBasis.CoRoots.S5_526
