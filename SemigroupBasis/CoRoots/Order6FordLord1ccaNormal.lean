/-
Statements-first normalizer layer for the Ford-Lord displayed system
Sigma_1ccaef90de83de0a.

Layer A: the fourteen displayed laws and their word-block instances.
Layer B1: the corrected D_1cca signature.
Layer B2: the oracle-validated canonicalization function.

Completeness, finite-table semantics, and order-six wrappers intentionally do
not appear in this checkpoint.
-/
import SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma

set_option maxRecDepth 4096

namespace SemigroupBasis.CoRoots.Order6FordLord1cca

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-! ## Layer A: exact displayed basis -/

def powerLaw : Identity Nat :=
  ⟨w 0 [0], w 0 [0, 0]⟩

def leftCollapseLaw : Identity Nat :=
  ⟨w 0 [0, 1, 0], w 0 [1, 0]⟩

def squareInterleaveLaw : Identity Nat :=
  ⟨w 0 [0, 1, 1], w 0 [1, 0, 1]⟩

def promotionLaw : Identity Nat :=
  ⟨w 0 [0, 1, 1, 2], w 0 [1, 0, 2]⟩

def leftTransportLaw : Identity Nat :=
  ⟨w 0 [0, 1, 2, 1], w 0 [1, 0, 2, 1]⟩

def crossTransportLaw : Identity Nat :=
  ⟨w 0 [0, 1, 2, 1], w 0 [1, 2, 0, 1]⟩

def rightDuplicationLaw : Identity Nat :=
  ⟨w 0 [1, 0], w 0 [1, 0, 0]⟩

def sandwichDuplicationLaw : Identity Nat :=
  ⟨w 0 [1, 0], w 0 [1, 0, 1, 0]⟩

def middleDuplicationLaw : Identity Nat :=
  ⟨w 0 [1, 0], w 0 [1, 1, 0]⟩

def middleCollapseLaw : Identity Nat :=
  ⟨w 0 [1, 0, 2, 0], w 0 [1, 2, 0]⟩

def tailTransportLaw : Identity Nat :=
  ⟨w 0 [1, 0, 2, 2], w 0 [1, 2, 0, 2]⟩

def headTransportLaw : Identity Nat :=
  ⟨w 0 [1, 1, 2, 0], w 0 [1, 2, 0]⟩

def lateDuplicationLeftLaw : Identity Nat :=
  ⟨w 0 [1, 2, 0], w 0 [1, 2, 1, 0]⟩

def lateDuplicationRightLaw : Identity Nat :=
  ⟨w 0 [1, 2, 0], w 0 [1, 2, 2, 0]⟩

def basis : List (Identity Nat) :=
  [powerLaw, leftCollapseLaw, squareInterleaveLaw, promotionLaw,
    leftTransportLaw, crossTransportLaw, rightDuplicationLaw,
    sandwichDuplicationLaw, middleDuplicationLaw, middleCollapseLaw,
    tailTransportLaw, headTransportLaw, lateDuplicationLeftLaw,
    lateDuplicationRightLaw]

theorem basis_length : basis.length = 14 := by decide

theorem basis_eq_displayed :
    basis =
      SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_1ccaef90de83de0a.basis := by
  decide

private theorem powerMem : powerLaw ∈ basis := by simp [basis]
private theorem leftCollapseMem : leftCollapseLaw ∈ basis := by simp [basis]
private theorem interleaveMem : squareInterleaveLaw ∈ basis := by simp [basis]
private theorem promotionMem : promotionLaw ∈ basis := by simp [basis]
private theorem leftTransportMem : leftTransportLaw ∈ basis := by simp [basis]
private theorem crossTransportMem : crossTransportLaw ∈ basis := by simp [basis]
private theorem rightDupMem : rightDuplicationLaw ∈ basis := by simp [basis]
private theorem sandwichDupMem : sandwichDuplicationLaw ∈ basis := by simp [basis]
private theorem middleDupMem : middleDuplicationLaw ∈ basis := by simp [basis]
private theorem middleCollapseMem : middleCollapseLaw ∈ basis := by simp [basis]
private theorem tailTransportMem : tailTransportLaw ∈ basis := by simp [basis]
private theorem headTransportMem : headTransportLaw ∈ basis := by simp [basis]
private theorem lateDupLeftMem : lateDuplicationLeftLaw ∈ basis := by simp [basis]
private theorem lateDupRightMem : lateDuplicationRightLaw ∈ basis := by simp [basis]

private def instantiateThree (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

/-- `X² ~ X³`. -/
theorem derivesPower (x : Word Nat) :
    Derives basis (x ++ x) ((x ++ x) ++ x) := by
  have core : Derives basis powerLaw.lhs powerLaw.rhs :=
    Derives.fromBasis powerMem
  have substituted := Derives.subst core (instantiateThree x x x)
  simpa [powerLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `X²YX ~ XYX`. -/
theorem derivesLeftCollapse (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ x) ((x ++ y) ++ x) := by
  have core : Derives basis leftCollapseLaw.lhs leftCollapseLaw.rhs :=
    Derives.fromBasis leftCollapseMem
  have substituted := Derives.subst core (instantiateThree x y y)
  simpa [leftCollapseLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `X²Y² ~ XYXY`. -/
theorem derivesSquareInterleave (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ y) (((x ++ y) ++ x) ++ y) := by
  have core : Derives basis squareInterleaveLaw.lhs
      squareInterleaveLaw.rhs :=
    Derives.fromBasis interleaveMem
  have substituted := Derives.subst core (instantiateThree x y y)
  simpa [squareInterleaveLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `X²Y²Z ~ XYXZ`. -/
theorem derivesPromotion (x y z : Word Nat) :
    Derives basis ((((x ++ x) ++ y) ++ y) ++ z)
      (((x ++ y) ++ x) ++ z) := by
  have core : Derives basis promotionLaw.lhs promotionLaw.rhs :=
    Derives.fromBasis promotionMem
  have substituted := Derives.subst core (instantiateThree x y z)
  simpa [promotionLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `X²YZY ~ XYXZY`. -/
theorem derivesLeftTransport (x y z : Word Nat) :
    Derives basis ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ x) ++ z) ++ y) := by
  have core : Derives basis leftTransportLaw.lhs leftTransportLaw.rhs :=
    Derives.fromBasis leftTransportMem
  have substituted := Derives.subst core (instantiateThree x y z)
  simpa [leftTransportLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `X²YZY ~ XYZXY`. -/
theorem derivesCrossTransport (x y z : Word Nat) :
    Derives basis ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ z) ++ x) ++ y) := by
  have core : Derives basis crossTransportLaw.lhs crossTransportLaw.rhs :=
    Derives.fromBasis crossTransportMem
  have substituted := Derives.subst core (instantiateThree x y z)
  simpa [crossTransportLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `XYX ~ XYX²`. -/
theorem derivesRightDuplication (x y : Word Nat) :
    Derives basis ((x ++ y) ++ x) (((x ++ y) ++ x) ++ x) := by
  have core : Derives basis rightDuplicationLaw.lhs
      rightDuplicationLaw.rhs :=
    Derives.fromBasis rightDupMem
  have substituted := Derives.subst core (instantiateThree x y y)
  simpa [rightDuplicationLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `XYX ~ XYXYX`. -/
theorem derivesSandwichDuplication (x y : Word Nat) :
    Derives basis ((x ++ y) ++ x)
      ((((x ++ y) ++ x) ++ y) ++ x) := by
  have core : Derives basis sandwichDuplicationLaw.lhs
      sandwichDuplicationLaw.rhs :=
    Derives.fromBasis sandwichDupMem
  have substituted := Derives.subst core (instantiateThree x y y)
  simpa [sandwichDuplicationLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `XYX ~ XY²X`. -/
theorem derivesMiddleDuplication (x y : Word Nat) :
    Derives basis ((x ++ y) ++ x) (((x ++ y) ++ y) ++ x) := by
  have core : Derives basis middleDuplicationLaw.lhs
      middleDuplicationLaw.rhs :=
    Derives.fromBasis middleDupMem
  have substituted := Derives.subst core (instantiateThree x y y)
  simpa [middleDuplicationLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `XYXZX ~ XYZX`. -/
theorem derivesMiddleCollapse (x y z : Word Nat) :
    Derives basis ((((x ++ y) ++ x) ++ z) ++ x)
      (((x ++ y) ++ z) ++ x) := by
  have core : Derives basis middleCollapseLaw.lhs middleCollapseLaw.rhs :=
    Derives.fromBasis middleCollapseMem
  have substituted := Derives.subst core (instantiateThree x y z)
  simpa [middleCollapseLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `XYXZ² ~ XYZ XZ`. -/
theorem derivesTailTransport (x y z : Word Nat) :
    Derives basis ((((x ++ y) ++ x) ++ z) ++ z)
      ((((x ++ y) ++ z) ++ x) ++ z) := by
  have core : Derives basis tailTransportLaw.lhs tailTransportLaw.rhs :=
    Derives.fromBasis tailTransportMem
  have substituted := Derives.subst core (instantiateThree x y z)
  simpa [tailTransportLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `XY²ZX ~ XYZX`. -/
theorem derivesHeadTransport (x y z : Word Nat) :
    Derives basis ((((x ++ y) ++ y) ++ z) ++ x)
      (((x ++ y) ++ z) ++ x) := by
  have core : Derives basis headTransportLaw.lhs headTransportLaw.rhs :=
    Derives.fromBasis headTransportMem
  have substituted := Derives.subst core (instantiateThree x y z)
  simpa [headTransportLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `XYZX ~ XYZ YX`. -/
theorem derivesLateDuplicationLeft (x y z : Word Nat) :
    Derives basis (((x ++ y) ++ z) ++ x)
      ((((x ++ y) ++ z) ++ y) ++ x) := by
  have core : Derives basis lateDuplicationLeftLaw.lhs
      lateDuplicationLeftLaw.rhs :=
    Derives.fromBasis lateDupLeftMem
  have substituted := Derives.subst core (instantiateThree x y z)
  simpa [lateDuplicationLeftLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `XYZX ~ XYZ²X`. -/
theorem derivesLateDuplicationRight (x y z : Word Nat) :
    Derives basis (((x ++ y) ++ z) ++ x)
      ((((x ++ y) ++ z) ++ z) ++ x) := by
  have core : Derives basis lateDuplicationRightLaw.lhs
      lateDuplicationRightLaw.rhs :=
    Derives.fromBasis lateDupRightMem
  have substituted := Derives.subst core (instantiateThree x y z)
  simpa [lateDuplicationRightLaw, w, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-! ## Layer B1: corrected D_1cca signature -/

def letterCount (u : Word Nat) (x : Nat) : Nat :=
  u.toList.count x

def lastIdxOf (letters : List Nat) (x : Nat) : Nat :=
  letters.length - 1 - letters.reverse.idxOf x

def truePlasmaSeq (u : Word Nat) : List Nat :=
  u.toList.eraseDups.filter (fun x => decide (2 ≤ letterCount u x))

def liesInsideTruePlasma (u : Word Nat) (x : Nat) : Bool :=
  (truePlasmaSeq u).any (fun p =>
    decide (u.toList.idxOf p < u.toList.idxOf x) &&
      decide (u.toList.idxOf x < lastIdxOf u.toList p))

def isPromotedPlasma (u : Word Nat) (x : Nat) : Bool :=
  decide (2 ≤ letterCount u x) ||
    (letterCount u x == 1 && liesInsideTruePlasma u x)

def IsPromotedPlasma (u : Word Nat) (x : Nat) : Prop :=
  isPromotedPlasma u x = true

instance (u : Word Nat) (x : Nat) : Decidable (IsPromotedPlasma u x) := by
  unfold IsPromotedPlasma
  infer_instance

/-- True plasma plus promoted singletons, in first-occurrence order. -/
def plasmaSeq (u : Word Nat) : List Nat :=
  u.toList.eraseDups.filter (isPromotedPlasma u)

/-- Count-one letters not promoted into plasma, in occurrence order. -/
def singlesSeq (u : Word Nat) : List Nat :=
  u.toList.filter (fun x =>
    letterCount u x == 1 && !(isPromotedPlasma u x))

def finalLetter (u : Word Nat) : Nat :=
  u.tail.getLastD u.head

/-- First-occurrence order of the non-head interior letters of a returning
word. -/
def returnSequence (u : Word Nat) : List Nat :=
  (u.tail.dropLast.filter (fun x => x != u.head)).eraseDups

/-- The before/after row of one unpromoted single against the promoted plasma
sequence. `true` means that the plasma interval has already closed. -/
def afterRow (u : Word Nat) (single : Nat) : List Bool :=
  (plasmaSeq u).map (fun p =>
    decide (lastIdxOf u.toList p < u.toList.idxOf single))

inductive Signature where
  | one (head : Nat)
  | returning (head : Nat) (interior : List Nat)
  | nonreturning
      (head final : Nat)
      (singles plasma : List Nat)
      (rows : List (List Bool))
deriving DecidableEq, Repr

def signatureOf (u : Word Nat) : Signature :=
  match u.tail with
  | [] => Signature.one u.head
  | _ :: _ =>
      if finalLetter u == u.head then
        Signature.returning u.head (returnSequence u)
      else
        Signature.nonreturning
          u.head
          (finalLetter u)
          (singlesSeq u)
          (plasmaSeq u)
          ((singlesSeq u).map (afterRow u))

def SameSignature (u v : Word Nat) : Prop :=
  signatureOf u = signatureOf v

instance (u v : Word Nat) : Decidable (SameSignature u v) := by
  unfold SameSignature
  infer_instance

/-! ## Layer B2: oracle-validated canonical word -/

/-- Number of promoted-plasma intervals already closed before a single. -/
def slotOf (u : Word Nat) (single : Nat) : Nat :=
  ((plasmaSeq u).filter (fun p =>
    decide (lastIdxOf u.toList p < u.toList.idxOf single))).length

def slotSingles (u : Word Nat) (slot : Nat) : List Nat :=
  (singlesSeq u).filter (fun single => slotOf u single == slot)

private def linearPlasmaBlocks (u : Word Nat) : List Nat :=
  let pseq := plasmaSeq u
  (List.range pseq.length).flatMap (fun i =>
    let p := pseq.getD i 0
    [p, p] ++ slotSingles u (i + 1))

private def finalPlasmaBlocks (u : Word Nat) : List Nat :=
  let pseq := plasmaSeq u
  let final := finalLetter u
  let finalIndex := pseq.idxOf final
  let before := (List.range finalIndex).flatMap (fun i =>
    let p := pseq.getD i 0
    [p, p] ++ slotSingles u (i + 1))
  let afterCount := pseq.length - (finalIndex + 1)
  let after := (List.range afterCount).flatMap (fun offset =>
    let p := pseq.getD (finalIndex + 1 + offset) 0
    [p, p])
  before ++ [final] ++ after ++ [final]

def canonicalList (u : Word Nat) : List Nat :=
  match u.tail with
  | [] => [u.head]
  | _ :: _ =>
      if finalLetter u == u.head then
        (u.head :: returnSequence u) ++ [u.head]
      else if isPromotedPlasma u (finalLetter u) then
        slotSingles u 0 ++ finalPlasmaBlocks u
      else
        slotSingles u 0 ++ linearPlasmaBlocks u

def canonicalize (u : Word Nat) : Word Nat :=
  ⟨(canonicalList u).headD u.head, (canonicalList u).tail⟩

end SemigroupBasis.CoRoots.Order6FordLord1cca
