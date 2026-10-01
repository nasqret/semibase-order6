/-
Statements-first normalizer layer for the Ford-Lord displayed system
Sigma_9808750adcf41d94.

Layer A: the eleven displayed laws and their word-block instances.
Layer B1: the corrected D_980 signature, which forgets both plasma orders.
Layer B2: the oracle-validated event-scheduled canonicalization function.

Completeness, finite-table semantics, and order-six wrappers intentionally do
not appear in this checkpoint.
-/
import SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma

set_option maxRecDepth 4096

namespace SemigroupBasis.CoRoots.Order6FordLord980

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-! ## Layer A: exact displayed basis -/

def powerLaw : Identity Nat :=
  ⟨w 0 [0], w 0 [0, 0]⟩

def leftCollapseLaw : Identity Nat :=
  ⟨w 0 [0, 1, 0], w 0 [1, 0]⟩

def interleaveLaw : Identity Nat :=
  ⟨w 0 [0, 1, 1], w 0 [1, 0, 1]⟩

def plasmaFordForgetLaw : Identity Nat :=
  ⟨w 0 [0, 1, 1], w 1 [0, 0, 1]⟩

def plasmaLordForgetLaw : Identity Nat :=
  ⟨w 0 [0, 1, 1, 2], w 0 [1, 1, 0, 2]⟩

def leftTransportLaw : Identity Nat :=
  ⟨w 0 [0, 1, 2, 1], w 0 [1, 0, 2, 1]⟩

def headForgetTransportLaw : Identity Nat :=
  ⟨w 0 [0, 1, 2, 1], w 1 [0, 0, 2, 1]⟩

def rightDuplicationLaw : Identity Nat :=
  ⟨w 0 [1, 0], w 0 [1, 0, 0]⟩

def middleCollapseLaw : Identity Nat :=
  ⟨w 0 [1, 0, 2, 0], w 0 [1, 2, 0]⟩

def tailTransportLaw : Identity Nat :=
  ⟨w 0 [1, 0, 2, 2], w 0 [1, 2, 0, 2]⟩

def lateHeadForgetLaw : Identity Nat :=
  ⟨w 0 [1, 2, 0, 1], w 1 [0, 2, 0, 1]⟩

def basis : List (Identity Nat) :=
  [powerLaw, leftCollapseLaw, interleaveLaw, plasmaFordForgetLaw,
    plasmaLordForgetLaw, leftTransportLaw, headForgetTransportLaw,
    rightDuplicationLaw, middleCollapseLaw, tailTransportLaw,
    lateHeadForgetLaw]

theorem basis_length : basis.length = 11 := by decide

theorem basis_eq_displayed :
    basis =
      SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_9808750adcf41d94.basis := by
  decide

private theorem powerMem : powerLaw ∈ basis := by simp [basis]
private theorem leftCollapseMem : leftCollapseLaw ∈ basis := by simp [basis]
private theorem interleaveMem : interleaveLaw ∈ basis := by simp [basis]
private theorem plasmaFordForgetMem : plasmaFordForgetLaw ∈ basis := by
  simp [basis]
private theorem plasmaLordForgetMem : plasmaLordForgetLaw ∈ basis := by
  simp [basis]
private theorem leftTransportMem : leftTransportLaw ∈ basis := by simp [basis]
private theorem headForgetTransportMem : headForgetTransportLaw ∈ basis := by
  simp [basis]
private theorem rightDupMem : rightDuplicationLaw ∈ basis := by simp [basis]
private theorem middleCollapseMem : middleCollapseLaw ∈ basis := by simp [basis]
private theorem tailTransportMem : tailTransportLaw ∈ basis := by simp [basis]
private theorem lateHeadForgetMem : lateHeadForgetLaw ∈ basis := by simp [basis]

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
theorem derivesInterleave (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ y) (((x ++ y) ++ x) ++ y) := by
  have core : Derives basis interleaveLaw.lhs interleaveLaw.rhs :=
    Derives.fromBasis interleaveMem
  have substituted := Derives.subst core (instantiateThree x y y)
  simpa [interleaveLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `X²Y² ~ YX²Y`. -/
theorem derivesPlasmaFordForget (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ y) (((y ++ x) ++ x) ++ y) := by
  have core : Derives basis plasmaFordForgetLaw.lhs
      plasmaFordForgetLaw.rhs :=
    Derives.fromBasis plasmaFordForgetMem
  have substituted := Derives.subst core (instantiateThree x y y)
  simpa [plasmaFordForgetLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `X²Y²Z ~ XY²XZ`. -/
theorem derivesPlasmaLordForget (x y z : Word Nat) :
    Derives basis ((((x ++ x) ++ y) ++ y) ++ z)
      ((((x ++ y) ++ y) ++ x) ++ z) := by
  have core : Derives basis plasmaLordForgetLaw.lhs
      plasmaLordForgetLaw.rhs :=
    Derives.fromBasis plasmaLordForgetMem
  have substituted := Derives.subst core (instantiateThree x y z)
  simpa [plasmaLordForgetLaw, w, instantiateThree, Word.bind, Word.append,
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

/-- `X²YZY ~ YX²ZY`. -/
theorem derivesHeadForgetTransport (x y z : Word Nat) :
    Derives basis ((((x ++ x) ++ y) ++ z) ++ y)
      ((((y ++ x) ++ x) ++ z) ++ y) := by
  have core : Derives basis headForgetTransportLaw.lhs
      headForgetTransportLaw.rhs :=
    Derives.fromBasis headForgetTransportMem
  have substituted := Derives.subst core (instantiateThree x y z)
  simpa [headForgetTransportLaw, w, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- `XYX ~ XYX²`. -/
theorem derivesRightDuplication (x y : Word Nat) :
    Derives basis ((x ++ y) ++ x) (((x ++ y) ++ x) ++ x) := by
  have core : Derives basis rightDuplicationLaw.lhs
      rightDuplicationLaw.rhs :=
    Derives.fromBasis rightDupMem
  have substituted := Derives.subst core (instantiateThree x y y)
  simpa [rightDuplicationLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `XYXZX ~ XYZX`. -/
theorem derivesMiddleCollapse (x y z : Word Nat) :
    Derives basis ((((x ++ y) ++ x) ++ z) ++ x)
      (((x ++ y) ++ z) ++ x) := by
  have core : Derives basis middleCollapseLaw.lhs
      middleCollapseLaw.rhs :=
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

/-- `XYZXY ~ YXZXY`. -/
theorem derivesLateHeadForget (x y z : Word Nat) :
    Derives basis ((((x ++ y) ++ z) ++ x) ++ y)
      ((((y ++ x) ++ z) ++ x) ++ y) := by
  have core : Derives basis lateHeadForgetLaw.lhs lateHeadForgetLaw.rhs :=
    Derives.fromBasis lateHeadForgetMem
  have substituted := Derives.subst core (instantiateThree x y z)
  simpa [lateHeadForgetLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-! ## Layer B1: corrected D_980 signature -/

def letterCount (u : Word Nat) (x : Nat) : Nat :=
  u.toList.count x

def lastIdxOf (letters : List Nat) (x : Nat) : Nat :=
  letters.length - 1 - letters.reverse.idxOf x

def firstOccurrenceSeq (u : Word Nat) : List Nat :=
  u.toList.eraseDups

def sortedSupport (u : Word Nat) : List Nat :=
  (firstOccurrenceSeq u).mergeSort (fun x y : Nat => decide (x ≤ y))

/-- Count-at-least-two letters in numeric order.  Neither Ford nor Lord
plasma order is retained by `D_980`. -/
def plasmaSeq (u : Word Nat) : List Nat :=
  (sortedSupport u).filter (fun x => decide (2 ≤ letterCount u x))

/-- Count-one letters in first-occurrence order. -/
def singlesSeq (u : Word Nat) : List Nat :=
  (firstOccurrenceSeq u).filter (fun x => letterCount u x == 1)

def cappedCounts (u : Word Nat) : List (Nat × Nat) :=
  (sortedSupport u).map (fun x => (x, min (letterCount u x) 2))

def finalLetter (u : Word Nat) : Nat :=
  u.tail.getLastD u.head

inductive RelativePosition where
  | before
  | inside
  | after
deriving DecidableEq, BEq, Repr

/-- Position of a singleton relative to the first/last interval of a plasma
letter. -/
def relation (u : Word Nat) (single plasma : Nat) : RelativePosition :=
  if u.toList.idxOf single < u.toList.idxOf plasma then
    RelativePosition.before
  else if lastIdxOf u.toList plasma < u.toList.idxOf single then
    RelativePosition.after
  else
    RelativePosition.inside

def relationRows (u : Word Nat) : List (List RelativePosition) :=
  (singlesSeq u).map (fun single =>
    (plasmaSeq u).map (relation u single))

structure Signature where
  plasma : List Nat
  capped : List (Nat × Nat)
  final : Nat
  singles : List Nat
  relations : List (List RelativePosition)
deriving DecidableEq, Repr

def signatureOf (u : Word Nat) : Signature where
  plasma := plasmaSeq u
  capped := cappedCounts u
  final := finalLetter u
  singles := singlesSeq u
  relations := relationRows u

def SameSignature (u v : Word Nat) : Prop :=
  signatureOf u = signatureOf v

instance (u v : Word Nat) : Decidable (SameSignature u v) := by
  unfold SameSignature
  infer_instance

/-! ## Layer B2: oracle-validated event schedule -/

structure ScheduleState where
  unopened : List Nat
  active : List Nat
  output : List Nat
deriving DecidableEq, Repr

private def eraseMembers (letters removed : List Nat) : List Nat :=
  letters.filter (fun x => !(removed.contains x))

/-- Open every interval needed by this singleton, close every interval for
which it is `after`, then emit the singleton. -/
private def scheduleSingle
    (u : Word Nat) (state : ScheduleState) (single : Nat) : ScheduleState :=
  let needed := state.unopened.filter (fun p =>
    relation u single p != RelativePosition.before)
  let active := state.active ++ needed
  let toClose := active.filter (fun p =>
    relation u single p == RelativePosition.after)
  {
    unopened := eraseMembers state.unopened needed
    active := eraseMembers active toClose
    output := state.output ++ needed ++ toClose ++ [single]
  }

private def singletonSchedule (u : Word Nat) : ScheduleState :=
  (singlesSeq u).foldl (scheduleSingle u) {
    unopened := plasmaSeq u
    active := []
    output := []
  }

/-- Plasma not required by any singleton opens after all singletons. -/
private def openRemaining (state : ScheduleState) : ScheduleState :=
  {
    unopened := []
    active := state.active ++ state.unopened
    output := state.output ++ state.unopened
  }

/-- Deterministic event schedule computed from `D_980`.  A plasma final letter
is forced to close after every other still-active plasma interval. -/
def canonicalList (u : Word Nat) : List Nat :=
  let opened := openRemaining (singletonSchedule u)
  let final := finalLetter u
  if (plasmaSeq u).contains final then
    opened.output ++
      opened.active.filter (fun p => p != final) ++ [final]
  else
    opened.output ++ opened.active

def canonicalize (u : Word Nat) : Word Nat :=
  ⟨(canonicalList u).headD u.head, (canonicalList u).tail⟩

end SemigroupBasis.CoRoots.Order6FordLord980
