/-
Statements-first normalizer layer for the Ford-Lord displayed system
Sigma_ae8f21b57d380dc3.

Layer A: the eight displayed laws and their word-block instances.
Layer B1: the corrected D_ae8 signature.
Layer B2: the oracle-validated event-scheduled canonicalization function.

Completeness, finite-table semantics, and order-six wrappers intentionally do
not appear in this checkpoint.
-/
import SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma

set_option maxRecDepth 4096

namespace SemigroupBasis.CoRoots.Order6FordLordAe8

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

def plasmaLordForgetLaw : Identity Nat :=
  ⟨w 0 [0, 1, 1, 2], w 0 [1, 1, 0, 2]⟩

def leftTransportLaw : Identity Nat :=
  ⟨w 0 [0, 1, 2, 1], w 0 [1, 0, 2, 1]⟩

def rightDuplicationLaw : Identity Nat :=
  ⟨w 0 [1, 0], w 0 [1, 0, 0]⟩

def middleCollapseLaw : Identity Nat :=
  ⟨w 0 [1, 0, 2, 0], w 0 [1, 2, 0]⟩

def tailTransportLaw : Identity Nat :=
  ⟨w 0 [1, 0, 2, 2], w 0 [1, 2, 0, 2]⟩

def basis : List (Identity Nat) :=
  [powerLaw, leftCollapseLaw, squareInterleaveLaw, plasmaLordForgetLaw,
    leftTransportLaw, rightDuplicationLaw, middleCollapseLaw,
    tailTransportLaw]

theorem basis_length : basis.length = 8 := by decide

theorem basis_eq_displayed :
    basis =
      SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ae8f21b57d380dc3.basis := by
  decide

private theorem powerMem : powerLaw ∈ basis := by simp [basis]
private theorem leftCollapseMem : leftCollapseLaw ∈ basis := by simp [basis]
private theorem interleaveMem : squareInterleaveLaw ∈ basis := by simp [basis]
private theorem plasmaLordForgetMem : plasmaLordForgetLaw ∈ basis := by
  simp [basis]
private theorem leftTransportMem : leftTransportLaw ∈ basis := by simp [basis]
private theorem rightDupMem : rightDuplicationLaw ∈ basis := by simp [basis]
private theorem middleCollapseMem : middleCollapseLaw ∈ basis := by simp [basis]
private theorem tailTransportMem : tailTransportLaw ∈ basis := by simp [basis]

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

/-! ## Layer B1: corrected D_ae8 signature -/

def letterCount (u : Word Nat) (x : Nat) : Nat :=
  u.toList.count x

def firstOccurrenceSequence (u : Word Nat) : List Nat :=
  u.toList.eraseDups

def finalLetter (u : Word Nat) : Nat :=
  u.tail.getLastD u.head

def lastIdxOf (letters : List Nat) (x : Nat) : Nat :=
  letters.length - 1 - letters.reverse.idxOf x

def isPlasma (u : Word Nat) (x : Nat) : Bool :=
  decide (2 ≤ letterCount u x)

def singlesSequence (u : Word Nat) : List Nat :=
  u.toList.filter (fun x => letterCount u x == 1)

def sortedSupport (u : Word Nat) : List Nat :=
  (u.toList.eraseDups).mergeSort
    (fun left right : Nat => decide (left ≤ right))

def plasmaSequence (u : Word Nat) : List Nat :=
  (sortedSupport u).filter (isPlasma u)

def cappedCounts (u : Word Nat) : List (Nat × Nat) :=
  (sortedSupport u).map (fun x => (x, Nat.min (letterCount u x) 2))

inductive IntervalRelation where
  | before
  | inside
  | after
deriving DecidableEq, Repr

def intervalRelation (u : Word Nat) (single plasma : Nat) :
    IntervalRelation :=
  if u.toList.idxOf single < u.toList.idxOf plasma then
    IntervalRelation.before
  else if lastIdxOf u.toList plasma < u.toList.idxOf single then
    IntervalRelation.after
  else
    IntervalRelation.inside

structure RelationEntry where
  single : Nat
  plasma : Nat
  position : IntervalRelation
deriving DecidableEq, Repr

def relationEntries (u : Word Nat) : List RelationEntry :=
  (singlesSequence u).flatMap (fun single =>
    (plasmaSequence u).map (fun plasma =>
      ⟨single, plasma, intervalRelation u single plasma⟩))

structure Signature where
  firstOccurrences : List Nat
  counts : List (Nat × Nat)
  final : Nat
  relations : List RelationEntry
deriving DecidableEq, Repr

def signatureOf (u : Word Nat) : Signature :=
  ⟨firstOccurrenceSequence u, cappedCounts u, finalLetter u,
    relationEntries u⟩

def SameSignature (u v : Word Nat) : Prop :=
  signatureOf u = signatureOf v

instance (u v : Word Nat) : Decidable (SameSignature u v) := by
  unfold SameSignature
  infer_instance

/-! ## Layer B2: oracle-validated event-scheduled canonical word -/

private structure ScheduleState where
  output : List Nat
  openPlasma : List Nat

/-- Open a plasma interval, or close every already-open interval that lies
strictly before the current singleton and then emit that singleton. -/
private def scheduleEvent (u : Word Nat) (state : ScheduleState)
    (letter : Nat) : ScheduleState :=
  if isPlasma u letter then
    { output := state.output ++ [letter]
      openPlasma := state.openPlasma ++ [letter] }
  else
    let closes := state.openPlasma.filter (fun plasma =>
      decide (intervalRelation u letter plasma = IntervalRelation.after))
    let remains := state.openPlasma.filter (fun plasma =>
      decide (intervalRelation u letter plasma ≠ IntervalRelation.after))
    { output := state.output ++ closes ++ [letter]
      openPlasma := remains }

private def scheduledPrefix (u : Word Nat) : ScheduleState :=
  (firstOccurrenceSequence u).foldl (scheduleEvent u)
    { output := [], openPlasma := [] }

/-- Close all remaining intervals in opening order.  When the original final
letter is plasma, close it last so that the descriptor's final-letter bit is
retained. -/
private def finishSchedule (u : Word Nat) (state : ScheduleState) : List Nat :=
  let final := finalLetter u
  if isPlasma u final then
    let nonfinal := state.openPlasma.filter (fun plasma =>
      decide (plasma ≠ final))
    state.output ++ nonfinal ++ [final]
  else
    state.output ++ state.openPlasma

def canonicalList (u : Word Nat) : List Nat :=
  finishSchedule u (scheduledPrefix u)

def canonicalize (u : Word Nat) : Word Nat :=
  ⟨(canonicalList u).headD u.head, (canonicalList u).tail⟩

end SemigroupBasis.CoRoots.Order6FordLordAe8
