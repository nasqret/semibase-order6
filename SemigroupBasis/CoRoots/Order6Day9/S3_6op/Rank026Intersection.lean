import SemigroupBasis.CoRoots.Order6Day9.S3_6op.Rank026GuardedReplay
import SemigroupBasis.CoRoots.S5_1099Semantics
import SemigroupBasis.CoRoots.S5_381Invariant
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Rank026 unrestricted completeness by guarded band replay

This proof does not revive or copy the retired D026 B10 scanner.  A repeated
initial letter admits one leading duplicate, so the full lower derivation
can be replayed behind that duplicate.  A globally simple initial letter
is cancelled only from the lower TRACE DATA: the lower normal list is the
two-copy head followed by the suffix normal list.  Its suffix derivation is
then replayed behind the original head using the exact B10 guarded macros.

The independent S5_1099 derivation is never used without this proved guard.
No class-specific finite table, split map, section, or joint injection is
constructed here; those remain S3's responsibility.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day9.S3_6op.Rank026Intersection

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day9.S3_6op.Rank026GuardedReplay

private abbrev Lower := SemigroupBasis.CoRoots.S5_1099.TraceState

theorem leftFactor_eq_initialMarker :
    leftTable.semigroup = finalMarkerThree.semigroup.opposite := by
  unfold leftTable Generated.Catalogue.S3_6.table
    Generated.Catalogue.S3_6.mul finalMarkerThree finalMarkerThreeMul
    FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext first second
  decide +revert

theorem sameHeads_of_factorValid (identity : Identity Nat)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have order := SemigroupBasis.CoRoots.S5_1099.valid_firstOccurrenceSequence_eq
    identity rightValid
  have heads := congrArg List.head? order
  simpa [firstOccurrenceSequence, Word.toList] using heads

theorem sameInitialSimplicity_of_factorValid (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup) (letter : Nat) :
    SemigroupBasis.CoRoots.S5_107.SimpleInitial identity.lhs letter ↔
      SemigroupBasis.CoRoots.S5_107.SimpleInitial identity.rhs letter := by
  rw [leftFactor_eq_initialMarker] at leftValid
  exact SemigroupBasis.CoRoots.S5_381Invariant.oppositeFinalMarkerValid_simpleInitial_iff
    identity leftValid letter

theorem simpleInitial_iff_head_absent (word : Word Nat) :
    SemigroupBasis.CoRoots.S5_107.SimpleInitial word word.head ↔
      word.head ∉ word.tail := by
  cases word
  simp [SemigroupBasis.CoRoots.S5_107.SimpleInitial,
    SemigroupBasis.CoRoots.S5_107.SimpleIn, Word.toList, List.count_eq_zero]

/-- Pure trace-state data, not a B10 scanner or a lower rewrite. -/
private def prependDoubleHead (head : Nat) (state : Lower) : Lower :=
  ⟨[head, head] ++ state.core, state.final⟩

private theorem traceStep_prependDoubleHead (head next : Nat) (state : Lower)
    (different : next ≠ head) :
    SemigroupBasis.CoRoots.S5_1099.traceStep (prependDoubleHead head state) next =
      prependDoubleHead head (SemigroupBasis.CoRoots.S5_1099.traceStep state next) := by
  by_cases member : next ∈ state.core
  · simp [SemigroupBasis.CoRoots.S5_1099.traceStep, prependDoubleHead, member, different]
  · simp [SemigroupBasis.CoRoots.S5_1099.traceStep, prependDoubleHead, member, different,
      List.append_assoc]

private theorem traceFold_prependDoubleHead (head : Nat) (state : Lower)
    (letters : List Nat) (absent : head ∉ letters) :
    letters.foldl SemigroupBasis.CoRoots.S5_1099.traceStep
        (prependDoubleHead head state) =
      prependDoubleHead head
        (letters.foldl SemigroupBasis.CoRoots.S5_1099.traceStep state) := by
  induction letters generalizing state with
  | nil => rfl
  | cons next rest induction =>
      have different : next ≠ head := by
        intro equal
        exact absent (by simp [equal])
      have absentRest : head ∉ rest := fun member => absent (List.Mem.tail next member)
      simp only [List.foldl_cons]
      rw [traceStep_prependDoubleHead head next state different]
      exact induction (SemigroupBasis.CoRoots.S5_1099.traceStep state next) absentRest

theorem simpleInitial_traceState_split (head next : Nat) (rest : List Nat)
    (absent : head ∉ next :: rest) :
    SemigroupBasis.CoRoots.S5_1099.traceState (Word.mk head (next :: rest)) =
      prependDoubleHead head
        (SemigroupBasis.CoRoots.S5_1099.traceState (Word.mk next rest)) := by
  have different : next ≠ head := by
    intro equal
    exact absent (by simp [equal])
  have absentRest : head ∉ rest := fun member => absent (List.Mem.tail next member)
  have initial :
      SemigroupBasis.CoRoots.S5_1099.traceStep ⟨[head], head⟩ next =
        prependDoubleHead head ⟨[next], next⟩ := by
    simp [SemigroupBasis.CoRoots.S5_1099.traceStep, prependDoubleHead, different]
  change rest.foldl SemigroupBasis.CoRoots.S5_1099.traceStep
      (SemigroupBasis.CoRoots.S5_1099.traceStep ⟨[head], head⟩ next) = _
  rw [initial]
  exact traceFold_prependDoubleHead head ⟨[next], next⟩ rest absentRest

/-- Cancelling a simple head is valid at the trace-data level only. -/
theorem simpleInitial_traceNormal_split (head next : Nat) (rest : List Nat)
    (absent : head ∉ next :: rest) :
    SemigroupBasis.CoRoots.S5_1099.traceNormalList (Word.mk head (next :: rest)) =
      [head, head] ++ SemigroupBasis.CoRoots.S5_1099.traceNormalList (Word.mk next rest) := by
  simp only [SemigroupBasis.CoRoots.S5_1099.traceNormalList,
    simpleInitial_traceState_split head next rest absent, prependDoubleHead,
    List.append_assoc]

theorem lowerDerives_of_normalList_eq (left right : Word Nat)
    (same : SemigroupBasis.CoRoots.S5_1099.traceNormalList left =
      SemigroupBasis.CoRoots.S5_1099.traceNormalList right) :
    Derives lowerBasis left right := by
  have leftNormal := SemigroupBasis.CoRoots.S5_1099.derivesTraceNormal left
  have rightNormal := SemigroupBasis.CoRoots.S5_1099.derivesTraceNormal right
  have normalWordEqual :
      SemigroupBasis.CoRoots.S5_1099.traceNormalWord left =
        SemigroupBasis.CoRoots.S5_1099.traceNormalWord right := by
    cases rightEq : SemigroupBasis.CoRoots.S5_1099.traceNormalList right with
    | nil =>
        exact False.elim (SemigroupBasis.CoRoots.S5_1099.traceNormalList_ne_nil right rightEq)
    | cons head tail =>
        have leftEq : SemigroupBasis.CoRoots.S5_1099.traceNormalList left = head :: tail :=
          same.trans rightEq
        simp [SemigroupBasis.CoRoots.S5_1099.traceNormalWord, leftEq, rightEq]
  rw [normalWordEqual] at leftNormal
  exact leftNormal.trans rightNormal.symm

theorem derivesOfSameHeadInitialTrace (head : Nat) (leftTail rightTail : List Nat)
    (sameNormal :
      SemigroupBasis.CoRoots.S5_1099.traceNormalList (Word.mk head leftTail) =
        SemigroupBasis.CoRoots.S5_1099.traceNormalList (Word.mk head rightTail))
    (sameInitial : (head ∉ leftTail) ↔ (head ∉ rightTail)) :
    Derives basis (Word.mk head leftTail) (Word.mk head rightTail) := by
  by_cases leftSimple : head ∉ leftTail
  · have rightSimple : head ∉ rightTail := sameInitial.mp leftSimple
    cases leftTail with
    | nil =>
        cases rightTail with
        | nil => exact Derives.refl _
        | cons next rest =>
            have split := simpleInitial_traceNormal_split head next rest rightSimple
            have impossible : SemigroupBasis.CoRoots.S5_1099.traceNormalList (Word.mk next rest) = [] := by
              rw [split] at sameNormal
              change [head, head] ++ [] = [head, head] ++ _ at sameNormal
              exact (List.append_cancel_left sameNormal).symm
            exact False.elim (SemigroupBasis.CoRoots.S5_1099.traceNormalList_ne_nil _ impossible)
    | cons next rest =>
        cases rightTail with
        | nil =>
            have split := simpleInitial_traceNormal_split head next rest leftSimple
            have impossible : SemigroupBasis.CoRoots.S5_1099.traceNormalList (Word.mk next rest) = [] := by
              rw [split] at sameNormal
              change [head, head] ++ _ = [head, head] ++ [] at sameNormal
              exact List.append_cancel_left sameNormal
            exact False.elim (SemigroupBasis.CoRoots.S5_1099.traceNormalList_ne_nil _ impossible)
        | cons other otherRest =>
            have sameTailNormal :
                SemigroupBasis.CoRoots.S5_1099.traceNormalList (Word.mk next rest) =
                  SemigroupBasis.CoRoots.S5_1099.traceNormalList (Word.mk other otherRest) := by
              rw [simpleInitial_traceNormal_split head next rest leftSimple,
                simpleInitial_traceNormal_split head other otherRest rightSimple] at sameNormal
              exact List.append_cancel_left sameNormal
            have lower := lowerDerives_of_normalList_eq _ _ sameTailNormal
            simpa [Word.singleton, Word.append] using
              liftLowerWithPrefixIdentity lower (Word.singleton head)
  · have leftRepeated : head ∈ leftTail := by simpa using leftSimple
    have rightRepeated : head ∈ rightTail := by
      apply Decidable.byContradiction
      intro absent
      exact leftSimple (sameInitial.mpr absent)
    have lower := lowerDerives_of_normalList_eq _ _ sameNormal
    have lifted : Derives basis (Word.mk head (head :: leftTail))
        (Word.mk head (head :: rightTail)) := by
      simpa [Word.singleton, Word.append] using
        liftLowerWithPrefixIdentity lower (Word.singleton head)
    exact (expandRepeatedInitial head leftTail leftRepeated).trans
      (lifted.trans (expandRepeatedInitial head rightTail rightRepeated).symm)

/-- Full unrestricted completeness of the exact reviewed B10 intersection. -/
theorem derivesOfFactorValid (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads := sameHeads_of_factorValid identity rightValid
  have normal := SemigroupBasis.CoRoots.S5_1099.traceNormalList_eq_of_signature
    (SemigroupBasis.CoRoots.S5_1099.valid_sameTraceSignature identity rightValid)
  have initial := sameInitialSimplicity_of_factorValid identity leftValid identity.lhs.head
  rcases identity with ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  change leftHead = rightHead at heads
  subst rightHead
  apply derivesOfSameHeadInitialTrace leftHead leftTail rightTail normal
  exact (simpleInitial_iff_head_absent (Word.mk leftHead leftTail)).symm.trans
    (initial.trans (simpleInitial_iff_head_absent (Word.mk leftHead rightTail)))

theorem factor_valid_iff_derives (identity : Identity Nat) :
    (identity.SatisfiedBy leftTable.semigroup ∧
      identity.SatisfiedBy rightTable.semigroup) ↔
      Derives basis identity.lhs identity.rhs := by
  constructor
  · rintro ⟨leftValid, rightValid⟩
    exact derivesOfFactorValid identity leftValid rightValid
  · intro derivation
    exact ⟨derivation.sound modelsLeft, derivation.sound modelsRight⟩

def intersectionBasis : IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

noncomputable def intersectionNormalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

end SemigroupBasis.CoRoots.Order6Day9.S3_6op.Rank026Intersection
