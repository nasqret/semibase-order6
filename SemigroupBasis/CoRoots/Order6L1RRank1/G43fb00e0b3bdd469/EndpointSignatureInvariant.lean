import SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.Canonical
import SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.Semantics

/-!
# Endpoint-pivot signature invariant for G43

This route-local module connects the proof-oriented selected-factor signature
to the reducible Layer-A signature used by the endpoint-pivot construction.
It deliberately imports no G43 `Primitives`, `Normalization`,
`Completeness`, or closed-route `CanonicalSemantics` module.

This is an off-tree static draft.  It has not been elaborated locally.
-/

namespace SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots
open SemigroupBasis.CoRoots.Order6L1RRank1

/-! ## Syntax bridges between the reducible and proof-oriented coordinates -/

/-- The Layer-A and public right-regular-band scans compute the same list. -/
theorem lastOccurrenceSequence_eq_s5_1092 :
    ∀ letters : List Nat,
      lastOccurrenceSequence letters =
        S5_1092.lastOccurrenceSequence letters
  | [] => rfl
  | letter :: rest => by
      rw [lastOccurrenceSequence, S5_1092.lastOccurrenceSequence,
        lastOccurrenceSequence_eq_s5_1092 rest]

private theorem mem_s5_1092_lastOccurrenceSequence_iff
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ S5_1092.lastOccurrenceSequence letters ↔
        selected ∈ letters
  | [] => by simp [S5_1092.lastOccurrenceSequence]
  | letter :: rest => by
      by_cases later : letter ∈ rest
      · rw [S5_1092.lastOccurrenceSequence, if_pos later,
          mem_s5_1092_lastOccurrenceSequence_iff selected rest]
        constructor
        · exact List.Mem.tail letter
        · intro member
          rcases List.mem_cons.mp member with equal | inRest
          · subst selected
            exact later
          · exact inRest
      · simp [S5_1092.lastOccurrenceSequence, later,
          mem_s5_1092_lastOccurrenceSequence_iff selected rest]

private theorem reducibleFirstOccurrences_eq :
    ∀ letters : List Nat,
      reducibleFirstOccurrences letters =
        firstOccurrenceSequence letters
  | [] => rfl
  | letter :: rest => by
      rw [reducibleFirstOccurrences, firstOccurrenceSequence,
        reducibleFirstOccurrences_eq rest]

/-- The transparent split used by Layer A agrees with the proof-oriented
prefix/final split. -/
private theorem reducibleSplitPrefixFinalData_eq
    : ∀ (head : Nat) (tail : List Nat),
      reducibleSplitPrefixFinalData head tail =
        splitPrefixFinal (Word.mk head tail)
  | head, [] => rfl
  | head, [next] => rfl
  | head, next :: after :: rest => by
      change
        (let split :=
            reducibleSplitPrefixFinalData next (after :: rest);
          (head :: split.1, split.2)) =
        (let split :=
            splitPrefixFinal (Word.mk next (after :: rest));
          (head :: split.1, split.2))
      rw [reducibleSplitPrefixFinalData_eq next (after :: rest)]

private theorem edmundsFourSixtyFourLongNormal_toList_bridge
    (initial : Nat) (remaining : List Nat) (final : Nat) :
    (edmundsFourSixtyFourLongNormal initial remaining final).toList =
      if final ∈ initial :: remaining then
        initial :: (remaining ++ [initial])
      else
        initial :: (remaining ++ [final]) := by
  by_cases finalMem : final ∈ initial :: remaining
  · simp only [edmundsFourSixtyFourLongNormal, finalMem, if_pos]
    rfl
  · simp only [edmundsFourSixtyFourLongNormal, finalMem, if_neg]
    rfl

/-- A common list presentation of the reducible and proof-oriented
`S4_64` normal forms. -/
private def s4_64BridgeList (word : Word Nat) : List Nat :=
  let split := splitPrefixFinal word
  match split.1 with
  | [] => word.toList
  | first :: rest =>
      match firstOccurrenceSequence (first :: rest) with
      | [] => word.toList
      | initial :: remaining =>
          if split.2 ∈ initial :: remaining then
            initial :: (remaining ++ [initial])
          else
            initial :: (remaining ++ [split.2])

private theorem reducibleS4_64NormalList_eq_bridge
    (word : Word Nat) :
    reducibleS4_64NormalList word = s4_64BridgeList word := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          let split := splitPrefixFinal (Word.mk next rest)
          have layerSplit :
              reducibleSplitPrefixFinalData head (next :: rest) =
                (head :: split.1, split.2) := by
            calc
              reducibleSplitPrefixFinalData head (next :: rest) =
                  splitPrefixFinal (Word.mk head (next :: rest)) :=
                reducibleSplitPrefixFinalData_eq head (next :: rest)
              _ = (head :: split.1, split.2) := rfl
          have proofSplit :
              splitPrefixFinal (Word.mk head (next :: rest)) =
                (head :: split.1, split.2) := rfl
          simp only [reducibleS4_64NormalList, s4_64BridgeList]
          rw [layerSplit, proofSplit, reducibleFirstOccurrences_eq]
          rfl

private theorem s4_64BridgeList_ne_nil (word : Word Nat) :
    s4_64BridgeList word ≠ [] := by
  have wordNonempty : word.toList ≠ [] := by
    cases word
    simp [Word.toList]
  unfold s4_64BridgeList
  dsimp only
  cases prefixEq : (splitPrefixFinal word).1 with
  | nil => simpa only [prefixEq] using wordNonempty
  | cons first rest =>
      simp only [prefixEq]
      cases firstEq : firstOccurrenceSequence (first :: rest) with
      | nil => simpa only [firstEq] using wordNonempty
      | cons initial remaining =>
          simp only [firstEq]
          split <;> simp

private theorem toList_wordOfList_of_ne_nil
    {letters : List Nat} (nonempty : letters ≠ []) :
    (wordOfList letters).toList = letters := by
  cases letters with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail => rfl

private theorem s4_64Normal_toList_eq_bridge
    (word : Word Nat) :
    (s4_64Normal word).toList = s4_64BridgeList word := by
  unfold s4_64Normal
  rw [toList_wordOfList_of_ne_nil]
  · exact reducibleS4_64NormalList_eq_bridge word
  · rw [reducibleS4_64NormalList_eq_bridge]
    exact s4_64BridgeList_ne_nil word

private theorem s4_64ProofNormal_toList_eq_bridge
    (word : Word Nat) :
    (s4_64ProofNormal word).toList = s4_64BridgeList word := by
  unfold s4_64ProofNormal s4_64BridgeList
  dsimp only
  cases prefixEq : (splitPrefixFinal word).1 with
  | nil => simp only [prefixEq]
  | cons first rest =>
      simp only [prefixEq]
      cases firstEq : firstOccurrenceSequence (first :: rest) with
      | nil => simp only [firstEq]
      | cons initial remaining =>
          simp only [firstEq]
          exact
            edmundsFourSixtyFourLongNormal_toList_bridge
              initial remaining (splitPrefixFinal word).2

/-- The Layer-A `S4_64` coordinate is the list underlying the proof normal. -/
theorem s4_64Normal_toList_eq_s4_64ProofNormal
    (word : Word Nat) :
    (s4_64Normal word).toList = (s4_64ProofNormal word).toList :=
  (s4_64Normal_toList_eq_bridge word).trans
    (s4_64ProofNormal_toList_eq_bridge word).symm

/-! ## Complete endpoint-route signature invariant -/

/-- The selected-factor semantics determine every coordinate used by the
endpoint-pivot route's Layer-A signature. -/
theorem jointSignature_eq_of_sameJointSignature
    {left right : Word Nat}
    (same : SameJointSignature left right) :
    jointSignature left = jointSignature right := by
  have supportEq :
      sortedSupport left.toList = sortedSupport right.toList := by
    apply sortedSupport_eq_of_mem_iff
    intro selected
    rw [← mem_s5_1092_lastOccurrenceSequence_iff selected left.toList,
      ← mem_s5_1092_lastOccurrenceSequence_iff selected right.toList,
      same.lastOccurrences]
  have lastOrderEq :
      lastOccurrenceSequence left.toList =
        lastOccurrenceSequence right.toList := by
    simpa only [lastOccurrenceSequence_eq_s5_1092] using
      same.lastOccurrences
  have factorNormalEq :
      (s4_64Normal left).toList = (s4_64Normal right).toList := by
    rw [s4_64Normal_toList_eq_s4_64ProofNormal,
      s4_64Normal_toList_eq_s4_64ProofNormal,
      same.factorNormal]
  unfold jointSignature
  dsimp only
  rw [supportEq, lastOrderEq, factorNormalEq]

/-- Every displayed-basis derivation preserves the endpoint-pivot signature. -/
theorem jointSignature_eq_of_derives
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    jointSignature left = jointSignature right := by
  apply jointSignature_eq_of_sameJointSignature
  exact sameJointSignature_of_factor_valid
    (Identity.mk left right)
    (fun valuation => derivation.sound left_models valuation)
    (fun valuation => derivation.sound right_models valuation)

end SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469
