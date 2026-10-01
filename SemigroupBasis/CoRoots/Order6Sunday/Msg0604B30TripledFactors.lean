import SemigroupBasis.CoRoots.Order6Sunday.Msg0604B30JointSignature

/-! A parity-preserving replacement for S5_402's first normalization step.
Every globally repeated occurrence can be tripled, at an arbitrary position,
using only B30 laws 0, 3 and 5. The literal simple-block scanner is reused.
This is unrestricted derivational progress, not a complete B30 normal form.
-/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0604B30TripledFactors

open SemigroupBasis
open Msg0521RepairedThirtyLawFinite
open S5_402 (renderTerminatedBlocks terminatedBlocks terminatedFinalBlock
  terminatedBlocks_render terminatedBlocks_marker_multiple)

abbrev ListDerives := S5_107.ListDerives basis

private def instantiate (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | _ => v

theorem derivesPairPower (u : Word Nat) :
    Derives basis (u ++ u) (((u ++ u) ++ u) ++ u) := by
  have law := Derives.fromBasis (basis := basis) (e := basisLaw0) (by simp [basis])
  have step := law.subst (instantiate u u)
  simpa [basisLaw0, instantiate, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using step

theorem derivesTripleLeft (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((((u ++ u) ++ u) ++ v) ++ u)) := by
  have law := Derives.fromBasis (basis := basis) (e := basisLaw3) (by simp [basis])
  have step := law.subst (instantiate u v)
  simpa [basisLaw3, instantiate, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using step

theorem derivesTripleRight (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((((u ++ v) ++ u) ++ u) ++ u)) := by
  have law := Derives.fromBasis (basis := basis) (e := basisLaw5) (by simp [basis])
  have step := law.subst (instantiate u v)
  simpa [basisLaw5, instantiate, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using step

theorem listDerivesTripleLeft (letter : Nat) :
    ∀ middle : List Nat,
      ListDerives ([letter] ++ middle ++ [letter])
        ([letter, letter, letter] ++ middle ++ [letter])
  | [] => by
      simpa [Word.singleton, Word.append] using
        (S5_107.ListDerives.ofWord (derivesPairPower (Word.singleton letter)))
  | head :: tail => by
      simpa [S5_107.listWordOfCons, Word.singleton, Word.append, List.append_assoc] using
        (S5_107.ListDerives.ofWord (derivesTripleLeft
          (Word.singleton letter) (S5_107.listWordOfCons head tail)))

theorem listDerivesTripleRight (letter : Nat) :
    ∀ middle : List Nat,
      ListDerives ([letter] ++ middle ++ [letter])
        ([letter] ++ middle ++ [letter, letter, letter])
  | [] => by
      simpa [Word.singleton, Word.append] using
        (S5_107.ListDerives.ofWord (derivesPairPower (Word.singleton letter)))
  | head :: tail => by
      simpa [S5_107.listWordOfCons, Word.singleton, Word.append, List.append_assoc] using
        (S5_107.ListDerives.ofWord (derivesTripleRight
          (Word.singleton letter) (S5_107.listWordOfCons head tail)))

/-- The second occurrence may be anywhere before or after the selected one. -/
theorem listDerivesTripleSelectedOccurrence (letter : Nat) (before after : List Nat)
    (multiple : 2 ≤ (before ++ [letter] ++ after).count letter) :
    ListDerives (before ++ [letter] ++ after)
      (before ++ [letter, letter, letter] ++ after) := by
  by_cases afterMember : letter ∈ after
  · obtain ⟨middle, suffix, split⟩ := List.mem_iff_append.mp afterMember
    have expanded := (listDerivesTripleLeft letter middle).context before suffix
    simpa [split, List.append_assoc] using expanded
  · have beforeMember : letter ∈ before := by
      apply Classical.byContradiction
      intro beforeAbsent
      have beforeZero : before.count letter = 0 := List.count_eq_zero.mpr beforeAbsent
      have afterZero : after.count letter = 0 := List.count_eq_zero.mpr afterMember
      have countOne : (before ++ [letter] ++ after).count letter = 1 := by
        simp [List.count_append, beforeZero, afterZero]
      rw [countOne] at multiple
      omega
    obtain ⟨beforePrefix, middle, split⟩ := List.mem_iff_append.mp beforeMember
    have expanded := (listDerivesTripleRight letter middle).context beforePrefix after
    simpa [split, List.append_assoc] using expanded

def renderTripledTerminatedBlocks : List (List Nat × Nat) → List Nat
  | [] => []
  | (block, marker) :: rest =>
      block ++ marker :: marker :: marker :: renderTripledTerminatedBlocks rest

theorem count_le_count_tripleSelected (tested inserted : Nat) (before after : List Nat) :
    (before ++ [inserted] ++ after).count tested ≤
      (before ++ [inserted, inserted, inserted] ++ after).count tested := by
  by_cases equality : tested = inserted
  · subst tested
    simp [List.count_append]
  · have reverseEquality : inserted ≠ tested := Ne.symm equality
    simp [List.count_append, reverseEquality]

/-- Triple the pending factors after any already processed prefix. -/
theorem listDerivesTripleTerminatedMarkersAux (final : List Nat) :
    ∀ (factors : List (List Nat × Nat)) (before : List Nat),
      (∀ factor ∈ factors,
        2 ≤ (before ++ renderTerminatedBlocks factors ++ final).count factor.2) →
      ListDerives (before ++ renderTerminatedBlocks factors ++ final)
        (before ++ renderTripledTerminatedBlocks factors ++ final)
  | [], before, _ => by
      simpa [renderTerminatedBlocks, renderTripledTerminatedBlocks] using
        (S5_107.ListDerives.refl (basis := basis) (before ++ final))
  | (block, marker) :: rest, before, multiples => by
      have markerMultiple :
          2 ≤ ((before ++ block) ++ [marker] ++
            (renderTerminatedBlocks rest ++ final)).count marker := by
        simpa [renderTerminatedBlocks, List.append_assoc] using
          multiples (block, marker) (by simp)
      have firstRaw := listDerivesTripleSelectedOccurrence marker (before ++ block)
        (renderTerminatedBlocks rest ++ final) markerMultiple
      have firstStep :
          ListDerives (before ++ renderTerminatedBlocks ((block, marker) :: rest) ++ final)
            ((before ++ block ++ [marker, marker, marker]) ++
              renderTerminatedBlocks rest ++ final) := by
        simpa [renderTerminatedBlocks, List.append_assoc] using firstRaw
      have restMultiples : ∀ factor ∈ rest,
          2 ≤ ((before ++ block ++ [marker, marker, marker]) ++
            renderTerminatedBlocks rest ++ final).count factor.2 := by
        intro factor member
        have oldMultiple :
            2 ≤ ((before ++ block) ++ [marker] ++
              (renderTerminatedBlocks rest ++ final)).count factor.2 := by
          simpa [renderTerminatedBlocks, List.append_assoc] using
            multiples factor (by simp [member])
        have monotone := count_le_count_tripleSelected factor.2 marker
          (before ++ block) (renderTerminatedBlocks rest ++ final)
        simpa [List.append_assoc] using Nat.le_trans oldMultiple monotone
      have restStep := listDerivesTripleTerminatedMarkersAux final rest
        (before ++ block ++ [marker, marker, marker]) restMultiples
      have combined := firstStep.trans restStep
      simpa [renderTripledTerminatedBlocks, List.append_assoc] using combined

/-- Arbitrary word lists derive under B30 to tripled repeated markers and
unchanged simple blocks. There is no length, alphabet, or occurrence bound. -/
theorem listDerivesTripleAllTerminatedMarkers (letters : List Nat) :
    ListDerives letters
      (renderTripledTerminatedBlocks (terminatedBlocks letters) ++ terminatedFinalBlock letters) := by
  have multiples : ∀ factor ∈ terminatedBlocks letters,
      2 ≤ (renderTerminatedBlocks (terminatedBlocks letters) ++
        terminatedFinalBlock letters).count factor.2 := by
    intro factor member
    rw [terminatedBlocks_render letters]
    exact terminatedBlocks_marker_multiple letters factor member
  have tripled := listDerivesTripleTerminatedMarkersAux
    (terminatedFinalBlock letters) (terminatedBlocks letters) [] (by simpa using multiples)
  simpa [terminatedBlocks_render letters] using tripled

end SemigroupBasis.CoRoots.Order6Sunday.Msg0604B30TripledFactors
