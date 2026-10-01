import SemigroupBasis.CoRoots.Order6Sunday.Msg0606B30BankCollection

/-! Unrestricted cubic-bank normalization. Permute by marker, group equal
markers, then contract each power to two or three copies according to parity.
The key list is an explicit duplicate-free enumeration of the bank support;
binding it to the scanner's global multiple letters is a separate theorem. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0606B30BankNormalization

open SemigroupBasis
open Msg0521RepairedThirtyLawFinite (basis)
open Msg0604B30TripledFactors
open Msg0606B30FactorSort
open Msg0606B30BankCollection
open S5_402 (repeatAtLeastTwo renderSquaredTerminatedBlocks
  renderSquaredTerminatedBlocks_append)

theorem derivesRepeatedBlockParity (block : Word Nat) :
    ∀ extra : Nat, Derives basis (repeatAtLeastTwo block extra)
      (repeatAtLeastTwo block (extra % 2))
  | 0 => Derives.refl _
  | 1 => Derives.refl _
  | n + 2 => by
      have first := ((derivesRepeatedBlockParity block n).appendRight block).appendRight block
      have reduce : Derives basis
          ((repeatAtLeastTwo block (n % 2) ++ block) ++ block)
          (repeatAtLeastTwo block (n % 2)) := by
        have cases : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases cases with even | odd
        · simpa [repeatAtLeastTwo, even] using (derivesPairPower block).symm
        · simpa [repeatAtLeastTwo, odd] using
            (derivesPairPower block).symm.appendRight block
      have modEq : (n + 2) % 2 = n % 2 := by omega
      simpa [repeatAtLeastTwo, modEq] using first.trans reduce

theorem repeatAtLeastTwo_singleton_list (x extra : Nat) :
    (repeatAtLeastTwo (Word.singleton x) extra).toList = List.replicate (2 + extra) x := by
  induction extra with
  | zero => rfl
  | succ n ih =>
      change (repeatAtLeastTwo (Word.singleton x) n).toList ++ [x] = _
      rw [ih]
      simpa only [Nat.add_assoc] using (List.replicate_succ' (a := x) (n := 2 + n)).symm

theorem listDerivesReplicateParity (x n : Nat) (large : 2 ≤ n) :
    ListDerives (List.replicate n x) (List.replicate (2 + n % 2) x) := by
  have step := S5_107.ListDerives.ofWord
    (derivesRepeatedBlockParity (Word.singleton x) (n - 2))
  have nEq : 2 + (n - 2) = n := by omega
  have parityEq : (n - 2) % 2 = n % 2 := by omega
  simpa only [repeatAtLeastTwo_singleton_list, nEq, parityEq] using step

theorem renderCubeBank_append (left right : List Nat) :
    renderCubeBank (left ++ right) = renderCubeBank left ++ renderCubeBank right := by
  induction left with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem renderCubeBank_replicate (x n : Nat) :
    renderCubeBank (List.replicate n x) = List.replicate (3 * n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate_succ, ih, Nat.mul_succ]

def expandedLabels (keys : List Nat) (weight : Nat → Nat) : List Nat :=
  keys.flatMap fun x => List.replicate (weight x) x

theorem count_expandedLabels (keys : List Nat) (weight : Nat → Nat)
    (nodup : keys.Nodup) (tested : Nat) :
    (expandedLabels keys weight).count tested = if tested ∈ keys then weight tested else 0 := by
  induction keys with
  | nil => simp [expandedLabels]
  | cons x xs ih =>
      have tail := ih (List.nodup_cons.mp nodup).2
      simp only [expandedLabels] at tail
      have absent : x ∉ xs := (List.nodup_cons.mp nodup).1
      by_cases same : tested = x
      · subst tested
        simp [expandedLabels, List.count_append, tail, absent]
      · simp [expandedLabels, List.count_append, List.count_replicate,
          tail, same, Ne.symm same]

theorem expandedLabels_perm (keys labels : List Nat) (nodup : keys.Nodup)
    (support : ∀ x, x ∈ keys ↔ x ∈ labels) :
    (expandedLabels keys labels.count).Perm labels := by
  rw [List.perm_iff_count]
  intro x
  rw [count_expandedLabels keys labels.count nodup x]
  by_cases present : x ∈ keys
  · simp [present]
  · have absent : x ∉ labels := fun h => present ((support x).mpr h)
    simp [present, List.count_eq_zero.mpr absent]

def parityBank (keys labels : List Nat) : List Nat :=
  keys.flatMap fun x => List.replicate (2 + labels.count x % 2) x

theorem listDerivesGroupedBank (keys : List Nat) (weight : Nat → Nat)
    (positive : ∀ x ∈ keys, 0 < weight x) :
    ListDerives (renderCubeBank (expandedLabels keys weight))
      (keys.flatMap fun x => List.replicate (2 + weight x % 2) x) := by
  induction keys with
  | nil => exact S5_107.ListDerives.empty
  | cons x xs ih =>
      have pos := positive x (by simp)
      have tail := ih (fun y hy => positive y (by simp [hy]))
      have head := listDerivesReplicateParity x (3 * weight x) (by omega)
      have parityEq : (3 * weight x) % 2 = weight x % 2 := by omega
      have head' : ListDerives (renderCubeBank (List.replicate (weight x) x))
          (List.replicate (2 + weight x % 2) x) := by
        simpa [renderCubeBank_replicate, parityEq] using head
      have step := (head'.append (renderCubeBank (expandedLabels xs weight))).trans
        (tail.prepend (List.replicate (2 + weight x % 2) x))
      simpa [expandedLabels, renderCubeBank_append] using step

theorem listDerivesCubeBankPermutation (first : List Nat × Nat)
    (retained : List (List Nat × Nat)) {left right : List Nat}
    (permutation : left.Perm right) (final : List Nat) :
    ListDerives
      (renderSquaredTerminatedBlocks (first :: retained) ++ renderCubeBank left ++ final)
      (renderSquaredTerminatedBlocks (first :: retained) ++ renderCubeBank right ++ final) := by
  have perm := List.Perm.append_left retained (permutation.map cubeFactor)
  have step := listDerivesSquaredTailPermutation perm first final
  simpa [renderCubeBank, cubeFactors, renderSquaredTerminatedBlocks,
    renderSquaredTerminatedBlocks_append, List.append_assoc] using step

/-- Genuine B30 derivation for any finite bank and any duplicate-free list
of its markers; there is no bound on the bank or on marker multiplicity. -/
theorem listDerivesNormalizeCubicBank (first : List Nat × Nat)
    (retained : List (List Nat × Nat)) (keys labels final : List Nat)
    (nodup : keys.Nodup) (support : ∀ x, x ∈ keys ↔ x ∈ labels) :
    ListDerives
      (renderSquaredTerminatedBlocks (first :: retained) ++ renderCubeBank labels ++ final)
      (renderSquaredTerminatedBlocks (first :: retained) ++ parityBank keys labels ++ final) := by
  have grouping := listDerivesCubeBankPermutation first retained
    (expandedLabels_perm keys labels nodup support).symm final
  have grouped := listDerivesGroupedBank keys labels.count (by
    intro x member
    exact List.count_pos_iff.mpr ((support x).mp member))
  have normalize := grouped.context (renderSquaredTerminatedBlocks (first :: retained)) final
  exact grouping.trans normalize

end SemigroupBasis.CoRoots.Order6Sunday.Msg0606B30BankNormalization
