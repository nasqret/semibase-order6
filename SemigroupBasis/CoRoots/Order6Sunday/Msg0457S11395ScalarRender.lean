import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ResolverProjection

/-! Flattened scalar resolution on actual simple-marker sectors. These
algebraic lemmas preserve the first sector's incoming state and reset it
on subsequent sectors. No semantic completeness premise is introduced. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ScalarRender

open SemigroupBasis
open Msg0457S11395WordGaps Msg0457S11395WordReduction Msg0457S11395PairResolver
open Msg0457S11395ResolveLetter Msg0457S11395CoordinateSectors
open Msg0457S11395SectorSignature Msg0457S11395ResolverProjection

def scalarRender (past : Bool) : List (List Nat) → List Nat
  | [] => []
  | block :: rest => resolve past block ++ (rest.map (resolve false)).flatten

def pairBlocks : List (List Nat) → List Nat
  | [] => []
  | block :: rest => endPair block.length ++ List.replicate rest.flatten.length 0

theorem scalarRender_false (blocks : List (List Nat)) :
    scalarRender false blocks = (blocks.map (resolve false)).flatten := by
  cases blocks <;> rfl

theorem positive_false_all_zero (counts : List Nat) (empty : positive counts = false) :
    ∀ count ∈ counts, count = 0 := by
  induction counts with
  | nil => simp
  | cons count rest ih =>
      have zero : count = 0 := by
        by_cases zero : count = 0
        · exact zero
        · have pos : 0 < count := Nat.pos_of_ne_zero zero
          simp [positive, pos] at empty
      subst count
      change positive rest = false at empty
      intro tested member
      rcases List.mem_cons.mp member with equal | later
      · exact equal
      · exact ih empty tested later

theorem all_zero_replicate (counts : List Nat) (zeros : ∀ count ∈ counts, count = 0) :
    counts = List.replicate counts.length 0 := by
  induction counts with
  | nil => rfl
  | cons count rest ih =>
      have zero := zeros count List.mem_cons_self
      have tailZeros : ∀ tested ∈ rest, tested = 0 := fun tested member =>
        zeros tested (List.mem_cons_of_mem count member)
      change count :: rest = 0 :: List.replicate rest.length 0
      rw [zero]
      exact congrArg (List.cons 0) (ih tailZeros)

theorem resolve_zero (past : Bool) (counts : List Nat) (zeros : ∀ count ∈ counts, count = 0) :
    resolve past counts = counts := by
  induction counts generalizing past with
  | nil => rfl
  | cons count rest ih =>
      have zero := zeros count List.mem_cons_self
      have tailZeros : ∀ tested ∈ rest, tested = 0 := fun tested member =>
        zeros tested (List.mem_cons_of_mem count member)
      subst count
      change 0 :: resolve (past || false) rest = 0 :: rest
      exact congrArg (List.cons 0) (ih (past || false) tailZeros)

theorem scalarRender_zero (past : Bool) (blocks : List (List Nat))
    (zeros : ∀ count ∈ blocks.flatten, count = 0) : scalarRender past blocks = blocks.flatten := by
  induction blocks generalizing past with
  | nil => rfl
  | cons block rest ih =>
      have blockZeros : ∀ count ∈ block, count = 0 := fun count member =>
        zeros count (List.mem_append_left _ member)
      have restZeros : ∀ count ∈ rest.flatten, count = 0 := fun count member =>
        zeros count (List.mem_append_right _ member)
      change resolve past block ++ (rest.map (resolve false)).flatten = block ++ rest.flatten
      rw [resolve_zero past block blockZeros, ← scalarRender_false rest, ih false restZeros]

theorem scalarRender_prepend_small (past cut : Bool) (count : Nat) (blocks : List (List Nat))
    (small : ¬ 2 ≤ count) :
    scalarRender past (prependSectorCell count cut blocks) =
      count :: scalarRender (if cut then false else past || decide (0 < count)) blocks := by
  cases blocks with
  | nil => simp [scalarRender, prependSectorCell, resolve, small]
  | cons block rest =>
      cases cut <;> simp [scalarRender, prependSectorCell, resolve, small]

theorem reducedCounts_pair (count : Nat) (rest : List Nat)
    (red : ReducedCounts (count :: rest)) (pair : 2 ≤ count) :
    count = 2 ∧ ∀ tested ∈ rest, tested = 0 := by
  have empty : positive rest = false := by
    cases active : positive rest with
    | false => rfl
    | true =>
        have bound : count ≤ 1 := by simpa only [active] using red.1
        omega
  have bound : count ≤ 2 := by simpa only [empty] using red.1
  exact ⟨by omega, positive_false_all_zero rest empty⟩

theorem scalarRender_pair (past : Bool) (block : List Nat) (rest : List (List Nat))
    (zeros : ∀ count ∈ rest.flatten, count = 0) :
    scalarRender past ((2 :: block) :: rest) =
      if past then 0 :: (block ++ rest.flatten)
      else endPair (block.length + 1) ++ rest.flatten := by
  have restFixed : (rest.map (resolve false)).flatten = rest.flatten :=
    (scalarRender_false rest).symm.trans (scalarRender_zero false rest zeros)
  cases past <;> simp [scalarRender, resolve, restFixed]

theorem pairBlocks_prepend_cut (count : Nat) (blocks : List (List Nat)) :
    pairBlocks (prependSectorCell count true blocks) =
      2 :: List.replicate blocks.flatten.length 0 := by
  cases blocks <;> rfl

theorem pairBlocks_prepend_join (count head : Nat) (block : List Nat) (rest : List (List Nat)) :
    pairBlocks (prependSectorCell count false ((head :: block) :: rest)) =
      0 :: pairBlocks ((head :: block) :: rest) := rfl

theorem sectorCounts_head_shape (whole : List Nat) (letter : Nat) (chain : Chain) :
    ∃ block rest, sectorCounts whole letter chain = ((headGap chain).count letter :: block) :: rest := by
  cases chain with
  | stop gap => exact ⟨[],[],rfl⟩
  | step gap fresh tail =>
      cases shape : sectorCounts whole letter tail with
      | nil => exact ⟨[],[],by simp [sectorCounts, shape, prependSectorCell, headGap]⟩
      | cons block rest =>
          by_cases cut : whole.count fresh = 1
          · exact ⟨[],block :: rest,by simp [sectorCounts, shape, prependSectorCell, headGap, cut]⟩
          · exact ⟨block,rest,by simp [sectorCounts, shape, prependSectorCell, headGap, cut]⟩

theorem gapProfile_length (letter : Nat) (chain : Chain) :
    (gapProfile letter chain).length = (introductions chain).length + 1 := by
  induction chain with
  | stop gap => rfl
  | step gap fresh tail ih => simp only [gapProfile, introductions, List.length_cons, ih]

theorem sectorCounts_flatten_length (whole : List Nat) (letter : Nat) (chain : Chain) :
    (sectorCounts whole letter chain).flatten.length = (introductions chain).length + 1 := by
  rw [sectorCounts_flatten, gapProfile_length]

theorem pairVector_eq_pairBlocks (whole : List Nat) (letter : Nat) (chain : Chain) :
    pairVector whole chain = pairBlocks (sectorCounts whole letter chain) := by
  induction chain with
  | stop gap => rfl
  | step gap fresh tail ih =>
      by_cases cut : whole.count fresh = 1
      · rw [pairVector, if_pos cut, sectorCounts]
        have flag : decide (whole.count fresh = 1) = true := by simp [cut]
        rw [flag, pairBlocks_prepend_cut, sectorCounts_flatten_length]
        rfl
      · rw [pairVector, if_neg cut, sectorCounts]
        have flag : decide (whole.count fresh = 1) = false := by simp [cut]
        obtain ⟨block,rest,shape⟩ := sectorCounts_head_shape whole letter tail
        rw [flag, shape, pairBlocks_prepend_join]
        rw [shape] at ih
        exact congrArg (List.cons 0) ih

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ScalarRender
