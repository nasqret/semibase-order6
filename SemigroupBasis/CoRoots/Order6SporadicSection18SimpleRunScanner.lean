import SemigroupBasis.CoRoots.Order6SporadicSection18CanonicalWord
import SemigroupBasis.CoRoots.S5_107BlockCombinatorics

/-! The pure globally-simple scanner reads exactly the gaps of a C7
canonical chain. The ambient multiplicity predicate stays fixed throughout
recursion. No S5_107 algebraic identity is used. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

def optionalSimpleRun (gap : List Nat) : List (List Nat) :=
  if gap = [] then [] else [gap]

theorem scan_simplePrefix (whole suffix : List Nat) :
    ∀ (gap current : List Nat),
      (∀ x ∈ gap, whole.count x = 1) →
      S5_107.simpleBlockScan whole current (gap ++ suffix) =
        S5_107.simpleBlockScan whole (gap.reverse ++ current) suffix
  | [], current, _ => rfl
  | head :: tail, current, simple => by
      have step : S5_107.simpleBlockScan whole current ((head :: tail) ++ suffix) =
          S5_107.simpleBlockScan whole (head :: current) (tail ++ suffix) := by
        cases current <;>
          simp only [List.cons_append, S5_107.simpleBlockScan,
            if_pos (simple head (List.Mem.head tail))]
      rw [step, scan_simplePrefix whole suffix tail (head :: current)
        (fun x member => simple x (List.Mem.tail head member))]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem scan_nonsimplePrefix (whole suffix : List Nat) :
    ∀ block : List Nat,
      (∀ x ∈ block, whole.count x ≠ 1) →
      S5_107.simpleBlockScan whole [] (block ++ suffix) =
        S5_107.simpleBlockScan whole [] suffix
  | [], _ => rfl
  | head :: tail, nonsimple => by
      rw [List.cons_append, S5_107.simpleBlockScan,
        if_neg (nonsimple head (List.Mem.head tail))]
      exact scan_nonsimplePrefix whole suffix tail
        (fun x member => nonsimple x (List.Mem.tail head member))

theorem scan_flush_block (whole current block suffix : List Nat)
    (nonempty : block ≠ []) (nonsimple : ∀ x ∈ block, whole.count x ≠ 1) :
    S5_107.simpleBlockScan whole current (block ++ suffix) =
      optionalSimpleRun current.reverse ++ S5_107.simpleBlockScan whole [] suffix := by
  obtain ⟨head, tail, shape⟩ := List.exists_cons_of_ne_nil nonempty
  have headNot : whole.count head ≠ 1 := nonsimple head (by simp [shape])
  have tailNot : ∀ x ∈ tail, whole.count x ≠ 1 := by
    intro x member
    exact nonsimple x (by simp [shape, member])
  rw [shape, List.cons_append]
  cases current with
  | nil =>
      rw [S5_107.simpleBlockScan, if_neg headNot]
      simpa [optionalSimpleRun] using scan_nonsimplePrefix whole suffix tail tailNot
  | cons first rest =>
      rw [S5_107.simpleBlockScan, if_neg headNot]
      · rw [scan_nonsimplePrefix whole suffix tail tailNot]
        simp [optionalSimpleRun]
      · simp

theorem scan_gap_block (whole gap block suffix : List Nat)
    (simple : ∀ x ∈ gap, whole.count x = 1)
    (nonempty : block ≠ []) (nonsimple : ∀ x ∈ block, whole.count x ≠ 1) :
    S5_107.simpleBlockScan whole [] (gap ++ block ++ suffix) =
      optionalSimpleRun gap ++ S5_107.simpleBlockScan whole [] suffix := by
  rw [List.append_assoc, scan_simplePrefix whole (block ++ suffix) gap [] simple,
    List.append_nil, scan_flush_block whole gap.reverse block suffix nonempty nonsimple,
    List.reverse_reverse]

theorem scan_render (whole : List Nat) (chain : List Slot)
    (nonempty : ∀ slot ∈ chain, slot.block ≠ [])
    (nonsimple : ∀ slot ∈ chain, ∀ x ∈ slot.block, whole.count x ≠ 1)
    (simple : ∀ slot ∈ chain, ∀ x ∈ slot.gap, whole.count x = 1) :
    S5_107.simpleBlockScan whole [] (render chain) =
      chain.flatMap (fun slot => optionalSimpleRun slot.gap) := by
  induction chain with
  | nil => rfl
  | cons slot rest ih =>
      have member : slot ∈ slot :: rest := List.Mem.head rest
      have squareNonempty : squareList slot.block ≠ [] := by
        obtain ⟨head, tail, shape⟩ := List.exists_cons_of_ne_nil (nonempty slot member)
        rw [shape, squareList_cons]
        simp
      have squareNonsimple : ∀ x ∈ squareList slot.block, whole.count x ≠ 1 := by
        intro x present
        exact nonsimple slot member x ((squareList_mem slot.block x).mp present)
      have tailScanned := ih
        (fun item present => nonempty item (List.Mem.tail slot present))
        (fun item present => nonsimple item (List.Mem.tail slot present))
        (fun item present => simple item (List.Mem.tail slot present))
      rw [render, scan_gap_block whole slot.gap (squareList slot.block) (render rest)
        (simple slot member) squareNonempty squareNonsimple, tailScanned, List.flatMap_cons]

private theorem nonempty_gaps_flatMap (chain : List Slot)
    (nonempty : ∀ slot ∈ chain, slot.gap ≠ []) :
    chain.flatMap (fun slot => optionalSimpleRun slot.gap) = chain.map Slot.gap := by
  induction chain with
  | nil => rfl
  | cons slot rest ih =>
      have tail := ih (fun item member => nonempty item (List.Mem.tail slot member))
      rw [List.flatMap_cons, List.map_cons, tail, optionalSimpleRun,
        if_neg (nonempty slot (List.Mem.head rest)), List.singleton_append]

/-- The scanner's output is the literal gap list of this very presentation,
not a separately chosen canonical chain. -/
theorem canonicalGapScanner (whole : List Nat) (first : Slot) (rest : List Slot)
    (shape : render (first :: rest) = whole) (firstEmpty : first.gap = [])
    (laterNonempty : ∀ slot ∈ rest, slot.gap ≠ [])
    (nonempty : ∀ slot ∈ first :: rest, slot.block ≠ [])
    (nonsimple : ∀ slot ∈ first :: rest, ∀ x ∈ slot.block, whole.count x ≠ 1)
    (simple : ∀ slot ∈ first :: rest, ∀ x ∈ slot.gap, whole.count x = 1) :
    S5_107.simpleBlocks whole = rest.map Slot.gap := by
  have scanned : S5_107.simpleBlocks whole =
      (first :: rest).flatMap (fun slot => optionalSimpleRun slot.gap) := by
    simpa only [S5_107.simpleBlocks, shape] using
      scan_render whole (first :: rest) nonempty nonsimple simple
  have headSkip : optionalSimpleRun first.gap = [] := by
    simp [optionalSimpleRun, firstEmpty]
  rw [scanned, List.flatMap_cons, headSkip, List.nil_append]
  exact nonempty_gaps_flatMap rest laterNonempty

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.scan_simplePrefix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.scan_nonsimplePrefix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.scan_flush_block
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.scan_gap_block
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.scan_render
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonicalGapScanner

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
