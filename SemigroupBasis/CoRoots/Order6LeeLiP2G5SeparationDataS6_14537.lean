import SemigroupBasis.CoRoots.Order6LeeLiP2G5Injection

/-! Separation data for the G5 member S6_14537 (machine-emitted;
see scripts/order6/emit_lee_li_p2_g5_separation_data.py).
The multiplication table uses the catalogue_op orientation.  Kernel
checks canonicals_eq_expected, fingerprints_eq_expected, and
fingerprints_nodup certify the finite three-generator data. -/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G5.S6_14537Data
open SemigroupBasis

def mulTable : List (List Nat) :=
  [[0, 0, 2, 3, 4, 5],
   [0, 0, 2, 3, 4, 5],
   [2, 2, 2, 3, 4, 5],
   [2, 2, 2, 3, 4, 5],
   [2, 3, 2, 3, 4, 5],
   [5, 5, 2, 3, 4, 5]]

def mul (a b : Nat) : Nat := ((mulTable.getD a []).getD b 0)

def evalWord (v : List Nat) (w : Word Nat) : Nat :=
  w.toList.tail.foldl (fun acc c => mul acc (v.getD c 0)) (v.getD w.head 0)

def canonicals : List (Word Nat) :=
  Injection.canonicalInventory

def expectedCanonicals : List (Word Nat) :=
  [⟨0, []⟩,
   ⟨0, [0]⟩,
   ⟨1, []⟩,
   ⟨1, [1]⟩,
   ⟨2, []⟩,
   ⟨2, [2]⟩,
   ⟨0, [1]⟩,
   ⟨0, [1, 1]⟩,
   ⟨0, [2]⟩,
   ⟨0, [2, 2]⟩,
   ⟨1, [0]⟩,
   ⟨1, [0, 0]⟩,
   ⟨1, [2]⟩,
   ⟨1, [2, 2]⟩,
   ⟨2, [0]⟩,
   ⟨2, [0, 0]⟩,
   ⟨2, [1]⟩,
   ⟨2, [1, 1]⟩,
   ⟨0, [1, 2]⟩,
   ⟨0, [1, 2, 2]⟩,
   ⟨0, [2, 1]⟩,
   ⟨0, [2, 1, 1]⟩,
   ⟨1, [0, 2]⟩,
   ⟨1, [0, 2, 2]⟩,
   ⟨1, [2, 0]⟩,
   ⟨1, [2, 0, 0]⟩,
   ⟨2, [0, 1]⟩,
   ⟨2, [0, 1, 1]⟩,
   ⟨2, [1, 0]⟩,
   ⟨2, [1, 0, 0]⟩]

theorem canonicals_eq_expected : canonicals = expectedCanonicals := by
  decide

def separatorValuations : List (List Nat) :=
  [[1, 1, 4],
   [1, 4, 1],
   [4, 1, 1],
   [0, 2, 5],
   [2, 0, 5],
   [2, 5, 0]]

def fingerprints : List (List Nat) :=
  canonicals.map (fun w => separatorValuations.map (fun v => evalWord v w))

def expectedFingerprints : List (List Nat) :=
  [[1, 1, 4, 0, 2, 2],
   [0, 0, 4, 0, 2, 2],
   [1, 4, 1, 2, 0, 5],
   [0, 4, 0, 2, 0, 5],
   [4, 1, 1, 5, 5, 0],
   [4, 0, 0, 5, 5, 0],
   [0, 4, 3, 2, 2, 5],
   [0, 4, 2, 2, 2, 5],
   [4, 0, 3, 5, 5, 2],
   [4, 0, 2, 5, 5, 2],
   [0, 3, 4, 2, 2, 2],
   [0, 2, 4, 2, 2, 2],
   [4, 3, 0, 5, 5, 5],
   [4, 2, 0, 5, 5, 5],
   [3, 0, 4, 5, 2, 2],
   [2, 0, 4, 5, 2, 2],
   [3, 4, 0, 2, 5, 5],
   [2, 4, 0, 2, 5, 5],
   [4, 3, 2, 5, 5, 5],
   [4, 2, 2, 5, 5, 5],
   [3, 4, 2, 2, 5, 5],
   [2, 4, 2, 2, 5, 5],
   [4, 2, 3, 5, 5, 2],
   [4, 2, 2, 5, 5, 2],
   [3, 2, 4, 5, 2, 2],
   [2, 2, 4, 5, 2, 2],
   [2, 4, 3, 2, 2, 5],
   [2, 4, 2, 2, 2, 5],
   [2, 3, 4, 2, 2, 2],
   [2, 2, 4, 2, 2, 2]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fingerprints_eq_expected : fingerprints = expectedFingerprints := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fingerprints_nodup : fingerprints.Nodup := by
  rw [fingerprints_eq_expected]
  decide

end SemigroupBasis.CoRoots.Order6LeeLiP2G5.S6_14537Data
