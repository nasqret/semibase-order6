import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4

open SemigroupBasis

/-!
# Lee--Zhang Proposition 20.7 / E4: exact syntax

This module freezes the direct 64-law ordinary expansion of the six
schematic identities (20.6a)--(20.6f).  The list order and orientation are
the exact sorted validation/source order used by the accepted S6_5661 route.
No completeness assertion is made here.
-/

/-! ## Frozen source provenance -/

def sourceRecordPath : String :=
  "l6d-work/s6_5661-route/source/" ++
    "published_sporadic_bases_sections16_27.json"

def sourceRecordSHA256 : String :=
  "315a2fa6fafd49335bba700ef24d16fa67f5c7a669e4f4fc26f95d4a7404cf88"

def primaryPDFSHA256 : String :=
  "4a9ea094f872738a6d935a63550416e426260dc81d59c1f6c87b8d76c4db641f"

def publishedBasisRecordSemanticSHA256 : String :=
  "395ef26d3c08cd07b1cc4a391790ee09d0066be9cec2378d79f9231a8578f874"

def directBasisSemanticSHA256 : String :=
  "f9b8ebf91de07549be634b39b6af0aebc76ba4774fa11561dbca3a4e390285aa"

def sourceDOI : String := "10.1112/S1461157014000412"
def sourceProposition : String := "20.7"
def publishedLabel : String := "E4"

/-! ## Literal expanded laws -/

/-- The nonempty word with the displayed head and tail. -/
def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-!
The shared finite coding is
`x = 0`, `y = 1`, `h = 2`, `k = a = 3`, `t = b = 4`,
`c = 5`, `z = 6`, and `d = 7`.

The aliases occur in disjoint schematic families: `k,t` occur only in
(20.6a)--(20.6e), whereas `a,b,c,d` occur only in (20.6f).  Thus no literal
expanded law identifies distinct displayed variables, and every law uses at
most the eight values `0,...,7`.
-/

/-- Frozen validation law 1: `xhxaybyczdz = xhxczdzayby`. -/
def law20_6f_HABCD : Identity Nat :=
  ⟨w 0 [2, 0, 3, 1, 4, 1, 5, 6, 7, 6],
    w 0 [2, 0, 5, 6, 7, 6, 3, 1, 4, 1]⟩

/-- Frozen validation law 2: `xhxaybyczz = xhxczzayby`. -/
def law20_6f_HABC : Identity Nat :=
  ⟨w 0 [2, 0, 3, 1, 4, 1, 5, 6, 6],
    w 0 [2, 0, 5, 6, 6, 3, 1, 4, 1]⟩

/-- Frozen validation law 3: `xhxaybyzdz = xhxzdzayby`. -/
def law20_6f_HABD : Identity Nat :=
  ⟨w 0 [2, 0, 3, 1, 4, 1, 6, 7, 6],
    w 0 [2, 0, 6, 7, 6, 3, 1, 4, 1]⟩

/-- Frozen validation law 4: `xhxaybyzz = xhxzzayby`. -/
def law20_6f_HAB : Identity Nat :=
  ⟨w 0 [2, 0, 3, 1, 4, 1, 6, 6],
    w 0 [2, 0, 6, 6, 3, 1, 4, 1]⟩

/-- Frozen validation law 5: `xhxayyczdz = xhxczdzayy`. -/
def law20_6f_HACD : Identity Nat :=
  ⟨w 0 [2, 0, 3, 1, 1, 5, 6, 7, 6],
    w 0 [2, 0, 5, 6, 7, 6, 3, 1, 1]⟩

/-- Frozen validation law 6: `xhxayyczz = xhxczzayy`. -/
def law20_6f_HAC : Identity Nat :=
  ⟨w 0 [2, 0, 3, 1, 1, 5, 6, 6],
    w 0 [2, 0, 5, 6, 6, 3, 1, 1]⟩

/-- Frozen validation law 7: `xhxayyzdz = xhxzdzayy`. -/
def law20_6f_HAD : Identity Nat :=
  ⟨w 0 [2, 0, 3, 1, 1, 6, 7, 6],
    w 0 [2, 0, 6, 7, 6, 3, 1, 1]⟩

/-- Frozen validation law 8: `xhxayyzz = xhxzzayy`. -/
def law20_6f_HA : Identity Nat :=
  ⟨w 0 [2, 0, 3, 1, 1, 6, 6],
    w 0 [2, 0, 6, 6, 3, 1, 1]⟩

/-- Frozen validation law 9: `xhxkx = xkxhx`. -/
def law20_6b_HK : Identity Nat :=
  ⟨w 0 [2, 0, 3, 0], w 0 [3, 0, 2, 0]⟩

/-- Frozen validation law 10: `xhxkxx = xhxkx`. -/
def law20_6a_HK : Identity Nat :=
  ⟨w 0 [2, 0, 3, 0, 0], w 0 [2, 0, 3, 0]⟩

/-- Frozen validation law 11: `xhxkyty = xhxtyky`. -/
def law20_6c_HKT : Identity Nat :=
  ⟨w 0 [2, 0, 3, 1, 4, 1], w 0 [2, 0, 4, 1, 3, 1]⟩

/-- Frozen validation law 12: `xhxkyy = xhxyky`. -/
def law20_6c_HK : Identity Nat :=
  ⟨w 0 [2, 0, 3, 1, 1], w 0 [2, 0, 1, 3, 1]⟩

/-- Frozen validation law 13: `xhxx = xxhx`. -/
def law20_6b_H : Identity Nat :=
  ⟨w 0 [2, 0, 0], w 0 [0, 2, 0]⟩

/-- Frozen validation law 14: `xhxxx = xhxx`. -/
def law20_6a_H : Identity Nat :=
  ⟨w 0 [2, 0, 0, 0], w 0 [2, 0, 0]⟩

/-- Frozen validation law 15: `xhxybyczdz = xhxczdzyby`. -/
def law20_6f_HBCD : Identity Nat :=
  ⟨w 0 [2, 0, 1, 4, 1, 5, 6, 7, 6],
    w 0 [2, 0, 5, 6, 7, 6, 1, 4, 1]⟩

/-- Frozen validation law 16: `xhxybyczz = xhxczzyby`. -/
def law20_6f_HBC : Identity Nat :=
  ⟨w 0 [2, 0, 1, 4, 1, 5, 6, 6],
    w 0 [2, 0, 5, 6, 6, 1, 4, 1]⟩

/-- Frozen validation law 17: `xhxybyzdz = xhxzdzyby`. -/
def law20_6f_HBD : Identity Nat :=
  ⟨w 0 [2, 0, 1, 4, 1, 6, 7, 6],
    w 0 [2, 0, 6, 7, 6, 1, 4, 1]⟩

/-- Frozen validation law 18: `xhxybyzz = xhxzzyby`. -/
def law20_6f_HB : Identity Nat :=
  ⟨w 0 [2, 0, 1, 4, 1, 6, 6],
    w 0 [2, 0, 6, 6, 1, 4, 1]⟩

/-- Frozen validation law 19: `xhxyty = xhxtyy`. -/
def law20_6c_HT : Identity Nat :=
  ⟨w 0 [2, 0, 1, 4, 1], w 0 [2, 0, 4, 1, 1]⟩

/-- Frozen validation law 20: `xhxyy = xhxyy`. -/
def law20_6c_H : Identity Nat :=
  ⟨w 0 [2, 0, 1, 1], w 0 [2, 0, 1, 1]⟩

/-- Frozen validation law 21: `xhxyyczdz = xhxczdzyy`. -/
def law20_6f_HCD : Identity Nat :=
  ⟨w 0 [2, 0, 1, 1, 5, 6, 7, 6],
    w 0 [2, 0, 5, 6, 7, 6, 1, 1]⟩

/-- Frozen validation law 22: `xhxyyczz = xhxczzyy`. -/
def law20_6f_HC : Identity Nat :=
  ⟨w 0 [2, 0, 1, 1, 5, 6, 6],
    w 0 [2, 0, 5, 6, 6, 1, 1]⟩

/-- Frozen validation law 23: `xhxyyzdz = xhxzdzyy`. -/
def law20_6f_HD : Identity Nat :=
  ⟨w 0 [2, 0, 1, 1, 6, 7, 6],
    w 0 [2, 0, 6, 7, 6, 1, 1]⟩

/-- Frozen validation law 24: `xhxyyzz = xhxzzyy`. -/
def law20_6f_H : Identity Nat :=
  ⟨w 0 [2, 0, 1, 1, 6, 6], w 0 [2, 0, 6, 6, 1, 1]⟩

/-- Frozen validation law 25: `xhykxty = xkxhyty`. -/
def law20_6d_HKT : Identity Nat :=
  ⟨w 0 [2, 1, 3, 0, 4, 1], w 0 [3, 0, 2, 1, 4, 1]⟩

/-- Frozen validation law 26: `xhykxy = xkxhyy`. -/
def law20_6d_HK : Identity Nat :=
  ⟨w 0 [2, 1, 3, 0, 1], w 0 [3, 0, 2, 1, 1]⟩

/-- Frozen validation law 27: `xhykytx = xtxhyky`. -/
def law20_6e_HKT : Identity Nat :=
  ⟨w 0 [2, 1, 3, 1, 4, 0], w 0 [4, 0, 2, 1, 3, 1]⟩

/-- Frozen validation law 28: `xhykyx = xxhyky`. -/
def law20_6e_HK : Identity Nat :=
  ⟨w 0 [2, 1, 3, 1, 0], w 0 [0, 2, 1, 3, 1]⟩

/-- Frozen validation law 29: `xhyxty = xxhyty`. -/
def law20_6d_HT : Identity Nat :=
  ⟨w 0 [2, 1, 0, 4, 1], w 0 [0, 2, 1, 4, 1]⟩

/-- Frozen validation law 30: `xhyxy = xxhyy`. -/
def law20_6d_H : Identity Nat :=
  ⟨w 0 [2, 1, 0, 1], w 0 [0, 2, 1, 1]⟩

/-- Frozen validation law 31: `xhyytx = xtxhyy`. -/
def law20_6e_HT : Identity Nat :=
  ⟨w 0 [2, 1, 1, 4, 0], w 0 [4, 0, 2, 1, 1]⟩

/-- Frozen validation law 32: `xhyyx = xxhyy`. -/
def law20_6e_H : Identity Nat :=
  ⟨w 0 [2, 1, 1, 0], w 0 [0, 2, 1, 1]⟩

/-- Frozen validation law 33: `xxaybyczdz = xxczdzayby`. -/
def law20_6f_ABCD : Identity Nat :=
  ⟨w 0 [0, 3, 1, 4, 1, 5, 6, 7, 6],
    w 0 [0, 5, 6, 7, 6, 3, 1, 4, 1]⟩

/-- Frozen validation law 34: `xxaybyczz = xxczzayby`. -/
def law20_6f_ABC : Identity Nat :=
  ⟨w 0 [0, 3, 1, 4, 1, 5, 6, 6],
    w 0 [0, 5, 6, 6, 3, 1, 4, 1]⟩

/-- Frozen validation law 35: `xxaybyzdz = xxzdzayby`. -/
def law20_6f_ABD : Identity Nat :=
  ⟨w 0 [0, 3, 1, 4, 1, 6, 7, 6],
    w 0 [0, 6, 7, 6, 3, 1, 4, 1]⟩

/-- Frozen validation law 36: `xxaybyzz = xxzzayby`. -/
def law20_6f_AB : Identity Nat :=
  ⟨w 0 [0, 3, 1, 4, 1, 6, 6],
    w 0 [0, 6, 6, 3, 1, 4, 1]⟩

/-- Frozen validation law 37: `xxayyczdz = xxczdzayy`. -/
def law20_6f_ACD : Identity Nat :=
  ⟨w 0 [0, 3, 1, 1, 5, 6, 7, 6],
    w 0 [0, 5, 6, 7, 6, 3, 1, 1]⟩

/-- Frozen validation law 38: `xxayyczz = xxczzayy`. -/
def law20_6f_AC : Identity Nat :=
  ⟨w 0 [0, 3, 1, 1, 5, 6, 6],
    w 0 [0, 5, 6, 6, 3, 1, 1]⟩

/-- Frozen validation law 39: `xxayyzdz = xxzdzayy`. -/
def law20_6f_AD : Identity Nat :=
  ⟨w 0 [0, 3, 1, 1, 6, 7, 6],
    w 0 [0, 6, 7, 6, 3, 1, 1]⟩

/-- Frozen validation law 40: `xxayyzz = xxzzayy`. -/
def law20_6f_A : Identity Nat :=
  ⟨w 0 [0, 3, 1, 1, 6, 6], w 0 [0, 6, 6, 3, 1, 1]⟩

/-- Frozen validation law 41: `xxkx = xkxx`. -/
def law20_6b_K : Identity Nat :=
  ⟨w 0 [0, 3, 0], w 0 [3, 0, 0]⟩

/-- Frozen validation law 42: `xxkxx = xxkx`. -/
def law20_6a_K : Identity Nat :=
  ⟨w 0 [0, 3, 0, 0], w 0 [0, 3, 0]⟩

/-- Frozen validation law 43: `xxkyty = xxtyky`. -/
def law20_6c_KT : Identity Nat :=
  ⟨w 0 [0, 3, 1, 4, 1], w 0 [0, 4, 1, 3, 1]⟩

/-- Frozen validation law 44: `xxkyy = xxyky`. -/
def law20_6c_K : Identity Nat :=
  ⟨w 0 [0, 3, 1, 1], w 0 [0, 1, 3, 1]⟩

/-- Frozen validation law 45: `xxx = xxx`. -/
def law20_6b_empty : Identity Nat :=
  ⟨w 0 [0, 0], w 0 [0, 0]⟩

/-- Frozen validation law 46: `xxxx = xxx`. -/
def law20_6a_empty : Identity Nat :=
  ⟨w 0 [0, 0, 0], w 0 [0, 0]⟩

/-- Frozen validation law 47: `xxybyczdz = xxczdzyby`. -/
def law20_6f_BCD : Identity Nat :=
  ⟨w 0 [0, 1, 4, 1, 5, 6, 7, 6],
    w 0 [0, 5, 6, 7, 6, 1, 4, 1]⟩

/-- Frozen validation law 48: `xxybyczz = xxczzyby`. -/
def law20_6f_BC : Identity Nat :=
  ⟨w 0 [0, 1, 4, 1, 5, 6, 6],
    w 0 [0, 5, 6, 6, 1, 4, 1]⟩

/-- Frozen validation law 49: `xxybyzdz = xxzdzyby`. -/
def law20_6f_BD : Identity Nat :=
  ⟨w 0 [0, 1, 4, 1, 6, 7, 6],
    w 0 [0, 6, 7, 6, 1, 4, 1]⟩

/-- Frozen validation law 50: `xxybyzz = xxzzyby`. -/
def law20_6f_B : Identity Nat :=
  ⟨w 0 [0, 1, 4, 1, 6, 6], w 0 [0, 6, 6, 1, 4, 1]⟩

/-- Frozen validation law 51: `xxyty = xxtyy`. -/
def law20_6c_T : Identity Nat :=
  ⟨w 0 [0, 1, 4, 1], w 0 [0, 4, 1, 1]⟩

/-- Frozen validation law 52: `xxyy = xxyy`. -/
def law20_6c_empty : Identity Nat :=
  ⟨w 0 [0, 1, 1], w 0 [0, 1, 1]⟩

/-- Frozen validation law 53: `xxyyczdz = xxczdzyy`. -/
def law20_6f_CD : Identity Nat :=
  ⟨w 0 [0, 1, 1, 5, 6, 7, 6], w 0 [0, 5, 6, 7, 6, 1, 1]⟩

/-- Frozen validation law 54: `xxyyczz = xxczzyy`. -/
def law20_6f_C : Identity Nat :=
  ⟨w 0 [0, 1, 1, 5, 6, 6], w 0 [0, 5, 6, 6, 1, 1]⟩

/-- Frozen validation law 55: `xxyyzdz = xxzdzyy`. -/
def law20_6f_D : Identity Nat :=
  ⟨w 0 [0, 1, 1, 6, 7, 6], w 0 [0, 6, 7, 6, 1, 1]⟩

/-- Frozen validation law 56: `xxyyzz = xxzzyy`. -/
def law20_6f_empty : Identity Nat :=
  ⟨w 0 [0, 1, 1, 6, 6], w 0 [0, 6, 6, 1, 1]⟩

/-- Frozen validation law 57: `xykxty = xkxyty`. -/
def law20_6d_KT : Identity Nat :=
  ⟨w 0 [1, 3, 0, 4, 1], w 0 [3, 0, 1, 4, 1]⟩

/-- Frozen validation law 58: `xykxy = xkxyy`. -/
def law20_6d_K : Identity Nat :=
  ⟨w 0 [1, 3, 0, 1], w 0 [3, 0, 1, 1]⟩

/-- Frozen validation law 59: `xykytx = xtxyky`. -/
def law20_6e_KT : Identity Nat :=
  ⟨w 0 [1, 3, 1, 4, 0], w 0 [4, 0, 1, 3, 1]⟩

/-- Frozen validation law 60: `xykyx = xxyky`. -/
def law20_6e_K : Identity Nat :=
  ⟨w 0 [1, 3, 1, 0], w 0 [0, 1, 3, 1]⟩

/-- Frozen validation law 61: `xyxty = xxyty`. -/
def law20_6d_T : Identity Nat :=
  ⟨w 0 [1, 0, 4, 1], w 0 [0, 1, 4, 1]⟩

/-- Frozen validation law 62: `xyxy = xxyy`. -/
def law20_6d_empty : Identity Nat :=
  ⟨w 0 [1, 0, 1], w 0 [0, 1, 1]⟩

/-- Frozen validation law 63: `xyytx = xtxyy`. -/
def law20_6e_T : Identity Nat :=
  ⟨w 0 [1, 1, 4, 0], w 0 [4, 0, 1, 1]⟩

/-- Frozen validation law 64: `xyyx = xxyy`. -/
def law20_6e_empty : Identity Nat :=
  ⟨w 0 [1, 1, 0], w 0 [0, 1, 1]⟩

/-- The exact direct Proposition 20.7/E4 expansion in frozen validation order
and orientation. -/
def basis : List (Identity Nat) :=
  [law20_6f_HABCD, law20_6f_HABC, law20_6f_HABD, law20_6f_HAB,
    law20_6f_HACD, law20_6f_HAC, law20_6f_HAD, law20_6f_HA,
    law20_6b_HK, law20_6a_HK, law20_6c_HKT, law20_6c_HK,
    law20_6b_H, law20_6a_H, law20_6f_HBCD, law20_6f_HBC,
    law20_6f_HBD, law20_6f_HB, law20_6c_HT, law20_6c_H,
    law20_6f_HCD, law20_6f_HC, law20_6f_HD, law20_6f_H,
    law20_6d_HKT, law20_6d_HK, law20_6e_HKT, law20_6e_HK,
    law20_6d_HT, law20_6d_H, law20_6e_HT, law20_6e_H,
    law20_6f_ABCD, law20_6f_ABC, law20_6f_ABD, law20_6f_AB,
    law20_6f_ACD, law20_6f_AC, law20_6f_AD, law20_6f_A,
    law20_6b_K, law20_6a_K, law20_6c_KT, law20_6c_K,
    law20_6b_empty, law20_6a_empty, law20_6f_BCD, law20_6f_BC,
    law20_6f_BD, law20_6f_B, law20_6c_T, law20_6c_empty,
    law20_6f_CD, law20_6f_C, law20_6f_D, law20_6f_empty,
    law20_6d_KT, law20_6d_K, law20_6e_KT, law20_6e_K,
    law20_6d_T, law20_6d_empty, law20_6e_T, law20_6e_empty]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

/-! ## Public primitive derivation interface -/

/-- Any literal member of the frozen expansion is available directly. -/
theorem derives_of_basis_member
    (identity : Identity Nat) (member : identity ∈ basis) :
    Derives basis identity.lhs identity.rhs :=
  Derives.fromBasis (e := identity) member

/-! ## Eight-variable finite reflection -/

/-- Exact finite coding for all eight variable slots used by (20.6f).
Natural codes outside the frozen basis are sent to the final slot. -/
def toFinEight : Nat → Fin 8
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 7

def finiteBasis : List (Identity (Fin 8)) :=
  basis.map fun identity => identity.map toFinEight

theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinEight).map Fin.val = identity)) = true := by
  decide

theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinEight).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- A single fused certificate for a literal member of the frozen basis is
sound for the corresponding natural-variable identity. -/
theorem satisfied_of_fused_check
    (candidate : FiniteTable) (identity : Identity Nat)
    (member : identity ∈ basis)
    (checked :
      candidate.checkIdentityFused (identity.map toFinEight) = true) :
    identity.SatisfiedBy candidate.semigroup := by
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound
      (identity.map toFinEight) checked
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

/-! ## Consecutive memory-bounded shards -/

def basisShard01 : List (Identity Nat) :=
  [law20_6f_HABCD, law20_6f_HABC, law20_6f_HABD, law20_6f_HAB,
    law20_6f_HACD, law20_6f_HAC, law20_6f_HAD, law20_6f_HA]

def basisShard02 : List (Identity Nat) :=
  [law20_6b_HK, law20_6a_HK, law20_6c_HKT, law20_6c_HK,
    law20_6b_H, law20_6a_H, law20_6f_HBCD, law20_6f_HBC]

def basisShard03 : List (Identity Nat) :=
  [law20_6f_HBD, law20_6f_HB, law20_6c_HT, law20_6c_H,
    law20_6f_HCD, law20_6f_HC, law20_6f_HD, law20_6f_H]

def basisShard04 : List (Identity Nat) :=
  [law20_6d_HKT, law20_6d_HK, law20_6e_HKT, law20_6e_HK,
    law20_6d_HT, law20_6d_H, law20_6e_HT, law20_6e_H]

def basisShard05 : List (Identity Nat) :=
  [law20_6f_ABCD, law20_6f_ABC, law20_6f_ABD, law20_6f_AB,
    law20_6f_ACD, law20_6f_AC, law20_6f_AD, law20_6f_A]

def basisShard06 : List (Identity Nat) :=
  [law20_6b_K, law20_6a_K, law20_6c_KT, law20_6c_K,
    law20_6b_empty, law20_6a_empty, law20_6f_BCD, law20_6f_BC]

def basisShard07 : List (Identity Nat) :=
  [law20_6f_BD, law20_6f_B, law20_6c_T, law20_6c_empty,
    law20_6f_CD, law20_6f_C, law20_6f_D, law20_6f_empty]

def basisShard08 : List (Identity Nat) :=
  [law20_6d_KT, law20_6d_K, law20_6e_KT, law20_6e_K,
    law20_6d_T, law20_6d_empty, law20_6e_T, law20_6e_empty]

def finiteBasisShard01 : List (Identity (Fin 8)) :=
  basisShard01.map fun identity => identity.map toFinEight

def finiteBasisShard02 : List (Identity (Fin 8)) :=
  basisShard02.map fun identity => identity.map toFinEight

def finiteBasisShard03 : List (Identity (Fin 8)) :=
  basisShard03.map fun identity => identity.map toFinEight

def finiteBasisShard04 : List (Identity (Fin 8)) :=
  basisShard04.map fun identity => identity.map toFinEight

def finiteBasisShard05 : List (Identity (Fin 8)) :=
  basisShard05.map fun identity => identity.map toFinEight

def finiteBasisShard06 : List (Identity (Fin 8)) :=
  basisShard06.map fun identity => identity.map toFinEight

def finiteBasisShard07 : List (Identity (Fin 8)) :=
  basisShard07.map fun identity => identity.map toFinEight

def finiteBasisShard08 : List (Identity (Fin 8)) :=
  basisShard08.map fun identity => identity.map toFinEight

theorem basis_eq_shards :
    basis =
      basisShard01 ++ basisShard02 ++ basisShard03 ++ basisShard04 ++
      basisShard05 ++ basisShard06 ++ basisShard07 ++ basisShard08 := by
  rfl

private theorem satisfied_of_fused_shard_checks
    (candidate : FiniteTable) (shard : List (Identity Nat))
    (identity : Identity Nat) (basisMember : identity ∈ basis)
    (shardMember : identity ∈ shard)
    (checked :
      (shard.map fun law => law.map toFinEight).all
        candidate.checkIdentityFused = true) :
    identity.SatisfiedBy candidate.semigroup := by
  have finiteMember :
      identity.map toFinEight ∈
        shard.map (fun law => law.map toFinEight) :=
    List.mem_map.mpr ⟨identity, shardMember, rfl⟩
  exact satisfied_of_fused_check candidate identity basisMember <|
    (List.all_eq_true.mp checked) _ finiteMember

/-- Eight fused shard certificates imply exact soundness of all 64 literal
laws while avoiding a single monolithic basis decision term. -/
theorem models_of_sharded_fused_checks
    (candidate : FiniteTable)
    (checkShard01 :
      finiteBasisShard01.all candidate.checkIdentityFused = true)
    (checkShard02 :
      finiteBasisShard02.all candidate.checkIdentityFused = true)
    (checkShard03 :
      finiteBasisShard03.all candidate.checkIdentityFused = true)
    (checkShard04 :
      finiteBasisShard04.all candidate.checkIdentityFused = true)
    (checkShard05 :
      finiteBasisShard05.all candidate.checkIdentityFused = true)
    (checkShard06 :
      finiteBasisShard06.all candidate.checkIdentityFused = true)
    (checkShard07 :
      finiteBasisShard07.all candidate.checkIdentityFused = true)
    (checkShard08 :
      finiteBasisShard08.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have basisMember : identity ∈ basis := member
  rw [basis_eq_shards] at member
  have shardMember :
      identity ∈ basisShard01 ∨ identity ∈ basisShard02 ∨
      identity ∈ basisShard03 ∨ identity ∈ basisShard04 ∨
      identity ∈ basisShard05 ∨ identity ∈ basisShard06 ∨
      identity ∈ basisShard07 ∨ identity ∈ basisShard08 := by
    simpa only [List.mem_append, or_assoc] using member
  rcases shardMember with inShard01 | inShard02 | inShard03 | inShard04 |
    inShard05 | inShard06 | inShard07 | inShard08
  · exact satisfied_of_fused_shard_checks candidate basisShard01 identity
      basisMember inShard01 (by simpa [finiteBasisShard01] using checkShard01)
  · exact satisfied_of_fused_shard_checks candidate basisShard02 identity
      basisMember inShard02 (by simpa [finiteBasisShard02] using checkShard02)
  · exact satisfied_of_fused_shard_checks candidate basisShard03 identity
      basisMember inShard03 (by simpa [finiteBasisShard03] using checkShard03)
  · exact satisfied_of_fused_shard_checks candidate basisShard04 identity
      basisMember inShard04 (by simpa [finiteBasisShard04] using checkShard04)
  · exact satisfied_of_fused_shard_checks candidate basisShard05 identity
      basisMember inShard05 (by simpa [finiteBasisShard05] using checkShard05)
  · exact satisfied_of_fused_shard_checks candidate basisShard06 identity
      basisMember inShard06 (by simpa [finiteBasisShard06] using checkShard06)
  · exact satisfied_of_fused_shard_checks candidate basisShard07 identity
      basisMember inShard07 (by simpa [finiteBasisShard07] using checkShard07)
  · exact satisfied_of_fused_shard_checks candidate basisShard08 identity
      basisMember inShard08 (by simpa [finiteBasisShard08] using checkShard08)


/-! ## Fully individual fused-check interface -/

/-- Section-27-style target soundness interface with one proof term per
literal expanded law.  This is the lowest-memory fallback when even an
eight-law shard is too large for a target checker. -/
theorem models_of_individual_fused_checks
    (candidate : FiniteTable)
    (check20_6f_HABCD :
      candidate.checkIdentityFused (law20_6f_HABCD.map toFinEight) = true)
    (check20_6f_HABC :
      candidate.checkIdentityFused (law20_6f_HABC.map toFinEight) = true)
    (check20_6f_HABD :
      candidate.checkIdentityFused (law20_6f_HABD.map toFinEight) = true)
    (check20_6f_HAB :
      candidate.checkIdentityFused (law20_6f_HAB.map toFinEight) = true)
    (check20_6f_HACD :
      candidate.checkIdentityFused (law20_6f_HACD.map toFinEight) = true)
    (check20_6f_HAC :
      candidate.checkIdentityFused (law20_6f_HAC.map toFinEight) = true)
    (check20_6f_HAD :
      candidate.checkIdentityFused (law20_6f_HAD.map toFinEight) = true)
    (check20_6f_HA :
      candidate.checkIdentityFused (law20_6f_HA.map toFinEight) = true)
    (check20_6b_HK :
      candidate.checkIdentityFused (law20_6b_HK.map toFinEight) = true)
    (check20_6a_HK :
      candidate.checkIdentityFused (law20_6a_HK.map toFinEight) = true)
    (check20_6c_HKT :
      candidate.checkIdentityFused (law20_6c_HKT.map toFinEight) = true)
    (check20_6c_HK :
      candidate.checkIdentityFused (law20_6c_HK.map toFinEight) = true)
    (check20_6b_H :
      candidate.checkIdentityFused (law20_6b_H.map toFinEight) = true)
    (check20_6a_H :
      candidate.checkIdentityFused (law20_6a_H.map toFinEight) = true)
    (check20_6f_HBCD :
      candidate.checkIdentityFused (law20_6f_HBCD.map toFinEight) = true)
    (check20_6f_HBC :
      candidate.checkIdentityFused (law20_6f_HBC.map toFinEight) = true)
    (check20_6f_HBD :
      candidate.checkIdentityFused (law20_6f_HBD.map toFinEight) = true)
    (check20_6f_HB :
      candidate.checkIdentityFused (law20_6f_HB.map toFinEight) = true)
    (check20_6c_HT :
      candidate.checkIdentityFused (law20_6c_HT.map toFinEight) = true)
    (check20_6c_H :
      candidate.checkIdentityFused (law20_6c_H.map toFinEight) = true)
    (check20_6f_HCD :
      candidate.checkIdentityFused (law20_6f_HCD.map toFinEight) = true)
    (check20_6f_HC :
      candidate.checkIdentityFused (law20_6f_HC.map toFinEight) = true)
    (check20_6f_HD :
      candidate.checkIdentityFused (law20_6f_HD.map toFinEight) = true)
    (check20_6f_H :
      candidate.checkIdentityFused (law20_6f_H.map toFinEight) = true)
    (check20_6d_HKT :
      candidate.checkIdentityFused (law20_6d_HKT.map toFinEight) = true)
    (check20_6d_HK :
      candidate.checkIdentityFused (law20_6d_HK.map toFinEight) = true)
    (check20_6e_HKT :
      candidate.checkIdentityFused (law20_6e_HKT.map toFinEight) = true)
    (check20_6e_HK :
      candidate.checkIdentityFused (law20_6e_HK.map toFinEight) = true)
    (check20_6d_HT :
      candidate.checkIdentityFused (law20_6d_HT.map toFinEight) = true)
    (check20_6d_H :
      candidate.checkIdentityFused (law20_6d_H.map toFinEight) = true)
    (check20_6e_HT :
      candidate.checkIdentityFused (law20_6e_HT.map toFinEight) = true)
    (check20_6e_H :
      candidate.checkIdentityFused (law20_6e_H.map toFinEight) = true)
    (check20_6f_ABCD :
      candidate.checkIdentityFused (law20_6f_ABCD.map toFinEight) = true)
    (check20_6f_ABC :
      candidate.checkIdentityFused (law20_6f_ABC.map toFinEight) = true)
    (check20_6f_ABD :
      candidate.checkIdentityFused (law20_6f_ABD.map toFinEight) = true)
    (check20_6f_AB :
      candidate.checkIdentityFused (law20_6f_AB.map toFinEight) = true)
    (check20_6f_ACD :
      candidate.checkIdentityFused (law20_6f_ACD.map toFinEight) = true)
    (check20_6f_AC :
      candidate.checkIdentityFused (law20_6f_AC.map toFinEight) = true)
    (check20_6f_AD :
      candidate.checkIdentityFused (law20_6f_AD.map toFinEight) = true)
    (check20_6f_A :
      candidate.checkIdentityFused (law20_6f_A.map toFinEight) = true)
    (check20_6b_K :
      candidate.checkIdentityFused (law20_6b_K.map toFinEight) = true)
    (check20_6a_K :
      candidate.checkIdentityFused (law20_6a_K.map toFinEight) = true)
    (check20_6c_KT :
      candidate.checkIdentityFused (law20_6c_KT.map toFinEight) = true)
    (check20_6c_K :
      candidate.checkIdentityFused (law20_6c_K.map toFinEight) = true)
    (check20_6b_empty :
      candidate.checkIdentityFused (law20_6b_empty.map toFinEight) = true)
    (check20_6a_empty :
      candidate.checkIdentityFused (law20_6a_empty.map toFinEight) = true)
    (check20_6f_BCD :
      candidate.checkIdentityFused (law20_6f_BCD.map toFinEight) = true)
    (check20_6f_BC :
      candidate.checkIdentityFused (law20_6f_BC.map toFinEight) = true)
    (check20_6f_BD :
      candidate.checkIdentityFused (law20_6f_BD.map toFinEight) = true)
    (check20_6f_B :
      candidate.checkIdentityFused (law20_6f_B.map toFinEight) = true)
    (check20_6c_T :
      candidate.checkIdentityFused (law20_6c_T.map toFinEight) = true)
    (check20_6c_empty :
      candidate.checkIdentityFused (law20_6c_empty.map toFinEight) = true)
    (check20_6f_CD :
      candidate.checkIdentityFused (law20_6f_CD.map toFinEight) = true)
    (check20_6f_C :
      candidate.checkIdentityFused (law20_6f_C.map toFinEight) = true)
    (check20_6f_D :
      candidate.checkIdentityFused (law20_6f_D.map toFinEight) = true)
    (check20_6f_empty :
      candidate.checkIdentityFused (law20_6f_empty.map toFinEight) = true)
    (check20_6d_KT :
      candidate.checkIdentityFused (law20_6d_KT.map toFinEight) = true)
    (check20_6d_K :
      candidate.checkIdentityFused (law20_6d_K.map toFinEight) = true)
    (check20_6e_KT :
      candidate.checkIdentityFused (law20_6e_KT.map toFinEight) = true)
    (check20_6e_K :
      candidate.checkIdentityFused (law20_6e_K.map toFinEight) = true)
    (check20_6d_T :
      candidate.checkIdentityFused (law20_6d_T.map toFinEight) = true)
    (check20_6d_empty :
      candidate.checkIdentityFused (law20_6d_empty.map toFinEight) = true)
    (check20_6e_T :
      candidate.checkIdentityFused (law20_6e_T.map toFinEight) = true)
    (check20_6e_empty :
      candidate.checkIdentityFused (law20_6e_empty.map toFinEight) = true)
    : Models candidate.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact satisfied_of_fused_check candidate law20_6f_HABCD
      (by simp [basis]) check20_6f_HABCD
  · exact satisfied_of_fused_check candidate law20_6f_HABC
      (by simp [basis]) check20_6f_HABC
  · exact satisfied_of_fused_check candidate law20_6f_HABD
      (by simp [basis]) check20_6f_HABD
  · exact satisfied_of_fused_check candidate law20_6f_HAB
      (by simp [basis]) check20_6f_HAB
  · exact satisfied_of_fused_check candidate law20_6f_HACD
      (by simp [basis]) check20_6f_HACD
  · exact satisfied_of_fused_check candidate law20_6f_HAC
      (by simp [basis]) check20_6f_HAC
  · exact satisfied_of_fused_check candidate law20_6f_HAD
      (by simp [basis]) check20_6f_HAD
  · exact satisfied_of_fused_check candidate law20_6f_HA
      (by simp [basis]) check20_6f_HA
  · exact satisfied_of_fused_check candidate law20_6b_HK
      (by simp [basis]) check20_6b_HK
  · exact satisfied_of_fused_check candidate law20_6a_HK
      (by simp [basis]) check20_6a_HK
  · exact satisfied_of_fused_check candidate law20_6c_HKT
      (by simp [basis]) check20_6c_HKT
  · exact satisfied_of_fused_check candidate law20_6c_HK
      (by simp [basis]) check20_6c_HK
  · exact satisfied_of_fused_check candidate law20_6b_H
      (by simp [basis]) check20_6b_H
  · exact satisfied_of_fused_check candidate law20_6a_H
      (by simp [basis]) check20_6a_H
  · exact satisfied_of_fused_check candidate law20_6f_HBCD
      (by simp [basis]) check20_6f_HBCD
  · exact satisfied_of_fused_check candidate law20_6f_HBC
      (by simp [basis]) check20_6f_HBC
  · exact satisfied_of_fused_check candidate law20_6f_HBD
      (by simp [basis]) check20_6f_HBD
  · exact satisfied_of_fused_check candidate law20_6f_HB
      (by simp [basis]) check20_6f_HB
  · exact satisfied_of_fused_check candidate law20_6c_HT
      (by simp [basis]) check20_6c_HT
  · exact satisfied_of_fused_check candidate law20_6c_H
      (by simp [basis]) check20_6c_H
  · exact satisfied_of_fused_check candidate law20_6f_HCD
      (by simp [basis]) check20_6f_HCD
  · exact satisfied_of_fused_check candidate law20_6f_HC
      (by simp [basis]) check20_6f_HC
  · exact satisfied_of_fused_check candidate law20_6f_HD
      (by simp [basis]) check20_6f_HD
  · exact satisfied_of_fused_check candidate law20_6f_H
      (by simp [basis]) check20_6f_H
  · exact satisfied_of_fused_check candidate law20_6d_HKT
      (by simp [basis]) check20_6d_HKT
  · exact satisfied_of_fused_check candidate law20_6d_HK
      (by simp [basis]) check20_6d_HK
  · exact satisfied_of_fused_check candidate law20_6e_HKT
      (by simp [basis]) check20_6e_HKT
  · exact satisfied_of_fused_check candidate law20_6e_HK
      (by simp [basis]) check20_6e_HK
  · exact satisfied_of_fused_check candidate law20_6d_HT
      (by simp [basis]) check20_6d_HT
  · exact satisfied_of_fused_check candidate law20_6d_H
      (by simp [basis]) check20_6d_H
  · exact satisfied_of_fused_check candidate law20_6e_HT
      (by simp [basis]) check20_6e_HT
  · exact satisfied_of_fused_check candidate law20_6e_H
      (by simp [basis]) check20_6e_H
  · exact satisfied_of_fused_check candidate law20_6f_ABCD
      (by simp [basis]) check20_6f_ABCD
  · exact satisfied_of_fused_check candidate law20_6f_ABC
      (by simp [basis]) check20_6f_ABC
  · exact satisfied_of_fused_check candidate law20_6f_ABD
      (by simp [basis]) check20_6f_ABD
  · exact satisfied_of_fused_check candidate law20_6f_AB
      (by simp [basis]) check20_6f_AB
  · exact satisfied_of_fused_check candidate law20_6f_ACD
      (by simp [basis]) check20_6f_ACD
  · exact satisfied_of_fused_check candidate law20_6f_AC
      (by simp [basis]) check20_6f_AC
  · exact satisfied_of_fused_check candidate law20_6f_AD
      (by simp [basis]) check20_6f_AD
  · exact satisfied_of_fused_check candidate law20_6f_A
      (by simp [basis]) check20_6f_A
  · exact satisfied_of_fused_check candidate law20_6b_K
      (by simp [basis]) check20_6b_K
  · exact satisfied_of_fused_check candidate law20_6a_K
      (by simp [basis]) check20_6a_K
  · exact satisfied_of_fused_check candidate law20_6c_KT
      (by simp [basis]) check20_6c_KT
  · exact satisfied_of_fused_check candidate law20_6c_K
      (by simp [basis]) check20_6c_K
  · exact satisfied_of_fused_check candidate law20_6b_empty
      (by simp [basis]) check20_6b_empty
  · exact satisfied_of_fused_check candidate law20_6a_empty
      (by simp [basis]) check20_6a_empty
  · exact satisfied_of_fused_check candidate law20_6f_BCD
      (by simp [basis]) check20_6f_BCD
  · exact satisfied_of_fused_check candidate law20_6f_BC
      (by simp [basis]) check20_6f_BC
  · exact satisfied_of_fused_check candidate law20_6f_BD
      (by simp [basis]) check20_6f_BD
  · exact satisfied_of_fused_check candidate law20_6f_B
      (by simp [basis]) check20_6f_B
  · exact satisfied_of_fused_check candidate law20_6c_T
      (by simp [basis]) check20_6c_T
  · exact satisfied_of_fused_check candidate law20_6c_empty
      (by simp [basis]) check20_6c_empty
  · exact satisfied_of_fused_check candidate law20_6f_CD
      (by simp [basis]) check20_6f_CD
  · exact satisfied_of_fused_check candidate law20_6f_C
      (by simp [basis]) check20_6f_C
  · exact satisfied_of_fused_check candidate law20_6f_D
      (by simp [basis]) check20_6f_D
  · exact satisfied_of_fused_check candidate law20_6f_empty
      (by simp [basis]) check20_6f_empty
  · exact satisfied_of_fused_check candidate law20_6d_KT
      (by simp [basis]) check20_6d_KT
  · exact satisfied_of_fused_check candidate law20_6d_K
      (by simp [basis]) check20_6d_K
  · exact satisfied_of_fused_check candidate law20_6e_KT
      (by simp [basis]) check20_6e_KT
  · exact satisfied_of_fused_check candidate law20_6e_K
      (by simp [basis]) check20_6e_K
  · exact satisfied_of_fused_check candidate law20_6d_T
      (by simp [basis]) check20_6d_T
  · exact satisfied_of_fused_check candidate law20_6d_empty
      (by simp [basis]) check20_6d_empty
  · exact satisfied_of_fused_check candidate law20_6e_T
      (by simp [basis]) check20_6e_T
  · exact satisfied_of_fused_check candidate law20_6e_empty
      (by simp [basis]) check20_6e_empty

end SemigroupBasis.CoRoots.Order6LeeZhangProposition20_7E4
