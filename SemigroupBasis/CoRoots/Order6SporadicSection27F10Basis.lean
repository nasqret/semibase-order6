import SemigroupBasis.CoRoots.Order6SporadicSection27F9G1

/-!
# The eighteen ordinary laws of Lee--Zhang Proposition 27.1 (F10)

The shared A-D identity literals are reused from the historical F9/G1 file,
but its twenty-two-law basis and its derivations are NOT the F10 basis.
The four additional E identities are absent: all four fail on F10.

The order below is the frozen direct F10 raw18 order. The shared literals
use x=0,y=1,h=2,k=3,t=4; a named renaming bridge binds them to the frozen
per-identity first-occurrence encoding at the final endpoint.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27.F10

open SemigroupBasis

def basis : List (Identity Nat) :=
  [lawA_empty, lawA_H,
   lawB_empty, lawB_K, lawB_H, lawB_HK,
   lawC_empty, lawC_K, lawC_H, lawC_HK,
   lawD_empty, lawD_T, lawD_K, lawD_KT,
   lawD_H, lawD_HT, lawD_HK, lawD_HKT]

def oppositeBasis : List (Identity Nat) := reversedBasis basis

theorem basis_length : basis.length = 18 := by decide

private theorem roundtrips :
    basis.all (fun e => decide ((e.map toFinFive).map Fin.val = e)) = true := by
  decide

/-- Only the eighteen displayed A-D identities are required. -/
theorem models_of_fused_checks (candidate : FiniteTable)
    (checks : ∀ e, e ∈ basis → candidate.checkIdentityFused (e.map toFinFive) = true) :
    Models candidate.semigroup basis := by
  intro e member
  have back : (e.map toFinFive).map Fin.val = e :=
    of_decide_eq_true ((List.all_eq_true.mp roundtrips) e member)
  have valid := candidate.checkIdentityFusedNat_sound (e.map toFinFive) (checks e member)
  rw [back] at valid
  exact valid

end SemigroupBasis.CoRoots.Order6SporadicSection27.F10

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.basis_length
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection27.F10.models_of_fused_checks
