import SemigroupBasis.CoRoots.Order6SporadicSection13Tables

namespace SemigroupBasis.CoRoots.Order6SporadicSection13

open SemigroupBasis

namespace S6_10411

private def toFinFive : Nat → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 4

private def finiteLaw1aEmpty : Identity (Fin 5) :=
  law_13_1a_empty.map toFinFive

private def finiteLaw1aH : Identity (Fin 5) :=
  law_13_1a_H.map toFinFive

private def finiteLaw1bEmpty : Identity (Fin 5) :=
  law_13_1b_empty.map toFinFive

private def finiteLaw1bH : Identity (Fin 5) :=
  law_13_1b_H.map toFinFive

private def finiteLaw1cEmpty : Identity (Fin 5) :=
  law_13_1c_empty.map toFinFive

private def finiteLaw1cH : Identity (Fin 5) :=
  law_13_1c_H.map toFinFive

private def finiteLaw1cK : Identity (Fin 5) :=
  law_13_1c_K.map toFinFive

private def finiteLaw1cHK : Identity (Fin 5) :=
  law_13_1c_HK.map toFinFive

private theorem finiteLaw1aEmpty_map :
    finiteLaw1aEmpty.map Fin.val = law_13_1a_empty := rfl

private theorem finiteLaw1aH_map :
    finiteLaw1aH.map Fin.val = law_13_1a_H := rfl

private theorem finiteLaw1bEmpty_map :
    finiteLaw1bEmpty.map Fin.val = law_13_1b_empty := rfl

private theorem finiteLaw1bH_map :
    finiteLaw1bH.map Fin.val = law_13_1b_H := rfl

private theorem finiteLaw1cEmpty_map :
    finiteLaw1cEmpty.map Fin.val = law_13_1c_empty := rfl

private theorem finiteLaw1cH_map :
    finiteLaw1cH.map Fin.val = law_13_1c_H := rfl

private theorem finiteLaw1cK_map :
    finiteLaw1cK.map Fin.val = law_13_1c_K := rfl

private theorem finiteLaw1cHK_map :
    finiteLaw1cHK.map Fin.val = law_13_1c_HK := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finiteLaw1aEmpty_checked :
    table.checkIdentityFused finiteLaw1aEmpty = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finiteLaw1aH_checked :
    table.checkIdentityFused finiteLaw1aH = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finiteLaw1bEmpty_checked :
    table.checkIdentityFused finiteLaw1bEmpty = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finiteLaw1bH_checked :
    table.checkIdentityFused finiteLaw1bH = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finiteLaw1cEmpty_checked :
    table.checkIdentityFused finiteLaw1cEmpty = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finiteLaw1cH_checked :
    table.checkIdentityFused finiteLaw1cH = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finiteLaw1cK_checked :
    table.checkIdentityFused finiteLaw1cK = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finiteLaw1cHK_checked :
    table.checkIdentityFused finiteLaw1cHK = true := by
  rfl

theorem representativeModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← finiteLaw1aEmpty_map]
    exact table.checkIdentityFusedNat_sound
      finiteLaw1aEmpty finiteLaw1aEmpty_checked
  · rw [← finiteLaw1aH_map]
    exact table.checkIdentityFusedNat_sound
      finiteLaw1aH finiteLaw1aH_checked
  · rw [← finiteLaw1bEmpty_map]
    exact table.checkIdentityFusedNat_sound
      finiteLaw1bEmpty finiteLaw1bEmpty_checked
  · rw [← finiteLaw1bH_map]
    exact table.checkIdentityFusedNat_sound
      finiteLaw1bH finiteLaw1bH_checked
  · rw [← finiteLaw1cEmpty_map]
    exact table.checkIdentityFusedNat_sound
      finiteLaw1cEmpty finiteLaw1cEmpty_checked
  · rw [← finiteLaw1cH_map]
    exact table.checkIdentityFusedNat_sound
      finiteLaw1cH finiteLaw1cH_checked
  · rw [← finiteLaw1cK_map]
    exact table.checkIdentityFusedNat_sound
      finiteLaw1cK finiteLaw1cK_checked
  · rw [← finiteLaw1cHK_map]
    exact table.checkIdentityFusedNat_sound
      finiteLaw1cHK finiteLaw1cHK_checked

theorem publishedModels : Models publishedSemigroup basis :=
  representativeModels

end S6_10411

end SemigroupBasis.CoRoots.Order6SporadicSection13
