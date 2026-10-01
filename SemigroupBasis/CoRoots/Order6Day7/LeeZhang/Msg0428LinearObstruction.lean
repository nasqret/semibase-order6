import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.NonlinearBasisObstruction
import SemigroupBasis.FiniteReflection

/-! Exact negative results for the approved msg0427 pair and msg0425 singleton.
The literal encoding uses x=0, y=1, z=2, t=3 consistently. Soundness is proved
separately and retained; it does not imply unrestricted completeness.
No amended basis is introduced. Opposites use literal reversal, not self-duality. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0428LinearObstruction

open SemigroupBasis NonlinearBasisObstruction

def zzy_zzzy : Identity Nat := ⟨⟨2, [2, 1]⟩, ⟨2, [2, 2, 1]⟩⟩
def zxyy_zyxy : Identity Nat := ⟨⟨2, [0, 1, 1]⟩, ⟨2, [1, 0, 1]⟩⟩
def zxyz_zyxz : Identity Nat := ⟨⟨2, [0, 1, 2]⟩, ⟨2, [1, 0, 2]⟩⟩
def zyzx_zzyx : Identity Nat := ⟨⟨2, [1, 2, 0]⟩, ⟨2, [2, 1, 0]⟩⟩
def yxzzy_zzyxy : Identity Nat := ⟨⟨1, [0, 2, 2, 1]⟩, ⟨2, [2, 1, 0, 1]⟩⟩
def yyzzy_zzyyz : Identity Nat := ⟨⟨1, [1, 2, 2, 1]⟩, ⟨2, [2, 1, 1, 2]⟩⟩
def xxyyzz_zxxyyz : Identity Nat := ⟨⟨0, [0, 1, 1, 2, 2]⟩, ⟨2, [0, 0, 1, 1, 2]⟩⟩
def zyyzy_zzyyz : Identity Nat := ⟨⟨2, [1, 1, 2, 1]⟩, ⟨2, [2, 1, 1, 2]⟩⟩

def pairBasis : List (Identity Nat) :=
  [zzy_zzzy, zxyy_zyxy, zxyz_zyxz, zyzx_zzyx,
   yxzzy_zzyxy, yyzzy_zzyyz, xxyyzz_zxxyyz]
def singletonBasis : List (Identity Nat) :=
  [zzy_zzzy, zxyy_zyxy, zxyz_zyxz, zyzx_zzyx, zyyzy_zzyyz]

def pairBasisSHA256 : String :=
  "7218cca277ecb7dff8504cf52a6938a1877aa5f396ba259fad24e360445040df"
def singletonBasisSHA256 : String :=
  "1fc40b66aea621dfeea43f66dd8c01fcaee6cf2f10a2a2b4734931f4457a9cef"
def table2683SHA256 : String :=
  "e3e1d9ce0aa06cc60e9cd6922bb1036a0f93af5ffbd1a4d42ceebd2017e0ca29"
def table2706SHA256 : String :=
  "f9652b7cf320011cfa97f7d4cbba5f4e97564d7fb5f20926c15bf2b83a0a88c8"
def table5603SHA256 : String :=
  "da3632b37970425ec9c40e351f62a6d4d7d3111bfadef4bdce73cc053997b8c2"

theorem pair_basis_length : pairBasis.length = 7 := rfl
theorem singleton_basis_length : singletonBasis.length = 5 := rfl

def mul2683 (left right : Fin 6) : Fin 6 :=
  if left = 5 then if right = 2 then 0 else right
  else if left = 3 ∨ left = 4 then
    if right = 4 then 1 else if right = 5 then 3 else 0
  else if left = 2 then if right = 5 then 2 else 0
  else 0

def mul2706 (left right : Fin 6) : Fin 6 :=
  if left = 5 then if right = 3 then 2 else right
  else if left = 3 then
    if right = 4 then 1 else if right = 5 then 3 else 0
  else if left = 2 ∨ left = 4 then
    if right = 4 then 1 else if right = 5 then 2 else 0
  else 0

def mul5603 (left right : Fin 6) : Fin 6 :=
  if left = 4 ∨ left = 5 then if right = 4 ∨ right = 5 then left else right
  else if left = 2 ∨ left = 3 then
    if right = 3 then 1 else if right = 4 ∨ right = 5 then 2 else 0
  else 0

def table2683 : FiniteTable := ⟨6, mul2683, by decide⟩
def table2706 : FiniteTable := ⟨6, mul2706, by decide⟩
def table5603 : FiniteTable := ⟨6, mul5603, by decide⟩

theorem table2683_rows_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul2683 a b).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,0,0,2],
       [0,0,0,0,1,3], [0,0,0,0,1,3], [0,1,0,3,4,5]] := by decide

theorem table2706_rows_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul2706 a b).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,0,1,2],
       [0,0,0,0,1,3], [0,0,0,0,1,2], [0,1,2,2,4,5]] := by decide

theorem table5603_rows_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul5603 a b).val)) =
      [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,1,2,2],
       [0,0,0,1,2,2], [0,1,2,3,4,4], [0,1,2,3,5,5]] := by decide

theorem pair_nonlinear : NonlinearSides pairBasis := by
  unfold NonlinearSides
  decide
theorem singleton_nonlinear : NonlinearSides singletonBasis := by
  unfold NonlinearSides
  decide

private def toFin : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem models_of_checks (table : FiniteTable) (basis : List (Identity Nat))
    (roundtrips : basis.all (fun e => decide ((e.map toFin).map Fin.val = e)) = true)
    (checks : basis.all (fun e => table.checkIdentityFused (e.map toFin)) = true) :
    Models table.semigroup basis := by
  intro identity member
  have roundtrip : (identity.map toFin).map Fin.val = identity :=
    of_decide_eq_true ((List.all_eq_true.mp roundtrips) identity member)
  have valid := table.checkIdentityFusedNat_sound (identity.map toFin)
    ((List.all_eq_true.mp checks) identity member)
  rw [roundtrip] at valid
  exact valid

theorem models2683 : Models table2683.semigroup pairBasis :=
  models_of_checks table2683 pairBasis (by decide) (by decide)
theorem models2706 : Models table2706.semigroup pairBasis :=
  models_of_checks table2706 pairBasis (by decide) (by decide)
theorem models5603 : Models table5603.semigroup singletonBasis :=
  models_of_checks table5603 singletonBasis (by decide) (by decide)

theorem models2683_opposite : Models table2683.semigroup.opposite (reversedBasis pairBasis) :=
  models2683.oppositeReversed
theorem models2706_opposite : Models table2706.semigroup.opposite (reversedBasis pairBasis) :=
  models2706.oppositeReversed
theorem models5603_opposite : Models table5603.semigroup.opposite (reversedBasis singletonBasis) :=
  models5603.oppositeReversed

/-- The omitted linear identity; this is a witness, not an adopted amendment. -/
def missingIdentity : Identity Nat := ⟨⟨0, [1, 2, 3]⟩, ⟨0, [2, 1, 3]⟩⟩
private def missingIdentityFin : Identity (Fin 4) := ⟨⟨0, [1, 2, 3]⟩, ⟨0, [2, 1, 3]⟩⟩
private theorem missingIdentity_map : missingIdentityFin.map Fin.val = missingIdentity := rfl

theorem missing_identity_linear : missingIdentity.lhs.toList.Nodup := by decide
theorem missing_identity_ne : missingIdentity.lhs ≠ missingIdentity.rhs := by decide

theorem missing_identity_valid2683 : missingIdentity.SatisfiedBy table2683.semigroup := by
  rw [← missingIdentity_map]
  exact table2683.checkIdentityFusedNat_sound missingIdentityFin (by decide)
theorem missing_identity_valid2706 : missingIdentity.SatisfiedBy table2706.semigroup := by
  rw [← missingIdentity_map]
  exact table2706.checkIdentityFusedNat_sound missingIdentityFin (by decide)
theorem missing_identity_valid5603 : missingIdentity.SatisfiedBy table5603.semigroup := by
  rw [← missingIdentity_map]
  exact table5603.checkIdentityFusedNat_sound missingIdentityFin (by decide)

theorem not_derivable_pair : ¬ Derives pairBasis missingIdentity.lhs missingIdentity.rhs :=
  not_derives_of_linear_ne pair_nonlinear missing_identity_linear missing_identity_ne
theorem not_derivable_singleton : ¬ Derives singletonBasis missingIdentity.lhs missingIdentity.rhs :=
  not_derives_of_linear_ne singleton_nonlinear missing_identity_linear missing_identity_ne

theorem not_complete2683 :
    ¬ (∀ e : Identity Nat, e.SatisfiedBy table2683.semigroup → Derives pairBasis e.lhs e.rhs) :=
  not_complete_of_valid_linear_identity pair_nonlinear missingIdentity
    missing_identity_valid2683 missing_identity_linear missing_identity_ne
theorem not_complete2706 :
    ¬ (∀ e : Identity Nat, e.SatisfiedBy table2706.semigroup → Derives pairBasis e.lhs e.rhs) :=
  not_complete_of_valid_linear_identity pair_nonlinear missingIdentity
    missing_identity_valid2706 missing_identity_linear missing_identity_ne
theorem not_complete5603 :
    ¬ (∀ e : Identity Nat, e.SatisfiedBy table5603.semigroup → Derives singletonBasis e.lhs e.rhs) :=
  not_complete_of_valid_linear_identity singleton_nonlinear missingIdentity
    missing_identity_valid5603 missing_identity_linear missing_identity_ne

theorem not_basisFor2683 : ¬ BasisFor table2683.semigroup pairBasis :=
  fun complete => not_complete2683 complete.2
theorem not_basisFor2706 : ¬ BasisFor table2706.semigroup pairBasis :=
  fun complete => not_complete2706 complete.2
theorem not_basisFor5603 : ¬ BasisFor table5603.semigroup singletonBasis :=
  fun complete => not_complete5603 complete.2

theorem not_complete2683_opposite :
    ¬ (∀ e : Identity Nat, e.SatisfiedBy table2683.semigroup.opposite →
      Derives (reversedBasis pairBasis) e.lhs e.rhs) :=
  not_complete_opposite_of_valid_linear_identity pair_nonlinear missingIdentity
    missing_identity_valid2683 missing_identity_linear missing_identity_ne
theorem not_complete2706_opposite :
    ¬ (∀ e : Identity Nat, e.SatisfiedBy table2706.semigroup.opposite →
      Derives (reversedBasis pairBasis) e.lhs e.rhs) :=
  not_complete_opposite_of_valid_linear_identity pair_nonlinear missingIdentity
    missing_identity_valid2706 missing_identity_linear missing_identity_ne
theorem not_complete5603_opposite :
    ¬ (∀ e : Identity Nat, e.SatisfiedBy table5603.semigroup.opposite →
      Derives (reversedBasis singletonBasis) e.lhs e.rhs) :=
  not_complete_opposite_of_valid_linear_identity singleton_nonlinear missingIdentity
    missing_identity_valid5603 missing_identity_linear missing_identity_ne

theorem not_basisFor2683_opposite :
    ¬ BasisFor table2683.semigroup.opposite (reversedBasis pairBasis) :=
  fun complete => not_complete2683_opposite complete.2
theorem not_basisFor2706_opposite :
    ¬ BasisFor table2706.semigroup.opposite (reversedBasis pairBasis) :=
  fun complete => not_complete2706_opposite complete.2
theorem not_basisFor5603_opposite :
    ¬ BasisFor table5603.semigroup.opposite (reversedBasis singletonBasis) :=
  fun complete => not_complete5603_opposite complete.2

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0428LinearObstruction
