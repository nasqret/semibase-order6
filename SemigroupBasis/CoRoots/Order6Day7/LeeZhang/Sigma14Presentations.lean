import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708Raw11Presentation
import SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203Obstruction
import SemigroupBasis.FiniteCertificate

/-! Exact two Sigma14 statement-review presentations from msg0422/0423.
Each list is the unchanged S2708 Sigma12 followed by exactly two named laws.
Only soundness and the precise proposed statements are provided here.
No positive class completeness or approval is inferred from bounded screens.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14

open SemigroupBasis

/-- xyx = yxx; x -> 0, y -> 1. -/
def swapLaw12 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 1 [0, 0]⟩
/-- xyy = yxy; x -> 0, y -> 1. -/
def swapLaw13 : Identity Nat := ⟨Word.mk 0 [1, 1], Word.mk 1 [0, 1]⟩
/-- xyx = xxyx; x -> 0, y -> 1. -/
def absorbLaw12 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [0, 1, 0]⟩
/-- xyx = xyxx; x -> 0, y -> 1. -/
def absorbLaw13 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 0]⟩

def swapBasis : List (Identity Nat) := S6_2708.sigma12 ++ [swapLaw12, swapLaw13]
def absorbBasis : List (Identity Nat) := S6_2708.sigma12 ++ [absorbLaw12, absorbLaw13]

def swapBasisSHA256 : String :=
  "c80e6ca6b6ad3ed813fe243b9a07193ff4e022476b2048647096fe1b6827fd80"
def absorbBasisSHA256 : String :=
  "8d4fbe7d7eab8794dcc552323e3b3ae25e2f94a8b3c77eabfaaff1b0423031e7"

theorem swapBasis_length : swapBasis.length = 14 := rfl
theorem absorbBasis_length : absorbBasis.length = 14 := rfl

theorem sigma12_subset_swap (identity : Identity Nat) (member : identity ∈ S6_2708.sigma12) :
    identity ∈ swapBasis := List.mem_append_left _ member
theorem sigma12_subset_absorb (identity : Identity Nat) (member : identity ∈ S6_2708.sigma12) :
    identity ∈ absorbBasis := List.mem_append_left _ member

abbrev table2636 := DualC4Raw6.S6_2636.table
abbrev table2637 := DualC4Raw6.S6_2637.table
abbrev table2705 := DualC4Raw6.S6_2705.table
abbrev table2676 := SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203.Obstruction.S6_2676.table
abbrev table2680 := SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203.Obstruction.S6_2680.table
abbrev table2702 := SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203.Obstruction.S6_2702.table

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private theorem fusedModels (T : FiniteTable) (laws : List (Identity Nat))
    (roundtrips : laws.all (fun identity => decide ((identity.map toFinThree).map Fin.val = identity)) = true)
    (checked : laws.all (fun identity => T.checkIdentityFused (identity.map toFinThree)) = true) :
    Models T.semigroup laws := by
  intro identity member
  have roundtrip : (identity.map toFinThree).map Fin.val = identity :=
    of_decide_eq_true ((List.all_eq_true.mp roundtrips) identity member)
  have valid := T.checkIdentityFusedNat_sound (identity.map toFinThree)
    ((List.all_eq_true.mp checked) identity member)
  rw [roundtrip] at valid
  exact valid

private theorem modelsWithPrefix (T : FiniteTable) (extras : List (Identity Nat))
    (roundtrips : (S6_2708.basis ++ extras).all
      (fun identity => decide ((identity.map toFinThree).map Fin.val = identity)) = true)
    (checked : (S6_2708.basis ++ extras).all
      (fun identity => T.checkIdentityFused (identity.map toFinThree)) = true)
    (linear : S6_2708.missingPrefixSwap.SatisfiedBy T.semigroup) :
    Models T.semigroup (S6_2708.sigma12 ++ extras) := by
  have nonlinear := fusedModels T (S6_2708.basis ++ extras) roundtrips checked
  intro identity member
  simp only [S6_2708.sigma12, List.mem_append, List.mem_singleton] at member
  rcases member with (original | rfl) | extra
  · exact nonlinear identity (List.mem_append_left _ original)
  · exact linear
  · exact nonlinear identity (List.mem_append_right _ extra)

/-- Reuse the already-proved four-variable law, changing only its variable names. -/
private theorem from_workload_prefix (T : FiniteTable)
    (valid : SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203.Obstruction.missingPrefixSwap.SatisfiedBy T.semigroup) :
    S6_2708.missingPrefixSwap.SatisfiedBy T.semigroup := by
  let rename : Nat → Nat
    | 0 => 1
    | 1 => 2
    | 2 => 3
    | _ => 0
  change (SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203.Obstruction.missingPrefixSwap.map rename).SatisfiedBy T.semigroup
  exact Identity.satisfiedBy_map _ rename T.semigroup valid

theorem models2636 : Models table2636.semigroup swapBasis :=
  modelsWithPrefix table2636 [swapLaw12, swapLaw13] (by decide) (by decide)
    DualC4Raw6.S6_2636.missingPrefixSwap_valid
theorem models2637 : Models table2637.semigroup swapBasis :=
  modelsWithPrefix table2637 [swapLaw12, swapLaw13] (by decide) (by decide)
    DualC4Raw6.S6_2637.missingPrefixSwap_valid
theorem models2705 : Models table2705.semigroup swapBasis :=
  modelsWithPrefix table2705 [swapLaw12, swapLaw13] (by decide) (by decide)
    DualC4Raw6.S6_2705.missingPrefixSwap_valid
theorem models2676 : Models table2676.semigroup absorbBasis :=
  modelsWithPrefix table2676 [absorbLaw12, absorbLaw13] (by decide) (by decide)
    (from_workload_prefix table2676 SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203.Obstruction.S6_2676.missingPrefixSwap_valid)
theorem models2680 : Models table2680.semigroup absorbBasis :=
  modelsWithPrefix table2680 [absorbLaw12, absorbLaw13] (by decide) (by decide)
    (from_workload_prefix table2680 SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203.Obstruction.S6_2680.missingPrefixSwap_valid)
theorem models2702 : Models table2702.semigroup absorbBasis :=
  modelsWithPrefix table2702 [absorbLaw12, absorbLaw13] (by decide) (by decide)
    (from_workload_prefix table2702 SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203.Obstruction.S6_2702.missingPrefixSwap_valid)

theorem models_opposite2636 : Models table2636.semigroup.opposite (reversedBasis swapBasis) :=
  models2636.oppositeReversed
theorem models_opposite2637 : Models table2637.semigroup.opposite (reversedBasis swapBasis) :=
  models2637.oppositeReversed
theorem models_opposite2705 : Models table2705.semigroup.opposite (reversedBasis swapBasis) :=
  models2705.oppositeReversed
theorem models_opposite2676 : Models table2676.semigroup.opposite (reversedBasis absorbBasis) :=
  models2676.oppositeReversed
theorem models_opposite2680 : Models table2680.semigroup.opposite (reversedBasis absorbBasis) :=
  models2680.oppositeReversed
theorem models_opposite2702 : Models table2702.semigroup.opposite (reversedBasis absorbBasis) :=
  models2702.oppositeReversed

theorem models_absorb_actual_left :
    Models SemigroupBasis.Generated.S3_8.table.semigroup absorbBasis :=
  modelsWithPrefix SemigroupBasis.Generated.S3_8.table [absorbLaw12, absorbLaw13] (by decide) (by decide)
    (from_workload_prefix SemigroupBasis.Generated.S3_8.table
      SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203.Obstruction.missingPrefixSwap_valid_left)
theorem models_absorb_actual_right :
    Models SemigroupBasis.CoRoots.S5_203.table.semigroup absorbBasis :=
  modelsWithPrefix SemigroupBasis.CoRoots.S5_203.table [absorbLaw12, absorbLaw13] (by decide) (by decide)
    (from_workload_prefix SemigroupBasis.CoRoots.S5_203.table
      SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203.Obstruction.missingPrefixSwap_valid_right)

def CompletenessStatement (table : FiniteTable) (basis : List (Identity Nat)) : Prop :=
  ∀ identity : Identity Nat, identity.SatisfiedBy table.semigroup →
    Derives basis identity.lhs identity.rhs

def OppositeCompletenessStatement (table : FiniteTable) (basis : List (Identity Nat)) : Prop :=
  ∀ identity : Identity Nat, identity.SatisfiedBy table.semigroup.opposite →
    Derives (reversedBasis basis) identity.lhs identity.rhs

/-- Exact six-orientation statement for the swap group, pending fable approval. -/
def ProposedSwapBothOrientations : Prop :=
  CompletenessStatement table2636 swapBasis ∧
  OppositeCompletenessStatement table2636 swapBasis ∧
  CompletenessStatement table2637 swapBasis ∧
  OppositeCompletenessStatement table2637 swapBasis ∧
  CompletenessStatement table2705 swapBasis ∧
  OppositeCompletenessStatement table2705 swapBasis

/-- Exact six-orientation statement for the absorption group, pending fable approval. -/
def ProposedAbsorbBothOrientations : Prop :=
  CompletenessStatement table2676 absorbBasis ∧
  OppositeCompletenessStatement table2676 absorbBasis ∧
  CompletenessStatement table2680 absorbBasis ∧
  OppositeCompletenessStatement table2680 absorbBasis ∧
  CompletenessStatement table2702 absorbBasis ∧
  OppositeCompletenessStatement table2702 absorbBasis

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14
