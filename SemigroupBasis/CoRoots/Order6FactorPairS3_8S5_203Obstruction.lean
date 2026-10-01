import SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203Prelude
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Order6.FactorPairJoin

/-!
# Workload85: the exact thirteen-law presentation is incomplete

All twenty-six displayed sides are nonlinear. A nonempty semigroup
substitution cannot put any such side into a square-free word. Derivations
therefore fix every square-free word, including `xyzt`.

The distinct word `yxzt` has the same value in BOTH ACTUAL factors, S3_8
direct and S5_203 direct. This gives unrestricted nonderivability, not a
finite-search completeness inference. The same missing identity is checked
directly in the literal tables of S6_2676, S6_2680, and S6_2702, independently
of the historical, terminally closed S6_2702 direct-power route.

The imported thirteen-law list is not edited. `sigmaPlus` and
`ProposedJointCompleteness` below are a statement awaiting fable review;
no positive completeness theorem for that amendment is asserted.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203.Obstruction

open SemigroupBasis

abbrev leftTable := SemigroupBasis.Generated.S3_8.table
abbrev rightTable := SemigroupBasis.CoRoots.S5_203.table

def displayedBasisSHA256 : String :=
  "f89879f779a8f98abf3ddbb9f4643b4e60bdb15f1be0a3f3336a1e0ad7e97e9f"

def missingPrefixSwap : Identity Nat :=
  ⟨Word.mk 0 [1, 2, 3], Word.mk 1 [0, 2, 3]⟩

private def missingPrefixSwapFin : Identity (Fin 4) :=
  ⟨Word.mk 0 [1, 2, 3], Word.mk 1 [0, 2, 3]⟩

theorem missingPrefixSwapFin_map :
    missingPrefixSwapFin.map Fin.val = missingPrefixSwap := rfl

theorem missingPrefixSwap_valid_left :
    missingPrefixSwap.SatisfiedBy leftTable.semigroup := by
  rw [← missingPrefixSwapFin_map]
  exact leftTable.checkIdentityNat_sound missingPrefixSwapFin (by decide)

theorem missingPrefixSwap_valid_right :
    missingPrefixSwap.SatisfiedBy rightTable.semigroup := by
  rw [← missingPrefixSwapFin_map]
  exact rightTable.checkIdentityNat_sound missingPrefixSwapFin (by decide)

def toFinThree (letter : Nat) : Fin 3 := ⟨letter % 3, Nat.mod_lt _ (by decide)⟩

theorem left_models_raw : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)

theorem right_models_raw : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

theorem displayedBasis_length : basis.length = 13 := rfl

theorem displayedBasis_has_repetition :
    ∀ identity ∈ basis,
      ¬ identity.lhs.toList.Nodup ∧ ¬ identity.rhs.toList.Nodup := by
  decide

private theorem nodup_of_flatMap_nodup
    (source : List Nat) (images : Nat → List Nat)
    (imageNonempty : ∀ letter, images letter ≠ [])
    (mappedNodup : (source.flatMap images).Nodup) : source.Nodup := by
  induction source with
  | nil => simp
  | cons head tail ih =>
      rw [List.flatMap_cons] at mappedNodup
      have split := List.nodup_append.mp mappedNodup
      apply List.nodup_cons.mpr
      constructor
      · intro headMember
        obtain ⟨marker, markerMember⟩ :=
          List.exists_mem_of_ne_nil (images head) (imageNonempty head)
        have markerInTail : marker ∈ tail.flatMap images := by
          simp only [List.mem_flatMap]
          exact ⟨head, headMember, markerMember⟩
        exact split.2.2 marker markerMember marker markerInTail rfl
      · exact ih split.2.1

private theorem source_nodup_of_bind_nodup
    (source : Word Nat) (substitution : Nat → Word Nat)
    (bound : (source.bind substitution).toList.Nodup) : source.toList.Nodup := by
  rw [Word.toList_bind] at bound
  apply nodup_of_flatMap_nodup source.toList
    (fun letter => (substitution letter).toList)
  · intro letter
    cases substitution letter
    simp [Word.toList]
  · exact bound

/-- Unrestricted rigidity under all derivation constructors, including
arbitrary contexts and nonempty simultaneous substitution. -/
theorem derives_squareFree_rigid
    {left right : Word Nat} (derivation : Derives basis left right) :
    (left.toList.Nodup → left = right) ∧
      (right.toList.Nodup → left = right) := by
  induction derivation with
  | fromBasis member =>
      have repeated := displayedBasis_has_repetition _ member
      exact ⟨fun nodup => False.elim (repeated.1 nodup),
        fun nodup => False.elim (repeated.2 nodup)⟩
  | refl => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | symm _ ih => exact ⟨fun nodup => (ih.2 nodup).symm,
      fun nodup => (ih.1 nodup).symm⟩
  | trans _ _ first second =>
      constructor
      · intro nodup
        have equalFirst := first.1 nodup
        subst_vars
        exact second.1 nodup
      · intro nodup
        have equalSecond := second.2 nodup
        subst_vars
        exact first.2 nodup
  | prepend _ _ ih =>
      constructor
      · intro nodup
        have suffixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).2.1
        rw [ih.1 suffixNodup]
      · intro nodup
        have suffixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).2.1
        rw [ih.2 suffixNodup]
  | appendRight _ _ ih =>
      constructor
      · intro nodup
        have prefixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).1
        rw [ih.1 prefixNodup]
      · intro nodup
        have prefixNodup : _ := (List.nodup_append.mp <| by
          simpa [Word.toList_append] using nodup).1
        rw [ih.2 prefixNodup]
  | subst _ substitution ih =>
      constructor
      · intro nodup
        have sourceNodup := source_nodup_of_bind_nodup _ substitution nodup
        rw [ih.1 sourceNodup]
      · intro nodup
        have targetNodup := source_nodup_of_bind_nodup _ substitution nodup
        rw [ih.2 targetNodup]

theorem missingPrefixSwap_not_derivable :
    ¬ Derives basis missingPrefixSwap.lhs missingPrefixSwap.rhs := by
  intro derivation
  have equal := (derives_squareFree_rigid derivation).1 (by decide)
  exact (by decide : missingPrefixSwap.lhs ≠ missingPrefixSwap.rhs) equal

theorem raw_jointCompleteness_isFalse :
    ¬ (∀ identity : Identity Nat,
      identity.SatisfiedBy leftTable.semigroup →
        identity.SatisfiedBy rightTable.semigroup →
          Derives basis identity.lhs identity.rhs) := by
  intro complete
  exact missingPrefixSwap_not_derivable
    (complete missingPrefixSwap missingPrefixSwap_valid_left missingPrefixSwap_valid_right)

theorem raw_intersectionBasis_isFalse :
    ¬ IntersectionBasis leftTable.semigroup rightTable.semigroup basis := by
  intro intersection
  exact missingPrefixSwap_not_derivable
    (intersection.complete missingPrefixSwap
      missingPrefixSwap_valid_left missingPrefixSwap_valid_right)

theorem raw_intersectionNormalizer_isFalse
    (normalizer : IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis) :
    False :=
  raw_intersectionBasis_isFalse
    (normalizer.toIntersectionBasis left_models_raw right_models_raw)

namespace S6_2676

def sourceTableSHA256 : String :=
  "e5d8b5c0ee1c07bd45f51db961a172e130cc4e9102bd9f0b9aa38396ca76ec70"

def mul (left right : Fin 6) : Fin 6 :=
  if left.val < 2 then 0
  else if left = 2 then if right = 5 then 2 else 0
  else if left.val < 5 then if right = 4 then 1 else 0
  else if right = 4 then 3 else right

theorem table_rows_exact :
    List.ofFn (fun (a : Fin 6) => List.ofFn (fun (b : Fin 6) => (mul a b).val)) =
      [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0],
       [0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0],
       [0, 0, 0, 0, 1, 0], [0, 1, 2, 3, 3, 5]] := by decide

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem models_raw : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

theorem missingPrefixSwap_valid : missingPrefixSwap.SatisfiedBy table.semigroup := by
  rw [← missingPrefixSwapFin_map]
  exact table.checkIdentityNat_sound missingPrefixSwapFin (by decide)

theorem raw_basis_isFalse : ¬ BasisFor table.semigroup basis := by
  intro complete
  exact missingPrefixSwap_not_derivable (complete.2 missingPrefixSwap missingPrefixSwap_valid)

end S6_2676

namespace S6_2680

def sourceTableSHA256 : String :=
  "6298105a5c7c522cabd7e6d6f7b38aa5028d8ae4b6b3443dab606741810b3526"

def mul (left right : Fin 6) : Fin 6 :=
  if left.val < 2 then 0
  else if left = 2 then if right = 5 then 2 else 0
  else if left.val < 5 then if right = 4 then 1 else if right = 5 then 2 else 0
  else if right = 4 then 3 else right

theorem table_rows_exact :
    List.ofFn (fun (a : Fin 6) => List.ofFn (fun (b : Fin 6) => (mul a b).val)) =
      [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0],
       [0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 2],
       [0, 0, 0, 0, 1, 2], [0, 1, 2, 3, 3, 5]] := by decide

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem models_raw : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

theorem missingPrefixSwap_valid : missingPrefixSwap.SatisfiedBy table.semigroup := by
  rw [← missingPrefixSwapFin_map]
  exact table.checkIdentityNat_sound missingPrefixSwapFin (by decide)

theorem raw_basis_isFalse : ¬ BasisFor table.semigroup basis := by
  intro complete
  exact missingPrefixSwap_not_derivable (complete.2 missingPrefixSwap missingPrefixSwap_valid)

end S6_2680

namespace S6_2702

def sourceTableSHA256 : String :=
  "15c870db3e301a7655622f5668a38657bafd32a5fc417635c3c55253738540db"

def mul (left right : Fin 6) : Fin 6 :=
  if left.val < 2 then 0
  else if left = 2 ∨ left = 4 then if right = 4 then 1 else 0
  else if left = 3 then
    if right = 2 ∨ right = 4 then 1 else if right = 5 then 3 else 0
  else if right = 4 then 2 else right

theorem table_rows_exact :
    List.ofFn (fun (a : Fin 6) => List.ofFn (fun (b : Fin 6) => (mul a b).val)) =
      [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0],
       [0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 3],
       [0, 0, 0, 0, 1, 0], [0, 1, 2, 3, 2, 5]] := by decide

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

theorem models_raw : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

theorem missingPrefixSwap_valid : missingPrefixSwap.SatisfiedBy table.semigroup := by
  rw [← missingPrefixSwapFin_map]
  exact table.checkIdentityNat_sound missingPrefixSwapFin (by decide)

theorem raw_basis_isFalse : ¬ BasisFor table.semigroup basis := by
  intro complete
  exact missingPrefixSwap_not_derivable (complete.2 missingPrefixSwap missingPrefixSwap_valid)

end S6_2702

/-- Candidate only. Approval and unrestricted completeness are both pending. -/
def sigmaPlus : List (Identity Nat) := basis ++ [missingPrefixSwap]

def proposedSigmaSHA256 : String :=
  "74f6f80110687537bfca4de8a677c02d238269ee90939885221b0ec28893ae3f"

/-- Exact unrestricted statement submitted for fable review, not a theorem. -/
def ProposedJointCompleteness : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy leftTable.semigroup →
      identity.SatisfiedBy rightTable.semigroup →
        Derives sigmaPlus identity.lhs identity.rhs

end SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_203.Obstruction
