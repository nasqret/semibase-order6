import SemigroupBasis.CoRoots.S5_215
import SemigroupBasis.CoRoots.S5_215Normalization
import SemigroupBasis.Examples.SemilatticeTwo
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_215Family

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_215
open SemigroupBasis.CoRoots.S5_215Normalization
open SemigroupBasis.Examples

namespace S5_215

theorem models :
    Models Generated.Catalogue.S5_215.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_215.table
    (by decide) (by decide)

theorem correctedModels :
    Models Generated.Catalogue.S5_215.table.semigroup correctedBasis :=
  correctedModels_of_finite_checks Generated.Catalogue.S5_215.table
    (by decide) (by decide) (by decide)

theorem squarefreeInsertion_valid :
    squarefreeInsertionLaw.SatisfiedBy
      Generated.Catalogue.S5_215.table.semigroup :=
  squarefreeInsertion_valid_of_check Generated.Catalogue.S5_215.table
    (by decide)

theorem not_basisFor :
    ¬ BasisFor Generated.Catalogue.S5_215.table.semigroup basis :=
  not_basisFor_of_squarefreeInsertion
    Generated.Catalogue.S5_215.table.semigroup squarefreeInsertion_valid

theorem oppositeModels :
    Models Generated.Catalogue.S5_215.table.semigroup.opposite
      oppositeBasis :=
  models.oppositeReversed

theorem not_oppositeBasisFor :
    ¬ BasisFor Generated.Catalogue.S5_215.table.semigroup.opposite
      oppositeBasis :=
  not_oppositeBasisFor_of_squarefreeInsertion
    Generated.Catalogue.S5_215.table.semigroup squarefreeInsertion_valid

def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_215.table.semigroup.opposite
      Generated.Catalogue.S5_215.table.semigroup where
  toFun := id
  map_mul := by
    intro a b
    exact by decide +revert
  injective := Function.injective_id

theorem selfDualInvolution (a : Fin 5) :
    selfDualEmbedding.toFun (selfDualEmbedding.toFun a) = a := rfl

private def supportEmbedding :
    Embedding semilatticeTwo.semigroup
      Generated.Catalogue.S5_215.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_215.table.semigroup) :
    SameSupport e.lhs e.rhs :=
  semilatticeValid_support_eq e
    (supportEmbedding.pullback_identity e valid)

private def lengthStateFour (n : Nat) : Fin 5 :=
  if n = 1 then 3
  else if n = 2 then 1
  else if n = 3 then 2
  else 0

private theorem lengthStep (n : Nat) (nPos : 0 < n) :
    Generated.Catalogue.S5_215.mul
        (lengthStateFour n) 3 =
      lengthStateFour (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · by_cases hn3 : n = 3
      · subst n
        rfl
      · have hn4 : 4 ≤ n := by omega
        have hn0 : n ≠ 0 := by omega
        simp [lengthStateFour, hn0, hn1, hn2, hn3,
          show n + 1 ≠ 2 by omega,
          show n + 1 ≠ 3 by omega,
          Generated.Catalogue.S5_215.mul]

private theorem lengthFold
    (xs : List Nat) (acc : Nat) (accPos : 0 < acc) :
    xs.foldl
        (fun current _ =>
          Generated.Catalogue.S5_215.mul current 3)
        (lengthStateFour acc) =
      lengthStateFour (acc + xs.length) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [lengthStep acc accPos, ih (acc + 1) (by omega)]
      congr 1
      omega

private theorem evalLength (w : Word Nat) :
    Generated.Catalogue.S5_215.table.semigroup.eval
        (fun _ => (3 : Fin 5)) w =
      lengthStateFour w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_215.mul current 3)
            3 =
          lengthStateFour (head :: tail).length
      simpa [lengthStateFour, Nat.add_comm] using
        lengthFold tail 1 (by omega)

private theorem lengthStateFour_capped_injective
    {m n : Nat} (mPos : 0 < m) (nPos : 0 < n)
    (equal : lengthStateFour m = lengthStateFour n) :
    min m 4 = min n 4 := by
  by_cases hm1 : m = 1
  · subst m
    by_cases hn1 : n = 1
    · subst n
      rfl
    · by_cases hn2 : n = 2
      · subst n
        have values := congrArg Fin.val equal
        simp [lengthStateFour] at values
        omega
      · by_cases hn3 : n = 3
        · subst n
          have values := congrArg Fin.val equal
          simp [lengthStateFour] at values
          omega
        · have hn4 : 4 ≤ n := by omega
          have values := congrArg Fin.val equal
          simp [lengthStateFour, hn1, hn2, hn3] at values
  · by_cases hm2 : m = 2
    · subst m
      by_cases hn1 : n = 1
      · subst n
        have values := congrArg Fin.val equal
        simp [lengthStateFour] at values
        omega
      · by_cases hn2 : n = 2
        · subst n
          rfl
        · by_cases hn3 : n = 3
          · subst n
            have values := congrArg Fin.val equal
            simp [lengthStateFour] at values
          · have hn4 : 4 ≤ n := by omega
            have values := congrArg Fin.val equal
            simp [lengthStateFour, hn1, hn2, hn3] at values
    · by_cases hm3 : m = 3
      · subst m
        by_cases hn1 : n = 1
        · subst n
          have values := congrArg Fin.val equal
          simp [lengthStateFour] at values
          omega
        · by_cases hn2 : n = 2
          · subst n
            have values := congrArg Fin.val equal
            simp [lengthStateFour] at values
          · by_cases hn3 : n = 3
            · subst n
              rfl
            · have hn4 : 4 ≤ n := by omega
              have values := congrArg Fin.val equal
              simp [lengthStateFour, hn1, hn2, hn3] at values
      · have hm4 : 4 ≤ m := by omega
        by_cases hn1 : n = 1
        · subst n
          have values := congrArg Fin.val equal
          simp [lengthStateFour, hm1, hm2, hm3] at values
          omega
        · by_cases hn2 : n = 2
          · subst n
            have values := congrArg Fin.val equal
            simp [lengthStateFour, hm1, hm2, hm3] at values
          · by_cases hn3 : n = 3
            · subst n
              have values := congrArg Fin.val equal
              simp [lengthStateFour, hm1, hm2, hm3] at values
            · have hn4 : 4 ≤ n := by omega
              simp [Nat.min_eq_right hm4,
                Nat.min_eq_right hn4]

theorem valid_capped_length (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_215.table.semigroup) :
    min e.lhs.toList.length 4 =
      min e.rhs.toList.length 4 := by
  have evaluated := valid (fun _ => (3 : Fin 5))
  rw [evalLength, evalLength] at evaluated
  exact lengthStateFour_capped_injective
    (by simp [Word.toList]) (by simp [Word.toList]) evaluated

/-- The repaired three-law list is an unconditional exact basis for the
representative. -/
theorem corrected_basis_complete :
    BasisFor Generated.Catalogue.S5_215.table.semigroup
      correctedBasis :=
  correctedBasis_complete_of_separates
    Generated.Catalogue.S5_215.table.semigroup
    correctedModels valid_support valid_capped_length

theorem corrected_opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_215.table.semigroup.opposite
      correctedOppositeBasis := by
  simpa [correctedOppositeBasis] using
    corrected_basis_complete.oppositeReversed

/-- Exact syntactic theory of the repaired basis: support together with
total length capped at four. -/
theorem derives_corrected_iff_class {u v : Word Nat} :
    Derives correctedBasis u v ↔ CorrectedClass u v := by
  constructor
  · intro derived
    let identity : Identity Nat := ⟨u, v⟩
    have valid :
        identity.SatisfiedBy
          Generated.Catalogue.S5_215.table.semigroup := by
      intro valuation
      exact derived.sound correctedModels valuation
    exact
      ⟨valid_support identity valid,
        valid_capped_length identity valid⟩
  · exact correctedDerivesOfClass

end S5_215

namespace S5_221

theorem models :
    Models Generated.Catalogue.S5_221.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_221.table
    (by decide) (by decide)

theorem correctedModels :
    Models Generated.Catalogue.S5_221.table.semigroup correctedBasis :=
  correctedModels_of_finite_checks Generated.Catalogue.S5_221.table
    (by decide) (by decide) (by decide)

theorem squarefreeInsertion_valid :
    squarefreeInsertionLaw.SatisfiedBy
      Generated.Catalogue.S5_221.table.semigroup :=
  squarefreeInsertion_valid_of_check Generated.Catalogue.S5_221.table
    (by decide)

theorem not_basisFor :
    ¬ BasisFor Generated.Catalogue.S5_221.table.semigroup basis :=
  not_basisFor_of_squarefreeInsertion
    Generated.Catalogue.S5_221.table.semigroup squarefreeInsertion_valid

theorem oppositeModels :
    Models Generated.Catalogue.S5_221.table.semigroup.opposite
      oppositeBasis :=
  models.oppositeReversed

theorem not_oppositeBasisFor :
    ¬ BasisFor Generated.Catalogue.S5_221.table.semigroup.opposite
      oppositeBasis :=
  not_oppositeBasisFor_of_squarefreeInsertion
    Generated.Catalogue.S5_221.table.semigroup squarefreeInsertion_valid

def selfDualEmbedding :
    Embedding Generated.Catalogue.S5_221.table.semigroup.opposite
      Generated.Catalogue.S5_221.table.semigroup where
  toFun := id
  map_mul := by
    intro a b
    exact by decide +revert
  injective := Function.injective_id

theorem selfDualInvolution (a : Fin 5) :
    selfDualEmbedding.toFun (selfDualEmbedding.toFun a) = a := rfl

/-- The two one-based maps `[1,2,3,4,1]` and `[5,5,5,5,1]` from the
authoritative certificate, assembled as a diagonal embedding
`S5_215 ↪ S5_221^2`. -/
def powerEmbedding :
    Embedding Generated.Catalogue.S5_215.table.semigroup
      (Generated.Catalogue.S5_221.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then
      if a = 0 then ⟨0, by decide⟩ else if a = 1 then ⟨1, by decide⟩
      else if a = 2 then ⟨2, by decide⟩ else if a = 3 then ⟨3, by decide⟩
      else ⟨0, by decide⟩
    else
      if a = 0 then ⟨4, by decide⟩ else if a = 1 then ⟨4, by decide⟩
      else if a = 2 then ⟨4, by decide⟩ else if a = 3 then ⟨4, by decide⟩
      else ⟨0, by decide⟩
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b equal
    have first := congrFun equal (0 : Fin 2)
    have second := congrFun equal (1 : Fin 2)
    clear equal
    exact by decide +revert

/-- Replay of the direct-power inheritance certificate. The premise is
explicit and is refuted by `S5_215.not_basisFor`; no unconditional
`BasisFor` endpoint is claimed. -/
theorem basisFor_of_root
    (root :
      BasisFor Generated.Catalogue.S5_215.table.semigroup basis) :
    BasisFor Generated.Catalogue.S5_221.table.semigroup basis :=
  root.inheritAlongPowerEmbedding powerEmbedding models

theorem oppositeBasisFor_of_root
    (root :
      BasisFor Generated.Catalogue.S5_215.table.semigroup basis) :
    BasisFor Generated.Catalogue.S5_221.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using (basisFor_of_root root).oppositeReversed

theorem rootPremiseImpossible
    (root :
      BasisFor Generated.Catalogue.S5_215.table.semigroup basis) :
    False :=
  S5_215.not_basisFor root

/-- The repaired exact basis transfers unconditionally along the recorded
direct-square embedding. -/
theorem corrected_basis_complete :
    BasisFor Generated.Catalogue.S5_221.table.semigroup
      correctedBasis :=
  S5_215.corrected_basis_complete.inheritAlongPowerEmbedding
    powerEmbedding correctedModels

theorem corrected_opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_221.table.semigroup.opposite
      correctedOppositeBasis := by
  simpa [correctedOppositeBasis] using
    corrected_basis_complete.oppositeReversed

end S5_221

end SemigroupBasis.CoRoots.S5_215Family
