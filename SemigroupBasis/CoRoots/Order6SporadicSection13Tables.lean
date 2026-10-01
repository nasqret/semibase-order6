import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.Generated.S4_96
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

/- The finite table declarations live separately from their expensive
   identity checks so each check can be elaborated in its own Lean process. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection13

open SemigroupBasis

def section13Word (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def word_13_1a_empty_left : Word Nat := section13Word 0 [0, 0, 0]
def word_13_1a_empty_right : Word Nat := section13Word 0 [0]
def law_13_1a_empty : Identity Nat := ⟨word_13_1a_empty_left, word_13_1a_empty_right⟩
def word_13_1a_H_left : Word Nat := section13Word 0 [3, 0, 0, 0]
def word_13_1a_H_right : Word Nat := section13Word 0 [3, 0]
def law_13_1a_H : Identity Nat := ⟨word_13_1a_H_left, word_13_1a_H_right⟩
def word_13_1b_empty_left : Word Nat := section13Word 0 [0, 0, 1]
def word_13_1b_empty_right : Word Nat := section13Word 0 [1]
def law_13_1b_empty : Identity Nat := ⟨word_13_1b_empty_left, word_13_1b_empty_right⟩
def word_13_1b_H_left : Word Nat := section13Word 0 [3, 0, 0, 1]
def word_13_1b_H_right : Word Nat := section13Word 0 [3, 1]
def law_13_1b_H : Identity Nat := ⟨word_13_1b_H_left, word_13_1b_H_right⟩
def word_13_1c_empty_left : Word Nat := section13Word 0 [1, 0, 1]
def word_13_1c_empty_right : Word Nat := section13Word 0 [1, 1, 0]
def law_13_1c_empty : Identity Nat := ⟨word_13_1c_empty_left, word_13_1c_empty_right⟩
def word_13_1c_H_left : Word Nat := section13Word 0 [3, 1, 0, 1]
def word_13_1c_H_right : Word Nat := section13Word 0 [3, 1, 1, 0]
def law_13_1c_H : Identity Nat := ⟨word_13_1c_H_left, word_13_1c_H_right⟩
def word_13_1c_K_left : Word Nat := section13Word 0 [1, 4, 0, 1]
def word_13_1c_K_right : Word Nat := section13Word 0 [1, 4, 1, 0]
def law_13_1c_K : Identity Nat := ⟨word_13_1c_K_left, word_13_1c_K_right⟩
def word_13_1c_HK_left : Word Nat := section13Word 0 [3, 1, 4, 0, 1]
def word_13_1c_HK_right : Word Nat := section13Word 0 [3, 1, 4, 1, 0]
def law_13_1c_HK : Identity Nat := ⟨word_13_1c_HK_left, word_13_1c_HK_right⟩

/-- The eight ordinary boundary instances of Proposition 13.1. -/
def basis : List (Identity Nat) :=
  [law_13_1a_empty, law_13_1a_H, law_13_1b_empty, law_13_1b_H, law_13_1c_empty, law_13_1c_H, law_13_1c_K, law_13_1c_HK]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

private def toFinFive : Nat → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 4

def finiteBasis : List (Identity (Fin 5)) :=
  basis.map fun identity => identity.map toFinFive

def finiteOppositeBasis : List (Identity (Fin 5)) :=
  oppositeBasis.map fun identity => identity.map toFinFive

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem oppositeBasis_roundTrip_checked :
    oppositeBasis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

private theorem oppositeBasis_roundTrip
    (identity : Identity Nat) (member : identity ∈ oppositeBasis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp oppositeBasis_roundTrip_checked) identity member

/-- Finite checks establish soundness of the displayed basis only. -/
theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

/-- Finite checks establish soundness of the reversed basis only. -/
theorem modelsOpposite_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteOppositeBasis.all candidate.checkIdentityFused = true) :
    Models candidate.semigroup oppositeBasis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteOppositeBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityFusedNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [oppositeBasis_roundTrip identity member] at finiteValid
  exact finiteValid

/-- The unrestricted content of Proposition 13.1.  This source interface is
inhabited only after the canonical-form and nonsimple-final proofs are built. -/
structure JoinCompleteness : Prop where
  derives :
    ∀ identity : Identity Nat,
      identity.SatisfiedBy Generated.S3_6.table.semigroup →
      identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite →
      Derives basis identity.lhs identity.rhs

theorem basisFor_of_joinCompleteness
    {S : Type u} (candidate : Semigroup S)
    (models : Models candidate basis)
    (validJ :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy candidate →
        identity.SatisfiedBy Generated.S3_6.table.semigroup)
    (validO :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy candidate →
        identity.SatisfiedBy Generated.S4_96.table.semigroup.opposite)
    (completion : JoinCompleteness) :
    BasisFor candidate basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact completion.derives identity
    (validJ identity valid) (validO identity valid)

namespace S6_10203

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,3,4,1,6],[6,6,4,3,6,1],[1,2,1,1,5,1],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (5 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d8373c72c3df8e241b90d8084a6f93c4f1eaacf1dd8634c300e3c9b75ed9be78"

/-- The orientation in which the published Section 13 table is read. -/
abbrev publishedSemigroup : Semigroup (Fin 6) :=
  table.semigroup

end S6_10203

namespace S6_10409

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,5,6],[1,2,4,3,6,5],[1,1,5,5,5,5],[1,1,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "647d52eadc89ee56a6c6290cba53169e45640ccf1d5ff6791ade928e4386fbcc"

/-- The orientation in which the published Section 13 table is read. -/
abbrev publishedSemigroup : Semigroup (Fin 6) :=
  table.semigroup

end S6_10409

namespace S6_10218

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,3,4,3,6],[6,6,4,3,4,1],[1,2,3,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b822d162e88c335e315b29b9b7b279db63024da6711d27324261acbf1eea1b2c"

/-- The orientation in which the published Section 13 table is read. -/
abbrev publishedSemigroup : Semigroup (Fin 6) :=
  table.semigroup

end S6_10218

namespace S6_10410

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,5,6],[1,2,4,3,6,5],[1,2,5,5,5,5],[1,2,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "67d7746884f3e050f0b1afde910111d56638c36e8b3841e547ca5b745f71b63b"

/-- The orientation in which the published Section 13 table is read. -/
abbrev publishedSemigroup : Semigroup (Fin 6) :=
  table.semigroup

end S6_10410

namespace S6_10411

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,5,6],[1,2,4,3,6,5],[5,5,5,5,5,5],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c3a4df7cde15464a4cfb80aa6ed6d66e4e6ea88ae67db40a6d589144bc19700b"

/-- The orientation in which the published Section 13 table is read. -/
abbrev publishedSemigroup : Semigroup (Fin 6) :=
  table.semigroup

end S6_10411

namespace S6_9882

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,5,6],[5,6,4,3,1,2],[5,5,5,5,5,5],[5,5,5,5,5,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (4 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "768221257f03a813a0c41c861e62bff77a604c649d42c9d386a8677432d15170"

/-- The orientation in which the published Section 13 table is read. -/
abbrev publishedSemigroup : Semigroup (Fin 6) :=
  table.semigroup

end S6_9882

namespace S6_8921

/-- Exact one-based catalogue table: `[[1,1,3,1,5,6],[1,1,3,1,5,6],[3,3,1,3,6,5],[1,2,3,4,5,6],[5,5,5,5,5,5],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4b734ee50e32191efccb042bee1535c1a85072a93d30fdfb29f7576521da537c"

/-- The orientation in which the published Section 13 table is read. -/
abbrev publishedSemigroup : Semigroup (Fin 6) :=
  table.semigroup

end S6_8921

namespace S6_9062

/-- Exact one-based catalogue table: `[[1,2,2,1,5,6],[2,1,1,2,5,6],[2,1,1,3,5,6],[1,2,2,4,5,6],[5,6,6,5,5,6],[6,5,5,6,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (1 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c7306e7e455cc773dae4f83d3296d6f689a66ff59dbd84e0434e2f9f0ca2db78"

/-- The orientation in which the published Section 13 table is read. -/
abbrev publishedSemigroup : Semigroup (Fin 6) :=
  table.semigroup.opposite

end S6_9062


end SemigroupBasis.CoRoots.Order6SporadicSection13
