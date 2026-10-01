import SemigroupBasis.CoRoots.Order6SporadicSection16Tables
import SemigroupBasis.CoRoots.S5_345Factors

/-! Lee-Zhang2015 Lemma16.2(i)-(iii): exact L2^1 and N2^1
subsemigroups, and the stated J subsemigroups or Rees quotients. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis SemigroupBasis.Examples


namespace S6_3813

def iniEmbedding : Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def countEmbedding : Embedding commutativeExponentThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def finalEmbedding : Embedding finalMarkerThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

theorem valid_ini (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  iniEmbedding.pullback_identity identity valid

theorem valid_count (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy commutativeExponentThree.semigroup :=
  countEmbedding.pullback_identity identity valid

theorem valid_final (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup :=
  finalEmbedding.pullback_identity identity valid

#print axioms valid_ini
#print axioms valid_count
#print axioms valid_final
end S6_3813


namespace S6_3815

def iniEmbedding : Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def countEmbedding : Embedding commutativeExponentThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def finalEmbedding : Embedding finalMarkerThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

theorem valid_ini (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  iniEmbedding.pullback_identity identity valid

theorem valid_count (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy commutativeExponentThree.semigroup :=
  countEmbedding.pullback_identity identity valid

theorem valid_final (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup :=
  finalEmbedding.pullback_identity identity valid

#print axioms valid_ini
#print axioms valid_count
#print axioms valid_final
end S6_3815


namespace S6_3826

def iniEmbedding : Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def countEmbedding : Embedding commutativeExponentThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def finalDivisorTableMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then (if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4)) else if a = 1 then (if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4)) else if a = 2 then (if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4)) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def finalDivisorTable : FiniteTable where
  order := 4
  mul := finalDivisorTableMul
  assoc := by decide

def finalDivisorEmbedding : Embedding finalDivisorTable.semigroup table.semigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def finalDivisorQuotient :
    SplitSurjection finalDivisorTable.semigroup finalMarkerThree.semigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else (2 : Fin 3)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  preimage := fun a : Fin 3 => if a = 0 then (0 : Fin 4) else if a = 1 then (2 : Fin 4) else (3 : Fin 4)
  right_inverse := by intro a; apply Fin.ext; revert a; decide

theorem valid_ini (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  iniEmbedding.pullback_identity identity valid

theorem valid_count (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy commutativeExponentThree.semigroup :=
  countEmbedding.pullback_identity identity valid

theorem valid_final (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup :=
  finalDivisorQuotient.pushforwardIdentity identity (finalDivisorEmbedding.pullback_identity identity valid)

#print axioms valid_ini
#print axioms valid_count
#print axioms valid_final
end S6_3826


namespace S6_3828

def iniEmbedding : Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def countEmbedding : Embedding commutativeExponentThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def finalDivisorTableMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then (if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4)) else if a = 1 then (if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4)) else if a = 2 then (if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4)) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def finalDivisorTable : FiniteTable where
  order := 4
  mul := finalDivisorTableMul
  assoc := by decide

def finalDivisorEmbedding : Embedding finalDivisorTable.semigroup table.semigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def finalDivisorQuotient :
    SplitSurjection finalDivisorTable.semigroup finalMarkerThree.semigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else (2 : Fin 3)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  preimage := fun a : Fin 3 => if a = 0 then (0 : Fin 4) else if a = 1 then (2 : Fin 4) else (3 : Fin 4)
  right_inverse := by intro a; apply Fin.ext; revert a; decide

theorem valid_ini (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  iniEmbedding.pullback_identity identity valid

theorem valid_count (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy commutativeExponentThree.semigroup :=
  countEmbedding.pullback_identity identity valid

theorem valid_final (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup :=
  finalDivisorQuotient.pushforwardIdentity identity (finalDivisorEmbedding.pullback_identity identity valid)

#print axioms valid_ini
#print axioms valid_count
#print axioms valid_final
end S6_3828


namespace S6_6437

def iniEmbedding : Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (3 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def countEmbedding : Embedding commutativeExponentThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def finalEmbedding : Embedding finalMarkerThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

theorem valid_ini (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  iniEmbedding.pullback_identity identity valid

theorem valid_count (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy commutativeExponentThree.semigroup :=
  countEmbedding.pullback_identity identity valid

theorem valid_final (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup :=
  finalEmbedding.pullback_identity identity valid

#print axioms valid_ini
#print axioms valid_count
#print axioms valid_final
end S6_6437


namespace S6_6444

def iniEmbedding : Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (3 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def countEmbedding : Embedding commutativeExponentThree.semigroup table.semigroup where
  toFun := fun a : Fin 3 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else (5 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def finalDivisorTableMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then (if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (0 : Fin 4)) else if a = 1 then (if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4)) else if a = 2 then (if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (0 : Fin 4) else (1 : Fin 4)) else if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else (3 : Fin 4)

def finalDivisorTable : FiniteTable where
  order := 4
  mul := finalDivisorTableMul
  assoc := by decide

def finalDivisorEmbedding : Embedding finalDivisorTable.semigroup table.semigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  injective := by intro a b; revert a b; decide

def finalDivisorQuotient :
    SplitSurjection finalDivisorTable.semigroup finalMarkerThree.semigroup where
  toFun := fun a : Fin 4 => if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (1 : Fin 3) else (2 : Fin 3)
  map_mul := by intro a b; apply Fin.ext; revert a b; decide
  preimage := fun a : Fin 3 => if a = 0 then (0 : Fin 4) else if a = 1 then (2 : Fin 4) else (3 : Fin 4)
  right_inverse := by intro a; apply Fin.ext; revert a; decide

theorem valid_ini (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  iniEmbedding.pullback_identity identity valid

theorem valid_count (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy commutativeExponentThree.semigroup :=
  countEmbedding.pullback_identity identity valid

theorem valid_final (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup :=
  finalDivisorQuotient.pushforwardIdentity identity (finalDivisorEmbedding.pullback_identity identity valid)

#print axioms valid_ini
#print axioms valid_count
#print axioms valid_final
end S6_6444


end SemigroupBasis.CoRoots.Order6SporadicSection16
