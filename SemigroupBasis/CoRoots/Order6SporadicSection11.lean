import SemigroupBasis.CoRoots.S5_345Syntax
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection11

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def word_11_1a_empty_left : Word Nat := w 0 [0, 0, 0]
def word_11_1a_empty_right : Word Nat := w 0 [0, 0]
def word_11_1a_H_left : Word Nat := w 0 [0, 0, 3, 0]
def word_11_1a_H_right : Word Nat := w 0 [0, 3, 0]
def word_11_1b_left : Word Nat := w 0 [1, 0, 2]
def word_11_1b_right : Word Nat := w 0 [0, 1, 2]
def word_11_1c_empty_left : Word Nat := w 0 [1, 0, 1]
def word_11_1c_empty_right : Word Nat := w 0 [1, 1, 0]
def word_11_1c_H_left : Word Nat := w 0 [3, 1, 0, 1]
def word_11_1c_H_right : Word Nat := w 0 [3, 1, 1, 0]
def word_11_1c_K_left : Word Nat := w 0 [1, 4, 0, 1]
def word_11_1c_K_right : Word Nat := w 0 [1, 4, 1, 0]
def word_11_1c_HK_left : Word Nat := w 0 [3, 1, 4, 0, 1]
def word_11_1c_HK_right : Word Nat := w 0 [3, 1, 4, 1, 0]

def law_11_1a_empty : Identity Nat := ⟨word_11_1a_empty_left, word_11_1a_empty_right⟩
def law_11_1a_H : Identity Nat := ⟨word_11_1a_H_left, word_11_1a_H_right⟩
def law_11_1b : Identity Nat := ⟨word_11_1b_left, word_11_1b_right⟩
def law_11_1c_empty : Identity Nat := ⟨word_11_1c_empty_left, word_11_1c_empty_right⟩
def law_11_1c_H : Identity Nat := ⟨word_11_1c_H_left, word_11_1c_H_right⟩
def law_11_1c_K : Identity Nat := ⟨word_11_1c_K_left, word_11_1c_K_right⟩
def law_11_1c_HK : Identity Nat := ⟨word_11_1c_HK_left, word_11_1c_HK_right⟩

/-- The seven ordinary identities obtained by expanding Proposition 11.1. -/
def basis : List (Identity Nat) :=
  [law_11_1a_empty, law_11_1a_H, law_11_1b, law_11_1c_empty, law_11_1c_H, law_11_1c_K, law_11_1c_HK]

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

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinFive).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFive).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Finite checks on the five displayed variables establish soundness only. -/
theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFive ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinFive)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

def firstOccurrenceSequenceList (letters : List Nat) : List Nat :=
  SemigroupBasis.Examples.firstOccurrenceSequence letters

def cappedCountsList (letters : List Nat) : List Nat :=
  (firstOccurrenceSequenceList letters).map fun letter =>
    Nat.min (letters.count letter) 3

inductive TerminalStatus where
  | simple (letter : Nat)
  | nonsimple
deriving DecidableEq, Repr

def terminalStatusOfOption : Option Nat → TerminalStatus
  | some letter => .simple letter
  | none => .nonsimple

def terminalStatusList (letters : List Nat) : TerminalStatus :=
  match letters.getLast? with
  | none => .nonsimple
  | some letter =>
      if letters.count letter = 1 then .simple letter else .nonsimple

structure Signature where
  firstOccurrences : List Nat
  cappedCounts : List Nat
  terminal : TerminalStatus
deriving DecidableEq, Repr

def signatureList (letters : List Nat) : Signature where
  firstOccurrences := firstOccurrenceSequenceList letters
  cappedCounts := cappedCountsList letters
  terminal := terminalStatusList letters

def signature (word : Word Nat) : Signature where
  firstOccurrences := firstOccurrenceSequenceList word.toList
  cappedCounts := cappedCountsList word.toList
  terminal := terminalStatusOfOption
    (SemigroupBasis.CoRoots.S5_345.simpleFinalVariable word)

theorem literalBasisSignaturesAgree :
    basis.all (fun identity =>
      decide (signature identity.lhs = signature identity.rhs)) = true := by
  decide

/-- The unrestricted syntactic obligation left by the source design. -/
structure SignatureDerivationCompleteness : Prop where
  derives :
    ∀ left right : Word Nat,
      signature left = signature right → Derives basis left right

/-- Target semantics must recover every field of the proposed signature. -/
structure SignatureSeparation (candidate : FiniteTable) : Prop where
  separate :
    ∀ identity : Identity Nat,
      identity.SatisfiedBy candidate.semigroup →
        signature identity.lhs = signature identity.rhs

theorem basisFor_of_signature
    (candidate : FiniteTable)
    (models : Models candidate.semigroup basis)
    (separation : SignatureSeparation candidate)
    (completeness : SignatureDerivationCompleteness) :
    BasisFor candidate.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact completeness.derives identity.lhs identity.rhs
    (separation.separate identity valid)

namespace S6_5614

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,1],[1,1,1,2,1,4],[5,5,5,5,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a6d6e2e91e0c2f6b22c7f58f64fb0af2bef670f573b5d426c77479651c85a234"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

theorem basisFor_of_obligations
    (separation : SignatureSeparation table)
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup basis :=
  basisFor_of_signature table models separation completeness

theorem oppositeBasisFor_of_obligations
    (separation : SignatureSeparation table)
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (basisFor_of_obligations separation completeness).oppositeReversed

end S6_5614

namespace S6_9582

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,2,1,1,3],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9deb0c2dc76a4f85362fce6ffea5157fb9d767cf8bcb58f91c8f74a8c36d3e1b"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

theorem basisFor_of_obligations
    (separation : SignatureSeparation table)
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup basis :=
  basisFor_of_signature table models separation completeness

theorem oppositeBasisFor_of_obligations
    (separation : SignatureSeparation table)
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (basisFor_of_obligations separation completeness).oppositeReversed

end S6_9582

namespace S6_5622

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,1,1,2,1,4],[5,5,5,5,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b3bbaeefa90004811d0670731ebb80d6f641a952f6bd21737c841a87c38fd44c"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

theorem basisFor_of_obligations
    (separation : SignatureSeparation table)
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup basis :=
  basisFor_of_signature table models separation completeness

theorem oppositeBasisFor_of_obligations
    (separation : SignatureSeparation table)
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (basisFor_of_obligations separation completeness).oppositeReversed

end S6_5622

namespace S6_9451

/-- Exact one-based catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,2,2,1,3],[1,1,2,2,1,3],[5,5,5,5,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2852a3791788bd596183c2694697df3d3e37ce378252e0cfb5307fd2c6975ba9"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

theorem basisFor_of_obligations
    (separation : SignatureSeparation table)
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup basis :=
  basisFor_of_signature table models separation completeness

theorem oppositeBasisFor_of_obligations
    (separation : SignatureSeparation table)
    (completeness : SignatureDerivationCompleteness) :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using
    (basisFor_of_obligations separation completeness).oppositeReversed

end S6_9451

end SemigroupBasis.CoRoots.Order6SporadicSection11
