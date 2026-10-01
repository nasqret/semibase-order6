import SemigroupBasis.ChainReplay
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.CoRoots.S5_804Completeness
import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_379

/-!
# Exact rank109 factor semantics and reversed ordered-envelope transport

The six frozen laws have sigma SHA-256
`76e3904fa36e45172e2a19e67ba54e326bcdde08ecc4ca90ba985078c6c76b65`.
The actual factors are S3_8 direct and S5_804 direct. Their necessary Key
pairs capped multiplicities with the exact ordered component-final signature.

Every reversed rank105 law has an explicit checked derivation from these
six laws. This permits reuse of individual envelope derivations; it does
NOT claim that the rank105 completeness theorem alone solves this coarser
intersection. The new pre-proof screen is bounded evidence only.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.Level2.Rank109

open SemigroupBasis
open SemigroupBasis.Examples

abbrev leftTable : FiniteTable := Generated.Catalogue.S3_8.table
abbrev rightTable : FiniteTable := Generated.Catalogue.S5_804.table

def law00 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
def law01 : Identity Nat := ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩
def law02 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩
def law03 : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩
def law04 : Identity Nat := ⟨⟨0, [1, 0, 2, 1]⟩, ⟨1, [0, 0, 2, 1]⟩⟩
def law05 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05]

def displayedBasisSHA256 : String :=
  "76e3904fa36e45172e2a19e67ba54e326bcdde08ecc4ca90ba985078c6c76b65"

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem leftModels : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)

theorem rightModels : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

/-- Literal table-coordinate identification, not a semantic analogy. -/
theorem leftTable_eq_exponent : leftTable = commutativeExponentThree := by
  unfold leftTable Generated.Catalogue.S3_8.table commutativeExponentThree
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext a b
  decide +revert

structure SameSignature (left right : Word Nat) : Prop where
  componentFinal : S5_804.SameConnectedCutSignature left right
  counts : ∀ tested, min (left.toList.count tested) 2 = min (right.toList.count tested) 2

theorem sameSignature_of_factorValid (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    SameSignature identity.lhs identity.rhs := by
  refine ⟨S5_804.valid_sameConnectedCutSignature identity rightValid, ?_⟩
  rw [leftTable_eq_exponent] at leftValid
  exact exponentValid_capped_count_eq identity leftValid

abbrev ListDerives : List Nat → List Nat → Prop := S5_107.ListDerives basis

theorem listDerives_cappedCounts {left right : List Nat} (derivation : ListDerives left right)
    (tested : Nat) : min (left.count tested) 2 = min (right.count tested) 2 := by
  cases derivation with
  | empty => rfl
  | @words leftHead rightHead leftTail rightTail proof =>
      let identity : Identity Nat := ⟨S5_107.listWordOfCons leftHead leftTail,
        S5_107.listWordOfCons rightHead rightTail⟩
      have valid : identity.SatisfiedBy leftTable.semigroup :=
        fun valuation => proof.sound leftModels valuation
      rw [leftTable_eq_exponent] at valid
      exact exponentValid_capped_count_eq identity valid tested

private def step (lawIndex : Nat) (direction : ChainReplay.Direction)
    (leftContext rightContext : List Nat) (substitution : List (List Nat)) :
    ChainReplay.Step Nat := {lawIndex, direction, leftContext, rightContext, substitution}

private def unchanged : List (List Nat) := [[0], [1], [2]]

theorem reverse105Law00 :
    Derives basis S3_16.Rank105.law00.reversed.lhs S3_16.Rank105.law00.reversed.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [step 0 .forward [] [] unchanged]) (by decide)

theorem reverse105Law01 :
    Derives basis S3_16.Rank105.law01.reversed.lhs S3_16.Rank105.law01.reversed.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [step 2 .backward [] [] unchanged]) (by decide)

theorem reverse105Law02 :
    Derives basis S3_16.Rank105.law02.reversed.lhs S3_16.Rank105.law02.reversed.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [step 1 .backward [] [] unchanged]) (by decide)

theorem reverse105Law03 :
    Derives basis S3_16.Rank105.law03.reversed.lhs S3_16.Rank105.law03.reversed.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [step 3 .forward [] [] [[1], [0], [2]]]) (by decide)

/-- xzxyx -> xxyzx -> xyzx -> xzyx. -/
theorem reverse105Law04 :
    Derives basis S3_16.Rank105.law04.reversed.lhs S3_16.Rank105.law04.reversed.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [step 5 .forward [] [] [[0], [2], [0, 1]],
      step 1 .forward [] [] [[0], [1, 2], [2]],
      step 5 .backward [] [] [[0], [2], [1]]]) (by decide)

/-- yzxyx -> yxzyx -> yxyzx -> xyyzx -> xzyyx. -/
theorem reverse105Law05 :
    Derives basis S3_16.Rank105.law05.reversed.lhs S3_16.Rank105.law05.reversed.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [step 5 .forward [] [0] [[1], [2], [0]],
      step 5 .forward [1] [] [[0], [2], [1]],
      step 4 .forward [] [] [[1], [0], [2]],
      step 5 .forward [] [] [[0], [1, 1], [2]]]) (by decide)

theorem reverse105Law06 :
    Derives basis S3_16.Rank105.law06.reversed.lhs S3_16.Rank105.law06.reversed.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [step 5 .forward [] [0] [[1], [2], [0]]]) (by decide)

/-- The final swap uses the genuine composite interior block yz. -/
theorem reverse105Law07 :
    Derives basis S3_16.Rank105.law07.reversed.lhs S3_16.Rank105.law07.reversed.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [step 5 .forward [] [0] [[1], [2], [0]],
      step 5 .forward [1] [] [[0], [2], [1]],
      step 4 .forward [] [] [[1], [0], [2]],
      step 5 .forward [] [] [[0], [1], [1, 2]]]) (by decide)

theorem reverse105Law08 :
    Derives basis S3_16.Rank105.law08.reversed.lhs S3_16.Rank105.law08.reversed.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := [step 4 .forward [] [] [[2], [0], [1]]]) (by decide)

theorem reversed105AxiomsDerive (identity : Identity Nat)
    (member : identity ∈ reversedBasis S3_16.Rank105.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [S3_16.Rank105.basis, reversedBasis, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reverse105Law00
  · exact reverse105Law01
  · exact reverse105Law02
  · exact reverse105Law03
  · exact reverse105Law04
  · exact reverse105Law05
  · exact reverse105Law06
  · exact reverse105Law07
  · exact reverse105Law08

/-- Transport real frozen-law derivations after literal word reversal. -/
theorem reverseTransport {left right : Word Nat}
    (derivation : Derives S3_16.Rank105.basis left right) :
    Derives basis left.reverse right.reverse :=
  derivation.reverse.transport reversed105AxiomsDerive

theorem reverseListTransport {left right : List Nat}
    (derivation : S3_16.Rank105.ListDerives left right) :
    ListDerives left.reverse right.reverse := by
  cases derivation with
  | empty => exact S5_107.ListDerives.empty
  | @words leftHead rightHead leftTail rightTail proof =>
      have result := S5_107.ListDerives.ofWord (reverseTransport proof)
      change ListDerives (S5_107.listWordOfCons leftHead leftTail).reverse.toList
        (S5_107.listWordOfCons rightHead rightTail).reverse.toList at result
      rw [Word.toList_reverse, Word.toList_reverse] at result
      exact result

private def instantiateThreeWords (left middle right : Word Nat) : Nat → Word Nat
  | 0 => left
  | 1 => middle
  | _ => right

theorem derivesClosedInteriorSwap (endpoint left right : Word Nat) :
    Derives basis (((endpoint ++ left) ++ right) ++ endpoint)
      (((endpoint ++ right) ++ left) ++ endpoint) := by
  have base : Derives basis law05.lhs law05.rhs :=
    Derives.fromBasis (e := law05) (by simp [basis])
  have substituted := Derives.subst base (instantiateThreeWords endpoint left right)
  simpa [law05, instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

end SemigroupBasis.CoRoots.Order6Day7.Level2.Rank109
