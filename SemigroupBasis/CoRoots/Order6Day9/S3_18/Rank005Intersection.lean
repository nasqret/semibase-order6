import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank005GuardedReplay
import SemigroupBasis.CoRoots.S5_1000Family
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.Generated.S2_4

/-!
# Full unrestricted C3 × S4_62 intersection over the original eleven laws

The two small embeddings below are internal factor-theory witnesses, not
six-element class subdirect witnesses.  S4_62 provides the actual head and
final-marker semantics; C3 provides multiplicities modulo three.  Together
they supply the independently complete S5_1000 signature.  A temporary triple
of the common head is removed by the raw fourth-power prefix law.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank005Intersection

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank005GuardedReplay

theorem leftTable_eq_cyclicThree : leftTable = cyclicThree := by
  unfold leftTable Generated.Catalogue.S3_18.table cyclicThree
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext first second
  decide +revert

/-- The three-state terminal marker is the actual {0,1,2} subsemigroup. -/
def markerEmbedding : Embedding finalMarkerThree.semigroup rightTable.semigroup where
  toFun := fun value =>
    if value.val = 0 then (0 : Fin 4) else
      if value.val = 1 then (1 : Fin 4) else (2 : Fin 4)
  map_mul := by
    intro first second
    apply Fin.ext
    revert first second
    decide
  injective := by
    intro first second equal
    revert first second
    decide

/-- The two actual idempotents {2,3} form the head-detecting left-zero factor. -/
def headEmbedding :
    Embedding Generated.S2_4.table.semigroup rightTable.semigroup where
  toFun := fun value => if value.val = 0 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by
    intro first second
    apply Fin.ext
    revert first second
    decide
  injective := by
    intro first second equal
    revert first second
    decide

theorem rightValid_marker
    (identity : Identity Nat) (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.SatisfiedBy finalMarkerThree.semigroup :=
  markerEmbedding.pullback_identity identity valid

theorem rightValid_head
    (identity : Identity Nat) (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have headValid := headEmbedding.pullback_identity identity valid
  change identity.SatisfiedBy leftZeroTwo.semigroup at headValid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := headValid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

private theorem finalMarkerZeroFold (tail : List Nat) :
    tail.foldl
      (fun current (_ : Nat) =>
        finalMarkerThree.semigroup.mul current (1 : Fin 3))
      (0 : Fin 3) = (0 : Fin 3) := by
  induction tail with
  | nil => rfl
  | cons first rest induction =>
      simpa [finalMarkerThree, finalMarkerThreeMul,
        FiniteTable.semigroup] using induction

theorem finalMarkerSingletonSeparator (word : Word Nat) :
    finalMarkerThree.semigroup.eval (fun _ => (1 : Fin 3)) word =
        (1 : Fin 3) ↔ word.tail = [] := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => simp [Semigroup.eval]
      | cons first rest =>
          change
            rest.foldl
                (fun current (_ : Nat) =>
                  finalMarkerThree.semigroup.mul current (1 : Fin 3))
                (finalMarkerThree.semigroup.mul (1 : Fin 3) (1 : Fin 3)) =
                (1 : Fin 3) ↔ first :: rest = []
          change
            rest.foldl
                (fun current (_ : Nat) =>
                  finalMarkerThree.semigroup.mul current (1 : Fin 3))
                (0 : Fin 3) = (1 : Fin 3) ↔ first :: rest = []
          rw [finalMarkerZeroFold]
          exact iff_of_false (by decide) (by simp)

theorem rightValid_tail_nil_iff
    (identity : Identity Nat) (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.lhs.tail = [] ↔ identity.rhs.tail = [] := by
  have markerValid := rightValid_marker identity valid
  have evaluated := markerValid (fun _ => (1 : Fin 3))
  constructor
  · intro leftSingleton
    apply (finalMarkerSingletonSeparator identity.rhs).mp
    rw [← evaluated]
    exact (finalMarkerSingletonSeparator identity.lhs).mpr leftSingleton
  · intro rightSingleton
    apply (finalMarkerSingletonSeparator identity.lhs).mp
    rw [evaluated]
    exact (finalMarkerSingletonSeparator identity.rhs).mpr rightSingleton

/-- Actual joint validity supplies the complete support/mod-three/simple-final
signature and hence an unrestricted derivation in the four-law lower calculus. -/
theorem lowerDerivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives lowerBasis identity.lhs identity.rhs := by
  have residueValid : identity.SatisfiedBy cyclicThree.semigroup := by
    exact Eq.mp
      (congrArg (fun table : FiniteTable => identity.SatisfiedBy table.semigroup)
        leftTable_eq_cyclicThree) leftValid
  have signature :=
    SemigroupBasis.CoRoots.S5_1000Invariant.sameSignature_of_marker_residue_valid
      identity (rightValid_marker identity rightValid) residueValid
  exact SemigroupBasis.CoRoots.S5_1000.derivesOfSameSignature signature

/-- Full unrestricted C3/S4_62 intersection completeness over the RAW eleven
laws, including literal singleton and arbitrary longer-word strata. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads := rightValid_head identity rightValid
  have singletonIff := rightValid_tail_nil_iff identity rightValid
  have lower := lowerDerivesOfFactorValid identity leftValid rightValid
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  change leftHead = rightHead at heads
  change leftTail = [] ↔ rightTail = [] at singletonIff
  subst rightHead
  cases leftTail with
  | nil =>
      have rightNil : rightTail = [] := singletonIff.mp rfl
      subst rightTail
      exact Derives.refl _
  | cons leftSecond leftRest =>
      cases rightTail with
      | nil =>
          have impossible : leftSecond :: leftRest = [] := singletonIff.mpr rfl
          simp at impossible
      | cons rightSecond rightRest =>
          let fixed := Word.singleton leftHead
          let leftSuffix : Word Nat := ⟨leftSecond, leftRest⟩
          let rightSuffix : Word Nat := ⟨rightSecond, rightRest⟩
          let triple := (fixed ++ fixed) ++ fixed
          let quadruple := ((fixed ++ fixed) ++ fixed) ++ fixed
          have lifted := liftLowerWithPrefixIdentity lower triple
          have prefixed :
              Derives basis (quadruple ++ leftSuffix) (quadruple ++ rightSuffix) := by
            simpa [fixed, leftSuffix, rightSuffix, triple, quadruple,
              Word.singleton, Word.append, Word.append_assoc] using lifted
          have leftExpanded :
              Derives basis
                (Word.mk leftHead (leftSecond :: leftRest))
                (quadruple ++ leftSuffix) := by
            simpa [fixed, leftSuffix, quadruple, Word.singleton, Word.append] using
              derivesPrefixExpansion fixed leftSuffix
          have rightExpanded :
              Derives basis
                (Word.mk leftHead (rightSecond :: rightRest))
                (quadruple ++ rightSuffix) := by
            simpa [fixed, rightSuffix, quadruple, Word.singleton, Word.append] using
              derivesPrefixExpansion fixed rightSuffix
          exact leftExpanded.trans (prefixed.trans rightExpanded.symm)

theorem factor_valid_iff_derives (identity : Identity Nat) :
    (identity.SatisfiedBy leftTable.semigroup ∧
      identity.SatisfiedBy rightTable.semigroup) ↔
      Derives basis identity.lhs identity.rhs := by
  constructor
  · rintro ⟨leftValid, rightValid⟩
    exact derivesOfFactorValid identity leftValid rightValid
  · intro derivation
    exact ⟨derivation.sound modelsLeft, derivation.sound modelsRight⟩

def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

noncomputable def intersectionNormalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The seven historical bounded-separator extensions, in their frozen order.
The four independently normalized four-variable laws are literally equal. -/
def sevenExtensionLaws : List (Identity Nat) :=
  [⟨Word.mk 0 [0, 0, 1, 2, 0], Word.mk 0 [1, 1, 1, 2, 1]⟩,
   ⟨Word.mk 0 [1, 1, 1, 2, 1], Word.mk 0 [1, 2, 0, 0, 0]⟩,
   ⟨Word.mk 0 [1, 0, 0, 2, 0], Word.mk 0 [1, 1, 1, 2, 1]⟩,
   ⟨Word.mk 0 [1, 2, 3, 0], Word.mk 0 [1, 3, 2, 0]⟩,
   ⟨Word.mk 0 [1, 2, 3, 0], Word.mk 0 [1, 3, 2, 0]⟩,
   ⟨Word.mk 0 [1, 2, 3, 0], Word.mk 0 [1, 3, 2, 0]⟩,
   ⟨Word.mk 0 [1, 2, 3, 0], Word.mk 0 [1, 3, 2, 0]⟩]

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem sevenExtensionLaws_leftModels :
    Models leftTable.semigroup sevenExtensionLaws :=
  FiniteCertificate.checkModels_sound leftTable sevenExtensionLaws toFinFour
    (by decide)

theorem sevenExtensionLaws_rightModels :
    Models rightTable.semigroup sevenExtensionLaws :=
  FiniteCertificate.checkModels_sound rightTable sevenExtensionLaws toFinFour
    (by decide)

/-- The bounded closure splits do not obstruct unrestricted derivability:
each of the seven old extensions is a CONSEQUENCE of the raw eleven laws. -/
theorem sevenExtensionLaws_deriveRawBasis
    (identity : Identity Nat) (member : identity ∈ sevenExtensionLaws) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfFactorValid identity
    (sevenExtensionLaws_leftModels identity member)
    (sevenExtensionLaws_rightModels identity member)

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank005Intersection
