import SemigroupBasis.Normalization.StagedNormalization

/-!
# Lee--Li P2 group G2: shared source contract

This module records the proposed two-law basis for the sixteen order-six roots
in group G2 of mailbox packet `msg-0050-g1-g2-exact-bases` and isolates the
remaining all-alphabet combinatorics.

The support component below is represented by a sorted duplicate-free list,
rather than a `Finset`, so the invariant remains directly computable with the
repository's mathlib-free core.  No member semigroup is claimed here.  A member
becomes complete only after supplying both a `NormalizationWitness` and a
semantic `InvariantSeparation` proof.
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G2

open SemigroupBasis
open SemigroupBasis.Normalization

/-! ## The two laws -/

def xyzw : Word Nat := ⟨0, [1, 2, 3]⟩
def yxzw : Word Nat := ⟨1, [0, 2, 3]⟩
def yx : Word Nat := ⟨0, [1]⟩
def yyx : Word Nat := ⟨0, [0, 1]⟩

/-- Interior commutation: `xyzw = yxzw`. -/
def interiorCommutationLaw : Identity Nat := ⟨xyzw, yxzw⟩

/-- Left duplication: `yx = yyx`.  The concrete variable names are immaterial;
the stored orientation is `01 = 001`. -/
def leftDuplicationLaw : Identity Nat := ⟨yx, yyx⟩

def basis : List (Identity Nat) :=
  [interiorCommutationLaw, leftDuplicationLaw]

private def instantiateFourWords
    (u v z w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | 3 => w
  | n + 4 => Word.singleton (n + 4)

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- Law A swaps two adjacent nonempty factors whenever two nonempty factors
remain to their right.  This is the local step used by interior sorting. -/
theorem derivesInteriorSwap (u v z w : Word Nat) :
    Derives basis
      (((u ++ v) ++ z) ++ w)
      (((v ++ u) ++ z) ++ w) := by
  have base : Derives basis xyzw yxzw :=
    Derives.fromBasis (e := interiorCommutationLaw) (by
      exact List.Mem.head _)
  have substituted := Derives.subst base (instantiateFourWords u v z w)
  simpa [basis, interiorCommutationLaw, xyzw, yxzw,
    instantiateFourWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Law B duplicates the first nonempty factor in front of a nonempty suffix.
Its reverse is the contraction step used after sorting and its forward
direction is the padding step used in the repeat case. -/
theorem derivesLeftDuplication (u v : Word Nat) :
    Derives basis (u ++ v) ((u ++ u) ++ v) := by
  have base : Derives basis yx yyx :=
    Derives.fromBasis (e := leftDuplicationLaw) (by
      exact List.Mem.tail _ (List.Mem.head _))
  have substituted := Derives.subst base (instantiateTwoWords u v)
  simpa [basis, leftDuplicationLaw, yx, yyx, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesLeftContraction (u v : Word Nat) :
    Derives basis ((u ++ u) ++ v) (u ++ v) :=
  (derivesLeftDuplication u v).symm

/-! ## The all-alphabet invariant and canonical word -/

/-- Keep one copy of each letter.  Sorting is performed separately so this
helper does not impose an order on an arbitrary intermediate list. -/
def deduplicateSupport : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ rest then deduplicateSupport rest
      else letter :: deduplicateSupport rest

def sortedSupport (word : Word Nat) : List Nat :=
  (deduplicateSupport word.toList).mergeSort
    (fun left right : Nat => decide (left ≤ right))

/-- The final two letters, in reading order.  A singleton has no
second-to-last letter. -/
def trailingPair (word : Word Nat) : Option (Nat × Nat) :=
  match word.toList.reverse with
  | last :: penultimate :: _ => some (penultimate, last)
  | _ => none

def finalLetter (word : Word Nat) : Nat :=
  match word.toList.reverse with
  | last :: _ => last
  | [] => word.head

/-- `fresh = true` means that the final occurrence of the final letter is also
its first occurrence. -/
def finalIsFresh (word : Word Nat) : Bool :=
  decide (word.toList.count (finalLetter word) = 1)

structure Invariant where
  support : List Nat
  secondToLast : Option Nat
  last : Nat
  fresh : Bool
deriving Repr, DecidableEq

def invariant (word : Word Nat) : Invariant :=
  let pair := trailingPair word
  { support := sortedSupport word
    secondToLast := pair.map Prod.fst
    last := finalLetter word
    fresh := finalIsFresh word }

private def renderPrefixAndLastTwo
    (stem : List Nat) (penultimate last : Nat) : Word Nat :=
  match stem with
  | [] => ⟨penultimate, [last]⟩
  | head :: tail => ⟨head, tail ++ [penultimate, last]⟩

private def freshPrefix
    (support : List Nat) (penultimate last : Nat) : List Nat :=
  support.filter
    (fun letter => decide (letter ≠ penultimate ∧ letter ≠ last))

/-- Canonical form determined by the G2 invariant.

* singleton: the final letter;
* fresh final occurrence: sorted support with the two terminal letters removed,
  followed by those terminal letters;
* repeated final occurrence: all sorted support letters, followed by the two
  terminal letters.
-/
def canonical (key : Invariant) : Word Nat :=
  match key.secondToLast with
  | none => Word.singleton key.last
  | some penultimate =>
      if key.fresh then
        renderPrefixAndLastTwo
          (freshPrefix key.support penultimate key.last)
          penultimate key.last
      else
        renderPrefixAndLastTwo key.support penultimate key.last

def normalForm (word : Word Nat) : Word Nat :=
  canonical (invariant word)

/-- The interior consists of all letters except the final two. -/
def interior (word : Word Nat) : List Nat :=
  word.toList.dropLast.dropLast

/-! ## Three-stage normalization contract -/

/-- The exact remaining combinatorial obligation for the G2 normalizer.

The fields deliberately expose three independent derivational stages:
sorting by law A, duplicate contraction by reverse law B, and repeat-case
support padding by forward law B.  The final equality is pure list
combinatorics.  Constructing a value of this structure is the main unresolved
Lean goal; declaring the interface does not assert that such a value exists. -/
structure NormalizationWitness where
  sortInterior : Word Nat → Word Nat
  collapseInteriorDuplicates : Word Nat → Word Nat
  padRepeatMissingSupport : Word Nat → Word Nat
  sort_derives : ∀ word,
    Derives basis word (sortInterior word)
  sort_invariant : ∀ word,
    invariant (sortInterior word) = invariant word
  sort_sorted : ∀ word,
    (interior (sortInterior word)).Pairwise (· ≤ ·)
  collapse_derives : ∀ word,
    Derives basis (sortInterior word)
      (collapseInteriorDuplicates (sortInterior word))
  collapse_invariant : ∀ word,
    invariant (collapseInteriorDuplicates (sortInterior word)) =
      invariant word
  collapse_nodup : ∀ word,
    (interior (collapseInteriorDuplicates (sortInterior word))).Nodup
  pad_derives : ∀ word,
    Derives basis
      (collapseInteriorDuplicates (sortInterior word))
      (padRepeatMissingSupport
        (collapseInteriorDuplicates (sortInterior word)))
  pad_invariant : ∀ word,
    invariant
        (padRepeatMissingSupport
          (collapseInteriorDuplicates (sortInterior word))) =
      invariant word
  result_eq_canonical : ∀ word,
    padRepeatMissingSupport
        (collapseInteriorDuplicates (sortInterior word)) =
      normalForm word

namespace NormalizationWitness

theorem derives_sortInterior (witness : NormalizationWitness)
    (word : Word Nat) :
    Derives basis word (witness.sortInterior word) :=
  witness.sort_derives word

theorem derives_collapseInteriorDuplicates
    (witness : NormalizationWitness) (word : Word Nat) :
    Derives basis (witness.sortInterior word)
      (witness.collapseInteriorDuplicates
        (witness.sortInterior word)) :=
  witness.collapse_derives word

theorem derives_padRepeatMissingSupport
    (witness : NormalizationWitness) (word : Word Nat) :
    Derives basis
      (witness.collapseInteriorDuplicates
        (witness.sortInterior word))
      (witness.padRepeatMissingSupport
        (witness.collapseInteriorDuplicates
          (witness.sortInterior word))) :=
  witness.pad_derives word

/-- Compose the three independently auditable stages. -/
theorem derives_normalForm (witness : NormalizationWitness)
    (word : Word Nat) : Derives basis word (normalForm word) := by
  have sorted := witness.derives_sortInterior word
  have collapsed := witness.derives_collapseInteriorDuplicates word
  have padded := witness.derives_padRepeatMissingSupport word
  rw [witness.result_eq_canonical word] at padded
  exact sorted.trans (collapsed.trans padded)

end NormalizationWitness

/-! ## Generic completeness endpoint -/

/-- Semantic separation says that every identity valid in a member has equal
G2 invariants on its two sides.  For a concrete order-six member this is the
second honest proof obligation, independent of normalization. -/
def InvariantSeparation (G : Semigroup S) : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy G →
      invariant identity.lhs = invariant identity.rhs

/-- A normalizer and semantic invariant separation turn model checking of the
two displayed laws into a complete basis theorem. -/
theorem basisFor_of_models_invariantSeparation
    {G : Semigroup S}
    (models : Models G basis)
    (witness : NormalizationWitness)
    (separates : InvariantSeparation G) :
    BasisFor G basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  have sameInvariant := separates identity valid
  have sameNormal : normalForm identity.lhs = normalForm identity.rhs :=
    congrArg canonical sameInvariant
  exact (witness.derives_normalForm identity.lhs).trans <| by
    rw [sameNormal]
    exact (witness.derives_normalForm identity.rhs).symm

end SemigroupBasis.CoRoots.Order6LeeLiP2G2
