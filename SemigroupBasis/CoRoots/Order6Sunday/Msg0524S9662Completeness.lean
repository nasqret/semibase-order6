import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey
import SemigroupBasis.Opposite

/-! Exact seven-law S9662 completeness. Prefix permutations and supported
insertions construct a common union prefix. No reach premise, finite window,
or completeness theorem for another semigroup is assumed. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662Completeness

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey

/-- The prescribed seven laws, in their recorded order and orientation. -/
def basis : List (Identity Nat) :=
  [⟨snoc [0, 0] 0, snoc [0, 0, 0] 0⟩,
   ⟨snoc [0, 0] 1, snoc [0, 0, 0] 1⟩,
   ⟨snoc [0, 1] 0, snoc [1, 0] 0⟩,
   ⟨snoc [0, 1] 0, snoc [0, 0, 1] 0⟩,
   ⟨snoc [0, 1] 0, snoc [0, 1, 1] 0⟩,
   ⟨snoc [0, 1] 2, snoc [1, 0] 2⟩,
   ⟨snoc [0, 1] 2, snoc [0, 0, 1] 2⟩]

theorem models : Models (table 3).semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply valid_of_key
  all_goals refine ⟨rfl, rfl, ?_⟩
  all_goals intro marker
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false]
  · simp
  · simp
  · exact or_comm
  · simp
  · simp
  · exact or_comm
  · simp

theorem snoc_cons (a : Nat) (stem : List Nat) (last : Nat) :
    snoc (a :: stem) last = Word.singleton a ++ snoc stem last := by
  cases stem <;> rfl

private def instantiateThreeWords (u v suffix : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => suffix
  | n + 3 => Word.singleton (n + 3)

theorem derivesPrefixSwap (u v suffix : Word Nat) :
    Derives basis ((u ++ v) ++ suffix) ((v ++ u) ++ suffix) := by
  have base : Derives basis (snoc [0, 1] 2) (snoc [1, 0] 2) :=
    Derives.fromBasis (e := ⟨snoc [0, 1] 2, snoc [1, 0] 2⟩) (by simp [basis])
  have substituted := Derives.subst base (instantiateThreeWords u v suffix)
  simpa [snoc, instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesLongDuplication (u v suffix : Word Nat) :
    Derives basis ((u ++ v) ++ suffix) (((u ++ u) ++ v) ++ suffix) := by
  have base : Derives basis (snoc [0, 1] 2) (snoc [0, 0, 1] 2) :=
    Derives.fromBasis (e := ⟨snoc [0, 1] 2, snoc [0, 0, 1] 2⟩) (by simp [basis])
  have substituted := Derives.subst base (instantiateThreeWords u v suffix)
  simpa [snoc, instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesPrefixPermutation {left right : List Nat}
    (permutation : left.Perm right) (last : Nat) :
    Derives basis (snoc left last) (snoc right last) := by
  induction permutation with
  | nil => exact Derives.refl _
  | cons x _ ih =>
      simpa only [snoc_cons] using Derives.prepend (Word.singleton x) ih
  | swap x y rest =>
      simpa only [snoc_cons, Word.append_assoc] using
        derivesPrefixSwap (Word.singleton y) (Word.singleton x) (snoc rest last)
  | trans _ _ first second => exact first.trans second

theorem derivesInsertSupportedPrefix (stem : List Nat) (last marker : Nat)
    (member : marker ∈ stem) (long : 2 ≤ stem.length) :
    Derives basis (snoc stem last) (snoc (marker :: stem) last) := by
  have expose : stem.Perm (marker :: stem.erase marker) := List.perm_cons_erase member
  have arranged := derivesPrefixPermutation expose last
  have restNonempty : stem.erase marker ≠ [] := by
    intro empty
    have lengthOne : stem.length = 1 := by simpa [empty] using expose.length_eq
    rw [lengthOne] at long
    exact (by decide : ¬ (2 ≤ 1)) long
  have duplicate : Derives basis (snoc (marker :: stem.erase marker) last)
      (snoc (marker :: marker :: stem.erase marker) last) := by
    cases restEq : stem.erase marker with
    | nil => exact False.elim (restNonempty restEq)
    | cons next rest =>
        have step := derivesLongDuplication (Word.singleton marker) (Word.mk next rest)
          (Word.singleton last)
        change Derives basis (snoc (marker :: next :: rest) last)
          (snoc (marker :: marker :: next :: rest) last) at step
        exact step
  have restore : (marker :: marker :: stem.erase marker).Perm (marker :: stem) :=
    (List.Perm.cons marker expose).symm
  exact arranged.trans (duplicate.trans (derivesPrefixPermutation restore last))

theorem derivesInsertList (stem extra : List Nat) (last : Nat)
    (long : 2 ≤ stem.length) (supported : ∀ x ∈ extra, x ∈ stem) :
    Derives basis (snoc stem last) (snoc (extra ++ stem) last) := by
  induction extra with
  | nil => exact Derives.refl _
  | cons x rest ih =>
      have first := ih (fun y hy => supported y (by simp [hy]))
      have present : x ∈ rest ++ stem :=
        List.mem_append.mpr (Or.inr (supported x (by simp)))
      have longer : 2 ≤ (rest ++ stem).length :=
        Nat.le_trans long (by simp [List.length_append])
      exact first.trans (derivesInsertSupportedPrefix (rest ++ stem) last x present longer)

theorem derivesLongPrefixSupport (left right : List Nat) (last : Nat)
    (leftLong : 2 ≤ left.length) (rightLong : 2 ≤ right.length)
    (support : ∀ x, x ∈ left ↔ x ∈ right) :
    Derives basis (snoc left last) (snoc right last) := by
  have first := derivesInsertList left right last leftLong
    (fun x hx => (support x).mpr hx)
  have second := derivesInsertList right left last rightLong
    (fun x hx => (support x).mp hx)
  have middle := derivesPrefixPermutation
    (List.perm_append_comm : (right ++ left).Perm (left ++ right)) last
  exact first.trans (middle.trans second.symm)

theorem derives_of_cut_key (left right : List Nat) (a b : Nat)
    (key : SameCutKey left a right b) :
    Derives basis (snoc left a) (snoc right b) := by
  rcases key with ⟨degree, finalSame, support⟩
  subst b
  cases left with
  | nil =>
      cases right with
      | nil => exact Derives.refl _
      | cons c rest => cases rest <;> simp [depth] at degree
  | cons c rest =>
      cases rest with
      | nil =>
          cases right with
          | nil => simp [depth] at degree
          | cons d rest =>
              cases rest with
              | nil =>
                  have same : c = d := by
                    have present := (support c).mp (by simp)
                    simpa using present
                  subst d
                  exact Derives.refl _
              | cons e rest => simp [depth] at degree
      | cons d rest =>
          cases right with
          | nil => simp [depth] at degree
          | cons e tail =>
              cases tail with
              | nil => simp [depth] at degree
              | cons f tail =>
                  exact derivesLongPrefixSupport _ _ a (by simp) (by simp) support

theorem complete (identity : Identity Nat) (valid : identity.SatisfiedBy (table 3).semigroup) :
    Derives basis identity.lhs identity.rhs := by
  rcases (semantic_key_iff identity.lhs identity.rhs).mp valid with
    ⟨leftStem, a, rightStem, b, hl, hr, key⟩
  rw [hl, hr]
  exact derives_of_cut_key leftStem rightStem a b key

theorem representative_basis : BasisFor (table 3).semigroup basis := ⟨models, complete⟩

theorem opposite_basis : BasisFor (table 3).semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662Completeness
