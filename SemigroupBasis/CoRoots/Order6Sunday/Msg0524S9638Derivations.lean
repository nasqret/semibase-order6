import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638SemanticKey

/-! Four-law calculus for S9638. A two-letter buffer lets the nonempty
suffix normalize by first occurrences without collapsing the short grade. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638Derivations

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey (snoc)
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642SemanticKey (UniqueInitial)
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638SemanticKey

def basis : List (Identity Nat) :=
  [⟨snoc [0,1] 0, snoc [0,0] 1⟩,
   ⟨snoc [0,1] 2, snoc [0,1,1] 2⟩,
   ⟨snoc [0,1] 2, snoc [0,1,2] 2⟩,
   ⟨snoc [0,1,2] 1, snoc [0,1] 2⟩]

theorem models : Models (table 0).semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals apply valid_of_key
  all_goals refine ⟨rfl, by decide, ?_⟩
  all_goals intro marker
  all_goals simp [UniqueInitial, snoc, eq_comm]
  all_goals intros
  all_goals simp_all

private def substitute (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

theorem derivesHeadReturn (x y : Word Nat) :
    Derives basis (x ++ (y ++ x)) (x ++ (x ++ y)) := by
  have base : Derives basis (Word.mk 0 [1,0]) (Word.mk 0 [0,1]) :=
    Derives.fromBasis (e := ⟨⟨0,[1,0]⟩,⟨0,[0,1]⟩⟩) (by simp [basis, snoc])
  simpa [substitute, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using Derives.subst base (substitute x y (Word.singleton 0))

theorem derivesMiddleDuplication (x y z : Word Nat) :
    Derives basis (x ++ (y ++ z)) (x ++ (y ++ (y ++ z))) := by
  have base : Derives basis (Word.mk 0 [1,2]) (Word.mk 0 [1,1,2]) :=
    Derives.fromBasis (e := ⟨⟨0,[1,2]⟩,⟨0,[1,1,2]⟩⟩) (by simp [basis, snoc])
  simpa [substitute, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using Derives.subst base (substitute x y z)

theorem derivesLastDuplication (x y z : Word Nat) :
    Derives basis (x ++ (y ++ z)) (x ++ (y ++ (z ++ z))) := by
  have base : Derives basis (Word.mk 0 [1,2]) (Word.mk 0 [1,2,2]) :=
    Derives.fromBasis (e := ⟨⟨0,[1,2]⟩,⟨0,[1,2,2]⟩⟩) (by simp [basis, snoc])
  simpa [substitute, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using Derives.subst base (substitute x y z)

theorem derivesReturnDeletion (front letter middle : Word Nat) :
    Derives basis (front ++ (letter ++ (middle ++ letter))) (front ++ (letter ++ middle)) := by
  have base : Derives basis (Word.mk 0 [1,2,1]) (Word.mk 0 [1,2]) :=
    Derives.fromBasis (e := ⟨⟨0,[1,2,1]⟩,⟨0,[1,2]⟩⟩) (by simp [basis, snoc])
  simpa [substitute, Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using Derives.subst base (substitute front letter middle)

theorem buffered_append (u v : Word Nat) (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat) :
    (((u ++ v) ++ Word.mk x xs) ++ Word.mk y ys) =
      (u ++ v) ++ Word.mk x (xs ++ y :: ys) := by
  rw [Word.append_assoc]
  rfl

theorem derivesEraseAfter (u v : Word Nat) (x : Nat) (before after : List Nat) :
    Derives basis ((u ++ v) ++ Word.mk x (before ++ x :: after))
      ((u ++ v) ++ Word.mk x (before ++ after)) := by
  have core : Derives basis ((u ++ v) ++ Word.mk x (before ++ [x]))
      ((u ++ v) ++ Word.mk x before) := by
    cases before with
    | nil =>
        simpa only [Word.append_assoc] using (derivesLastDuplication u v (Word.singleton x)).symm
    | cons a rest =>
        simpa only [Word.append_assoc] using
          derivesReturnDeletion (u ++ v) (Word.singleton x) (Word.mk a rest)
  cases after with
  | nil => simpa only [List.append_nil] using core
  | cons a rest =>
      have extended := Derives.appendRight core (Word.mk a rest)
      rw [buffered_append, buffered_append] at extended
      simpa only [List.append_assoc, List.singleton_append] using extended

theorem derivesFilterAfter (u v : Word Nat) (x : Nat) (before after : List Nat) :
    Derives basis ((u ++ v) ++ Word.mk x (before ++ after))
      ((u ++ v) ++ Word.mk x (before ++ after.filter (fun y => decide (y ≠ x)))) := by
  induction after generalizing before with
  | nil => exact Derives.refl _
  | cons y rest ih =>
      by_cases same : y = x
      · subst y
        have first := derivesEraseAfter u v x before rest
        simpa [List.filter_cons] using first.trans (ih before)
      · simpa [List.filter_cons, same, List.append_assoc] using ih (before ++ [y])

def suffixNormal (word : Word Nat) : Word Nat :=
  ⟨word.head, (firstOccurrenceSequence word.tail).filter (fun y => decide (y ≠ word.head))⟩

theorem suffixNormal_toList (word : Word Nat) :
    (suffixNormal word).toList = firstOccurrenceSequence word.toList := by
  cases word
  rfl

theorem derivesNormalizeBuffered (u v : Word Nat) (head : Nat) (tail : List Nat) :
    Derives basis ((u ++ v) ++ Word.mk head tail)
      ((u ++ v) ++ suffixNormal (Word.mk head tail)) := by
  induction tail generalizing u v head with
  | nil => exact Derives.refl _
  | cons b rest ih =>
      have first : Derives basis ((u ++ v) ++ Word.mk head (b :: rest))
          ((u ++ v) ++ Word.mk head (suffixNormal (Word.mk b rest)).toList) := by
        simpa only [Word.append_assoc] using ih u (v ++ Word.singleton head) b
      rw [suffixNormal_toList] at first
      exact first.trans (derivesFilterAfter u v head [] (firstOccurrenceSequence (b :: rest)))

theorem derivesBufferedSameOrder (u v : Word Nat) (a b : Nat) (left right : List Nat)
    (order : firstOccurrenceSequence (a :: left) = firstOccurrenceSequence (b :: right)) :
    Derives basis ((u ++ v) ++ Word.mk a left) ((u ++ v) ++ Word.mk b right) := by
  have first := derivesNormalizeBuffered u v a left
  have second := derivesNormalizeBuffered u v b right
  have equal : suffixNormal (Word.mk a left) = suffixNormal (Word.mk b right) := by
    apply Word.toList_injective
    rw [suffixNormal_toList, suffixNormal_toList]
    exact order
  rw [equal] at first
  exact first.trans second.symm

theorem derivesLongNormal (head second : Nat) (tail : List Nat) (nonempty : tail ≠ []) :
    Derives basis (Word.mk head (second :: tail))
      ((Word.singleton head ++ Word.singleton second) ++ suffixNormal (Word.mk second tail)) := by
  cases tail with
  | nil => exact False.elim (nonempty rfl)
  | cons third rest =>
      have first : Derives basis (Word.mk head (second :: third :: rest))
          ((Word.singleton head ++ Word.singleton second) ++ Word.mk second (third :: rest)) := by
        simpa only [Word.append_assoc] using
          derivesMiddleDuplication (Word.singleton head) (Word.singleton second) (Word.mk third rest)
      exact first.trans (derivesNormalizeBuffered (Word.singleton head) (Word.singleton second) second (third :: rest))

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638Derivations
