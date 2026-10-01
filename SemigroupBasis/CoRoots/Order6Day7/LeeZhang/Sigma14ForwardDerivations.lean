import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14Presentations
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708Sigma12Normalization

/-! Unrestricted derivational preparation for the two unapproved Sigma14
statements. These are explicit consequences of the displayed laws, never a
semantic-to-derivability completeness field for an unapproved class.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14

open SemigroupBasis
open S6_2708.Sigma12
open S4_71Suffix (put put_toList put_word)

theorem core_to_swap {left right : Word Nat} (derivation : Derives coreBasis left right) :
    Derives swapBasis left right :=
  Derives.transport (fun identity member =>
    Derives.fromBasis (sigma12_subset_swap identity (core_subset_sigma12 identity member))) derivation

theorem core_to_absorb {left right : Word Nat} (derivation : Derives coreBasis left right) :
    Derives absorbBasis left right :=
  Derives.transport (fun identity member =>
    Derives.fromBasis (sigma12_subset_absorb identity (core_subset_sigma12 identity member))) derivation

theorem derives_base_normal_swap (word : Word Nat) : Derives swapBasis word (normalForm word) :=
  core_to_swap (derives_normalForm word)
theorem derives_base_normal_absorb (word : Word Nat) : Derives absorbBasis word (normalForm word) :=
  core_to_absorb (derives_normalForm word)

private def sub2 (x y : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | letter + 2 => Word.singleton (letter + 2)

theorem swap_sandwich_square (x middle : Word Nat) :
    Derives swapBasis ((x ++ middle) ++ x) (middle ++ (x ++ x)) := by
  have primitive : Derives swapBasis swapLaw12.lhs swapLaw12.rhs :=
    Derives.fromBasis (by simp [swapBasis])
  simpa [swapLaw12, sub2, Word.bind, Word.append, Word.append_assoc] using primitive.subst (sub2 x middle)

/-- The second extra law is retained literally, although the first derives it. -/
theorem swapLaw13_derived_from12 : Derives swapBasis swapLaw13.lhs swapLaw13.rhs := by
  simpa [swapLaw13, Word.singleton, Word.append] using
    (swap_sandwich_square (Word.singleton 1) (Word.singleton 0)).symm

theorem absorb_sandwich_cube (x middle : Word Nat) :
    Derives absorbBasis ((x ++ middle) ++ x) (middle ++ ((x ++ x) ++ x)) := by
  have primitive : Derives absorbBasis absorbLaw12.lhs absorbLaw12.rhs :=
    Derives.fromBasis (by simp [absorbBasis])
  have first : Derives absorbBasis ((x ++ middle) ++ x) (((x ++ x) ++ middle) ++ x) := by
    simpa [absorbLaw12, sub2, Word.bind, Word.append, Word.append_assoc] using primitive.subst (sub2 x middle)
  exact first.trans (core_to_absorb (derivesHeavyGather x middle))

theorem swap_separated_square (middle : List Nat) (last : Nat) :
    Derives swapBasis (Word.singleton last ++ put middle (Word.singleton last))
      (put middle (Word.mk last [last])) := by
  cases middle with
  | nil => exact Derives.refl _
  | cons first rest =>
      change Derives swapBasis
        (Word.singleton last ++ put (Word.mk first rest).toList (Word.singleton last))
        (put (Word.mk first rest).toList (Word.mk last [last]))
      rw [put_word, put_word]
      simpa only [Word.append_assoc] using swap_sandwich_square (Word.singleton last) (Word.mk first rest)

theorem absorb_separated_cube (middle : List Nat) (last : Nat) (nonempty : middle ≠ []) :
    Derives absorbBasis (Word.singleton last ++ put middle (Word.singleton last))
      (put middle (Word.mk last [last, last])) := by
  cases middle with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      change Derives absorbBasis
        (Word.singleton last ++ put (Word.mk first rest).toList (Word.singleton last))
        (put (Word.mk first rest).toList (Word.mk last [last, last]))
      rw [put_word, put_word]
      simpa only [Word.append_assoc] using absorb_sandwich_cube (Word.singleton last) (Word.mk first rest)

def heavyWord (whole : List Nat) : Word Nat :=
  let selected := pivot whole
  put (bulk [selected] whole) (Word.mk selected [selected, selected])

theorem caps_bulk_cube (whole : List Nat) (last : Nat) (many : 2 ≤ whole.count last) :
    SameCaps whole (bulk [last] whole ++ [last, last, last]) := by
  intro letter
  rw [List.count_append, count_bulk]
  by_cases equal : letter = last
  · subst letter
    simp only [List.mem_singleton, ite_true, List.count_cons_self, List.count_nil, Nat.zero_add]
    omega
  · have different : last ≠ letter := Ne.symm equal
    simp only [List.mem_singleton, if_neg equal, List.count_cons_of_ne different, List.count_nil, Nat.add_zero]
    omega

theorem bulk_nonempty_of_other {whole : List Nat} {letter last : Nat}
    (different : letter ≠ last) (present : letter ∈ whole) : bulk [last] whole ≠ [] := by
  intro empty
  have count := count_bulk [last] whole letter
  rw [empty, List.count_nil] at count
  simp only [List.mem_singleton, if_neg different] at count
  have positive := List.count_pos_iff.mpr present
  omega

theorem core_cube_to_heavy (whole : List Nat) (last : Nat) (many : 2 ≤ whole.count last) :
    Derives coreBasis (put (bulk [last] whole) (Word.mk last [last, last])) (heavyWord whole) := by
  let middle := bulk [last] whole
  let generated := middle ++ [last, last, last]
  have same : SameCaps whole generated := caps_bulk_cube whole last many
  have heavy : 3 ≤ (middle ++ [last] ++ [last, last]).count last := by
    simp only [List.count_append, List.count_cons_self, List.count_nil]
    omega
  have first := relHeavyNormal (middle ++ [last]) last last heavy
  have step : Rel generated
      (bulk [pivot generated] generated ++ [pivot generated, pivot generated, pivot generated]) := by
    simpa only [generated, List.append_assoc] using first
  rw [← pivot_eq_of_caps same, ← bulk_eq_of_caps [pivot whole] same] at step
  have listDerivation : Rel (put (bulk [last] whole) (Word.mk last [last, last])).toList
      (heavyWord whole).toList := by
    simp only [heavyWord, put_toList]
    exact step
  exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord listDerivation

theorem absorb_separated_heavy (whole : List Nat) (last : Nat)
    (many : 2 ≤ whole.count last) (nonempty : bulk [last] whole ≠ []) :
    Derives absorbBasis (Word.singleton last ++ put (bulk [last] whole) (Word.singleton last))
      (heavyWord whole) :=
  (absorb_separated_cube (bulk [last] whole) last nonempty).trans
    (core_to_absorb (core_cube_to_heavy whole last many))

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14
