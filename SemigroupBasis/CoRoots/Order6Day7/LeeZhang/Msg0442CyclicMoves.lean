import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442CyclicPresentation

/-! Genuine derivations from the approved three-law pair presentation.
Long words admit copies of an existing prefix letter. Behind three nonempty
blocks the complete final-marker theory is replayed, with substitutions and
both contexts kept explicit. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Cyclic

open SemigroupBasis Examples

def substituteFour (x y z t : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

theorem prefixSwap (u v q : Word Nat) :
    Derives pairBasis ((u ++ v) ++ q) ((v ++ u) ++ q) := by
  have primitive : Derives pairBasis prefixSwapLaw.lhs prefixSwapLaw.rhs :=
    Derives.fromBasis (e := prefixSwapLaw) (by simp [pairBasis])
  have substituted := Derives.subst primitive (substituteFour q q u v)
  simpa [prefixSwapLaw, substituteFour, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem sandwich (u v : Word Nat) :
    Derives pairBasis ((u ++ v) ++ u) ((v ++ u) ++ v) := by
  have primitive : Derives pairBasis sandwichLaw.lhs sandwichLaw.rhs :=
    Derives.fromBasis (e := sandwichLaw) (by simp [pairBasis])
  have substituted := Derives.subst primitive (substituteFour u u u v)
  simpa [sandwichLaw, substituteFour, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem longDuplication (a b c d : Word Nat) :
    Derives pairBasis (((a ++ b) ++ c) ++ d) ((((a ++ b) ++ b) ++ c) ++ d) := by
  have primitive : Derives pairBasis duplicationLaw.lhs duplicationLaw.rhs :=
    Derives.fromBasis (e := duplicationLaw) (by simp [pairBasis])
  have substituted := Derives.subst primitive (substituteFour a b c d)
  simpa [duplicationLaw, substituteFour, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem copyFinal (u v : Word Nat) :
    Derives pairBasis ((u ++ v) ++ u) ((u ++ v) ++ v) :=
  (sandwich u v).trans (prefixSwap v u v)

theorem prefixPermutation {p q : List Nat} (permuted : p.Perm q) (final : Nat) :
    Derives pairBasis (wordOfPrefixFinal p final) (wordOfPrefixFinal q final) := by
  induction permuted with
  | nil => exact Derives.refl _
  | cons x _ ih => simpa using Derives.prepend (Word.singleton x) ih
  | swap x y tail =>
      simpa [Word.append_assoc] using
        prefixSwap (Word.singleton y) (Word.singleton x) (wordOfPrefixFinal tail final)
  | trans _ _ first second => exact first.trans second

theorem longHeadDuplication (a b c d : Word Nat) :
    Derives pairBasis (((a ++ b) ++ c) ++ d) ((((a ++ a) ++ b) ++ c) ++ d) := by
  have first : Derives pairBasis (((a ++ b) ++ c) ++ d) (((b ++ a) ++ c) ++ d) := by
    simpa [Word.append_assoc] using prefixSwap a b (c ++ d)
  have middle := longDuplication b a c d
  have last : Derives pairBasis ((((b ++ a) ++ a) ++ c) ++ d) ((((a ++ a) ++ b) ++ c) ++ d) := by
    simpa [Word.append_assoc] using prefixSwap b (a ++ a) (c ++ d)
  exact first.trans (middle.trans last)

theorem insertHead (word : Word Nat) (long : 4 ≤ word.toList.length) :
    Derives pairBasis word (Word.singleton word.head ++ word) := by
  rcases word with ⟨a, tail⟩
  rcases tail with _ | ⟨b, rest⟩
  · simp [Word.toList] at long
  rcases rest with _ | ⟨c, remaining⟩
  · simp [Word.toList] at long
  rcases remaining with _ | ⟨d, suffix⟩
  · simp [Word.toList] at long
  simpa [Word.singleton, Word.append, Word.append_assoc] using
    longHeadDuplication (Word.singleton a) (Word.singleton b)
      (Word.singleton c) (Word.mk d suffix)

theorem insertPrefixLetter (p : List Nat) (final tested : Nat)
    (member : tested ∈ p) (long : 4 ≤ (wordOfPrefixFinal p final).toList.length) :
    Derives pairBasis (wordOfPrefixFinal p final)
      (Word.singleton tested ++ wordOfPrefixFinal p final) := by
  have permuted : p.Perm (tested :: p.erase tested) := List.perm_cons_erase member
  have move := prefixPermutation permuted final
  have length : 4 ≤ (wordOfPrefixFinal (tested :: p.erase tested) final).toList.length := by
    rw [toList_wordOfPrefixFinal] at long ⊢
    simp only [List.length_append, List.length_singleton] at long ⊢
    rw [← permuted.length_eq]
    exact long
  have insert := insertHead (wordOfPrefixFinal (tested :: p.erase tested) final) length
  have restore := Derives.prepend (Word.singleton tested) move.symm
  exact move.trans (insert.trans restore)

theorem insertThreePrefixLetters (p : List Nat) (final tested : Nat)
    (member : tested ∈ p) (long : 4 ≤ (wordOfPrefixFinal p final).toList.length) :
    Derives pairBasis (wordOfPrefixFinal p final)
      (((Word.singleton tested ++ Word.singleton tested) ++ Word.singleton tested) ++
        wordOfPrefixFinal p final) := by
  let letter := Word.singleton tested
  have first := insertPrefixLetter p final tested member long
  have second := Derives.prepend letter first
  have third := Derives.prepend (letter ++ letter) first
  simpa [letter, Word.append_assoc] using first.trans (second.trans third)

theorem guardedDuplication (a b c u v : Word Nat) :
    Derives pairBasis ((((a ++ b) ++ c) ++ u) ++ v)
      (((((a ++ b) ++ c) ++ u) ++ u) ++ v) := by
  have move : Derives pairBasis ((((a ++ b) ++ c) ++ u) ++ v)
      (((a ++ u) ++ (b ++ c)) ++ v) := by
    simpa [Word.append_assoc] using Derives.prepend a (prefixSwap (b ++ c) u v)
  have duplicate := longDuplication a u (b ++ c) v
  have restore : Derives pairBasis ((((a ++ u) ++ u) ++ (b ++ c)) ++ v)
      (((((a ++ b) ++ c) ++ u) ++ u) ++ v) := by
    simpa [Word.append_assoc] using Derives.prepend a (prefixSwap (u ++ u) (b ++ c) v)
  exact move.trans (duplicate.trans restore)

theorem bindAppend (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution = left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

theorem bindBind (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second = word.bind (fun x => (first x).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

theorem bindSingleton (word : Word Nat) : word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp

/-- Every final-marker derivation lifts behind three blocks. This is a
structural induction on Derives, not a finite-window extrapolation. -/
theorem liftFinalMarker {left right : Word Nat}
    (derivation : Derives finalMarkerThreeBasis left right)
    (a b c : Word Nat) (substitution : Nat → Word Nat) :
    Derives pairBasis (((a ++ b) ++ c) ++ left.bind substitution)
      (((a ++ b) ++ c) ++ right.bind substitution) := by
  induction derivation generalizing a b c substitution with
  | fromBasis member =>
      simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · simpa [finalMarkerPowerLaw, finalMarkerXX, finalMarkerXXX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          guardedDuplication a b c (substitution 0) (substitution 0)
      · simpa [finalMarkerPrefixDuplicationLaw, finalMarkerXY, finalMarkerXXY,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          guardedDuplication a b c (substitution 0) (substitution 1)
      · simpa [finalMarkerCopyLaw, finalMarkerXYX, finalMarkerXYY,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend ((a ++ b) ++ c) (copyFinal (substitution 0) (substitution 1))
      · simpa [finalMarkerRotateLaw, finalMarkerXYX, finalMarkerYXX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend ((a ++ b) ++ c) (prefixSwap (substitution 0) (substitution 1) (substitution 0))
  | refl => exact Derives.refl _
  | symm _ ih => exact (ih a b c substitution).symm
  | trans _ _ first second => exact (first a b c substitution).trans (second a b c substitution)
  | prepend stem _ ih =>
      simpa [bindAppend, Word.append_assoc] using ih a b (c ++ stem.bind substitution) substitution
  | appendRight _ suffix ih =>
      simpa [bindAppend, Word.append_assoc] using
        Derives.appendRight (ih a b c substitution) (suffix.bind substitution)
  | subst _ next ih =>
      simpa [bindBind] using ih a b c (fun x => (next x).bind substitution)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0442Cyclic
