import SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleTables
import SemigroupBasis.CoRoots.S5_107ListDerives

/-!
Derived rules of Σ4 with word variables, and their padded list-level cores.

* `derivesCube`     : `u = u u u`
* `derivesM3`       : `y a y y b y = y a b y`          (Σ4's third law)
* `derivesM2a`      : `y a y s b y c s = y a s y b y c s`   (3 steps)
* `derivesM2b`      : `y a y s b s c y = y a s y b s c y`   (5 steps)

The list-level cores allow the blocker lists `A B C` to be empty: the
neighbouring letters are cubed first (`x = xxx`), the word law is applied,
and the cubes are contracted again.
-/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleRules

open SemigroupBasis
open Msg0607TripleTables

abbrev ListDerives := S5_107.ListDerives basis

private def instantiate4 (u v z t : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

/-- `u = uuu`. -/
theorem derivesCube (u : Word Nat) : Derives basis u ((u ++ u) ++ u) := by
  have law := Derives.fromBasis (basis := basis) (e := cubeLaw) (by simp [basis])
  have step := law.subst (instantiate4 u u u u)
  simpa [cubeLaw, instantiate4, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using step

/-- `xxyzxty = xyxzxty` with word variables. -/
theorem derivesSwapLaw (x y z t : Word Nat) :
    Derives basis (x ++ x ++ y ++ z ++ x ++ t ++ y) (x ++ y ++ x ++ z ++ x ++ t ++ y) := by
  have law := Derives.fromBasis (basis := basis) (e := swapLaw) (by simp [basis])
  have step := law.subst (instantiate4 x y z t)
  simpa [swapLaw, instantiate4, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using step

/-- `xyxxzx = xyzx` with word variables. -/
theorem derivesDeleteLaw (x y z : Word Nat) :
    Derives basis (x ++ y ++ x ++ x ++ z ++ x) (x ++ y ++ z ++ x) := by
  have law := Derives.fromBasis (basis := basis) (e := deleteLaw) (by simp [basis])
  have step := law.subst (instantiate4 x y z z)
  simpa [deleteLaw, instantiate4, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using step

/-- M3: delete a square strictly between an earlier and a later occurrence. -/
theorem derivesM3 (y a b : Word Nat) :
    Derives basis (y ++ a ++ y ++ y ++ b ++ y) (y ++ a ++ b ++ y) :=
  derivesDeleteLaw y a b

/-- M2a: swap `y s` given an earlier `y` and later `y … s`. -/
theorem derivesM2a (y a s b c : Word Nat) :
    Derives basis (y ++ a ++ y ++ s ++ b ++ y ++ c ++ s)
      (y ++ a ++ s ++ y ++ b ++ y ++ c ++ s) := by
  have step1 : Derives basis (y ++ a ++ y ++ s ++ b ++ y ++ c ++ s)
      (y ++ a ++ (y ++ y ++ y) ++ s ++ b ++ y ++ c ++ s) := by
    have raw := ((derivesCube y).prepend (y ++ a)).appendRight (s ++ b ++ y ++ c ++ s)
    simpa [Word.append_assoc] using raw
  have step2 : Derives basis (y ++ a ++ (y ++ y ++ y) ++ s ++ b ++ y ++ c ++ s)
      (y ++ a ++ y ++ (y ++ s ++ y ++ b ++ y ++ c ++ s)) := by
    have raw := (derivesSwapLaw y s b c).prepend (y ++ a ++ y)
    simpa [Word.append_assoc] using raw
  have step3 : Derives basis (y ++ a ++ y ++ (y ++ s ++ y ++ b ++ y ++ c ++ s))
      (y ++ a ++ s ++ y ++ b ++ y ++ c ++ s) := by
    have raw := (derivesDeleteLaw y a s).appendRight (b ++ y ++ c ++ s)
    simpa [Word.append_assoc] using raw
  exact step1.trans (step2.trans step3)

/-- M2b: swap `y s` given an earlier `y` and later `s … y`. -/
theorem derivesM2b (y a s b c : Word Nat) :
    Derives basis (y ++ a ++ y ++ s ++ b ++ s ++ c ++ y)
      (y ++ a ++ s ++ y ++ b ++ s ++ c ++ y) := by
  -- W1 = y a (yyy) s b s c y
  have step1 : Derives basis (y ++ a ++ y ++ s ++ b ++ s ++ c ++ y)
      (y ++ a ++ (y ++ y ++ y) ++ s ++ b ++ s ++ c ++ y) := by
    have raw := ((derivesCube y).prepend (y ++ a)).appendRight (s ++ b ++ s ++ c ++ y)
    simpa [Word.append_assoc] using raw
  -- W2 = y (a yyy s) y y (b s c) y   by the delete law reversed
  have step2 : Derives basis (y ++ a ++ (y ++ y ++ y) ++ s ++ b ++ s ++ c ++ y)
      (y ++ (a ++ y ++ y ++ y ++ s) ++ y ++ y ++ (b ++ s ++ c) ++ y) := by
    have raw := (derivesDeleteLaw y (a ++ y ++ y ++ y ++ s) (b ++ s ++ c)).symm
    simpa [Word.append_assoc] using raw
  -- W3 = y a y (y s y y y b s) c y   by the swap law (x := y, y := s, z := y, t := b)
  have step3 : Derives basis (y ++ (a ++ y ++ y ++ y ++ s) ++ y ++ y ++ (b ++ s ++ c) ++ y)
      (y ++ a ++ y ++ (y ++ s ++ y ++ y ++ y ++ b ++ s) ++ c ++ y) := by
    have raw := ((derivesSwapLaw y s y b).prepend (y ++ a ++ y)).appendRight (c ++ y)
    simpa [Word.append_assoc] using raw
  -- W4 = y a y y s y b s c y   by contracting the cube
  have step4 : Derives basis (y ++ a ++ y ++ (y ++ s ++ y ++ y ++ y ++ b ++ s) ++ c ++ y)
      (y ++ a ++ y ++ y ++ s ++ y ++ b ++ s ++ c ++ y) := by
    have raw := ((derivesCube y).symm.prepend (y ++ a ++ y ++ y ++ s)).appendRight
      (b ++ s ++ c ++ y)
    simpa [Word.append_assoc] using raw
  -- W5 = y a s y b s c y   by the delete law
  have step5 : Derives basis (y ++ a ++ y ++ y ++ s ++ y ++ b ++ s ++ c ++ y)
      (y ++ a ++ s ++ y ++ b ++ s ++ c ++ y) := by
    have raw := (derivesDeleteLaw y a s).appendRight (b ++ s ++ c ++ y)
    simpa [Word.append_assoc] using raw
  exact step1.trans (step2.trans (step3.trans (step4.trans step5)))

/-! ## List-level cores with possibly empty blockers -/

/-- The word whose letters are `front ++ [last]`. -/
def snocWord (front : List Nat) (last : Nat) : Word Nat :=
  match front with
  | [] => Word.singleton last
  | head :: tail => ⟨head, tail ++ [last]⟩

@[simp]
theorem toList_snocWord (front : List Nat) (last : Nat) :
    (snocWord front last).toList = front ++ [last] := by
  cases front <;> simp [snocWord, Word.toList, Word.singleton]

@[simp]
theorem toList_mk (head : Nat) (tail : List Nat) : (Word.mk head tail).toList = head :: tail := rfl

theorem listDerivesCube (m : Nat) : ListDerives [m] [m, m, m] := by
  simpa [Word.toList, Word.singleton, Word.append] using
    S5_107.ListDerives.ofWord (derivesCube (Word.singleton m))

theorem listDerivesUncube (m : Nat) : ListDerives [m, m, m] [m] :=
  (listDerivesCube m).symm

/-- M3 core: `y A y y B y = y A B y` for arbitrary lists `A B`. -/
theorem deleteCore (y : Nat) (A B : List Nat) :
    ListDerives ([y] ++ A ++ [y, y] ++ B ++ [y]) ([y] ++ A ++ B ++ [y]) := by
  have pad1 : ListDerives ([y] ++ A ++ [y, y] ++ B ++ [y])
      ([y, y, y] ++ A ++ [y, y] ++ B ++ [y]) := by
    simpa [List.append_assoc] using (listDerivesCube y).context [] (A ++ [y, y] ++ B ++ [y])
  have pad2 : ListDerives ([y, y, y] ++ A ++ [y, y] ++ B ++ [y])
      ([y, y, y] ++ A ++ [y, y] ++ B ++ [y, y, y]) := by
    simpa [List.append_assoc] using
      (listDerivesCube y).context ([y, y, y] ++ A ++ [y, y] ++ B) []
  have law : ListDerives ([y, y, y] ++ A ++ [y, y] ++ B ++ [y, y, y])
      ([y, y, y] ++ A ++ B ++ [y, y, y]) := by
    have raw := S5_107.ListDerives.ofWord
      (derivesM3 (Word.singleton y) ⟨y, y :: A⟩ (snocWord (B ++ [y]) y))
    simpa [toList_mk, toList_snocWord, Word.toList_append, Word.toList_singleton,
      List.append_assoc] using raw
  have unpad1 : ListDerives ([y, y, y] ++ A ++ B ++ [y, y, y]) ([y] ++ A ++ B ++ [y, y, y]) := by
    simpa [List.append_assoc] using (listDerivesUncube y).context [] (A ++ B ++ [y, y, y])
  have unpad2 : ListDerives ([y] ++ A ++ B ++ [y, y, y]) ([y] ++ A ++ B ++ [y]) := by
    simpa [List.append_assoc] using (listDerivesUncube y).context ([y] ++ A ++ B) []
  exact pad1.trans (pad2.trans (law.trans (unpad1.trans unpad2)))

/-- M2a core: `y A y s B y C s = y A s y B y C s` for arbitrary lists. -/
theorem swapCore1 (y s : Nat) (A B C : List Nat) :
    ListDerives ([y] ++ A ++ [y, s] ++ B ++ [y] ++ C ++ [s])
      ([y] ++ A ++ [s, y] ++ B ++ [y] ++ C ++ [s]) := by
  have pad1 : ListDerives ([y] ++ A ++ [y, s] ++ B ++ [y] ++ C ++ [s])
      ([y, y, y] ++ A ++ [y, s] ++ B ++ [y] ++ C ++ [s]) := by
    simpa [List.append_assoc] using
      (listDerivesCube y).context [] (A ++ [y, s] ++ B ++ [y] ++ C ++ [s])
  have pad2 : ListDerives ([y, y, y] ++ A ++ [y, s] ++ B ++ [y] ++ C ++ [s])
      ([y, y, y] ++ A ++ [y, s] ++ B ++ [y, y, y] ++ C ++ [s]) := by
    simpa [List.append_assoc] using
      (listDerivesCube y).context ([y, y, y] ++ A ++ [y, s] ++ B) (C ++ [s])
  have pad3 : ListDerives ([y, y, y] ++ A ++ [y, s] ++ B ++ [y, y, y] ++ C ++ [s])
      ([y, y, y] ++ A ++ [y, s] ++ B ++ [y, y, y] ++ C ++ [s, s, s]) := by
    simpa [List.append_assoc] using
      (listDerivesCube s).context ([y, y, y] ++ A ++ [y, s] ++ B ++ [y, y, y] ++ C) []
  have law : ListDerives ([y, y, y] ++ A ++ [y, s] ++ B ++ [y, y, y] ++ C ++ [s, s, s])
      ([y, y, y] ++ A ++ [s, y] ++ B ++ [y, y, y] ++ C ++ [s, s, s]) := by
    have raw := S5_107.ListDerives.ofWord
      (derivesM2a (Word.singleton y) ⟨y, y :: A⟩ (Word.singleton s)
        (snocWord (B ++ [y]) y) (snocWord (C ++ [s]) s))
    simpa [toList_mk, toList_snocWord, Word.toList_append, Word.toList_singleton,
      List.append_assoc] using raw
  have unpad1 : ListDerives ([y, y, y] ++ A ++ [s, y] ++ B ++ [y, y, y] ++ C ++ [s, s, s])
      ([y] ++ A ++ [s, y] ++ B ++ [y, y, y] ++ C ++ [s, s, s]) := by
    simpa [List.append_assoc] using
      (listDerivesUncube y).context [] (A ++ [s, y] ++ B ++ [y, y, y] ++ C ++ [s, s, s])
  have unpad2 : ListDerives ([y] ++ A ++ [s, y] ++ B ++ [y, y, y] ++ C ++ [s, s, s])
      ([y] ++ A ++ [s, y] ++ B ++ [y] ++ C ++ [s, s, s]) := by
    simpa [List.append_assoc] using
      (listDerivesUncube y).context ([y] ++ A ++ [s, y] ++ B) (C ++ [s, s, s])
  have unpad3 : ListDerives ([y] ++ A ++ [s, y] ++ B ++ [y] ++ C ++ [s, s, s])
      ([y] ++ A ++ [s, y] ++ B ++ [y] ++ C ++ [s]) := by
    simpa [List.append_assoc] using
      (listDerivesUncube s).context ([y] ++ A ++ [s, y] ++ B ++ [y] ++ C) []
  exact pad1.trans (pad2.trans (pad3.trans (law.trans (unpad1.trans (unpad2.trans unpad3)))))

/-- M2b core: `y A y s B s C y = y A s y B s C y` for arbitrary lists. -/
theorem swapCore2 (y s : Nat) (A B C : List Nat) :
    ListDerives ([y] ++ A ++ [y, s] ++ B ++ [s] ++ C ++ [y])
      ([y] ++ A ++ [s, y] ++ B ++ [s] ++ C ++ [y]) := by
  have pad1 : ListDerives ([y] ++ A ++ [y, s] ++ B ++ [s] ++ C ++ [y])
      ([y, y, y] ++ A ++ [y, s] ++ B ++ [s] ++ C ++ [y]) := by
    simpa [List.append_assoc] using
      (listDerivesCube y).context [] (A ++ [y, s] ++ B ++ [s] ++ C ++ [y])
  have pad2 : ListDerives ([y, y, y] ++ A ++ [y, s] ++ B ++ [s] ++ C ++ [y])
      ([y, y, y] ++ A ++ [y, s] ++ B ++ [s, s, s] ++ C ++ [y]) := by
    simpa [List.append_assoc] using
      (listDerivesCube s).context ([y, y, y] ++ A ++ [y, s] ++ B) (C ++ [y])
  have pad3 : ListDerives ([y, y, y] ++ A ++ [y, s] ++ B ++ [s, s, s] ++ C ++ [y])
      ([y, y, y] ++ A ++ [y, s] ++ B ++ [s, s, s] ++ C ++ [y, y, y]) := by
    simpa [List.append_assoc] using
      (listDerivesCube y).context ([y, y, y] ++ A ++ [y, s] ++ B ++ [s, s, s] ++ C) []
  have law : ListDerives ([y, y, y] ++ A ++ [y, s] ++ B ++ [s, s, s] ++ C ++ [y, y, y])
      ([y, y, y] ++ A ++ [s, y] ++ B ++ [s, s, s] ++ C ++ [y, y, y]) := by
    have raw := S5_107.ListDerives.ofWord
      (derivesM2b (Word.singleton y) ⟨y, y :: A⟩ (Word.singleton s)
        (snocWord (B ++ [s]) s) (snocWord (C ++ [y]) y))
    simpa [toList_mk, toList_snocWord, Word.toList_append, Word.toList_singleton,
      List.append_assoc] using raw
  have unpad1 : ListDerives ([y, y, y] ++ A ++ [s, y] ++ B ++ [s, s, s] ++ C ++ [y, y, y])
      ([y] ++ A ++ [s, y] ++ B ++ [s, s, s] ++ C ++ [y, y, y]) := by
    simpa [List.append_assoc] using
      (listDerivesUncube y).context [] (A ++ [s, y] ++ B ++ [s, s, s] ++ C ++ [y, y, y])
  have unpad2 : ListDerives ([y] ++ A ++ [s, y] ++ B ++ [s, s, s] ++ C ++ [y, y, y])
      ([y] ++ A ++ [s, y] ++ B ++ [s] ++ C ++ [y, y, y]) := by
    simpa [List.append_assoc] using
      (listDerivesUncube s).context ([y] ++ A ++ [s, y] ++ B) (C ++ [y, y, y])
  have unpad3 : ListDerives ([y] ++ A ++ [s, y] ++ B ++ [s] ++ C ++ [y, y, y])
      ([y] ++ A ++ [s, y] ++ B ++ [s] ++ C ++ [y]) := by
    simpa [List.append_assoc] using
      (listDerivesUncube y).context ([y] ++ A ++ [s, y] ++ B ++ [s] ++ C) []
  exact pad1.trans (pad2.trans (pad3.trans (law.trans (unpad1.trans (unpad2.trans unpad3)))))

end SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleRules
