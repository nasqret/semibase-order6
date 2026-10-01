import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S4_96
import SemigroupBasis.CoRoots.S5_505Family
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Exact direct B5 for S4_96 / S5_506. The complete pre-proof screens are
bounded evidence only. All list contexts below are explicit; no cancellation
or affine period-two contraction is used in the displayed B5 calculus. -/

namespace SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095Macros

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_107

def law00 : Identity Nat := ⟨Word.mk 0 [], Word.mk 0 [0, 0, 0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [0, 1, 0], Word.mk 1 [0, 0, 0]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [1, 0, 1], Word.mk 1 [0, 0, 1]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 1], Word.mk 1 [0, 0, 2, 1]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [1, 2, 0, 1], Word.mk 1 [0, 2, 0, 1]⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04]
abbrev displayedBasisSHA256 : String := "5689e30d5537d600e1a38b2cd0520e3b6f7a209b561548318a64c4644d56ae1b"
abbrev leftTable : FiniteTable := Generated.S4_96.table
abbrev rightTable : FiniteTable := CoRoots.S5_505Family.S5_506.table
abbrev D := ListDerives basis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_length : basis.length = 5 := by decide
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)
theorem affineBasis_complete : BasisFor leftTable.semigroup affineParityFourBasis :=
  Generated.S4_96.representative_basis
theorem modFourBasis_complete : BasisFor rightTable.semigroup CoRoots.S5_505.basis :=
  CoRoots.S5_505Family.S5_506.basis_complete

theorem powerFive (x : Nat) : D [x] [x, x, x, x, x] := by
  have primitive : Derives basis law00.lhs law00.rhs :=
    Derives.fromBasis (e := law00) (by decide)
  have mapped := primitive.subst (fun _ => Word.singleton x)
  simpa [law00, Word.bind, Word.append, Word.singleton, Word.toList] using
    ListDerives.ofWord mapped

theorem moveSquare (x : Nat) (middle : List Nat) :
    D ([x, x] ++ middle ++ [x]) (middle ++ [x, x, x]) := by
  cases middle with
  | nil => exact ListDerives.refl _
  | cons y ys =>
      have primitive : Derives basis law01.lhs law01.rhs :=
        Derives.fromBasis (e := law01) (by decide)
      have mapped := primitive.subst (fun
        | 0 => Word.singleton x
        | 1 => Word.mk y ys
        | _ => Word.singleton x)
      simpa [law01, Word.bind, Word.append, Word.singleton, Word.toList,
        List.append_assoc] using ListDerives.ofWord mapped

theorem rawGuardedPair (x y : Nat) : D [x, y, x, y] [y, x, x, y] := by
  have primitive : Derives basis law02.lhs law02.rhs :=
    Derives.fromBasis (e := law02) (by decide)
  have mapped := primitive.subst (fun
    | 0 => Word.singleton x
    | 1 => Word.singleton y
    | _ => Word.singleton x)
  simpa [law02, Word.bind, Word.append, Word.singleton, Word.toList] using
    ListDerives.ofWord mapped

theorem rawSeparatedPair (x y z : Nat) : D [x, y, x, z, y] [y, x, x, z, y] := by
  have primitive : Derives basis law03.lhs law03.rhs :=
    Derives.fromBasis (e := law03) (by decide)
  have mapped := primitive.subst (fun
    | 0 => Word.singleton x
    | 1 => Word.singleton y
    | 2 => Word.singleton z
    | _ => Word.singleton x)
  simpa [law03, Word.bind, Word.append, Word.singleton, Word.toList] using
    ListDerives.ofWord mapped

theorem rawPrefixedPair (x y z : Nat) : D [x, y, z, x, y] [y, x, z, x, y] := by
  have primitive : Derives basis law04.lhs law04.rhs :=
    Derives.fromBasis (e := law04) (by decide)
  have mapped := primitive.subst (fun
    | 0 => Word.singleton x
    | 1 => Word.singleton y
    | 2 => Word.singleton z
    | _ => Word.singleton x)
  simpa [law04, Word.bind, Word.append, Word.singleton, Word.toList] using
    ListDerives.ofWord mapped

/-- A guarded pair can pass an arbitrary prefix without being deleted. -/
theorem squareSlide (x : Nat) (pre suffix : List Nat) (guard : x ∈ suffix) :
    D (pre ++ [x, x] ++ suffix) ([x, x] ++ pre ++ suffix) := by
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp guard
  have first : D (pre ++ [x, x] ++ (before ++ x :: after))
      ((pre ++ before) ++ [x, x, x] ++ after) := by
    simpa [List.append_assoc] using ((moveSquare x before).prepend pre).append after
  have second : D ([x, x] ++ pre ++ (before ++ x :: after))
      ((pre ++ before) ++ [x, x, x] ++ after) := by
    simpa [List.append_assoc] using (moveSquare x (pre ++ before)).append after
  exact first.trans second.symm

/-- Four copies, not two, can be erased before a suffix containing x. -/
theorem deleteFour (x : Nat) (suffix : List Nat) (guard : x ∈ suffix) :
    D ([x, x, x, x] ++ suffix) suffix := by
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp guard
  have first : D ([x, x, x, x] ++ (before ++ x :: after))
      ([x, x] ++ before ++ [x, x, x] ++ after) := by
    simpa [List.append_assoc] using ((moveSquare x before).prepend [x, x]).append after
  have second : D ([x, x] ++ before ++ [x, x, x] ++ after)
      (before ++ [x, x, x, x, x] ++ after) := by
    simpa [List.append_assoc] using ((moveSquare x before).append [x, x]).append after
  have third : D (before ++ [x, x, x, x, x] ++ after) (before ++ x :: after) := by
    simpa [List.append_assoc] using ((powerFive x).symm.prepend before).append after
  exact first.trans (second.trans third)

/-- Explicit buffer insertion and four-copy deletions give guarded commutation.
There is no cancellation principle in this proof. -/
theorem guardedSwap (x y : Nat) (suffix : List Nat)
    (xGuard : x ∈ suffix) (yGuard : y ∈ suffix) :
    D ([x, y] ++ suffix) ([y, x] ++ suffix) := by
  have yGuardLong : y ∈ [x, x, x] ++ suffix := by simp [yGuard]
  have leftFirst : D ([x, y, x, y] ++ ([y, y, y, x, x, x] ++ suffix))
      ([x, y, x, x, x, x] ++ suffix) := by
    simpa [List.append_assoc] using
      (deleteFour y ([x, x, x] ++ suffix) yGuardLong).prepend [x, y, x]
  have leftLast : D ([x, y, x, x, x, x] ++ suffix) ([x, y] ++ suffix) := by
    simpa [List.append_assoc] using (deleteFour x suffix xGuard).prepend [x, y]
  have rightFirst : D ([y, x, x, y] ++ ([y, y, y, x, x, x] ++ suffix))
      ([y, x, x, x, x, x] ++ suffix) := by
    simpa [List.append_assoc] using
      (deleteFour y ([x, x, x] ++ suffix) yGuardLong).prepend [y, x, x]
  have rightLast : D ([y, x, x, x, x, x] ++ suffix) ([y, x] ++ suffix) := by
    simpa [List.append_assoc] using (deleteFour x suffix xGuard).prepend [y, x]
  have middle : D ([x, y, x, y] ++ ([y, y, y, x, x, x] ++ suffix))
      ([y, x, x, y] ++ ([y, y, y, x, x, x] ++ suffix)) :=
    (rawGuardedPair x y).append ([y, y, y, x, x, x] ++ suffix)
  exact (leftFirst.trans leftLast).symm.trans (middle.trans (rightFirst.trans rightLast))

theorem guardedPermutation (suffix : List Nat) {left right : List Nat}
    (permutation : left.Perm right) (guard : ∀ x, x ∈ left → x ∈ suffix) :
    D (left ++ suffix) (right ++ suffix) := by
  revert guard
  induction permutation with
  | nil => intro _; exact ListDerives.refl _
  | cons x permutation ih =>
      intro guard
      have tail := ih (fun z hz => guard z (List.Mem.tail x hz))
      simpa using tail.prepend [x]
  | swap x y rest =>
      intro guard
      have xGuard : x ∈ rest ++ suffix := by simp [guard x (by simp)]
      have yGuard : y ∈ rest ++ suffix := by simp [guard y (by simp)]
      simpa [List.append_assoc] using guardedSwap y x (rest ++ suffix) yGuard xGuard
  | trans first second ihFirst ihSecond =>
      intro guard
      exact (ihFirst guard).trans
        (ihSecond (fun x hx => guard x (first.mem_iff.mpr hx)))

def doubleLetters (buffer : List Nat) : List Nat := buffer.flatMap (fun x => [x, x])

@[simp] theorem doubleLetters_nil : doubleLetters [] = [] := rfl
@[simp] theorem doubleLetters_cons (x : Nat) (xs : List Nat) :
    doubleLetters (x :: xs) = x :: x :: doubleLetters xs := rfl
@[simp] theorem doubleLetters_append (xs ys : List Nat) :
    doubleLetters (xs ++ ys) = doubleLetters xs ++ doubleLetters ys := by
  simp [doubleLetters]

theorem bufferSlide (buffer pre suffix : List Nat)
    (guard : ∀ x, x ∈ buffer → x ∈ suffix) :
    D (pre ++ doubleLetters buffer ++ suffix) (doubleLetters buffer ++ pre ++ suffix) := by
  revert guard
  induction buffer with
  | nil =>
      intro _
      simpa using (ListDerives.refl (basis := basis) (pre ++ suffix))
  | cons x xs ih =>
      intro guard
      have hx : x ∈ doubleLetters xs ++ suffix := by simp [guard x (by simp)]
      have first : D (pre ++ doubleLetters (x :: xs) ++ suffix)
          ([x, x] ++ pre ++ doubleLetters xs ++ suffix) := by
        simpa [List.append_assoc] using squareSlide x pre (doubleLetters xs ++ suffix) hx
      have second : D ([x, x] ++ pre ++ doubleLetters xs ++ suffix)
          (doubleLetters (x :: xs) ++ pre ++ suffix) := by
        simpa [List.append_assoc] using
          (ih (fun z hz => guard z (List.Mem.tail x hz))).prepend [x, x]
      exact first.trans second

end SemigroupBasis.CoRoots.Order6Day10.S4_96.Rank095Macros
