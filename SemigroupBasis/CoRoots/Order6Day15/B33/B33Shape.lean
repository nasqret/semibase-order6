import SemigroupBasis.CoRoots.Order6Day15.B33.B33Insert

namespace SemigroupBasis.CoRoots.Order6Day15.B33

@[simp] theorem letters_nil : letters [] = [] := rfl
@[simp] theorem letters_cons (b : Block) (bs : List Block) :
    letters (b :: bs) = b.letter :: letters bs := rfl

/-- Only the global head and the last block may have exponent three. -/
def Small : Bool → List Block → Prop
  | _, [] => True
  | _, [_] => True
  | isHead, b :: c :: bs => (isHead = true ∨ b.power ≠ .three) ∧ Small false (c :: bs)

def Normal (bs : List Block) : Prop := (letters bs).Nodup ∧ Small true bs

theorem small_cons (isHead : Bool) (b : Block) (bs : List Block)
    (hfirst : isHead = true ∨ b.power ≠ .three) (hrest : Small false bs) :
    Small isHead (b :: bs) := by
  cases bs with
  | nil => trivial
  | cons c cs => exact ⟨hfirst,hrest⟩

theorem small_markLast (isHead : Bool) (bs : List Block) (h : Small isHead bs) :
    Small isHead (markLast bs) := by
  induction bs generalizing isHead with
  | nil => trivial
  | cons b bs ih =>
    cases bs with
    | nil => trivial
    | cons c cs =>
      change Small isHead (b :: markLast (c :: cs))
      exact small_cons isHead b _ h.1 (ih false h.2)

theorem bump_small (isHead : Bool) (power : Power) :
    isHead = true ∨ power.bump isHead ≠ .three := by
  cases isHead with
  | true => exact Or.inl rfl
  | false => cases power <;> simp [Power.bump]

theorem small_insert (isHead : Bool) (bs : List Block) (a : Nat) (h : Small isHead bs) :
    Small isHead (insert isHead bs a) := by
  induction bs generalizing isHead with
  | nil => trivial
  | cons b bs ih =>
    cases bs with
    | nil =>
      by_cases e : b.letter = a
      · simp only [insert,if_pos e]; trivial
      · simp only [insert,if_neg e]
        apply small_cons
        · cases isHead with
          | true => exact Or.inl rfl
          | false => cases b.power <;> simp [Power.thin]
        · trivial
    | cons c cs =>
      by_cases e : b.letter = a
      · simp only [insert,if_pos e]
        exact small_cons isHead _ _ (bump_small isHead b.power) (small_markLast false _ h.2)
      · simp only [insert,if_neg e]
        exact small_cons isHead b _ h.1 (ih false h.2)

theorem insert_letters (isHead : Bool) (bs : List Block) (a : Nat) :
    letters (insert isHead bs a) =
      if a ∈ letters bs then letters bs else letters bs ++ [a] := by
  induction bs generalizing isHead with
  | nil => simp [insert]
  | cons b bs ih =>
    cases bs with
    | nil =>
      by_cases e : b.letter = a
      · simp [insert,e]
      · have ae : a ≠ b.letter := Ne.symm e
        simp [insert,e,ae]
    | cons c cs =>
      by_cases e : b.letter = a
      · simp [insert,e,markLast_letters]
      · have ae : a ≠ b.letter := Ne.symm e
        simp [insert,e,ae,ih]
        split <;> rfl

theorem insert_nodup (isHead : Bool) (bs : List Block) (a : Nat)
    (h : (letters bs).Nodup) : (letters (insert isHead bs a)).Nodup := by
  rw [insert_letters]
  split
  · exact h
  · rename_i absent
    apply List.nodup_append.mpr
    refine ⟨h,by simp,?_⟩
    intro x hx y hy equal
    have ya : y = a := by simpa using hy
    have xa : x = a := equal.trans ya
    exact absent (by simpa only [xa] using hx)

theorem build_small (bs : List Block) (xs : List Nat) (h : Small true bs) :
    Small true (build bs xs) := by
  induction xs generalizing bs with
  | nil => exact h
  | cons a xs ih => exact ih _ (small_insert true bs a h)

theorem build_nodup (bs : List Block) (xs : List Nat) (h : (letters bs).Nodup) :
    (letters (build bs xs)).Nodup := by
  induction xs generalizing bs with
  | nil => exact h
  | cons a xs ih => exact ih _ (insert_nodup true bs a h)

theorem normalBlocks_normal (w : Word Nat) : Normal (normalBlocks w) :=
  ⟨build_nodup [] w.toList (by simp),build_small [] w.toList (by trivial)⟩

def firstsFrom : List Nat → List Nat → List Nat
  | acc, [] => acc
  | acc, a :: xs => firstsFrom (if a ∈ acc then acc else acc ++ [a]) xs

theorem build_letters (bs : List Block) (xs : List Nat) :
    letters (build bs xs) = firstsFrom (letters bs) xs := by
  induction xs generalizing bs with
  | nil => rfl
  | cons a xs ih =>
    simp only [build, firstsFrom]
    rw [ih, insert_letters]

theorem normalBlocks_letters (w : Word Nat) :
    letters (normalBlocks w) = firstsFrom [] w.toList := build_letters [] w.toList

end SemigroupBasis.CoRoots.Order6Day15.B33
