import SemigroupBasis.CoRoots.Order6Day15.B33.B33Blocks

namespace SemigroupBasis.CoRoots.Order6Day15.B33

theorem append_block_ne_nil (p : List Nat) (b : Block) : p ++ b.word ≠ [] := by
  cases p with
  | nil => exact b.word_ne_nil
  | cons x xs => intro h; cases h

theorem bump_last (b : Block) :
    Rel (b.word ++ [b.letter]) ({ b with power := b.power.bump true } : Block).word := by
  cases b with
  | mk a power =>
    cases power with
    | one => exact Rel.refl _
    | two => exact Rel.refl _
    | three =>
      simpa only [Block.word, Power.bump, List.cons_append, List.nil_append,
        List.append_nil] using four_two a [] []

theorem fresh_block (isHead : Bool) (p : List Nat) (b : Block) (a : Nat)
    (hp : isHead = false → p ≠ []) :
    Rel (p ++ b.word ++ [a])
      (p ++ ({ b with power := if isHead then b.power else b.power.thin } : Block).word ++ [a]) := by
  cases isHead with
  | true => exact Rel.refl _
  | false =>
    cases b with
    | mk x power =>
      cases power with
      | one => exact Rel.refl _
      | two => exact Rel.refl _
      | three =>
        simpa only [Block.word, Power.thin, Bool.false_eq_true, if_false] using
          thin_internal p [a] x (hp rfl) (by simp)

theorem bump_followed (isHead : Bool) (p : List Nat) (b : Block) (s : List Nat)
    (hp : isHead = false → p ≠ []) (hs : s ≠ []) :
    Rel (p ++ b.word ++ [b.letter] ++ s)
      (p ++ ({ b with power := b.power.bump isHead } : Block).word ++ s) := by
  cases b with
  | mk a power =>
    cases power with
    | one =>
      simpa only [Block.word, Power.bump, List.append_assoc, List.cons_append, List.nil_append] using
        Rel.refl (p ++ [a,a] ++ s)
    | two =>
      cases isHead with
      | true =>
        simpa only [Block.word, Power.bump, List.append_assoc, List.cons_append, List.nil_append] using
          Rel.refl (p ++ [a,a,a] ++ s)
      | false =>
        simpa only [Block.word, Power.bump, Bool.false_eq_true, if_false,
          List.append_assoc, List.cons_append, List.nil_append] using thin_internal p s a (hp rfl) hs
    | three =>
      simpa only [Block.word, Power.bump, List.append_assoc, List.cons_append, List.nil_append] using four_two a p s

theorem gather_block (b : Block) (bs : List Block) (h : bs ≠ []) :
    Rel (b.word ++ render bs ++ [b.letter])
      (b.word ++ [b.letter] ++ render (markLast bs)) := by
  cases b with
  | mk a power =>
    cases power with
    | one =>
      simpa only [Block.word, List.nil_append, List.cons_append] using gather_render a [] bs h
    | two =>
      simpa only [Block.word, List.nil_append, List.cons_append] using gather_render a [a] bs h
    | three =>
      simpa only [Block.word, List.nil_append, List.cons_append] using gather_render a [a,a] bs h

/-- Each insertion is an actual B33 derivation in its possibly empty outside prefix. -/
theorem insert_correct (isHead : Bool) (bs : List Block) (a : Nat) (p : List Nat)
    (hp : isHead = false → p ≠ []) :
    Rel (p ++ render bs ++ [a]) (p ++ render (insert isHead bs a)) := by
  induction bs generalizing isHead p with
  | nil =>
    simpa only [render, insert, Block.word, List.nil_append, List.append_nil] using Rel.refl (p ++ [a])
  | cons b bs ih =>
    cases bs with
    | nil =>
      by_cases e : b.letter = a
      · subst a
        simpa [insert, render, List.append_assoc] using
          (bump_last b).prepend p
      · simpa only [insert, if_neg e, render, Block.word, List.append_nil, List.append_assoc] using
          fresh_block isHead p b a hp
    | cons c cs =>
      by_cases e : b.letter = a
      · subst a
        have h1 : Rel (p ++ b.word ++ render (c :: cs) ++ [b.letter])
            (p ++ b.word ++ [b.letter] ++ render (markLast (c :: cs))) := by
          simpa only [List.append_assoc] using (gather_block b (c :: cs) (by simp)).prepend p
        have nonempty : render (markLast (c :: cs)) ≠ [] := by
          apply render_ne_nil
          intro bad
          have := (markLast_eq_nil (c :: cs)).mp bad
          cases this
        have h2 := bump_followed isHead p b (render (markLast (c :: cs))) hp nonempty
        simpa [insert, render, List.append_assoc] using h1.trans h2
      · have step := ih false (p ++ b.word) (fun _ => append_block_ne_nil p b)
        simpa only [insert, if_neg e, render, List.append_assoc] using step

/-- The recursive builder derives its output for arbitrary input length and rank. -/
theorem build_correct (bs : List Block) (xs : List Nat) :
    Rel (render bs ++ xs) (render (build bs xs)) := by
  induction xs generalizing bs with
  | nil => simpa only [build, List.append_nil] using Rel.refl (render bs)
  | cons a xs ih =>
    have step : Rel (render bs ++ [a]) (render (insert true bs a)) := by
      simpa only [List.nil_append] using insert_correct true bs a [] (by intro h; cases h)
    have lifted := step.suffix xs
    simpa only [build, List.append_assoc, List.cons_append, List.nil_append] using
      lifted.trans (ih (insert true bs a))

theorem normalBlocks_correct (w : Word Nat) : Rel w.toList (render (normalBlocks w)) := by
  simpa only [normalBlocks, render, List.nil_append] using build_correct [] w.toList

theorem Rel.right_ne_nil {u v : List Nat} (h : Rel u v) (hu : u ≠ []) : v ≠ [] := by
  intro hv
  subst v
  cases u with
  | nil => exact hu rfl
  | cons a u => exact h

theorem normal_render_ne_nil (w : Word Nat) : render (normalBlocks w) ≠ [] :=
  (normalBlocks_correct w).right_ne_nil (by cases w; simp [Word.toList])

def wordOfList (xs : List Nat) (h : xs ≠ []) : Word Nat :=
  match xs with
  | [] => False.elim (h rfl)
  | a :: xs => ⟨a, xs⟩

theorem wordOfList_toList (xs : List Nat) (h : xs ≠ []) :
    (wordOfList xs h).toList = xs := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons a xs => rfl

def normalWord (w : Word Nat) : Word Nat :=
  wordOfList (render (normalBlocks w)) (normal_render_ne_nil w)

theorem normalWord_toList (w : Word Nat) : (normalWord w).toList = render (normalBlocks w) :=
  wordOfList_toList _ _

/-- Actual unbounded B33 derivation to the computed block-form output. -/
theorem normalWord_derives (w : Word Nat) : Derives basis w (normalWord w) := by
  apply Rel.toDerives
  rw [normalWord_toList]
  exact normalBlocks_correct w

end SemigroupBasis.CoRoots.Order6Day15.B33
