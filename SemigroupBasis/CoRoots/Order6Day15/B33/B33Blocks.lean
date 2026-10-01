import SemigroupBasis.CoRoots.Order6Day15.B33.B33Moves

namespace SemigroupBasis.CoRoots.Order6Day15.B33

inductive Power where
  | one | two | three
  deriving Repr, DecidableEq

def Power.bump (isHead : Bool) : Power → Power
  | .one => .two
  | .two => if isHead then .three else .one
  | .three => .two

def Power.thin : Power → Power
  | .three => .one
  | p => p

def Power.mark : Power → Power
  | .one => .three
  | p => p

structure Block where
  letter : Nat
  power : Power
  deriving Repr, DecidableEq

def Block.word (b : Block) : List Nat :=
  match b.power with
  | .one => [b.letter]
  | .two => [b.letter, b.letter]
  | .three => [b.letter, b.letter, b.letter]

def render : List Block → List Nat
  | [] => []
  | b :: bs => b.word ++ render bs

def letters (bs : List Block) : List Nat := bs.map Block.letter

def markLast : List Block → List Block
  | [] => []
  | [b] => [{ b with power := b.power.mark }]
  | b :: c :: bs => b :: markLast (c :: bs)

/-- Append one letter to a block form; `isHead` records whether its first block is global. -/
def insert (isHead : Bool) : List Block → Nat → List Block
  | [], a => [⟨a, .one⟩]
  | [b], a =>
    if b.letter = a then [{ b with power := b.power.bump true }]
    else [{ b with power := if isHead then b.power else b.power.thin }, ⟨a, .one⟩]
  | b :: c :: bs, a =>
    if b.letter = a then { b with power := b.power.bump isHead } :: markLast (c :: bs)
    else b :: insert false (c :: bs) a

def build : List Block → List Nat → List Block
  | bs, [] => bs
  | bs, a :: xs => build (insert true bs a) xs

def normalBlocks (w : Word Nat) : List Block := build [] w.toList

theorem Block.word_ne_nil (b : Block) : b.word ≠ [] := by
  cases b with
  | mk a p => cases p <;> simp [Block.word]

@[simp] theorem render_eq_nil (bs : List Block) : render bs = [] ↔ bs = [] := by
  cases bs with
  | nil => simp [render]
  | cons b bs =>
    cases b with
    | mk a p => cases p <;> simp [render, Block.word]

theorem render_ne_nil {bs : List Block} (h : bs ≠ []) : render bs ≠ [] := by
  intro e; exact h ((render_eq_nil bs).mp e)

@[simp] theorem markLast_eq_nil (bs : List Block) : markLast bs = [] ↔ bs = [] := by
  cases bs with
  | nil => simp [markLast]
  | cons b bs => cases bs <;> simp [markLast]

theorem markLast_letters (bs : List Block) : letters (markLast bs) = letters bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases bs with
    | nil => rfl
    | cons c cs =>
      simpa only [markLast, letters, List.map_cons] using congrArg (b.letter :: ·) ih

theorem insert_ne_nil (isHead : Bool) (bs : List Block) (a : Nat) :
    insert isHead bs a ≠ [] := by
  cases bs with
  | nil => simp [insert]
  | cons b bs =>
    cases bs with
    | nil => simp only [insert]; split <;> simp
    | cons c cs => simp only [insert]; split <;> simp

/-- Uniform gathering through arbitrarily many blocks, not a finite-rank macro. -/
theorem gather_render (a : Nat) (m : List Nat) (bs : List Block) : bs ≠ [] →
    Rel ([a] ++ m ++ render bs ++ [a]) ([a, a] ++ m ++ render (markLast bs)) := by
  induction bs generalizing m with
  | nil => intro h; exact False.elim (h rfl)
  | cons b bs ih =>
    intro _
    cases bs with
    | nil =>
      cases b with
      | mk b p =>
        cases p with
        | one =>
          simpa only [render, Block.word, markLast, Power.mark, List.append_nil,
            List.append_assoc, List.cons_append, List.nil_append] using gather_single a b m
        | two =>
          simpa only [render, Block.word, markLast, Power.mark, List.append_nil,
            List.append_assoc, List.cons_append, List.nil_append] using gather_square a b m
        | three =>
          simpa only [render, Block.word, markLast, Power.mark, List.append_nil,
            List.append_assoc, List.cons_append, List.nil_append] using gather_cube a b m
    | cons c cs =>
      simpa only [render, markLast, List.append_assoc] using
        ih (m ++ b.word) (by simp)

end SemigroupBasis.CoRoots.Order6Day15.B33
