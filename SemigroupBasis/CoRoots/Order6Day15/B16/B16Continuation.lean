import SemigroupBasis.CoRoots.Order6Day15.B16.B16PositiveKey

namespace SemigroupBasis.CoRoots.Order6Day15.B16

/-- An empty tail acts on an existing value; no semigroup unit is introduced. -/
def runTail (S : Semigroup α) (a : α) (xs : List α) : α := xs.foldl S.mul a

theorem runTail_nil (S : Semigroup α) (a : α) : runTail S a [] = a := rfl

theorem runTail_cons (S : Semigroup α) (a x : α) (xs : List α) :
    runTail S a (x :: xs) = runTail S (S.mul a x) xs := rfl

theorem runTail_append (S : Semigroup α) (a : α) (xs ys : List α) :
    runTail S a (xs ++ ys) = runTail S (runTail S a xs) ys := by
  exact List.foldl_append

theorem runTail_mul (S : Semigroup α) (a b : α) (xs : List α) :
    runTail S (S.mul a b) xs = S.mul a (runTail S b xs) := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
      rw [runTail_cons, runTail_cons, S.assoc]
      exact ih (S.mul b x)

/-- Structural hypotheses only. Low includes zero and has square zero. -/
structure SplitAction (S : Semigroup α) where
  zero : α
  Pos : α → Prop
  Low : α → Prop
  cover : ∀ a, Pos a ∨ Low a
  zero_low : Low zero
  zero_mul : ∀ a, S.mul zero a = zero
  mul_zero : ∀ a, S.mul a zero = zero
  positive_positive : ∀ a b, Pos a → Pos b → Pos (S.mul a b)
  positive_low : ∀ a b, Pos a → Low b → S.mul a b = b
  low_positive : ∀ a b, Low a → Pos b → Low (S.mul a b)
  low_low : ∀ a b, Low a → Low b → S.mul a b = zero

theorem runTail_zero {S : Semigroup α} (D : SplitAction S) (xs : List α) :
    runTail S D.zero xs = D.zero := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [runTail_cons, D.zero_mul, ih]

theorem mul_into_low {S : Semigroup α} (D : SplitAction S)
    (a b : α) (hb : D.Low b) : D.Low (S.mul a b) := by
  rcases D.cover a with ha | ha
  · rw [D.positive_low a b ha hb]
    exact hb
  · rw [D.low_low a b ha hb]
    exact D.zero_low

theorem low_mul_any {S : Semigroup α} (D : SplitAction S)
    (a b : α) (ha : D.Low a) : D.Low (S.mul a b) := by
  rcases D.cover b with hb | hb
  · exact D.low_positive a b ha hb
  · rw [D.low_low a b ha hb]
    exact D.zero_low

theorem runTail_low {S : Semigroup α} (D : SplitAction S)
    (a : α) (ha : D.Low a) (xs : List α) : D.Low (runTail S a xs) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
      rw [runTail_cons]
      exact ih (S.mul a x) (low_mul_any D a x ha)

theorem runTail_positive {S : Semigroup α} (D : SplitAction S)
    (a : α) (ha : D.Pos a) (xs : List α) (hxs : ∀ x ∈ xs, D.Pos x) :
    D.Pos (runTail S a xs) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
      rw [runTail_cons]
      exact ih (S.mul a x) (D.positive_positive a x ha (hxs x (List.Mem.head _)))
        (fun y hy => hxs y (List.Mem.tail _ hy))

theorem runTail_low_at {S : Semigroup α} (D : SplitAction S)
    (a b : α) (ha : D.Low a) (hb : D.Low b) (mid post : List α) :
    runTail S a (mid ++ b :: post) = D.zero := by
  rw [runTail_append, runTail_cons]
  have hmid : D.Low (runTail S a mid) := runTail_low D a ha mid
  rw [D.low_low (runTail S a mid) b hmid hb, runTail_zero]

theorem runTail_two_low {S : Semigroup α} (D : SplitAction S)
    (a i j : α) (hi : D.Low i) (hj : D.Low j) (pre mid post : List α) :
    runTail S a (pre ++ i :: (mid ++ j :: post)) = D.zero := by
  rw [runTail_append, runTail_cons]
  exact runTail_low_at D (S.mul (runTail S a pre) i) j
    (mul_into_low D (runTail S a pre) i hi) hj mid post

theorem runTail_positive_prefix_low {S : Semigroup α} (D : SplitAction S)
    (a i : α) (ha : D.Pos a) (hi : D.Low i) (pre post : List α)
    (hpre : ∀ x ∈ pre, D.Pos x) :
    runTail S a (pre ++ i :: post) = runTail S i post := by
  rw [runTail_append, runTail_cons]
  have hp : D.Pos (runTail S a pre) := runTail_positive D a ha pre hpre
  rw [D.positive_low (runTail S a pre) i hp hi]

/-- None records an empty word; it is not a value in S. -/
def evalValues (S : Semigroup α) : List α → Option α
  | [] => none
  | a :: xs => some (runTail S a xs)

theorem evalValues_word (S : Semigroup α) (w : Word α) :
    evalValues S w.toList = some (S.eval id w) := rfl

theorem evalValues_one_low {S : Semigroup α} (D : SplitAction S)
    (pre post : List α) (i : α) (hi : D.Low i) (hp : ∀ x ∈ pre, D.Pos x) :
    evalValues S (pre ++ i :: post) = some (runTail S i post) := by
  cases pre with
  | nil => rfl
  | cons a pre =>
      change some (runTail S a (pre ++ i :: post)) = some (runTail S i post)
      have ha : D.Pos a := hp a (List.Mem.head _)
      have hpre : ∀ x ∈ pre, D.Pos x := fun x hx => hp x (List.Mem.tail _ hx)
      exact congrArg some (runTail_positive_prefix_low D a i ha hi pre post hpre)

theorem evalValues_two_low {S : Semigroup α} (D : SplitAction S)
    (pre mid post : List α) (i j : α) (hi : D.Low i) (hj : D.Low j) :
    evalValues S (pre ++ i :: (mid ++ j :: post)) = some D.zero := by
  cases pre with
  | nil =>
      change some (runTail S i (mid ++ j :: post)) = some D.zero
      exact congrArg some (runTail_low_at D i j hi hj mid post)
  | cons a pre =>
      change some (runTail S a (pre ++ i :: (mid ++ j :: post))) = some D.zero
      exact congrArg some (runTail_two_low D a i j hi hj pre mid post)

theorem evalValues_zero_at {S : Semigroup α} (D : SplitAction S)
    (pre post : List α) : evalValues S (pre ++ D.zero :: post) = some D.zero := by
  cases pre with
  | nil =>
      change some (runTail S D.zero post) = some D.zero
      exact congrArg some (runTail_zero D post)
  | cons a pre =>
      change some (runTail S a (pre ++ D.zero :: post)) = some D.zero
      rw [runTail_append, runTail_cons, D.mul_zero, runTail_zero]

end SemigroupBasis.CoRoots.Order6Day15.B16
