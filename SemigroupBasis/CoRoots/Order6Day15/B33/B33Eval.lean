import SemigroupBasis.CoRoots.Order6Day15.B33.B33Shape

namespace SemigroupBasis.CoRoots.Order6Day15.B33

/-- A bookkeeping identity adjoined to a semigroup; no empty word is substituted. -/
def optMul (G : Semigroup S) : Option S → Option S → Option S
  | none,b => b
  | some a,none => some a
  | some a,some b => some (G.mul a b)

theorem optMul_assoc (G : Semigroup S) (a b c : Option S) :
    optMul G (optMul G a b) c = optMul G a (optMul G b c) := by
  cases a <;> cases b <;> cases c <;> simp only [optMul, G.assoc]

def evalList (G : Semigroup S) (v : Nat → S) : List Nat → Option S
  | [] => none
  | a :: xs => optMul G (some (v a)) (evalList G v xs)

theorem evalList_append (G : Semigroup S) (v : Nat → S) (xs ys : List Nat) :
    evalList G v (xs ++ ys) = optMul G (evalList G v xs) (evalList G v ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.cons_append, evalList, ih, optMul_assoc]

theorem evalList_word (G : Semigroup S) (v : Nat → S) (w : Word Nat) :
    evalList G v w.toList = some (G.eval v w) := by
  rcases w with ⟨a,xs⟩
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    change optMul G (some (v a)) (evalList G v (Word.toList ⟨b,bs⟩)) = _
    rw [ih]
    change some (G.mul (v a) (G.eval v ⟨b,bs⟩)) =
      some (G.eval v (Word.singleton a ++ ⟨b,bs⟩))
    rw [G.eval_append]
    rfl

def Power.value (p : Power) (G : Semigroup S) (a : S) : S :=
  match p with
  | .one => a
  | .two => G.mul a a
  | .three => G.mul (G.mul a a) a

theorem evalList_block (G : Semigroup S) (v : Nat → S) (b : Block) :
    evalList G v b.word = some (b.power.value G (v b.letter)) := by
  cases b with
  | mk a power => cases power <;> simp only [Block.word,evalList,optMul,Power.value,G.assoc]

def evalBlocks (G : Semigroup S) (v : Nat → S) (bs : List Block) : Option S :=
  evalList G v (render bs)

@[simp] theorem evalBlocks_nil (G : Semigroup S) (v : Nat → S) :
    evalBlocks G v [] = none := rfl

theorem evalBlocks_cons (G : Semigroup S) (v : Nat → S) (b : Block) (bs : List Block) :
    evalBlocks G v (b :: bs) =
      optMul G (some (b.power.value G (v b.letter))) (evalBlocks G v bs) := by
  unfold evalBlocks
  rw [render,evalList_append,evalList_block]

theorem normalBlocks_eval (G : Semigroup S) (hm : Models G basis)
    (v : Nat → S) (w : Word Nat) :
    evalBlocks G v (normalBlocks w) = some (G.eval v w) := by
  change evalList G v (render (normalBlocks w)) = _
  rw [← normalWord_toList,evalList_word]
  exact congrArg some (Derives.sound hm (normalWord_derives w) v).symm

theorem evalBlocks_congr (G : Semigroup S) (bs : List Block) (v u : Nat → S)
    (same : ∀ a, a ∈ letters bs → v a = u a) :
    evalBlocks G v bs = evalBlocks G u bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [evalBlocks_cons,evalBlocks_cons,same b.letter (by simp)]
    rw [ih (fun a h => same a (by simp [h]))]

end SemigroupBasis.CoRoots.Order6Day15.B33
