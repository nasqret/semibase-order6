namespace SemigroupBasis

/-- A word in the free semigroup: a head letter followed by a possibly empty tail. -/
structure Word (α : Type u) where
  head : α
  tail : List α
deriving Repr, DecidableEq

namespace Word

def toList (w : Word α) : List α :=
  w.head :: w.tail

theorem toList_injective : Function.Injective (@toList α) := by
  intro u v h
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          simp only [toList] at h
          injection h with headEq tailEq
          cases headEq
          cases tailEq
          rfl

def singleton (x : α) : Word α := ⟨x, []⟩

def append (u v : Word α) : Word α :=
  ⟨u.head, u.tail ++ v.head :: v.tail⟩

instance : Append (Word α) where
  append := append

@[simp]
theorem singleton_head (x : α) : (singleton x).head = x := rfl

@[simp]
theorem singleton_tail (x : α) : (singleton x).tail = [] := rfl

@[simp]
theorem append_head (u v : Word α) : (u ++ v).head = u.head := rfl

@[simp]
theorem append_tail (u v : Word α) :
    (u ++ v).tail = u.tail ++ v.head :: v.tail := rfl

@[simp]
theorem singleton_append (x : α) (v : Word α) :
    singleton x ++ v = ⟨x, v.head :: v.tail⟩ := rfl

@[simp]
theorem toList_singleton (x : α) : (singleton x).toList = [x] := rfl

@[simp]
theorem toList_append (u v : Word α) :
    (u ++ v).toList = u.toList ++ v.toList := by
  simp [toList]

theorem append_assoc (u v w : Word α) : (u ++ v) ++ w = u ++ (v ++ w) := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases w with
          | mk wHead wTail =>
              change
                Word.mk uHead ((uTail ++ vHead :: vTail) ++ wHead :: wTail) =
                  Word.mk uHead (uTail ++ vHead :: (vTail ++ wHead :: wTail))
              rw [List.append_assoc]
              rfl

def map (f : α → β) (w : Word α) : Word β :=
  ⟨f w.head, w.tail.map f⟩

/-- Simultaneous nonempty-word substitution. -/
def bind (w : Word α) (σ : α → Word β) : Word β :=
  w.tail.foldl (fun acc x => acc ++ σ x) (σ w.head)

private theorem toList_bind_fold (σ : α → Word β) (xs : List α)
    (initial : Word β) :
    (xs.foldl (fun acc x => acc ++ σ x) initial).toList =
      initial.toList ++ xs.flatMap (fun x => (σ x).toList) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih, toList_append, List.flatMap_cons, List.append_assoc]

theorem toList_bind (w : Word α) (σ : α → Word β) :
    (w.bind σ).toList =
      w.toList.flatMap (fun x => (σ x).toList) := by
  unfold bind
  rw [toList_bind_fold]
  rfl

end Word

/-- A semigroup operation, kept explicit so many finite tables can coexist. -/
structure Semigroup (S : Type u) where
  mul : S → S → S
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

namespace Semigroup

def eval (G : Semigroup S) (valuation : α → S) (w : Word α) : S :=
  w.tail.foldl (fun acc x => G.mul acc (valuation x)) (valuation w.head)

private theorem foldl_mul_assoc (G : Semigroup S) (valuation : α → S)
    (a b : S) (xs : List α) :
    xs.foldl (fun acc x => G.mul acc (valuation x)) (G.mul a b) =
      G.mul a (xs.foldl (fun acc x => G.mul acc (valuation x)) b) := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [G.assoc]
      exact ih (G.mul b (valuation x))

@[simp]
theorem eval_singleton (G : Semigroup S) (valuation : α → S) (x : α) :
    G.eval valuation (Word.singleton x) = valuation x := rfl

theorem eval_append (G : Semigroup S) (valuation : α → S) (u v : Word α) :
    G.eval valuation (u ++ v) = G.mul (G.eval valuation u) (G.eval valuation v) := by
  simp only [eval, Word.append_tail, Word.append_head, List.foldl_append,
    List.foldl_cons]
  exact foldl_mul_assoc G valuation
    (List.foldl (fun acc x => G.mul acc (valuation x)) (valuation u.head) u.tail)
    (valuation v.head)
    v.tail

private theorem eval_bind_fold (G : Semigroup S) (valuation : β → S)
    (σ : α → Word β) (xs : List α) (acc : Word β) :
    G.eval valuation (xs.foldl (fun current x => current ++ σ x) acc) =
      xs.foldl (fun current x => G.mul current (G.eval valuation (σ x)))
        (G.eval valuation acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih, eval_append]

theorem eval_bind (G : Semigroup S) (valuation : β → S)
    (w : Word α) (σ : α → Word β) :
    G.eval valuation (w.bind σ) =
      G.eval (fun x => G.eval valuation (σ x)) w := by
  unfold Word.bind
  rw [eval_bind_fold]
  rfl

end Semigroup
end SemigroupBasis
