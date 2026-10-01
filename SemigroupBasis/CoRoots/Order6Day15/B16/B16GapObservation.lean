import SemigroupBasis.CoRoots.Order6Day15.B16.B16WordNormalization

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

def GapPin (a : Nat) : List Nat → List Nat → Prop
  | [], _ => False
  | b :: bs, post => b = a ∧ a ∉ bs ++ post

def SameGapObservation (xs post ys post' : List Nat) : Prop :=
  (xs = [] ↔ ys = []) ∧
  (∀ a, a ∈ xs ++ post ↔ a ∈ ys ++ post') ∧
  (∀ a, a ∈ post ↔ a ∈ post') ∧
  (∀ a, GapPin a xs post ↔ GapPin a ys post')

theorem leastActive_eq_of_support (ns : List Nat) (a b : Nat) (xs post ys post' : List Nat)
    (ha : a ∈ ns) (hb : b ∈ ns)
    (same : ∀ c, c ∈ a :: (xs ++ post) ↔ c ∈ b :: (ys ++ post')) :
    leastActive ns a xs post = leastActive ns b ys post' := by
  have left := leastActive_spec ns a xs post ha
  have right := leastActive_spec ns b ys post' hb
  have lmem : leastActive ns a xs post ∈ a :: (xs ++ post) := List.mem_cons.mpr left.2.1
  have rmem : leastActive ns b ys post' ∈ b :: (ys ++ post') := List.mem_cons.mpr right.2.1
  exact Nat.le_antisymm (left.2.2 _ right.1 ((same _).mpr rmem))
    (right.2.2 _ left.1 ((same _).mp lmem))

theorem finalLetters_eq_of_union_support (xs post ys post' : List Nat)
    (total : ∀ a, a ∈ xs ++ post ↔ a ∈ ys ++ post')
    (future : ∀ a, a ∈ post ↔ a ∈ post') :
    canonicalSupport (finalLetters xs post) = canonicalSupport (finalLetters ys post') := by
  apply canonicalSupport_eq_of_support
  intro a
  rw [mem_finalLetters_iff, mem_finalLetters_iff]
  constructor
  · intro h
    have absent : a ∉ post' := fun hp => h.2 ((future a).mpr hp)
    have mem : a ∈ ys ++ post' := (total a).mp (List.mem_append.mpr (Or.inl h.1))
    exact ⟨(List.mem_append.mp mem).resolve_right absent, absent⟩
  · intro h
    have absent : a ∉ post := fun hp => h.2 ((future a).mp hp)
    have mem : a ∈ xs ++ post := (total a).mpr (List.mem_append.mpr (Or.inl h.1))
    exact ⟨(List.mem_append.mp mem).resolve_right absent, absent⟩

/-- The computed G renderer depends only on empty/total/future/pinned data. -/
theorem renderedGap_eq_of_observation (ns xs post ys post' : List Nat)
    (leftCovered : ∀ a ∈ xs, a ∈ ns) (rightCovered : ∀ a ∈ ys, a ∈ ns)
    (obs : SameGapObservation xs post ys post') :
    renderedGap ns xs post = renderedGap ns ys post' := by
  rcases obs with ⟨empty,total,future,pins⟩
  cases xs with
  | nil =>
      have rightEmpty : ys = [] := empty.mp rfl
      rw [rightEmpty]; rfl
  | cons a xs =>
      cases ys with
      | nil => have bad := empty.mpr rfl; cases bad
      | cons b ys =>
          have ha : a ∈ ns := leftCovered a (List.Mem.head _)
          have hb : b ∈ ns := rightCovered b (List.Mem.head _)
          by_cases later : a ∈ xs ++ post
          · have later' : b ∈ ys ++ post' := by
              by_cases present : b ∈ ys ++ post'
              · exact present
              have pin : GapPin b (b :: ys) post' := ⟨rfl,present⟩
              have old : a = b ∧ b ∉ xs ++ post := (pins b).mpr pin
              exact False.elim (old.2 (old.1 ▸ later))
            have anchors : leastActive ns a xs post = leastActive ns b ys post' :=
              leastActive_eq_of_support ns a b xs post ys post' ha hb total
            let c := leastActive ns b ys post'
            have total' : ∀ z, z ∈ (a :: xs) ++ (c :: post) ↔ z ∈ (b :: ys) ++ (c :: post') := by
              intro z
              have expand (g p : List Nat) : z ∈ g ++ (c :: p) ↔ z ∈ g ++ p ∨ z = c := by
                constructor
                · intro h
                  rcases List.mem_append.mp h with left | right
                  · exact Or.inl (List.mem_append.mpr (Or.inl left))
                  · rcases List.mem_cons.mp right with eq | mem
                    · exact Or.inr eq
                    · exact Or.inl (List.mem_append.mpr (Or.inr mem))
                · intro h
                  rcases h with old | eq
                  · rcases List.mem_append.mp old with left | right
                    · exact List.mem_append.mpr (Or.inl left)
                    · exact List.mem_append.mpr (Or.inr (List.Mem.tail _ right))
                  · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl eq)))
              exact (expand (a :: xs) post).trans
                ((or_congr (total z) Iff.rfl).trans (expand (b :: ys) post').symm)
            have future' : ∀ z, z ∈ c :: post ↔ z ∈ c :: post' := by
              intro z
              simp only [List.mem_cons, future z]
            have tails := finalLetters_eq_of_union_support (a :: xs) (c :: post) (b :: ys) (c :: post') total' future'
            rw [renderedGap, if_pos later, renderedGap, if_pos later', anchors]
            exact congrArg (fun fs => c :: c :: squares fs) tails
          · have pin : GapPin a (a :: xs) post := ⟨rfl,later⟩
            rcases (show b = a ∧ a ∉ ys ++ post' from (pins a).mp pin) with ⟨heads,absent⟩
            subst b
            have tailTotal : ∀ z, z ∈ xs ++ post ↔ z ∈ ys ++ post' := by
              intro z
              constructor
              · intro hz
                have ne : z ≠ a := fun eq => later (eq ▸ hz)
                have mem : z ∈ a :: (ys ++ post') := (total z).mp (List.Mem.tail _ hz)
                exact (List.mem_cons.mp mem).resolve_left ne
              · intro hz
                have ne : z ≠ a := fun eq => absent (eq ▸ hz)
                have mem : z ∈ a :: (xs ++ post) := (total z).mpr (List.Mem.tail _ hz)
                exact (List.mem_cons.mp mem).resolve_left ne
            have tails := finalLetters_eq_of_union_support xs post ys post' tailTotal future
            rw [renderedGap, if_neg later, renderedGap, if_neg absent]
            exact congrArg (fun fs => a :: squares fs) tails

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach
