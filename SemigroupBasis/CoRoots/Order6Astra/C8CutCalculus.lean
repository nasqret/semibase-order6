import SemigroupBasis.CoRoots.Order6Astra.C8SemanticKey

namespace SemigroupBasis.CoRoots.Order6Astra.C8CutCalculus

open C8TailCuts C8SemanticKey

theorem disjoint_symm {u v : List Nat} (h : Disjoint u v) : Disjoint v u :=
  fun x hx hy => h x hy hx

theorem same_refl (u : List Nat) : SameSupport u u := fun _ => Iff.rfl

theorem same_symm {u v : List Nat} (h : SameSupport u v) : SameSupport v u :=
  fun x => (h x).symm

/-- Two cuts of one literal list are comparable, with the intervening word
retained explicitly. -/
theorem compare_cuts {α : Type} (a b c d : List α) (equal : a ++ b = c ++ d) :
    (∃ middle, c = a ++ middle ∧ b = middle ++ d) ∨
      (∃ middle, a = c ++ middle ∧ d = middle ++ b) := by
  induction a generalizing c with
  | nil => exact Or.inl ⟨c, rfl, equal⟩
  | cons x xs ih =>
    cases c with
    | nil => exact Or.inr ⟨x :: xs, rfl, equal.symm⟩
    | cons y ys =>
      obtain ⟨headEqual, tailEqual⟩ := List.cons.inj equal
      subst y
      rcases ih ys tailEqual with ⟨middle, first, second⟩ | ⟨middle, first, second⟩
      · exact Or.inl ⟨middle, congrArg (List.cons x) first, second⟩
      · exact Or.inr ⟨middle, congrArg (List.cons x) first, second⟩

theorem cut_support_unique (a b c d : List Nat) (equal : a ++ b = c ++ d)
    (apart : Disjoint a b) (apart' : Disjoint c d) (same : SameSupport a c) :
    a = c ∧ b = d := by
  rcases compare_cuts a b c d equal with ⟨middle, first, second⟩ | ⟨middle, first, second⟩
  · have empty : middle = [] := by
      cases middle with
      | nil => rfl
      | cons x xs =>
        have inC : x ∈ c := by rw [first]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
        have inB : x ∈ b := by rw [second]; exact List.mem_append.mpr (Or.inl List.mem_cons_self)
        exact False.elim (apart x ((same x).mpr inC) inB)
    simpa only [empty, List.append_nil, List.nil_append] using And.intro first.symm second
  · have empty : middle = [] := by
      cases middle with
      | nil => rfl
      | cons x xs =>
        have inA : x ∈ a := by rw [first]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
        have inD : x ∈ d := by rw [second]; exact List.mem_append.mpr (Or.inl List.mem_cons_self)
        exact False.elim (apart' x ((same x).mp inA) inD)
    simpa only [empty, List.append_nil, List.nil_append] using And.intro first second.symm

theorem marker_split_unique (t : Nat) (p s q r : List Nat)
    (equal : p ++ t :: s = q ++ t :: r) (leftAbsent : t ∉ p) (rightAbsent : t ∉ q) :
    p = q ∧ s = r := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => exact ⟨rfl, (List.cons.inj equal).2⟩
    | cons x xs =>
      have same : t = x := (List.cons.inj equal).1
      exact False.elim (rightAbsent (List.mem_cons.mpr (Or.inl same)))
  | cons x xs ih =>
    cases q with
    | nil =>
      have same : t = x := (List.cons.inj equal).1.symm
      exact False.elim (leftAbsent (List.mem_cons.mpr (Or.inl same)))
    | cons y ys =>
      have both := List.cons.inj equal
      obtain ⟨tails, final⟩ := ih ys both.2
        (fun hx => leftAbsent (List.mem_cons_of_mem x hx))
        (fun hy => rightAbsent (List.mem_cons_of_mem y hy))
      exact ⟨by rw [both.1, tails], final⟩

theorem tailAt_at_split (letters : List Nat) (t : Nat) (p s z : List Nat)
    (split : letters = p ++ t :: s) (simple : letters.count t = 1) :
    TailAt letters t z ↔ Tail p s z := by
  constructor
  · rintro ⟨q, r, actual, tail⟩
    have first := marker_absent letters p s t split simple
    have second := marker_absent letters q r t actual simple
    obtain ⟨eqP, eqS⟩ := marker_split_unique t p s q r (split.symm.trans actual) first.1 second.1
    simpa only [eqP, eqS] using tail
  · intro tail
    exact ⟨p, s, split, tail⟩

/-- A suffix avoiding a displayed barrier starts strictly after that barrier. -/
theorem suffix_after_barrier (left : List Nat) (barrier : Nat) (p a b : List Nat)
    (equal : left ++ barrier :: p = a ++ b) (absent : barrier ∉ b) :
    ∃ middle, p = middle ++ b ∧ a = left ++ barrier :: middle := by
  induction left generalizing a with
  | nil =>
    cases a with
    | nil =>
      change barrier :: p = b at equal
      have present : barrier ∈ b := by rw [← equal]; exact List.mem_cons_self
      exact False.elim (absent present)
    | cons x xs =>
      have both := List.cons.inj equal
      exact ⟨xs, both.2, by rw [both.1]; rfl⟩
  | cons x xs ih =>
    cases a with
    | nil =>
      change (x :: xs) ++ barrier :: p = b at equal
      have present : barrier ∈ b := by
        rw [← equal]
        exact List.mem_append.mpr (Or.inr List.mem_cons_self)
      exact False.elim (absent present)
    | cons y ys =>
      have both := List.cons.inj equal
      obtain ⟨middle, split, actual⟩ := ih ys both.2
      exact ⟨middle, split, by rw [both.1, actual]; rfl⟩

/-- A recurring separator blocks every tail from crossing the left frame.
Support-isolation supplies the converse; the branch itself is arbitrary. -/
theorem tail_frame (left right p s z : List Nat) (barrier : Nat)
    (recurs : barrier ∈ right) (isolated : Disjoint (p ++ s) (left ++ barrier :: right)) :
    Tail (left ++ barrier :: p) (s ++ right) z ↔ Tail p s z := by
  constructor
  · rintro ⟨a, b, equal, same, apart⟩
    have absent : barrier ∉ b := by
      intro member
      exact apart barrier member (List.mem_append.mpr (Or.inr
        (List.mem_append.mpr (Or.inr recurs))))
    obtain ⟨middle, localSplit, globalSplit⟩ := suffix_after_barrier left barrier p a b equal absent
    refine ⟨middle, b, localSplit, same, ?_⟩
    intro x hx contrary
    apply apart x hx
    rcases List.mem_append.mp contrary with inMiddle | inS
    · apply List.mem_append.mpr
      apply Or.inl
      rw [globalSplit]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem barrier inMiddle))
    · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl inS)))
  · rintro ⟨middle, b, localSplit, same, apart⟩
    refine ⟨left ++ barrier :: middle, b, ?_, same, ?_⟩
    · simp only [localSplit, List.append_assoc, List.cons_append]
    · intro x hx contrary
      have inBranch : x ∈ p ++ s := by
        rw [localSplit]
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx)))
      rcases List.mem_append.mp contrary with inLeft | inRight
      · rcases List.mem_append.mp inLeft with outside | later
        · exact isolated x inBranch (List.mem_append.mpr (Or.inl outside))
        · rcases List.mem_cons.mp later with barrierEqual | inMiddle
          · exact isolated x inBranch
              (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl barrierEqual))))
          · exact apart x hx (List.mem_append.mpr (Or.inl inMiddle))
      · rcases List.mem_append.mp inRight with inS | outside
        · exact apart x hx (List.mem_append.mpr (Or.inr inS))
        · exact isolated x inBranch
            (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem barrier outside)))

end SemigroupBasis.CoRoots.Order6Astra.C8CutCalculus

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8CutCalculus.cut_support_unique
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8CutCalculus.tailAt_at_split
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8CutCalculus.tail_frame
