import SemigroupBasis.CoRoots.Order6SporadicSection26Derivations

/-! The three cases of Lemma26.2 unified without a finite alphabet bound.
Two already-seen trailing letters can be replaced by one trailing letter,
while the removed occurrence is moved beside its first occurrence. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection26.F7
open SemigroupBasis

def bumpFirst (x : Nat) : List Nat → List Nat
  | [] => []
  | h :: t => if h = x then h :: h :: t else h :: bumpFirst x t

theorem bumpFirst_append_of_not_mem (x : Nat) (before after : List Nat)
    (missing : x ∉ before) :
    bumpFirst x (before ++ after) = before ++ bumpFirst x after := by
  induction before with
  | nil => rfl
  | cons h t ih =>
      have different : h ≠ x := by
        intro same
        subst h
        exact missing (by simp)
      have missingTail : x ∉ t := by
        intro present
        exact missing (by simp [present])
      simp only [List.cons_append,bumpFirst,if_neg different,ih missingTail]

theorem exists_first_split (x : Nat) (letters : List Nat) (present : x ∈ letters) :
    ∃ before after, x ∉ before ∧ letters = before ++ x :: after := by
  induction letters with
  | nil => simp at present
  | cons h t ih =>
      by_cases same : h = x
      · subst h
        exact ⟨[],t,by simp,rfl⟩
      · have tailPresent : x ∈ t := by simpa [same,Ne.symm same] using present
        obtain ⟨before,after,missing,shape⟩ := ih tailPresent
        refine ⟨h :: before,after,?_,?_⟩
        · simp [missing,same,Ne.symm same]
        · simp only [shape,List.cons_append]

theorem absorbPair (stem : List Nat) (x y : Nat)
    (seenX : x ∈ stem) (seenY : y ∈ stem) :
    ListDerives (stem ++ [x,y]) (bumpFirst x stem ++ [y]) := by
  induction stem with
  | nil => simp at seenX
  | cons h t ih =>
      by_cases hx : h = x
      · subst h
        by_cases xy : x = y
        · subst y
          have first : ListDerives ([x] ++ t ++ [x,x]) ([x] ++ t ++ [x]) :=
            (duplicateLast x t).symm
          have second := duplicateFirst x t
          simpa [bumpFirst,List.append_assoc] using first.trans second
        · have tailY : y ∈ t := by simpa [xy,Ne.symm xy] using seenY
          obtain ⟨before,after,shape⟩ := List.mem_iff_append.mp tailY
          simpa [bumpFirst,shape,List.append_assoc] using pairMove x y before after
      · have tailX : x ∈ t := by simpa [hx,Ne.symm hx] using seenX
        by_cases hy : h = y
        · subst h
          obtain ⟨before,after,missing,shape⟩ := exists_first_split x t tailX
          have bump : bumpFirst x (y :: t) = y :: (before ++ x :: x :: after) := by
            rw [bumpFirst,if_neg hx,shape,bumpFirst_append_of_not_mem x before (x :: after) missing]
            simp [bumpFirst]
          rw [bump]
          cases after with
          | nil =>
              simpa [shape,List.append_assoc] using
                (S5_107.ListDerives.refl (basis := basis) (y :: (before ++ [x,x,y])))
          | cons k ks =>
              have raw := crossingFold y x before (Word.mk k ks)
              simpa [shape,Word.toList,List.append_assoc] using raw
        · have tailY : y ∈ t := by simpa [hy,Ne.symm hy] using seenY
          have raw := (ih tailX tailY).prepend [h]
          simpa [bumpFirst,hx,List.append_assoc] using raw

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.bumpFirst_append_of_not_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.exists_first_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.absorbPair
end SemigroupBasis.CoRoots.Order6SporadicSection26.F7
