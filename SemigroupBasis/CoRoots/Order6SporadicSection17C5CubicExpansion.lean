import SemigroupBasis.CoRoots.Order6SporadicSection17C5Restricted

/-! The first unrestricted stage of Lemma17.4. Every occurrence of an
unrestricted letter may be replaced by a cube. The proof first constructs
a genuine separated occurrence pair, then retains a cubic anchor while
expanding both contexts. An isolated square never satisfies the premise. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
open SemigroupBasis

def Separated (x : Nat) (letters : List Nat) : Prop :=
  ∃ before gap after, gap ≠ [] ∧ letters = before ++ [x] ++ gap ++ [x] ++ after

theorem unrestricted_separated (x : Nat) (letters : List Nat) (unrestricted : Unrestricted x letters) :
    Separated x letters := by
  induction letters with
  | nil => simp [Unrestricted] at unrestricted
  | cons y ys ih =>
      by_cases equal : y = x
      · subst y
        have found : x ∈ ys := by
          by_cases present : x ∈ ys
          · exact present
          · have zero := List.count_eq_zero.mpr present
            exact False.elim (unrestricted.2.1 (by simp [zero]))
        obtain ⟨gap,after,shape⟩ := List.mem_iff_append.mp found
        cases gap with
        | nil =>
            have shape' : ys = x :: after := by simpa using shape
            have again : x ∈ after := by
              by_cases present : x ∈ after
              · exact present
              · exact False.elim (unrestricted.2.2
                  ((restricted_cons_same x ys).mpr ⟨after,shape',present⟩))
            obtain ⟨middle,last,lastShape⟩ := List.mem_iff_append.mp again
            refine ⟨[],x :: middle,last,by simp,?_⟩
            simp [shape',lastShape,List.append_assoc]
        | cons h tail =>
            exact ⟨[],h :: tail,after,by simp,by simp [shape,List.append_assoc]⟩
      · have tailUnrestricted : Unrestricted x ys := by
          refine ⟨?_,?_,?_⟩
          · exact (List.mem_cons.mp unrestricted.1).resolve_left (Ne.symm equal)
          · simpa [List.count_cons_of_ne equal] using unrestricted.2.1
          · intro restricted
            exact unrestricted.2.2 ((restricted_cons_ne x y ys equal).mpr restricted)
        obtain ⟨before,gap,after,nonempty,shape⟩ := ih tailUnrestricted
        exact ⟨y :: before,gap,after,nonempty,by simp [shape,List.append_assoc]⟩

def tripleMarker (marker : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if x = marker then x :: x :: x :: tripleMarker marker xs
      else x :: tripleMarker marker xs

theorem tripleMarker_append (marker : Nat) (left right : List Nat) :
    tripleMarker marker (left ++ right) = tripleMarker marker left ++ tripleMarker marker right := by
  induction left with
  | nil => rfl
  | cons x xs ih => by_cases equal : x = marker <;> simp [tripleMarker,equal,ih]

theorem cubeBeforeAnchor (x : Nat) (gap : List Nat) :
    ListDerives ([x] ++ gap ++ [x,x,x]) ([x,x,x] ++ gap ++ [x,x,x]) := by
  have nonempty : gap ++ [x,x] ≠ [] := by simp
  simpa [List.append_assoc] using cubeFirst x (gap ++ [x,x]) nonempty

theorem cubeAfterAnchor (x : Nat) (gap : List Nat) :
    ListDerives ([x,x,x] ++ gap ++ [x]) ([x,x,x] ++ gap ++ [x,x,x]) := by
  have nonempty : [x,x] ++ gap ≠ [] := by simp
  simpa [List.append_assoc] using cubeLast x ([x,x] ++ gap) nonempty

theorem tripleBeforeCube (x : Nat) (before after : List Nat) :
    ListDerives (before ++ [x,x,x] ++ after)
      (tripleMarker x before ++ [x,x,x] ++ after) := by
  induction before with
  | nil => exact S5_107.ListDerives.refl _
  | cons y ys ih =>
      by_cases equal : y = x
      · subst y
        have first : ListDerives ((x :: ys) ++ [x,x,x] ++ after)
            ([x,x,x] ++ ys ++ [x,x,x] ++ after) := by
          simpa [List.append_assoc] using (cubeBeforeAnchor x ys).append after
        have second : ListDerives ([x,x,x] ++ ys ++ [x,x,x] ++ after)
            ([x,x,x] ++ tripleMarker x ys ++ [x,x,x] ++ after) := by
          simpa [List.append_assoc] using ih.prepend [x,x,x]
        simpa [tripleMarker,List.append_assoc] using first.trans second
      · simpa [tripleMarker,equal,List.append_assoc] using ih.prepend [y]

theorem tripleAfterCube (x : Nat) (stem suffix : List Nat) :
    ListDerives ([x,x,x] ++ stem ++ suffix)
      ([x,x,x] ++ stem ++ tripleMarker x suffix) := by
  induction suffix generalizing stem with
  | nil => exact S5_107.ListDerives.refl _
  | cons y ys ih =>
      by_cases equal : y = x
      · subst y
        have first : ListDerives ([x,x,x] ++ stem ++ x :: ys)
            ([x,x,x] ++ stem ++ [x,x,x] ++ ys) := by
          simpa [List.append_assoc] using (cubeAfterAnchor x stem).append ys
        have second : ListDerives ([x,x,x] ++ stem ++ [x,x,x] ++ ys)
            ([x,x,x] ++ stem ++ [x,x,x] ++ tripleMarker x ys) := by
          simpa [List.append_assoc] using ih (stem ++ [x,x,x])
        simpa [tripleMarker,List.append_assoc] using first.trans second
      · simpa [tripleMarker,equal,List.append_assoc] using ih (stem ++ [y])

theorem tripleMarker_of_separated (x : Nat) (letters : List Nat) (separated : Separated x letters) :
    ListDerives letters (tripleMarker x letters) := by
  obtain ⟨before,gap,after,nonempty,shape⟩ := separated
  have first : ListDerives letters (before ++ [x,x,x] ++ gap ++ [x] ++ after) := by
    simpa [shape,List.append_assoc] using ((cubeFirst x gap nonempty).prepend before).append after
  have second : ListDerives (before ++ [x,x,x] ++ gap ++ [x] ++ after)
      (tripleMarker x before ++ [x,x,x] ++ gap ++ [x] ++ after) := by
    simpa [List.append_assoc] using tripleBeforeCube x before (gap ++ [x] ++ after)
  have third : ListDerives (tripleMarker x before ++ [x,x,x] ++ gap ++ [x] ++ after)
      (tripleMarker x before ++ [x,x,x] ++ tripleMarker x (gap ++ [x] ++ after)) := by
    simpa [List.append_assoc] using (tripleAfterCube x [] (gap ++ [x] ++ after)).prepend (tripleMarker x before)
  have combined := first.trans (second.trans third)
  simpa [shape,tripleMarker_append,tripleMarker,List.append_assoc] using combined

theorem tripleMarker_derives (x : Nat) (letters : List Nat) (unrestricted : Unrestricted x letters) :
    ListDerives letters (tripleMarker x letters) :=
  tripleMarker_of_separated x letters (unrestricted_separated x letters unrestricted)

/-- No completeness assumption: raw13 Models and the proved detector preserve
unrestricted status while the already-expanded context grows. -/
theorem ListDerives.unrestricted_iff {left right : List Nat} (derivation : ListDerives left right) (x : Nat) :
    Unrestricted x left ↔ Unrestricted x right :=
  (Semantics.derives_sameEval false derivation).unrestricted x

def tripleMarkers : List Nat → List Nat → List Nat
  | [], letters => letters
  | x :: xs, letters => tripleMarker x (tripleMarkers xs letters)

theorem tripleMarkers_derives (markers letters : List Nat)
    (selected : ∀ x ∈ markers, Unrestricted x letters) :
    ListDerives letters (tripleMarkers markers letters) := by
  induction markers with
  | nil => exact S5_107.ListDerives.refl _
  | cons x xs ih =>
      have tailSelected : ∀ y ∈ xs, Unrestricted y letters :=
        fun y member => selected y (List.mem_cons.mpr (Or.inr member))
      have first := ih tailSelected
      have current : Unrestricted x (tripleMarkers xs letters) :=
        (ListDerives.unrestricted_iff first x).mp (selected x (List.mem_cons_self))
      exact first.trans (tripleMarker_derives x _ current)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.unrestricted_separated
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeBeforeAnchor
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.cubeAfterAnchor
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tripleBeforeCube
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tripleAfterCube
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tripleMarker_of_separated
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tripleMarker_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.ListDerives.unrestricted_iff
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.tripleMarkers_derives

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6
