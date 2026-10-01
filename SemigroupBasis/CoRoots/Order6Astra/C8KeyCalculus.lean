import SemigroupBasis.CoRoots.Order6Astra.C8CutCalculus

namespace SemigroupBasis.CoRoots.Order6Astra.C8KeyCalculus

open C8TailCuts C8SemanticKey C8CutCalculus

theorem cut_of_tail (letters z tailSupport : List Nat)
    (tail : Tail letters [] tailSupport) (whole : SameSupport letters (z ++ tailSupport))
    (partition : Disjoint z tailSupport) : Cut letters z := by
  obtain ⟨a, b, split, same, apart⟩ := tail
  have disjoint : Disjoint b a := by simpa only [List.append_nil] using apart
  refine ⟨a, b, split, ?_, disjoint_symm disjoint⟩
  intro x
  constructor
  · intro hx
    have inWhole : x ∈ letters := by rw [split]; exact List.mem_append.mpr (Or.inl hx)
    rcases List.mem_append.mp ((whole x).mp inWhole) with inZ | inTail
    · exact inZ
    · exact False.elim (disjoint x ((same x).mpr inTail) hx)
  · intro hx
    have inWhole := (whole x).mpr (List.mem_append.mpr (Or.inl hx))
    rw [split] at inWhole
    rcases List.mem_append.mp inWhole with inA | inB
    · exact inA
    · exact False.elim (partition x hx ((same x).mp inB))

theorem cuts_of_tails_forward (u v : List Nat) (same : SameSupport u v)
    (tails : ∀ z, Tail u [] z → Tail v [] z) (z : List Nat) (cut : Cut u z) : Cut v z := by
  obtain ⟨a, b, split, support, apart⟩ := cut
  have tail : Tail u [] b := ⟨a, b, split, same_refl b, by
    simpa only [List.append_nil] using disjoint_symm apart⟩
  apply cut_of_tail v z b (tails b tail)
  · intro x
    rw [← same x, split, List.mem_append, List.mem_append, support x]
  · intro x hx hb
    exact apart x ((support x).mpr hx) hb

theorem cuts_of_tails (u v : List Nat) (same : SameSupport u v)
    (tails : ∀ z, Tail u [] z ↔ Tail v [] z) : ∀ z, Cut u z ↔ Cut v z := by
  intro z
  exact ⟨cuts_of_tails_forward u v same (fun z => (tails z).mp) z,
    cuts_of_tails_forward v u (same_symm same) (fun z => (tails z).mpr) z⟩

theorem singleton_of_support_count (letters : List Nat) (marker : Nat)
    (onlyMarker : ∀ x ∈ letters, x = marker) (count : letters.count marker = 1) :
    letters = [marker] := by
  cases letters with
  | nil => simp at count
  | cons x xs =>
    have equal := onlyMarker x List.mem_cons_self
    subst x
    cases xs with
    | nil => rfl
    | cons y ys =>
      have equal := onlyMarker y (List.mem_cons_of_mem marker List.mem_cons_self)
      subst y
      simp only [List.count_cons_self] at count
      omega

/-- Two adjacent cut-support signatures isolate a simple singleton component.
Thus the full-prefix flag is reconstructible from proved cut data. -/
theorem full_of_cuts_forward (u v : List Nat) (marker : Nat)
    (simpleU : u.count marker = 1) (simpleV : v.count marker = 1)
    (cuts : ∀ z, Cut u z → Cut v z) (full : FullAt u marker) : FullAt v marker := by
  obtain ⟨p, s, split, apart⟩ := full
  have absent := marker_absent u p s marker split simpleU
  have before : Cut u p := by
    refine ⟨p, marker :: s, split, same_refl p, ?_⟩
    intro x hx contrary
    rcases List.mem_cons.mp contrary with equal | inS
    · subst x
      exact absent.1 hx
    · exact apart x hx inS
  have after : Cut u (p ++ [marker]) := by
    refine ⟨p ++ [marker], s, ?_, same_refl _, ?_⟩
    · simpa only [List.append_assoc, List.singleton_append] using split
    · intro x hx contrary
      rcases List.mem_append.mp hx with inP | isMarker
      · exact apart x inP contrary
      · have equal := List.mem_singleton.mp isMarker
        subst x
        exact absent.2 contrary
  obtain ⟨a, b, first, firstSupport, firstApart⟩ := cuts p before
  obtain ⟨c, d, second, secondSupport, _⟩ := cuts (p ++ [marker]) after
  have notA : marker ∉ a := fun h => absent.1 ((firstSupport marker).mp h)
  have inC : marker ∈ c := (secondSupport marker).mpr (List.mem_append.mpr (Or.inr List.mem_cons_self))
  rcases compare_cuts a b c d (first.symm.trans second) with
    ⟨middle, cSplit, bSplit⟩ | ⟨middle, aSplit, _⟩
  · have onlyMarker : ∀ x ∈ middle, x = marker := by
      intro x hx
      have memberC : x ∈ c := by rw [cSplit]; exact List.mem_append.mpr (Or.inr hx)
      have memberB : x ∈ b := by rw [bSplit]; exact List.mem_append.mpr (Or.inl hx)
      rcases List.mem_append.mp ((secondSupport x).mp memberC) with inP | equal
      · exact False.elim (firstApart x ((firstSupport x).mpr inP) memberB)
      · exact List.mem_singleton.mp equal
    have inMiddle : marker ∈ middle := by
      rw [cSplit, List.mem_append] at inC
      exact inC.resolve_left notA
    have positive := List.one_le_count_iff.mpr inMiddle
    have middleCount : middle.count marker = 1 := by
      rw [first, bSplit, List.count_append, List.count_append] at simpleV
      omega
    have singleton := singleton_of_support_count middle marker onlyMarker middleCount
    refine ⟨a, d, ?_, ?_⟩
    · simpa only [bSplit, singleton, List.singleton_append] using first
    · intro x hx hd
      apply firstApart x hx
      rw [bSplit]
      exact List.mem_append.mpr (Or.inr hd)
  · have inA : marker ∈ a := by rw [aSplit]; exact List.mem_append.mpr (Or.inl inC)
    exact False.elim (notA inA)

/-- If the tested support is disjoint from the exterior, its tail query is
unchanged by adding that exterior. Unlike `tail_frame`, no barrier is needed. -/
theorem tail_frame_disjoint (left right p s z : List Nat)
    (outside : Disjoint z (left ++ right)) :
    Tail (left ++ p) (s ++ right) z ↔ Tail p s z := by
  constructor
  · rintro ⟨a, b, literal, same, apart⟩
    have localCut : ∃ middle, p = middle ++ b ∧ a = left ++ middle := by
      rcases compare_cuts left p a b literal with ⟨middle, first, second⟩ | ⟨middle, first, second⟩
      · exact ⟨middle, second, first⟩
      · have empty : middle = [] := by
          cases middle with
          | nil => rfl
          | cons x xs =>
            have inLeft : x ∈ left := by rw [first]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
            have inB : x ∈ b := by rw [second]; exact List.mem_append.mpr (Or.inl List.mem_cons_self)
            exact False.elim (outside x ((same x).mp inB) (List.mem_append.mpr (Or.inl inLeft)))
        refine ⟨[], ?_, ?_⟩
        · simpa only [empty, List.nil_append] using second.symm
        · simpa only [empty, List.append_nil] using first.symm
    obtain ⟨middle, split, actual⟩ := localCut
    refine ⟨middle, b, split, same, ?_⟩
    intro x hx contrary
    apply apart x hx
    rcases List.mem_append.mp contrary with inMiddle | inS
    · apply List.mem_append.mpr
      apply Or.inl
      rw [actual]
      exact List.mem_append.mpr (Or.inr inMiddle)
    · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl inS)))
  · rintro ⟨middle, b, split, same, apart⟩
    refine ⟨left ++ middle, b, ?_, same, ?_⟩
    · simp only [split, List.append_assoc]
    · intro x hx contrary
      rcases List.mem_append.mp contrary with inBefore | inAfter
      · rcases List.mem_append.mp inBefore with inLeft | inMiddle
        · exact outside x ((same x).mp hx) (List.mem_append.mpr (Or.inl inLeft))
        · exact apart x hx (List.mem_append.mpr (Or.inl inMiddle))
      · rcases List.mem_append.mp inAfter with inS | inRight
        · exact apart x hx (List.mem_append.mpr (Or.inr inS))
        · exact outside x ((same x).mp hx) (List.mem_append.mpr (Or.inr inRight))

end SemigroupBasis.CoRoots.Order6Astra.C8KeyCalculus

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8KeyCalculus.cuts_of_tails
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8KeyCalculus.full_of_cuts_forward
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8KeyCalculus.tail_frame_disjoint
