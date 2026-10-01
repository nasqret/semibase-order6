import SemigroupBasis.CoRoots.Order6Astra.C8IslandKey

namespace SemigroupBasis.CoRoots.Order6Astra.C8SplitKeys

open C8TailCuts C8SemanticKey C8CutCalculus C8KeyCalculus C8IslandKey

theorem remaining_support (a b c d : List Nat) (first : SameSupport a c)
    (whole : SameSupport (a ++ b) (c ++ d)) (apart : Disjoint a b) (apart' : Disjoint c d) :
    SameSupport b d := by
  intro x
  constructor
  · intro hx
    have present := (whole x).mp (List.mem_append.mpr (Or.inr hx))
    rcases List.mem_append.mp present with inC | inD
    · exact False.elim (apart x ((first x).mpr inC) hx)
    · exact inD
  · intro hx
    have present := (whole x).mpr (List.mem_append.mpr (Or.inr hx))
    rcases List.mem_append.mp present with inA | inB
    · exact False.elim (apart' x ((first x).mp inA) hx)
    · exact inB

theorem tails_of_cuts_forward (u v : List Nat) (same : SameSupport u v)
    (cuts : ∀ z, Cut u z → Cut v z) (z : List Nat) (tail : Tail u [] z) : Tail v [] z := by
  obtain ⟨a, b, literal, support, apart⟩ := tail
  have apartAB : Disjoint a b := disjoint_symm (by simpa only [List.append_nil] using apart)
  obtain ⟨c, d, target, cSupport, targetApart⟩ := cuts a ⟨a, b, literal, same_refl a, apartAB⟩
  have whole : SameSupport (a ++ b) (c ++ d) := by simpa only [literal, target] using same
  have rest := remaining_support a b c d (same_symm cSupport) whole apartAB targetApart
  refine ⟨c, d, target, ?_, ?_⟩
  · intro x
    exact (rest x).symm.trans (support x)
  · simpa only [List.append_nil] using disjoint_symm targetApart

theorem cut_left_forward (left right z : List Nat) (apart : Disjoint left right)
    (covered : ∀ x ∈ z, x ∈ left) (cut : Cut (left ++ right) z) : Cut left z := by
  obtain ⟨a, b, literal, same, disjoint⟩ := cut
  rcases compare_cuts left right a b literal with ⟨middle, first, second⟩ | ⟨middle, first, second⟩
  · have empty : middle = [] := by
      cases middle with
      | nil => rfl
      | cons x xs =>
        have inA : x ∈ a := by rw [first]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
        have inRight : x ∈ right := by rw [second]; exact List.mem_append.mpr (Or.inl List.mem_cons_self)
        exact False.elim (apart x (covered x ((same x).mp inA)) inRight)
    have equal : a = left := by simpa only [empty, List.append_nil] using first
    refine ⟨left, [], (List.append_nil _).symm, ?_, ?_⟩
    · simpa only [equal] using same
    · intro x _ impossible
      cases impossible
  · refine ⟨a, middle, first, same, ?_⟩
    intro x hx contrary
    apply disjoint x hx
    rw [second]
    exact List.mem_append.mpr (Or.inl contrary)

theorem cut_left_backward (left right z : List Nat) (apart : Disjoint left right)
    (cut : Cut left z) : Cut (left ++ right) z := by
  obtain ⟨a, b, literal, same, disjoint⟩ := cut
  refine ⟨a, b ++ right, by rw [literal, List.append_assoc], same, ?_⟩
  intro x hx contrary
  rcases List.mem_append.mp contrary with inB | inRight
  · exact disjoint x hx inB
  · apply apart x
    · rw [literal]
      exact List.mem_append.mpr (Or.inl hx)
    · exact inRight

theorem left_cuts_forward (a b c d : List Nat) (key : Key (a ++ b) (c ++ d))
    (apart : Disjoint a b) (apart' : Disjoint c d) (same : SameSupport a c)
    (z : List Nat) (cut : Cut a z) : Cut c z := by
  have covered : ∀ x ∈ z, x ∈ c := by
    obtain ⟨p, s, literal, support, _⟩ := cut
    intro x hx
    apply (same x).mp
    rw [literal]
    exact List.mem_append.mpr (Or.inl ((support x).mpr hx))
  exact cut_left_forward c d z apart' covered
    ((key.cuts z).mp (cut_left_backward a b z apart cut))

theorem right_tails_forward (a b c d : List Nat) (key : Key (a ++ b) (c ++ d))
    (apart : Disjoint a b) (apart' : Disjoint c d) (same : SameSupport b d)
    (z : List Nat) (tail : Tail b [] z) : Tail d [] z := by
  have covered := tail_coverage b [] z tail
  have firstOutside : Disjoint z (a ++ []) := by
    intro x hx contrary
    exact apart x (by simpa only [List.append_nil] using contrary) (covered x hx)
  have secondOutside : Disjoint z (c ++ []) := by
    intro x hx contrary
    exact apart' x (by simpa only [List.append_nil] using contrary) ((same x).mp (covered x hx))
  have wholeTail : Tail (a ++ b) [] z := (tail_frame_disjoint a [] b [] z firstOutside).mpr tail
  have targetTail := tails_of_cuts_forward (a ++ b) (c ++ d) key.support
    (fun z => (key.cuts z).mp) z wholeTail
  exact (tail_frame_disjoint c [] d [] z secondOutside).mp targetTail

/-- A support-disjoint factor cut transfers the full key to both factors.
The two factor keys, including their local full flags, are actual conclusions. -/
theorem split_keys (a b c d : List Nat) (key : Key (a ++ b) (c ++ d))
    (apart : Disjoint a b) (apart' : Disjoint c d) (same : SameSupport a c) :
    Key a c ∧ Key b d := by
  have rest := remaining_support a b c d same key.support apart apart'
  have leftCuts : ∀ z, Cut a z ↔ Cut c z := fun z =>
    ⟨left_cuts_forward a b c d key apart apart' same z,
      left_cuts_forward c d a b key.symm apart' apart (same_symm same) z⟩
  have rightTails : ∀ z, Tail b [] z ↔ Tail d [] z := fun z =>
    ⟨right_tails_forward a b c d key apart apart' rest z,
      right_tails_forward c d a b key.symm apart' apart (same_symm rest) z⟩
  let leftIsland : Island (a ++ b) a := ⟨[], b, rfl, apart⟩
  let targetLeft : Island (c ++ d) c := ⟨[], d, rfl, apart'⟩
  let rightIsland : Island (a ++ b) b := ⟨a, [], (List.append_nil _).symm,
    by simpa only [List.append_nil] using disjoint_symm apart⟩
  let targetRight : Island (c ++ d) d := ⟨c, [], (List.append_nil _).symm,
    by simpa only [List.append_nil] using disjoint_symm apart'⟩
  exact ⟨key_islands key leftIsland targetLeft same leftCuts,
    key_islands key rightIsland targetRight rest (cuts_of_tails b d rest rightTails)⟩

end SemigroupBasis.CoRoots.Order6Astra.C8SplitKeys

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8SplitKeys.tails_of_cuts_forward
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8SplitKeys.split_keys
