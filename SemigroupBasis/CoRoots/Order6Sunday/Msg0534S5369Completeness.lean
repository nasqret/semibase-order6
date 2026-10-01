import SemigroupBasis.CoRoots.Order6Sunday.Msg0534S5369Derivations
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0534S5369Completeness

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107 (ListDerives)
open Msg0524S5369Evaluator Msg0524S5369Observations Msg0524S5369SemanticKey
open Msg0534S5369Derivations

macro "count_perm" : tactic => `(tactic|
  (apply List.perm_iff_count.mpr
   intro t
   simp only [List.count_cons, List.count_nil] <;> omega))

theorem rebalance (h x y : Nat) : LD [h,x,y,y] [h,x,x,y] := by
  have first : LD [h,x,y,y] [h,y,y,x] := tailPermutation (by count_perm) h
  have middle : LD [h,h,y,x] [h,h,x,y] := tailPermutation (by count_perm) h
  exact first.trans ((doubleShift h y x).symm.trans (middle.trans (doubleShift h x y)))

theorem support_two (h x a b c : Nat) (different : x ≠ h)
    (support : ∀ t, t ∈ [h,a,b,c] ↔ t=h ∨ t=x) :
    LD [h,a,b,c] [h,x,x,x] := by
  have ha := (support a).mp (by simp)
  have hb := (support b).mp (by simp)
  have hc := (support c).mp (by simp)
  have present := (support x).mpr (Or.inr rfl)
  clear support
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  all_goals subst a
  all_goals subst b
  all_goals subst c
  all_goals simp_all
  all_goals first
    | (apply tailPermutation; count_perm)
    | (refine ListDerives.trans (middle := [h,h,h,x]) ?_ (tripleToSingle h x)
       apply tailPermutation
       count_perm)
    | (refine ListDerives.trans (middle := [h,h,x,x]) ?_
         ((tripleToDouble h x).symm.trans (tripleToSingle h x))
       apply tailPermutation
       count_perm)

theorem support_three (h x y a b c : Nat) (xh : x ≠ h) (yh : y ≠ h) (xy : x ≠ y)
    (support : ∀ t, t ∈ [h,a,b,c] ↔ t=h ∨ t=x ∨ t=y) :
    LD [h,a,b,c] [h,x,x,y] := by
  have ha := (support a).mp (by simp)
  have hb := (support b).mp (by simp)
  have hc := (support c).mp (by simp)
  have px := (support x).mpr (by simp)
  have py := (support y).mpr (by simp)
  clear support
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    rcases hc with hc | hc | hc
  all_goals subst a
  all_goals subst b
  all_goals subst c
  all_goals simp_all
  all_goals first
    | (apply tailPermutation; count_perm)
    | (refine ListDerives.trans (middle := [h,h,x,y]) ?_ (doubleShift h x y)
       apply tailPermutation
       count_perm)
    | (refine ListDerives.trans (middle := [h,x,y,y]) ?_ (rebalance h x y)
       apply tailPermutation
       count_perm)

theorem four_distinct (h x y z a b c : Nat)
    (xh : x ≠ h) (yh : y ≠ h) (zh : z ≠ h)
    (xy : x ≠ y) (xz : x ≠ z) (yz : y ≠ z)
    (support : ∀ t, t ∈ [h,x,y,z] ↔ t ∈ [h,a,b,c]) :
    LD [h,x,y,z] [h,a,b,c] := by
  have ha : a=h ∨ a=x ∨ a=y ∨ a=z := by simpa using (support a).mpr (by simp)
  have hb : b=h ∨ b=x ∨ b=y ∨ b=z := by simpa using (support b).mpr (by simp)
  have hc : c=h ∨ c=x ∨ c=y ∨ c=z := by simpa using (support c).mpr (by simp)
  have px := (support x).mp (by simp)
  have py := (support y).mp (by simp)
  have pz := (support z).mp (by simp)
  clear support
  rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;>
    rcases hc with hc | hc | hc | hc
  all_goals subst a
  all_goals subst b
  all_goals subst c
  all_goals simp_all
  all_goals exact tailPermutation (by count_perm) h

theorem four_via_two {h a b c d e f : Nat} (x : Nat) (xh : x ≠ h)
    (shape : ∀ t, t ∈ [h,a,b,c] ↔ t=h ∨ t=x)
    (support : ∀ t, t ∈ [h,a,b,c] ↔ t ∈ [h,d,e,f]) :
    LD [h,a,b,c] [h,d,e,f] :=
  (support_two h x a b c xh shape).trans
    (support_two h x d e f xh (fun t => (support t).symm.trans (shape t))).symm

theorem four_via_three {h a b c d e f : Nat} (x y : Nat)
    (xh : x ≠ h) (yh : y ≠ h) (xy : x ≠ y)
    (shape : ∀ t, t ∈ [h,a,b,c] ↔ t=h ∨ t=x ∨ t=y)
    (support : ∀ t, t ∈ [h,a,b,c] ↔ t ∈ [h,d,e,f]) :
    LD [h,a,b,c] [h,d,e,f] :=
  (support_three h x y a b c xh yh xy shape).trans
    (support_three h x y d e f xh yh xy (fun t => (support t).symm.trans (shape t))).symm

theorem four_of_support (h x y z a b c : Nat)
    (support : ∀ t, t ∈ [h,x,y,z] ↔ t ∈ [h,a,b,c]) :
    LD [h,x,y,z] [h,a,b,c] := by
  by_cases xh : x=h
  · subst x
    by_cases yh : y=h
    · subst y
      by_cases zh : z=h
      · subst z
        have ha : a=h := by simpa using (support a).mpr (by simp)
        have hb : b=h := by simpa using (support b).mpr (by simp)
        have hc : c=h := by simpa using (support c).mpr (by simp)
        subst a; subst b; subst c
        exact ListDerives.refl _
      · exact four_via_two z zh (by intro t; simp [or_comm,or_left_comm,or_assoc]) support
    · by_cases zh : z=h
      · subst z
        exact four_via_two y yh (by intro t; simp [or_comm,or_left_comm,or_assoc]) support
      · by_cases yz : y=z
        · subst z
          exact four_via_two y yh (by intro t; simp [or_comm,or_left_comm,or_assoc]) support
        · exact four_via_three y z yh zh yz (by intro t; simp [or_comm,or_left_comm,or_assoc]) support
  · by_cases yh : y=h
    · subst y
      by_cases zh : z=h
      · subst z
        exact four_via_two x xh (by intro t; simp [or_comm,or_left_comm,or_assoc]) support
      · by_cases xz : x=z
        · subst z
          exact four_via_two x xh (by intro t; simp [or_comm,or_left_comm,or_assoc]) support
        · exact four_via_three x z xh zh xz (by intro t; simp [or_comm,or_left_comm,or_assoc]) support
    · by_cases zh : z=h
      · subst z
        by_cases xy : x=y
        · subst y
          exact four_via_two x xh (by intro t; simp [or_comm,or_left_comm,or_assoc]) support
        · exact four_via_three x y xh yh xy (by intro t; simp [or_comm,or_left_comm,or_assoc]) support
      · by_cases xy : x=y
        · subst y
          by_cases xz : x=z
          · subst z
            exact four_via_two x xh (by intro t; simp [or_comm,or_left_comm,or_assoc]) support
          · exact four_via_three x z xh zh xz (by intro t; simp [or_comm,or_left_comm,or_assoc]) support
        · by_cases xz : x=z
          · subst z
            exact four_via_three x y xh yh xy (by intro t; simp [or_comm,or_left_comm,or_assoc]) support
          · by_cases yz : y=z
            · subst z
              exact four_via_three x y xh yh xy (by intro t; simp [or_comm,or_left_comm,or_assoc]) support
            · exact four_distinct h x y z a b c xh yh zh xy xz yz support

theorem three_of_counts (h x y a b : Nat)
    (counts : ∀ t, min ([h,x,y].count t) 2 = min ([h,a,b].count t) 2) :
    LD [h,x,y] [h,a,b] := by
  have support := support_of_counts [h,x,y] [h,a,b] 2 (by decide) counts
  have ha : a=h ∨ a=x ∨ a=y := by simpa using (support a).mpr (by simp)
  have hb : b=h ∨ b=x ∨ b=y := by simpa using (support b).mpr (by simp)
  have ch := counts h
  have cx := counts x
  have cy := counts y
  clear counts support
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
  all_goals subst a
  all_goals subst b
  all_goals by_cases xh : x=h
  all_goals by_cases yh : y=h
  all_goals by_cases xy : x=y
  all_goals try have hx : h ≠ x := fun e => xh e.symm
  all_goals try have hy : h ≠ y := fun e => yh e.symm
  all_goals try have hyx : y ≠ x := fun e => xy e.symm
  all_goals simp_all only [List.count_cons, List.count_nil, beq_iff_eq,
    beq_self_eq_true, if_pos, if_neg, ite_true, ite_false]
  all_goals first | exact tailPermutation (by count_perm) h | omega

theorem small_of_counts (h : Nat) (left right : List Nat) (bound : Nat)
    (lb : left.length+1 ≤ bound) (rb : right.length+1 ≤ bound)
    (counts : ∀ t, min ((h::left).count t) bound = min ((h::right).count t) bound) :
    LD (h::left) (h::right) := by
  apply tailPermutation
  apply List.perm_iff_count.mpr
  intro t
  have lc : (h::left).count t ≤ left.length+1 := List.count_le_length
  have rc : (h::right).count t ≤ right.length+1 := List.count_le_length
  have equal := counts t
  have total : (h::left).count t = (h::right).count t := by omega
  simp only [List.count_cons] at total
  omega

private theorem shape_two (l : List Nat) (len : l.length=2) : ∃ a b, l=[a,b] := by
  cases l with
  | nil => simp at len
  | cons a l =>
    cases l with
    | nil => simp at len
    | cons b l =>
      cases l with
      | nil => exact ⟨a,b,rfl⟩
      | cons c rest => simp only [List.length_cons] at len; omega

private theorem shape_three (l : List Nat) (len : l.length=3) : ∃ a b c, l=[a,b,c] := by
  cases l with
  | nil => simp at len
  | cons a l =>
    obtain ⟨b,c,rfl⟩ := shape_two l (by simpa using len)
    exact ⟨a,b,c,rfl⟩

theorem key_derives (left right : Word Nat) (key : SameKey left right) :
    Derives basis left right := by
  rcases key with ⟨heads,lengths,counts⟩
  by_cases long : 5 ≤ left.toList.length
  · apply long_derives left right heads long
    unfold lengthCap at lengths
    omega
  · rcases left with ⟨h,l⟩
    rcases right with ⟨k,r⟩
    change h=k at heads
    subst k
    change min (l.length+1) 5 = min (r.length+1) 5 at lengths
    change ¬ 5 ≤ l.length+1 at long
    have lens : l.length=r.length := by omega
    have capped : ∀ t, min ((h::l).count t) (4-l.length) =
        min ((h::r).count t) (4-l.length) := by
      intro t
      have same := counts t
      simp only [lengthCap,Word.toList,List.length_cons] at same
      omega
    have lists : LD (h::l) (h::r) := by
      by_cases tiny : l.length ≤ 1
      · exact small_of_counts h l r (4-l.length) (by omega) (by omega) capped
      · by_cases two : l.length=2
        · obtain ⟨x,y,rfl⟩ := shape_two l two
          obtain ⟨a,b,rfl⟩ := shape_two r (by simpa using lens.symm)
          exact three_of_counts h x y a b (by simpa using capped)
        · have three : l.length=3 := by omega
          obtain ⟨x,y,z,rfl⟩ := shape_three l three
          obtain ⟨a,b,c,rfl⟩ := shape_three r (by simpa using lens.symm)
          apply four_of_support
          exact support_of_counts _ _ 1 (by decide) (by simpa using capped)
    exact _root_.SemigroupBasis.CoRoots.S5_107.ListDerives.toWord lists

theorem complete (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  key_derives identity.lhs identity.rhs (key_of_valid _ _ valid)

theorem representative_basis : BasisFor table.semigroup basis := ⟨models,complete⟩

theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6Sunday.Msg0534S5369Completeness
