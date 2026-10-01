import SemigroupBasis.CoRoots.Order6Astra.C8StarFrames
import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSemanticRootPartition

namespace SemigroupBasis.CoRoots.Order6Astra.C8StarKeyFacts

open Order6SporadicSection19.Published
open C8Star C8StarFrames C8TailCuts C8CutCalculus C8SemanticKey

theorem tailAt_coverage (letters : List Nat) (marker : Nat) (z : List Nat)
    (tail : TailAt letters marker z) : ∀ x ∈ z, x ∈ letters := by
  obtain ⟨p, s, split, tail⟩ := tail
  intro x hx
  rw [split]
  exact List.mem_append.mpr (Or.inl (tail_coverage p s z tail x hx))

theorem tail_self (p : List Nat) : Tail p [] p := by
  refine ⟨[], p, rfl, same_refl p, ?_⟩
  intro x _ impossible
  cases impossible

theorem terminal_simple (star : Star) (branch : Word Nat) (member : branch ∈ star.branches)
    (p : List Nat) (t : Nat) (literal : branch.toList = p ++ [t]) (fresh : t ∉ p) :
    star.word.toList.count t = 1 := by
  have present : t ∈ branch.toList := by
    rw [literal]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  rw [branch_count star branch member t present, literal]
  simp [List.count_eq_zero.mpr fresh]

theorem terminal_tail_iff (star : Star) (branch : Word Nat) (member : branch ∈ star.branches)
    (p : List Nat) (t : Nat) (literal : branch.toList = p ++ [t]) (fresh : t ∉ p) (z : List Nat) :
    TailAt star.word.toList t z ↔ Tail p [] z := by
  have present : t ∈ branch.toList := by rw [literal]; exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have simple : branch.toList.count t = 1 := by rw [literal]; simp [List.count_eq_zero.mpr fresh]
  rw [branch_tail star branch member t present simple z]
  exact tailAt_at_split branch.toList t p [] z literal simple

theorem prefix_before_last (p q s : List Nat) (last marker : Nat)
    (equal : p ++ [last] = q ++ marker :: s) : ∀ x ∈ q, x ∈ p := by
  rcases compare_cuts p [last] q (marker :: s) equal with
    ⟨middle, first, second⟩ | ⟨middle, first, _⟩
  · have lengths := congrArg List.length second
    simp only [List.length_append, List.length_cons, List.length_nil] at lengths
    have empty : middle = [] := by
      cases middle with
      | nil => rfl
      | cons x xs => simp only [List.length_cons] at lengths; omega
    rw [empty, List.append_nil] at first
    intro x hx
    simpa only [first] using hx
  · intro x hx
    rw [first]
    exact List.mem_append.mpr (Or.inl hx)

theorem terminal_tail_absent (p : List Nat) (t marker : Nat) (z : List Nat)
    (fresh : t ∉ p) (tail : TailAt (p ++ [t]) marker z) : t ∉ z := by
  obtain ⟨q, s, split, tail⟩ := tail
  intro member
  exact fresh (prefix_before_last p q s t marker split t (tail_coverage q s z tail t member))

theorem shared_branch_eq (star : Star) (first second : Word Nat)
    (firstMember : first ∈ star.branches) (secondMember : second ∈ star.branches)
    (x : Nat) (inFirst : x ∈ first.toList) (inSecond : x ∈ second.toList) : first = second := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp firstMember
  have outside := pairwise_outside star.branches before after first star.pairwise split
  rw [split, List.mem_append, List.mem_cons] at secondMember
  rcases secondMember with earlier | equal | later
  · exact False.elim (outside second (List.mem_append.mpr (Or.inl earlier)) x inFirst inSecond)
  · exact equal.symm
  · exact False.elim (outside second (List.mem_append.mpr (Or.inr later)) x inFirst inSecond)

def Top (letters : List Nat) (t : Nat) : Prop :=
  letters.count t = 1 ∧ ∀ marker, letters.count marker = 1 →
    ∀ z, TailAt letters marker z → t ∉ z

theorem terminal_top (star : Star) (branch : Word Nat) (member : branch ∈ star.branches)
    (p : List Nat) (t : Nat) (literal : branch.toList = p ++ [t]) (fresh : t ∉ p) :
    Top star.word.toList t := by
  refine ⟨terminal_simple star branch member p t literal fresh, ?_⟩
  intro marker simple z tail contrary
  obtain ⟨other, otherMember, inside, otherSimple⟩ := simple_in_branch star marker simple
  have localTail := (branch_tail star other otherMember marker inside otherSimple z).mp tail
  have inOther := tailAt_coverage other.toList marker z localTail t contrary
  have inBranch : t ∈ branch.toList := by
    rw [literal]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have equal := shared_branch_eq star branch other member otherMember t inBranch inOther
  rw [← equal, literal] at localTail
  exact terminal_tail_absent p t marker z fresh localTail contrary

theorem top_iff_terminal (star : Star) (t : Nat) :
    Top star.word.toList t ↔ ∃ branch ∈ star.branches, ∃ p : List Nat,
      branch.toList = p ++ [t] ∧ t ∉ p := by
  constructor
  · intro top
    obtain ⟨branch, member, inside, _⟩ := simple_in_branch star t top.1
    obtain ⟨p, marker, literal, fresh⟩ := star.marked branch member
    have equal : t = marker := by
      apply Classical.byContradiction
      intro different
      have inPrefix : t ∈ p := by simpa only [literal, List.mem_append,
        List.mem_singleton, different, or_false] using inside
      have tail := (terminal_tail_iff star branch member p marker literal fresh p).mpr (tail_self p)
      exact top.2 marker (terminal_simple star branch member p marker literal fresh) p tail inPrefix
    exact ⟨branch, member, p, by simpa only [equal] using literal,
      by simpa only [equal] using fresh⟩
  · rintro ⟨branch, member, p, literal, fresh⟩
    exact terminal_top star branch member p t literal fresh

theorem key_top_forward {left right : List Nat} (key : Key left right) (t : Nat)
    (top : Top left t) : Top right t := by
  refine ⟨(key.simple t).mp top.1, ?_⟩
  intro marker simple z tail
  have sourceSimple := (key.simple marker).mpr simple
  exact top.2 marker sourceSimple z ((key.tails marker sourceSimple z).mpr tail)

def Core (letters : List Nat) (x : Nat) : Prop :=
  x ∈ letters ∧ letters.count x ≠ 1 ∧ ∀ marker, letters.count marker = 1 →
    ∀ z, TailAt letters marker z → x ∉ z

theorem root_iff_core (star : Star) (x : Nat) : x ∈ star.root.toList ↔ Core star.word.toList x := by
  constructor
  · intro inRoot
    refine ⟨(star.support x).mpr (Or.inl inRoot), ?_, ?_⟩
    · have repeated := root_repeated star x inRoot
      omega
    · intro marker simple z tail contrary
      obtain ⟨branch, member, inside, localSimple⟩ := simple_in_branch star marker simple
      have localTail := (branch_tail star branch member marker inside localSimple z).mp tail
      exact star.apart branch member x (tailAt_coverage _ marker z localTail x contrary) inRoot
  · rintro ⟨present, nonsimple, excluded⟩
    rcases (star.support x).mp present with root | ⟨branch, member, inside⟩
    · exact root
    · obtain ⟨p, t, literal, fresh⟩ := star.marked branch member
      rw [literal, List.mem_append, List.mem_singleton] at inside
      have simple := terminal_simple star branch member p t literal fresh
      rcases inside with inPrefix | equal
      · exact False.elim (excluded t simple p
          ((terminal_tail_iff star branch member p t literal fresh p).mpr (tail_self p)) inPrefix)
      · subst x
        exact False.elim (nonsimple simple)

theorem key_core_forward {left right : List Nat} (key : Key left right) (x : Nat)
    (core : Core left x) : Core right x := by
  refine ⟨(key.support x).mp core.1, fun h => core.2.1 ((key.simple x).mpr h), ?_⟩
  intro marker simple z tail
  have sourceSimple := (key.simple marker).mpr simple
  exact core.2.2 marker sourceSimple z ((key.tails marker sourceSimple z).mpr tail)

theorem matching_roots (left right : Star) (key : Key left.word.toList right.word.toList) :
    left.root = right.root := by
  apply SemanticRootPartition.root_shape_support_injective left.root right.root left.shape right.shape
  intro x
  constructor
  · intro inside
    exact (root_iff_core right x).mpr (key_core_forward key x ((root_iff_core left x).mp inside))
  · intro inside
    exact (root_iff_core left x).mpr (key_core_forward key.symm x ((root_iff_core right x).mp inside))

theorem matching_branch (left right : Star) (key : Key left.word.toList right.word.toList)
    (branch : Word Nat) (member : branch ∈ left.branches) (p : List Nat) (t : Nat)
    (literal : branch.toList = p ++ [t]) (fresh : t ∉ p) :
    ∃ other ∈ right.branches, ∃ q : List Nat,
      other.toList = q ++ [t] ∧ t ∉ q ∧ SameSupport p q ∧
        ∀ z, Tail p [] z ↔ Tail q [] z := by
  obtain ⟨other, otherMember, q, target, targetFresh⟩ := (top_iff_terminal right t).mp
    (key_top_forward key t (terminal_top left branch member p t literal fresh))
  have simple := terminal_simple left branch member p t literal fresh
  have tails : ∀ z, Tail p [] z ↔ Tail q [] z := by
    intro z
    exact (terminal_tail_iff left branch member p t literal fresh z).symm.trans
      ((key.tails t simple z).trans (terminal_tail_iff right other otherMember q t target targetFresh z))
  refine ⟨other, otherMember, q, target, targetFresh, ?_, tails⟩
  intro x
  exact ⟨tail_coverage q [] p ((tails p).mp (tail_self p)) x,
    tail_coverage p [] q ((tails q).mpr (tail_self q)) x⟩

end SemigroupBasis.CoRoots.Order6Astra.C8StarKeyFacts

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8StarKeyFacts.top_iff_terminal
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8StarKeyFacts.matching_roots
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8StarKeyFacts.matching_branch
