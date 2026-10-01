import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedPositiveRefinement

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily

open FactorBoundaries BlockAlignment MacroWitnesses FactorCodec SquarePermutation
open PositiveRefinement

def Apart (left right : Word Nat) : Prop :=
  ∀ value ∈ left.toList, value ∉ right.toList

def RootShape (root : Word Nat) : Prop :=
  root.toList.Nodup ∧ root.toList.Pairwise (· ≤ ·)

/-- A genuine current family: actual ordered distinct-letter roots, mutually
disjoint supports, and actual nonvacuous maximal-square perfection. -/
def Family (roots : List (Word Nat)) (word : Word Nat) : Prop :=
  roots.Pairwise Apart ∧ ∀ root ∈ roots, RootShape root ∧ CanonicalPerfect root word

def Covered (roots : List (Word Nat)) (value : Nat) : Prop :=
  ∃ root ∈ roots, value ∈ root.toList

def SameCoverage (first second : List (Word Nat)) : Prop :=
  ∀ value, Covered first value ↔ Covered second value

def Mergeable (roots : List (Word Nat)) (word : Word Nat) : Prop :=
  ∃ left right : Word Nat, ∃ rest : List (Word Nat),
    roots.Perm (left :: right :: rest) ∧ GeneralizedRelated left right word

def Terminal (roots : List (Word Nat)) (word : Word Nat) : Prop :=
  ¬ Mergeable roots word

theorem apart_symm (left right : Word Nat) (apart : Apart left right) : Apart right left := by
  intro value inRight inLeft
  exact apart value inLeft inRight

theorem apart_ne (left right : Word Nat) (apart : Apart left right) : left ≠ right := by
  intro equal
  subst right
  exact apart left.head (word_head_member left) (word_head_member left)

theorem family_perm (roots other : List (Word Nat)) (word : Word Nat)
    (permutation : roots.Perm other) (family : Family roots word) : Family other word := by
  refine ⟨permutation.pairwise family.1 ?_, ?_⟩
  · intro left right apart
    exact apart_symm left right apart
  · intro root member
    exact family.2 root (permutation.mem_iff.mpr member)

theorem coverage_perm (roots other : List (Word Nat)) (permutation : roots.Perm other) :
    SameCoverage roots other := by
  intro value
  constructor
  · rintro ⟨root, member, present⟩
    exact ⟨root, permutation.mem_iff.mp member, present⟩
  · rintro ⟨root, member, present⟩
    exact ⟨root, permutation.mem_iff.mpr member, present⟩

theorem covered_cons (root : Word Nat) (rest : List (Word Nat)) (value : Nat) :
    Covered (root :: rest) value ↔ value ∈ root.toList ∨ Covered rest value := by
  constructor
  · rintro ⟨piece, member, present⟩
    rcases List.mem_cons.mp member with equal | later
    · subst piece
      exact Or.inl present
    · exact Or.inr ⟨piece, later, present⟩
  · rintro (present | later)
    · exact ⟨root, List.mem_cons.mpr (Or.inl rfl), present⟩
    · obtain ⟨piece, member, present⟩ := later
      exact ⟨piece, List.mem_cons.mpr (Or.inr member), present⟩

theorem union_members (left right : Word Nat) (value : Nat) :
    value ∈ (sortedRoot (left ++ right)).toList ↔
      value ∈ left.toList ∨ value ∈ right.toList := by
  have same := (sortedRoot_perm (left ++ right)).symm.mem_iff (a := value)
  simpa only [Word.toList_append, List.mem_append] using same

theorem coverage_merge (left right : Word Nat) (rest : List (Word Nat)) :
    SameCoverage (left :: right :: rest) (sortedRoot (left ++ right) :: rest) := by
  intro value
  rw [covered_cons, covered_cons, covered_cons, union_members]
  exact or_assoc.symm

/-- One actual merge. Every untouched root's perfection is obtained from the
proved earlier-root preservation theorem, not supplied as a postcondition. -/
theorem merge_heads (left right word : Word Nat) (rest : List (Word Nat))
    (family : Family (left :: right :: rest) word)
    (related : GeneralizedRelated left right word) :
    ∃ normal : Word Nat, Derives basis word normal ∧
      Family (sortedRoot (left ++ right) :: rest) normal ∧
      SameCoverage (left :: right :: rest) (sortedRoot (left ++ right) :: rest) ∧
      taggedSkeleton (unionTag (supportTag left) (supportTag right)) word.toList =
        taggedSkeleton (unionTag (supportTag left) (supportTag right)) normal.toList := by
  have first := List.pairwise_cons.mp family.1
  have second := List.pairwise_cons.mp first.2
  have apart : Apart left right := first.1 right (List.mem_cons.mpr (Or.inl rfl))
  have leftData := family.2 left (List.mem_cons.mpr (Or.inl rfl))
  have rightData := family.2 right (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  have mergedShape := sorted_union_perfect left right leftData.1.1 rightData.1.1
    (fun a inLeft b inRight equal => apart a inLeft (equal.symm ▸ inRight))
  obtain ⟨normal, derived, mergedPerfect, skeleton, earlier⟩ :=
    generalized_fusion_preserves_earlier left right word apart leftData.2 rightData.2 related
  have newFamily : Family (sortedRoot (left ++ right) :: rest) normal := by
    constructor
    · apply List.pairwise_cons.mpr
      refine ⟨?_, second.2⟩
      intro other member value present contrary
      rcases (union_members left right value).mp present with inLeft | inRight
      · exact first.1 other (List.mem_cons.mpr (Or.inr member)) value inLeft contrary
      · exact second.1 other member value inRight contrary
    · intro root member
      rcases List.mem_cons.mp member with equal | later
      · subst root
        exact ⟨⟨mergedShape.1, mergedShape.2.1⟩, mergedPerfect⟩
      · have original := family.2 root
          (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr later))))
        have disjointLeft : Apart root left :=
          apart_symm left root (first.1 root (List.mem_cons.mpr (Or.inr later)))
        have disjointRight : Apart root right := apart_symm right root (second.1 root later)
        exact ⟨original.1, earlier root disjointLeft disjointRight original.2⟩
  exact ⟨normal, derived, newFamily, coverage_merge left right rest, skeleton⟩

theorem merge_selected (roots : List (Word Nat)) (word left right : Word Nat)
    (rest : List (Word Nat)) (family : Family roots word)
    (permutation : roots.Perm (left :: right :: rest))
    (related : GeneralizedRelated left right word) :
    ∃ normal : Word Nat, Derives basis word normal ∧
      Family (sortedRoot (left ++ right) :: rest) normal ∧
      SameCoverage roots (sortedRoot (left ++ right) :: rest) ∧
      (sortedRoot (left ++ right) :: rest).length + 1 = roots.length := by
  obtain ⟨normal, derived, good, coverage, _⟩ :=
    merge_heads left right word rest (family_perm roots _ word permutation family) related
  refine ⟨normal, derived, good, ?_, ?_⟩
  · intro value
    exact (coverage_perm roots _ permutation value).trans (coverage value)
  · have count := permutation.length_eq
    simp only [List.length_cons] at count ⊢
    omega

theorem select_member_pair (roots : List (Word Nat)) (left right : Word Nat)
    (leftMember : left ∈ roots) (rightMember : right ∈ roots) (different : left ≠ right) :
    ∃ rest : List (Word Nat), roots.Perm (left :: right :: rest) := by
  classical
  have afterLeft : right ∈ roots.erase left :=
    (List.mem_erase_of_ne (Ne.symm different)).mpr rightMember
  exact ⟨(roots.erase left).erase right,
    (List.perm_cons_erase leftMember).trans
      (List.Perm.cons left (List.perm_cons_erase afterLeft))⟩

theorem terminal_members (roots : List (Word Nat)) (word : Word Nat)
    (terminal : Terminal roots word) (left right : Word Nat)
    (leftMember : left ∈ roots) (rightMember : right ∈ roots) (different : left ≠ right) :
    ¬ GeneralizedRelated left right word := by
  intro related
  obtain ⟨rest, permutation⟩ := select_member_pair roots left right leftMember rightMember different
  exact terminal ⟨left, right, rest, permutation, related⟩

/-- No initial root-family construction or uniqueness is concealed here.
The output is a derived actual word and a terminal actual current family. -/
def Normalized (roots : List (Word Nat)) (word : Word Nat) : Prop :=
  ∃ normal : Word Nat, ∃ finalRoots : List (Word Nat),
    Derives basis word normal ∧ Family finalRoots normal ∧ SameCoverage roots finalRoots ∧
    finalRoots.length ≤ roots.length ∧ (finalRoots = [] ↔ roots = []) ∧ Terminal finalRoots normal

theorem normalize_of_size (size : Nat) :
    ∀ (roots : List (Word Nat)) (word : Word Nat), roots.length = size →
      Family roots word → Normalized roots word := by
  refine Nat.strongRecOn (motive := fun n =>
    ∀ (roots : List (Word Nat)) (word : Word Nat), roots.length = n →
      Family roots word → Normalized roots word) size ?_
  intro n ih roots word count family
  classical
  by_cases merge : Mergeable roots word
  · obtain ⟨left, right, rest, permutation, related⟩ := merge
    obtain ⟨firstWord, step, firstFamily, firstCoverage, decrease⟩ :=
      merge_selected roots word left right rest family permutation related
    let nextRoots := sortedRoot (left ++ right) :: rest
    have smaller : nextRoots.length < n := by
      change (sortedRoot (left ++ right) :: rest).length < n
      omega
    obtain ⟨normal, finalRoots, later, finalFamily, finalCoverage, finalCount, empty, terminal⟩ :=
      ih nextRoots.length smaller nextRoots firstWord rfl firstFamily
    refine ⟨normal, finalRoots, step.trans later, finalFamily, ?_, ?_, ?_, terminal⟩
    · intro value
      exact (firstCoverage value).trans (finalCoverage value)
    · change finalRoots.length ≤ nextRoots.length at finalCount
      have strict : nextRoots.length < roots.length := by omega
      omega
    · constructor
      · intro finalEmpty
        have impossible : nextRoots = [] := empty.mp finalEmpty
        change (sortedRoot (left ++ right) :: rest) = [] at impossible
        cases impossible
      · intro originalEmpty
        have zero : roots.length = 0 := by rw [originalEmpty]; rfl
        have positive : 0 < nextRoots.length := by
          change 0 < (sortedRoot (left ++ right) :: rest).length
          simp only [List.length_cons]
          omega
        omega
  · exact ⟨word, roots, Derives.refl _, family, (fun _ => Iff.rfl),
      Nat.le_refl _, Iff.rfl, merge⟩

/-- Any finite actual family reaches a family with no related distinct roots.
Each merge lowers the number of roots, and the existing algebra supplies the
new word and all remaining perfect-root witnesses at each induction step. -/
theorem normalize (roots : List (Word Nat)) (word : Word Nat) (family : Family roots word) :
    Normalized roots word := normalize_of_size roots.length roots word rfl family

theorem normalize_unrelated (roots : List (Word Nat)) (word : Word Nat)
    (family : Family roots word) :
    ∃ normal : Word Nat, ∃ finalRoots : List (Word Nat),
      Derives basis word normal ∧ Family finalRoots normal ∧ SameCoverage roots finalRoots ∧
      finalRoots.length ≤ roots.length ∧ (finalRoots = [] ↔ roots = []) ∧
      ∀ left ∈ finalRoots, ∀ right ∈ finalRoots, left ≠ right →
        ¬ GeneralizedRelated left right normal := by
  obtain ⟨normal, finalRoots, derived, good, coverage, count, empty, terminal⟩ :=
    normalize roots word family
  refine ⟨normal, finalRoots, derived, good, coverage, count, empty, ?_⟩
  intro left leftMember right rightMember different
  exact terminal_members finalRoots normal terminal left right leftMember rightMember different

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.apart_symm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.apart_ne
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.family_perm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.coverage_perm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.covered_cons
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.union_members
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.coverage_merge
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.merge_heads
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.merge_selected
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.select_member_pair
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.terminal_members
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.normalize_of_size
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.normalize
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFamily.normalize_unrelated
