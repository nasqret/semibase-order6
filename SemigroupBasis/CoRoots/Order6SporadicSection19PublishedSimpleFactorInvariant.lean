import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedCoarsening
import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSingletonPerfection

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant

open MaximalFactors FactorCodec BlockAlignment MacroWitnesses SquarePermutation
open RootFamily TaggedLayout Coarsening SingletonPerfection

def MarkedRoots (classify : Nat → Bool) (roots : List (Word Nat)) : Prop :=
  ∀ root ∈ roots, Positive classify root

theorem marked_transport (classify : Nat → Bool) (first second : List (Word Nat))
    (marked : MarkedRoots classify first) (coverage : SameCoverage first second) :
    MarkedRoots classify second := by
  intro root member value inside
  obtain ⟨old, oldMember, present⟩ := (coverage value).mpr ⟨root, member, inside⟩
  exact marked old oldMember value present

/-- The existing merger supplies its actual union skeleton. Coarsening turns
that witness into the fixed global action invariant, without a supplied
post-merger compatibility assumption. -/
theorem merge_preserving (classify : Nat → Bool) (roots : List (Word Nat))
    (word left right : Word Nat) (rest : List (Word Nat))
    (family : Family roots word) (marked : MarkedRoots classify roots)
    (permutation : roots.Perm (left :: right :: rest))
    (related : GeneralizedRelated left right word) :
    ∃ normal : Word Nat, Derives basis word normal ∧
      Family (sortedRoot (left ++ right) :: rest) normal ∧
      SameCoverage roots (sortedRoot (left ++ right) :: rest) ∧
      (sortedRoot (left ++ right) :: rest).length + 1 = roots.length ∧
      SameWordEffect classify word normal := by
  have leftMember : left ∈ roots :=
    permutation.mem_iff.mpr (List.mem_cons.mpr (Or.inl rfl))
  have rightMember : right ∈ roots :=
    permutation.mem_iff.mpr
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  have contained : Coarser (unionTag (supportTag left) (supportTag right)) classify := by
    intro value positive
    cases flag : supportTag left value with
    | false =>
        have rightPositive : supportTag right value = true := by
          simpa only [unionTag, flag, Bool.false_or] using positive
        exact marked right rightMember value ((supportTag_true right value).mp rightPositive)
    | true =>
        exact marked left leftMember value ((supportTag_true left value).mp flag)
  obtain ⟨normal, derived, good, coverage, skeleton⟩ :=
    merge_heads left right word rest (family_perm roots _ word permutation family) related
  refine ⟨normal, derived, good, ?_, ?_,
    same_effect_of_skeleton _ classify contained skeleton⟩
  · intro value
    exact (coverage_perm roots _ permutation value).trans (coverage value)
  · have count := permutation.length_eq
    simp only [List.length_cons] at count ⊢
    omega

def StableNormalized (classify : Nat → Bool) (roots : List (Word Nat))
    (word : Word Nat) : Prop :=
  ∃ normal : Word Nat, ∃ finalRoots : List (Word Nat),
    Derives basis word normal ∧ Family finalRoots normal ∧ SameCoverage roots finalRoots ∧
    Terminal finalRoots normal ∧ SameWordEffect classify word normal

theorem normalize_of_size (classify : Nat → Bool) (size : Nat) :
    ∀ (roots : List (Word Nat)) (word : Word Nat), roots.length = size →
      Family roots word → MarkedRoots classify roots → StableNormalized classify roots word := by
  refine Nat.strongRecOn (motive := fun n =>
    ∀ (roots : List (Word Nat)) (word : Word Nat), roots.length = n →
      Family roots word → MarkedRoots classify roots → StableNormalized classify roots word) size ?_
  intro n ih roots word count family marked
  classical
  by_cases merge : Mergeable roots word
  · obtain ⟨left, right, rest, permutation, related⟩ := merge
    obtain ⟨firstWord, step, firstFamily, firstCoverage, decrease, firstSame⟩ :=
      merge_preserving classify roots word left right rest family marked permutation related
    let nextRoots := sortedRoot (left ++ right) :: rest
    have smaller : nextRoots.length < n := by
      change (sortedRoot (left ++ right) :: rest).length < n
      omega
    have nextMarked : MarkedRoots classify nextRoots :=
      marked_transport classify roots nextRoots marked firstCoverage
    obtain ⟨normal, finalRoots, later, finalFamily, finalCoverage, terminal, laterSame⟩ :=
      ih nextRoots.length smaller nextRoots firstWord rfl firstFamily nextMarked
    refine ⟨normal, finalRoots, step.trans later, finalFamily, ?_, terminal,
      word_trans firstSame laterSame⟩
    intro value
    exact (firstCoverage value).trans (finalCoverage value)
  · exact ⟨word, roots, Derives.refl _, family, (fun _ => Iff.rfl), merge, word_refl word⟩

theorem normalize_preserving (classify : Nat → Bool) (roots : List (Word Nat))
    (word : Word Nat) (family : Family roots word) (marked : MarkedRoots classify roots) :
    StableNormalized classify roots word :=
  normalize_of_size classify roots.length roots word rfl family marked

theorem adjoin_preserving (classify : Nat → Bool) (roots : List (Word Nat))
    (word : Word Nat) (x : Nat) (family : Family roots word)
    (repeated : 2 ≤ word.toList.count x) (disjoint : ∀ root ∈ roots, x ∉ root.toList)
    (marked : classify x = true) :
    ∃ normal : Word Nat, Derives basis word normal ∧
      Family (Word.singleton x :: roots) normal ∧
      (∀ value, value ≠ x → normal.toList.count value = word.toList.count value) ∧
      SameWordEffect classify word normal := by
  obtain ⟨normal, derived, perfect, skeleton, counts, earlier⟩ :=
    singleton_perfection x word repeated
  have contained : Coarser (supportTag (Word.singleton x)) classify := by
    intro value positive
    have equal : value = x :=
      List.mem_singleton.mp ((supportTag_true (Word.singleton x) value).mp positive)
    rw [equal]
    exact marked
  refine ⟨normal, derived, ?_, counts, same_effect_of_skeleton _ classify contained skeleton⟩
  constructor
  · apply List.pairwise_cons.mpr
    refine ⟨?_, family.1⟩
    intro root member value inside contrary
    have equal : value = x := List.mem_singleton.mp inside
    exact disjoint root member (equal ▸ contrary)
  · intro root member
    rcases List.mem_cons.mp member with equal | old
    · subst root
      exact ⟨singleton_shape x, perfect⟩
    · have original := family.2 root old
      exact ⟨original.1, earlier root (disjoint root old) original.2⟩

/-- Actual singleton seeding retains the fixed classifier action in addition
to the untouched-letter counts needed to seed the next actual letter. -/
theorem seed_list_preserving (classify : Nat → Bool) (letters : List Nat)
    (unique : letters.Nodup) (roots : List (Word Nat)) (word : Word Nat)
    (family : Family roots word) (repeated : ∀ value ∈ letters, 2 ≤ word.toList.count value)
    (disjoint : ∀ value ∈ letters, ∀ root ∈ roots, value ∉ root.toList)
    (marked : ∀ value ∈ letters, classify value = true) :
    ∃ normal : Word Nat, Derives basis word normal ∧
      Family (letters.reverse.map Word.singleton ++ roots) normal ∧
      (∀ value, value ∉ letters → normal.toList.count value = word.toList.count value) ∧
      SameWordEffect classify word normal := by
  induction letters generalizing roots word with
  | nil =>
      exact ⟨word, Derives.refl _, family, (fun _ _ => rfl), word_refl word⟩
  | cons first rest ih =>
      have distinct := List.nodup_cons.mp unique
      have firstMember : first ∈ first :: rest := List.mem_cons.mpr (Or.inl rfl)
      obtain ⟨seeded, step, seededFamily, firstCounts, firstSame⟩ :=
        adjoin_preserving classify roots word first family (repeated first firstMember)
          (disjoint first firstMember) (marked first firstMember)
      have restRepeated : ∀ value ∈ rest, 2 ≤ seeded.toList.count value := by
        intro value member
        have different : value ≠ first := by
          intro equal
          exact distinct.1 (equal ▸ member)
        rw [firstCounts value different]
        exact repeated value (List.mem_cons.mpr (Or.inr member))
      have restDisjoint : ∀ value ∈ rest, ∀ root ∈ Word.singleton first :: roots,
          value ∉ root.toList := by
        intro value member root rootMember
        rcases List.mem_cons.mp rootMember with equal | old
        · subst root
          intro inside
          have equal : value = first := List.mem_singleton.mp inside
          exact distinct.1 (equal ▸ member)
        · exact disjoint value (List.mem_cons.mpr (Or.inr member)) root old
      have restMarked : ∀ value ∈ rest, classify value = true := by
        intro value member
        exact marked value (List.mem_cons.mpr (Or.inr member))
      obtain ⟨normal, later, finalFamily, laterCounts, laterSame⟩ :=
        ih distinct.2 (Word.singleton first :: roots) seeded seededFamily restRepeated restDisjoint restMarked
      refine ⟨normal, step.trans later, ?_, ?_, word_trans firstSame laterSame⟩
      · simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.cons_append, List.nil_append] using finalFamily
      · intro value outside
        have outsideRest : value ∉ rest := by
          intro member
          exact outside (List.mem_cons.mpr (Or.inr member))
        have different : value ≠ first := by
          intro equal
          exact outside (List.mem_cons.mpr (Or.inl equal))
        exact (laterCounts value outsideRest).trans (firstCounts value different)

def repeatedTag (word : Word Nat) (value : Nat) : Bool :=
  decide (2 ≤ word.toList.count value)

theorem initial_family_preserving (word : Word Nat) :
    ∃ normal : Word Nat, ∃ roots : List (Word Nat),
      Derives basis word normal ∧ Family roots normal ∧
      (∀ value, Covered roots value ↔ 2 ≤ word.toList.count value) ∧
      SameWordEffect (repeatedTag word) word normal := by
  have emptyFamily : Family [] word := by
    constructor
    · exact List.Pairwise.nil
    · intro root member
      cases member
  have repeated : ∀ value ∈ initialLetters word, 2 ≤ word.toList.count value := by
    intro value member
    exact (initial_letters_spec word value).mp member
  have disjoint : ∀ value ∈ initialLetters word, ∀ root ∈ ([] : List (Word Nat)),
      value ∉ root.toList := by
    intro value member root impossible
    cases impossible
  have marked : ∀ value ∈ initialLetters word, repeatedTag word value = true := by
    intro value member
    exact decide_eq_true (repeated value member)
  obtain ⟨normal, derived, family, _, same⟩ :=
    seed_list_preserving (repeatedTag word) (initialLetters word) (distinct_nodup _)
      [] word emptyFamily repeated disjoint marked
  refine ⟨normal, (initialLetters word).reverse.map Word.singleton, derived, ?_, ?_, same⟩
  · simpa only [List.append_nil] using family
  · intro value
    exact (singleton_coverage (initialLetters word) value).trans (initial_letters_spec word value)

theorem arbitrary_word_preserving (word : Word Nat) :
    ∃ normal : Word Nat, ∃ roots : List (Word Nat),
      Derives basis word normal ∧ Family roots normal ∧
      (∀ value, Covered roots value ↔ 2 ≤ word.toList.count value) ∧
      Terminal roots normal ∧ SameWordEffect (repeatedTag word) word normal := by
  obtain ⟨seeded, initialRoots, first, initialFamily, initialCoverage, initialSame⟩ :=
    initial_family_preserving word
  have marked : MarkedRoots (repeatedTag word) initialRoots := by
    intro root member value inside
    exact decide_eq_true ((initialCoverage value).mp ⟨root, member, inside⟩)
  obtain ⟨normal, roots, later, family, coverage, terminal, laterSame⟩ :=
    normalize_preserving (repeatedTag word) initialRoots seeded initialFamily marked
  refine ⟨normal, roots, first.trans later, family, ?_, terminal,
    word_trans initialSame laterSame⟩
  intro value
  exact (coverage value).symm.trans (initialCoverage value)

theorem perfect_member_repeated (root word : Word Nat) (perfect : CanonicalPerfect root word)
    (value : Nat) (inside : value ∈ root.toList) : 2 ≤ word.toList.count value := by
  have positive : 1 ≤ root.toList.count value := by
    by_cases zero : root.toList.count value = 0
    · exact False.elim ((List.count_eq_zero.mp zero) inside)
    · omega
  obtain ⟨before, after, split⟩ := canonical_perfect_literal_factor root word perfect
  have counted : word.toList.count value =
      before.count value + (root.toList.count value + root.toList.count value + after.count value) := by
    rw [split]
    simp only [Word.toList_append, List.count_append]
  omega

theorem covered_repeated (roots : List (Word Nat)) (word : Word Nat)
    (family : Family roots word) (value : Nat) (covered : Covered roots value) :
    2 ≤ word.toList.count value := by
  obtain ⟨root, member, inside⟩ := covered
  exact perfect_member_repeated root word (family.2 root member).2 value inside

/-- The actual final nonsimple set, all initially simple/absent counts, and the
whole simple-factor skeleton now survive the entire normalization loop. -/
theorem normalize_arbitrary_word (word : Word Nat) :
    ∃ normal : Word Nat, ∃ roots : List (Word Nat),
      Derives basis word normal ∧ Family roots normal ∧ Terminal roots normal ∧
      (∀ value, Covered roots value ↔ 2 ≤ word.toList.count value) ∧
      (∀ value, Covered roots value ↔ 2 ≤ normal.toList.count value) ∧
      (∀ value, word.toList.count value < 2 → normal.toList.count value = word.toList.count value) ∧
      taggedSkeleton (repeatedTag word) word.toList =
        taggedSkeleton (repeatedTag normal) normal.toList := by
  obtain ⟨normal, roots, derived, family, coverage, terminal, same⟩ := arbitrary_word_preserving word
  have counts : ∀ value, word.toList.count value < 2 →
      normal.toList.count value = word.toList.count value := by
    intro value simple
    have negative : repeatedTag word value = false := by
      apply decide_eq_false
      omega
    exact (same_negative_count same value negative).symm
  have finalCoverage : ∀ value, Covered roots value ↔ 2 ≤ normal.toList.count value := by
    intro value
    constructor
    · exact covered_repeated roots normal family value
    · intro repeated
      apply (coverage value).mpr
      by_cases original : 2 ≤ word.toList.count value
      · exact original
      · have simple : word.toList.count value < 2 := by omega
        have equal := counts value simple
        omega
  have tags : repeatedTag word = repeatedTag normal := by
    funext value
    have equivalent : (2 ≤ word.toList.count value) ↔ (2 ≤ normal.toList.count value) :=
      (coverage value).symm.trans (finalCoverage value)
    change decide (2 ≤ word.toList.count value) = decide (2 ≤ normal.toList.count value)
    by_cases originalRepeated : 2 ≤ word.toList.count value
    · have finalRepeated := equivalent.mp originalRepeated
      rw [decide_eq_true originalRepeated, decide_eq_true finalRepeated]
    · have finalNotRepeated : ¬ 2 ≤ normal.toList.count value := by
        intro finalRepeated
        exact originalRepeated (equivalent.mpr finalRepeated)
      rw [decide_eq_false originalRepeated, decide_eq_false finalNotRepeated]
  refine ⟨normal, roots, derived, family, terminal, coverage, finalCoverage, counts, ?_⟩
  have skeleton := word_skeleton same
  rw [← tags]
  exact skeleton

def simpleFactors (word : Word Nat) : List (Word Nat) :=
  (taggedSkeleton (repeatedTag word) word.toList).filterMap id

theorem simple_factors_of_skeleton (word normal : Word Nat)
    (same : taggedSkeleton (repeatedTag word) word.toList =
      taggedSkeleton (repeatedTag normal) normal.toList) :
    simpleFactors word = simpleFactors normal := by
  unfold simpleFactors
  rw [same]

theorem normalize_simple_factors (word : Word Nat) :
    ∃ normal : Word Nat, ∃ roots : List (Word Nat),
      Derives basis word normal ∧ Family roots normal ∧ Terminal roots normal ∧
      (∀ value, Covered roots value ↔ 2 ≤ normal.toList.count value) ∧
      (∀ value, word.toList.count value = 1 ↔ normal.toList.count value = 1) ∧
      simpleFactors word = simpleFactors normal := by
  obtain ⟨normal, roots, derived, family, terminal, original, current, counts, skeleton⟩ :=
    normalize_arbitrary_word word
  refine ⟨normal, roots, derived, family, terminal, current, ?_,
    simple_factors_of_skeleton word normal skeleton⟩
  intro value
  constructor
  · intro simple
    have low : word.toList.count value < 2 := by omega
    exact (counts value low).trans simple
  · intro simple
    by_cases repeated : 2 ≤ word.toList.count value
    · have impossible := (current value).mp ((original value).mpr repeated)
      omega
    · have low : word.toList.count value < 2 := by omega
      exact (counts value low).symm.trans simple

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant.marked_transport
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant.merge_preserving
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant.normalize_of_size
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant.normalize_preserving
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant.adjoin_preserving
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant.seed_list_preserving
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant.initial_family_preserving
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant.arbitrary_word_preserving
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant.perfect_member_repeated
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant.covered_repeated
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant.normalize_arbitrary_word
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant.simple_factors_of_skeleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SimpleFactorInvariant.normalize_simple_factors
