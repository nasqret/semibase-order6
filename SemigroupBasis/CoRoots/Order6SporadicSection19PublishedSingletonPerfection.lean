import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedTaggedLayout

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection

open MaximalFactors FactorContexts FactorBoundaries OccurrenceWitnesses
  CrossFactor CrossSweep BinaryPowers MarkedZones SquareCoalescing
  MaximalSquareCover OrderedSquareForm BlockAlignment FactorCodec
  DecodedFusion UnionPerfection SkeletonTransport PositiveRefinement RootFamily
open TaggedLayout

/-- Two actual positions, not an assumed binary projection or an empty word. -/
theorem two_occurrences (x : Nat) (letters : List Nat) (repeated : 2 ≤ letters.count x) :
    ∃ before middle after : List Nat,
      letters = before ++ x :: (middle ++ x :: after) := by
  induction letters with
  | nil =>
      have impossible : 2 ≤ (0 : Nat) := repeated
      omega
  | cons first rest ih =>
      by_cases equal : first = x
      · subst first
        have present : x ∈ rest := by
          by_cases present : x ∈ rest
          · exact present
          · have zero : rest.count x = 0 := List.count_eq_zero.mpr present
            have count : (x :: rest).count x = 1 := by rw [List.count_cons_self, zero]
            have impossible : False := by omega
            exact impossible.elim
        obtain ⟨middle, after, split⟩ := split_letter x rest present
        exact ⟨[], middle, after, congrArg (List.cons x) split⟩
      · have repeatedRest : 2 ≤ rest.count x := by
          simpa only [List.count_cons_of_ne equal] using repeated
        obtain ⟨before, middle, after, split⟩ := ih repeatedRest
        exact ⟨first :: before, middle, after, congrArg (List.cons first) split⟩

theorem singleton_tag_true (x : Nat) : supportTag (Word.singleton x) x = true := by
  apply decide_eq_true
  exact List.mem_singleton.mpr rfl

theorem singleton_tag_false (x value : Nat) (different : value ≠ x) :
    supportTag (Word.singleton x) value = false := by
  apply decide_eq_false
  intro present
  exact different (List.mem_singleton.mp present)

/-- Both duplications use the existing other occurrence, including an empty gap. -/
theorem seed_derives (u : Word Nat) (middle : Option (Word Nat)) :
    Derives basis (gap u middle ++ u) (anchor u u middle) := by
  have step := duplicate_last u middle
  change Derives basis (gap u middle ++ u) (((gap u middle ++ u) ++ u) ++ u)
  exact step.trans (Derives.appendRight step u)

theorem seed_layout {classify : Nat → Bool} (u : Word Nat) (middle : Option (Word Nat))
    (marked : Positive classify u) :
    SameWordEffect classify (gap u middle ++ u) (anchor u u middle) := by
  have back : SameWordEffect classify u (u ++ (u ++ u)) :=
    positive_words marked (positive_append marked (positive_append marked marked))
  have step := word_append (word_refl (gap u middle)) back
  simpa only [anchor, Word.append_assoc] using step

def singletonNormal (x : Nat) (before middle after : List Nat) : Word Nat :=
  Context.frame (contextWord (encodeLeft x x before).1)
    (contextWord (encodeRight x x after).2)
    (chain (Word.singleton x ++ Word.singleton x)
      (keepNonempty (actualGaps x x before middle after)))

theorem fourth_to_square (u : Word Nat) : Derives basis (square u u) (u ++ u) := by
  simpa only [square, copies, Word.append_assoc] using copies_stabilize u 2

theorem singleton_normal_derives (x : Nat) (before middle after : List Nat) :
    Derives basis (coalescedSquareBlocks x x before middle after)
      (singletonNormal x before middle after) :=
  framed_chain_derives (fourth_to_square (Word.singleton x))
    (keepNonempty (actualGaps x x before middle after))
    (encodeLeft x x before).1 (encodeRight x x after).2

theorem singleton_normal_layout {classify : Nat → Bool} (x : Nat)
    (before middle after : List Nat) (marked : classify x = true) :
    SameWordEffect classify (coalescedSquareBlocks x x before middle after)
      (singletonNormal x before middle after) := by
  have atom : Positive classify (Word.singleton x) := positive_singleton x marked
  exact word_frame _ _ (chain_layout
    (positive_words (positive_square atom atom) (positive_append atom atom)) _)

theorem outside_singleton (x : Nat) (letters : List Nat) (clean : Outside x x letters) :
    TagClean (supportTag (Word.singleton x)) letters := by
  intro value member
  exact singleton_tag_false x value (clean value member).1

theorem singleton_normal_perfect (x : Nat) (before middle after : List Nat) :
    CanonicalPerfect (Word.singleton x) (singletonNormal x before middle after) := by
  have boundary := coalesced_boundaries x x before middle after
  have headClean := outside_singleton x (encodeLeft x x before).1 boundary.1
  have tailClean := outside_singleton x (encodeRight x x after).2 boundary.2.1
  have clean : ∀ piece ∈ gapWords (actualGaps x x before middle after),
      TagClean (supportTag (Word.singleton x)) piece.toList := by
    intro piece member
    exact outside_singleton x piece.toList
      (actual_gaps_outside x x before middle after piece.toList
        (gapWords_member (actualGaps x x before middle after) piece member))
  have perfect := canonical_framed_root (Word.singleton x)
    (encodeLeft x x before).1 (encodeRight x x after).2
    (gapWords (actualGaps x x before middle after)) headClean tailClean clean
  simpa only [gapWords_lists, singletonNormal] using perfect

/-- Actual repeated-letter perfectification with its full contextual action. -/
theorem normalize_singleton (x : Nat) (word : Word Nat) (repeated : 2 ≤ word.toList.count x) :
    ∃ normal : Word Nat, Derives basis word normal ∧
      CanonicalPerfect (Word.singleton x) normal ∧
      SameWordEffect (supportTag (Word.singleton x)) word normal := by
  obtain ⟨before, middle, after, split⟩ := two_occurrences x word.toList repeated
  have framed : word = Context.frame (contextWord before) (contextWord after)
      (gap (Word.singleton x) (contextWord middle) ++ Word.singleton x) := by
    apply Word.toList_injective
    rw [split, frame_of_lists_toList, Word.toList_append, gap_toList, contextLetters_contextWord]
    simp only [Word.toList_singleton, List.cons_append, List.nil_append, List.append_assoc]
  have toSeed : Derives basis word
      (Context.frame (contextWord before) (contextWord after)
        (anchor (Word.singleton x) (Word.singleton x) (contextWord middle))) := by
    rw [framed]
    exact Context.frame_derives (seed_derives (Word.singleton x) (contextWord middle))
      (contextWord before) (contextWord after)
  have seedSame : SameWordEffect (supportTag (Word.singleton x)) word
      (Context.frame (contextWord before) (contextWord after)
        (anchor (Word.singleton x) (Word.singleton x) (contextWord middle))) := by
    rw [framed]
    exact word_frame _ _ (seed_layout (Word.singleton x) (contextWord middle)
      (positive_singleton x (singleton_tag_true x)))
  refine ⟨singletonNormal x before middle after,
    (toSeed.trans (arbitrary_anchor_coalesced x x before middle after)).trans
      (singleton_normal_derives x before middle after),
    singleton_normal_perfect x before middle after, ?_⟩
  exact word_trans
    (word_trans seedSame (TaggedLayout.arbitrary_anchor_coalesced_layout x x before middle after
      (singleton_tag_true x) (singleton_tag_true x)))
    (singleton_normal_layout x before middle after (singleton_tag_true x))

/-- The full seed interface: literal complement, all other counts, and every
earlier disjoint perfect root are preserved; no postcondition is assumed. -/
theorem singleton_perfection (x : Nat) (word : Word Nat) (repeated : 2 ≤ word.toList.count x) :
    ∃ normal : Word Nat, Derives basis word normal ∧
      CanonicalPerfect (Word.singleton x) normal ∧
      taggedSkeleton (supportTag (Word.singleton x)) word.toList =
        taggedSkeleton (supportTag (Word.singleton x)) normal.toList ∧
      (∀ value, value ≠ x → normal.toList.count value = word.toList.count value) ∧
      (∀ root : Word Nat, x ∉ root.toList →
        CanonicalPerfect root word → CanonicalPerfect root normal) := by
  obtain ⟨normal, derived, perfect, same⟩ := normalize_singleton x word repeated
  have skeleton := word_skeleton same
  refine ⟨normal, derived, perfect, skeleton, ?_, ?_⟩
  · intro value different
    exact (same_negative_count same value (singleton_tag_false x value different)).symm
  · intro root excluded earlier
    apply canonical_perfect_transport root (supportTag (Word.singleton x)) word normal ?_ skeleton earlier
    intro value positive
    have member := (supportTag_true root value).mp positive
    have different : value ≠ x := by
      intro equal
      exact excluded (equal ▸ member)
    exact singleton_tag_false x value different

theorem singleton_shape (x : Nat) : RootShape (Word.singleton x) := by
  change ([x] : List Nat).Nodup ∧ ([x] : List Nat).Pairwise (· ≤ ·)
  constructor
  · apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_nil⟩
    intro present
    cases present
  · apply List.pairwise_cons.mpr
    refine ⟨?_, List.Pairwise.nil⟩
    intro value present
    cases present

theorem adjoin_singleton (roots : List (Word Nat)) (word : Word Nat) (x : Nat)
    (family : Family roots word) (repeated : 2 ≤ word.toList.count x)
    (disjoint : ∀ root ∈ roots, x ∉ root.toList) :
    ∃ normal : Word Nat, Derives basis word normal ∧
      Family (Word.singleton x :: roots) normal ∧
      (∀ value, value ≠ x → normal.toList.count value = word.toList.count value) := by
  obtain ⟨normal, derived, perfect, _, counts, earlier⟩ := singleton_perfection x word repeated
  refine ⟨normal, derived, ?_, counts⟩
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

/-- Induction on actual distinct repeated letters retains the existing family
and preserves every count outside the selected list. -/
theorem seed_list (letters : List Nat) (unique : letters.Nodup)
    (roots : List (Word Nat)) (word : Word Nat) (family : Family roots word)
    (repeated : ∀ value ∈ letters, 2 ≤ word.toList.count value)
    (disjoint : ∀ value ∈ letters, ∀ root ∈ roots, value ∉ root.toList) :
    ∃ normal : Word Nat, Derives basis word normal ∧
      Family (letters.reverse.map Word.singleton ++ roots) normal ∧
      (∀ value, value ∉ letters → normal.toList.count value = word.toList.count value) := by
  induction letters generalizing roots word with
  | nil =>
      exact ⟨word, Derives.refl _, family, fun _ _ => rfl⟩
  | cons first rest ih =>
      have distinct := List.nodup_cons.mp unique
      have firstMember : first ∈ first :: rest := List.mem_cons.mpr (Or.inl rfl)
      obtain ⟨seeded, step, seededFamily, firstCounts⟩ :=
        adjoin_singleton roots word first family (repeated first firstMember)
          (disjoint first firstMember)
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
      obtain ⟨normal, later, finalFamily, laterCounts⟩ :=
        ih distinct.2 (Word.singleton first :: roots) seeded seededFamily restRepeated restDisjoint
      refine ⟨normal, step.trans later, ?_, ?_⟩
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

/-- A small explicit support selector; its uniqueness does not depend on a
missing library theorem for the implementation of eraseDups. -/
def distinctLetters : List Nat → List Nat
  | [] => []
  | first :: rest =>
      if first ∈ distinctLetters rest then distinctLetters rest else first :: distinctLetters rest

theorem distinct_nodup (letters : List Nat) : (distinctLetters letters).Nodup := by
  induction letters with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
      by_cases present : first ∈ distinctLetters rest
      · rw [distinctLetters, if_pos present]
        exact ih
      · rw [distinctLetters, if_neg present]
        exact List.nodup_cons.mpr ⟨present, ih⟩

theorem mem_distinct (letters : List Nat) (value : Nat) :
    value ∈ distinctLetters letters ↔ value ∈ letters := by
  induction letters generalizing value with
  | nil => rfl
  | cons first rest ih =>
      by_cases present : first ∈ distinctLetters rest
      · rw [distinctLetters, if_pos present, ih value, List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (equal | member)
          · subst value
            exact (ih first).mp present
          · exact member
      · rw [distinctLetters, if_neg present]
        simp only [List.mem_cons, ih]

def initialLetters (word : Word Nat) : List Nat :=
  distinctLetters (word.toList.filter (fun value => decide (2 ≤ word.toList.count value)))

theorem initial_letters_spec (word : Word Nat) (value : Nat) :
    value ∈ initialLetters word ↔ 2 ≤ word.toList.count value := by
  rw [initialLetters, mem_distinct, List.mem_filter]
  constructor
  · intro member
    exact of_decide_eq_true member.2
  · intro repeated
    refine ⟨?_, decide_eq_true repeated⟩
    by_cases present : value ∈ word.toList
    · exact present
    · have zero : word.toList.count value = 0 := List.count_eq_zero.mpr present
      have impossible : False := by omega
      exact impossible.elim

theorem singleton_coverage (letters : List Nat) (value : Nat) :
    Covered (letters.reverse.map Word.singleton) value ↔ value ∈ letters := by
  constructor
  · rintro ⟨root, member, inside⟩
    obtain ⟨letter, listed, equal⟩ := List.mem_map.mp member
    subst root
    have same : value = letter := List.mem_singleton.mp inside
    rw [same]
    exact List.mem_reverse.mp listed
  · intro member
    exact ⟨Word.singleton value,
      List.mem_map.mpr ⟨value, List.mem_reverse.mpr member, rfl⟩,
      List.mem_singleton.mpr rfl⟩

/-- Every word supplies a real initial family, covering exactly its nonsimple
letters, with all previously simple or absent letters retaining their counts. -/
theorem initial_family (word : Word Nat) :
    ∃ normal : Word Nat, ∃ roots : List (Word Nat),
      Derives basis word normal ∧ Family roots normal ∧
      (∀ value, Covered roots value ↔ 2 ≤ word.toList.count value) ∧
      (∀ value, word.toList.count value < 2 → normal.toList.count value = word.toList.count value) := by
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
  obtain ⟨normal, derived, family, counts⟩ :=
    seed_list (initialLetters word) (distinct_nodup _) [] word emptyFamily repeated disjoint
  refine ⟨normal, (initialLetters word).reverse.map Word.singleton, derived, ?_, ?_, ?_⟩
  · simpa only [List.append_nil] using family
  · intro value
    exact (singleton_coverage (initialLetters word) value).trans (initial_letters_spec word value)
  · intro value simple
    apply counts value
    intro member
    have repeated := (initial_letters_spec word value).mp member
    omega

/-- The earlier terminal-family theorem now applies to every actual word,
without an assumed initial Family or a caller-supplied normalization witness. -/
theorem normalize_arbitrary_word (word : Word Nat) :
    ∃ normal : Word Nat, ∃ roots : List (Word Nat),
      Derives basis word normal ∧ Family roots normal ∧
      (∀ value, Covered roots value ↔ 2 ≤ word.toList.count value) ∧ Terminal roots normal := by
  obtain ⟨seeded, initialRoots, first, initialFamily, initialCoverage, _⟩ := initial_family word
  obtain ⟨normal, roots, later, family, coverage, _, _, terminal⟩ :=
    RootFamily.normalize initialRoots seeded initialFamily
  refine ⟨normal, roots, first.trans later, family, ?_, terminal⟩
  intro value
  exact (coverage value).symm.trans (initialCoverage value)

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection.two_occurrences
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection.seed_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection.fourth_to_square
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection.singleton_normal_perfect
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection.normalize_singleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection.singleton_perfection
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection.adjoin_singleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection.seed_list
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection.distinct_nodup
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection.initial_letters_spec
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection.initial_family
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SingletonPerfection.normalize_arbitrary_word
