import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSimpleFactorInvariant

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootBlockPartition

open MaximalFactors FactorBoundaries BlockAlignment RootFamily SimpleFactorInvariant

/-- The restriction-stable part of perfection. A root may be absent from a
subfactor; every positive run which is present is still its actual square. -/
def SquareCovered (roots : List (Word Nat)) (word : Word Nat) : Prop :=
  ∀ root ∈ roots, ∀ piece ∈ decompose (supportTag root) word.toList,
    supportTag root piece.head = true → piece = root ++ root

def Outside (roots : List (Word Nat)) (piece : Word Nat) : Prop :=
  ∀ value ∈ piece.toList, ¬ Covered roots value

def RootPiece (roots : List (Word Nat)) (piece : Word Nat) : Prop :=
  (∃ root ∈ roots, piece = root ++ root) ∨ Outside roots piece

/-- Factors are nonempty words, not support-set labels. The equality records
their literal order and multiplicities in the original word. -/
def SquarePartition (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) : Prop :=
  flatten pieces = word.toList ∧ ∀ piece ∈ pieces, RootPiece roots piece

theorem family_square_covered (roots : List (Word Nat)) (word : Word Nat)
    (family : Family roots word) : SquareCovered roots word := by
  intro root member piece pieceMember positive
  exact (family.2 root member).2.2 piece pieceMember positive

theorem part_letter_mem (word : Word Nat) (pieces : List (Word Nat))
    (equal : flatten pieces = word.toList) (piece : Word Nat)
    (member : piece ∈ pieces) (value : Nat) (inside : value ∈ piece.toList) :
    value ∈ word.toList := by
  rw [← equal]
  exact (mem_flatten value pieces).mpr ⟨piece, member, inside⟩

/-- A negative run for the first root preserves the complete positive runs
of every disjoint remaining root. No clipped root square is substituted. -/
theorem square_covered_negative (first : Word Nat) (roots : List (Word Nat))
    (word outer : Word Nat) (apart : ∀ root ∈ roots, Apart first root)
    (covered : SquareCovered (first :: roots) word)
    (member : outer ∈ decompose (supportTag first) word.toList)
    (negative : supportTag first outer.head = false) :
    SquareCovered roots outer := by
  intro root rootMember inner innerMember innerPositive
  have reverseApart : Apart root first := apart_symm first root (apart root rootMember)
  have contained : ∀ value, supportTag root value = true →
      Bool.not (supportTag first value) = true := by
    intro value positive
    have present : value ∈ root.toList := (supportTag_true root value).mp positive
    cases flag : supportTag first value with
    | false => rfl
    | true =>
        exact False.elim (reverseApart value present ((supportTag_true first value).mp flag))
  have outerMember : outer ∈
      decompose (fun value => Bool.not (supportTag first value)) word.toList := by
    rw [decompose_not]
    exact member
  have outerPositive : Bool.not (supportTag first outer.head) = true := by
    rw [negative]
    rfl
  have original : inner ∈ decompose (supportTag root) word.toList :=
    positive_refinement (supportTag root) (fun value => Bool.not (supportTag first value))
      word outer inner contained outerMember outerPositive innerMember innerPositive
  exact covered root (List.mem_cons.mpr (Or.inr rootMember)) inner original innerPositive

/-- Assemble actual refinements in their original factor order. -/
theorem assemble_refinements (test : Word Nat → Prop) (factors : List (Word Nat)) :
    (∀ factor ∈ factors, ∃ parts : List (Word Nat),
      flatten parts = factor.toList ∧ ∀ part ∈ parts, test part) →
    ∃ parts : List (Word Nat),
      flatten parts = flatten factors ∧ ∀ part ∈ parts, test part := by
  induction factors with
  | nil =>
      intro _
      refine ⟨[], rfl, ?_⟩
      intro part impossible
      cases impossible
  | cons factor factors ih =>
      intro each
      obtain ⟨first, firstEqual, firstTest⟩ :=
        each factor (List.mem_cons.mpr (Or.inl rfl))
      have tailEach : ∀ next ∈ factors, ∃ parts : List (Word Nat),
          flatten parts = next.toList ∧ ∀ part ∈ parts, test part := by
        intro next member
        exact each next (List.mem_cons.mpr (Or.inr member))
      obtain ⟨last, lastEqual, lastTest⟩ := ih tailEach
      refine ⟨first ++ last, ?_, ?_⟩
      · rw [flatten_append, firstEqual, lastEqual]
        rfl
      · intro part member
        rcases List.mem_append.mp member with earlier | later
        · exact firstTest part earlier
        · exact lastTest part later

/-- Pairwise disjoint roots whose actual positive runs are squares have a
literal square/outside partition of the whole word, without a pre-supplied
factorization or an assumption that every root occurs in every subfactor. -/
theorem partition_of_square_covered (roots : List (Word Nat)) :
    ∀ word : Word Nat, roots.Pairwise Apart → SquareCovered roots word →
      ∃ pieces : List (Word Nat), SquarePartition roots word pieces := by
  induction roots with
  | nil =>
      intro word _ _
      refine ⟨[word], ?_, ?_⟩
      · simp only [flatten, List.append_nil]
      · intro piece member
        have equal : piece = word := List.mem_singleton.mp member
        subst piece
        right
        intro value _ covered
        obtain ⟨root, impossible, _⟩ := covered
        cases impossible
  | cons first roots ih =>
      intro word disjoint covered
      have apart := List.pairwise_cons.mp disjoint
      have each : ∀ outer ∈ decompose (supportTag first) word.toList,
          ∃ parts : List (Word Nat), flatten parts = outer.toList ∧
            ∀ part ∈ parts, RootPiece (first :: roots) part := by
        intro outer member
        cases tag : supportTag first outer.head with
        | true =>
            have square : outer = first ++ first :=
              covered first (List.mem_cons.mpr (Or.inl rfl)) outer member tag
            refine ⟨[outer], ?_, ?_⟩
            · simp only [flatten, List.append_nil]
            · intro part partMember
              have equal : part = outer := List.mem_singleton.mp partMember
              subst part
              exact Or.inl ⟨first, List.mem_cons.mpr (Or.inl rfl), square⟩
        | false =>
            have restricted : SquareCovered roots outer :=
              square_covered_negative first roots word outer apart.1 covered member tag
            obtain ⟨parts, partsEqual, partsKinds⟩ := ih outer apart.2 restricted
            refine ⟨parts, partsEqual, ?_⟩
            intro part partMember
            rcases partsKinds part partMember with square | outside
            · obtain ⟨root, rootMember, equal⟩ := square
              exact Or.inl ⟨root, List.mem_cons.mpr (Or.inr rootMember), equal⟩
            · right
              intro value inside present
              rcases (covered_cons first roots value).mp present with inFirst | inRest
              · have inOuter : value ∈ outer.toList :=
                  part_letter_mem outer parts partsEqual part partMember value inside
                have constant : Constant (supportTag first) outer :=
                  good_member_constant (supportTag first)
                    (decompose_good (supportTag first) word.toList) member
                have valueNegative : supportTag first value = false :=
                  (constant value inOuter).trans tag
                have valuePositive : supportTag first value = true :=
                  (supportTag_true first value).mpr inFirst
                have impossible : (false : Bool) = true := valueNegative.symm.trans valuePositive
                cases impossible
              · exact outside value inside inRest
      obtain ⟨parts, equal, kinds⟩ :=
        assemble_refinements (RootPiece (first :: roots))
          (decompose (supportTag first) word.toList) each
      exact ⟨parts, equal.trans (flatten_decompose (supportTag first) word.toList), kinds⟩

theorem family_partition (roots : List (Word Nat)) (word : Word Nat)
    (family : Family roots word) :
    ∃ pieces : List (Word Nat), SquarePartition roots word pieces :=
  partition_of_square_covered roots word family.1 (family_square_covered roots word family)

theorem partition_nonempty (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (partition : SquarePartition roots word pieces) :
    pieces ≠ [] := by
  intro empty
  have impossible : word.toList = [] := by
    rw [← partition.1, empty]
    rfl
  exact piece_nonempty word impossible

theorem outside_part_simple (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (partition : SquarePartition roots word pieces)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value)
    (part : Word Nat) (member : part ∈ pieces) (outside : Outside roots part) :
    ∀ value ∈ part.toList, word.toList.count value = 1 := by
  intro value inside
  have present : value ∈ word.toList :=
    part_letter_mem word pieces partition.1 part member value inside
  have positive : 1 ≤ word.toList.count value := by
    by_cases zero : word.toList.count value = 0
    · exact False.elim ((List.count_eq_zero.mp zero) present)
    · omega
  have notRepeated : ¬ 2 ≤ word.toList.count value := by
    intro repeated
    exact outside value inside ((coverage value).mpr repeated)
  omega

/-- Every word derives an actual ordered root-square/simple-word partition.
The existing global simple-factor sequence remains unchanged. This does not
yet assert canonical uniqueness, a semantic comparison, or BasisFor. -/
theorem normalize_with_partition (word : Word Nat) :
    ∃ normal : Word Nat, ∃ roots : List (Word Nat), ∃ pieces : List (Word Nat),
      Derives basis word normal ∧ Family roots normal ∧ Terminal roots normal ∧
      (∀ value, Covered roots value ↔ 2 ≤ word.toList.count value) ∧
      (∀ value, Covered roots value ↔ 2 ≤ normal.toList.count value) ∧
      SquarePartition roots normal pieces ∧
      (∀ part ∈ pieces, (∃ root ∈ roots, part = root ++ root) ∨
        (∀ value ∈ part.toList,
          word.toList.count value = 1 ∧ normal.toList.count value = 1)) ∧
      simpleFactors word = simpleFactors normal := by
  obtain ⟨normal, roots, derived, family, terminal, original, current, counts, skeleton⟩ :=
    normalize_arbitrary_word word
  obtain ⟨pieces, partition⟩ := family_partition roots normal family
  refine ⟨normal, roots, pieces, derived, family, terminal, original, current, partition,
    ?_, simple_factors_of_skeleton word normal skeleton⟩
  intro part member
  rcases partition.2 part member with square | outside
  · exact Or.inl square
  · right
    intro value inside
    have finalSimple : normal.toList.count value = 1 :=
      outside_part_simple roots normal pieces partition current part member outside value inside
    have originalNotRepeated : ¬ 2 ≤ word.toList.count value := by
      intro repeated
      exact outside value inside ((original value).mpr repeated)
    have originalLow : word.toList.count value < 2 := by omega
    have unchanged : normal.toList.count value = word.toList.count value := counts value originalLow
    exact ⟨unchanged.symm.trans finalSimple, finalSimple⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootBlockPartition

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootBlockPartition.family_square_covered
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootBlockPartition.part_letter_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootBlockPartition.square_covered_negative
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootBlockPartition.assemble_refinements
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootBlockPartition.partition_of_square_covered
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootBlockPartition.family_partition
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootBlockPartition.partition_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootBlockPartition.outside_part_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootBlockPartition.normalize_with_partition
