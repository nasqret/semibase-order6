import SemigroupBasis.FiniteNilpotentCertificate

namespace SemigroupBasis
namespace FiniteNilpotentRestrictedGrowthEnumerator

open FiniteVariableRenaming

/-- Enumerate restricted-growth suffixes of a fixed length when `next`
variable names have already been introduced.  The order matches the metadata
materializer: all previously seen codes first, followed by the fresh code. -/
def enumerateFrom : (next length : Nat) → List (List Nat)
  | _, 0 => [[]]
  | next, length + 1 =>
      ((List.range next).flatMap fun code =>
        (enumerateFrom next length).map (List.cons code)) ++
        (enumerateFrom (next + 1) length).map (List.cons next)

/-- The cardinality recurrence for `enumerateFrom`, kept separate from the
materialized list so large candidate-domain offsets can be simplified without
traversing every preceding row. -/
def enumerateFromCount : (next length : Nat) → Nat
  | _, 0 => 1
  | next, length + 1 =>
      next * enumerateFromCount next length +
        enumerateFromCount (next + 1) length

private theorem length_flatMap_consMap
    (codes : List Nat) (rows : List (List Nat)) :
    (codes.flatMap fun code => rows.map (List.cons code)).length =
      codes.length * rows.length := by
  induction codes with
  | nil => simp
  | cons code codes induction =>
      simp [induction, Nat.succ_mul, Nat.add_comm]

/-- `enumerateFromCount` computes the length of the restricted-growth
enumerator without constructing its exponentially larger output list. -/
theorem length_enumerateFrom (next length : Nat) :
    (enumerateFrom next length).length =
      enumerateFromCount next length := by
  induction length generalizing next with
  | zero =>
      simp [enumerateFrom, enumerateFromCount]
  | succ length induction =>
      simp only [enumerateFrom, List.length_append, List.length_map]
      rw [length_flatMap_consMap, List.length_range,
        induction, induction]
      rfl

/-- Every restricted-growth sequence occurs in the executable enumerator. -/
theorem mem_enumerateFrom
    {next final : Nat} {codes : List Nat}
    (growth : RestrictedGrowthFrom next codes final) :
    codes ∈ enumerateFrom next codes.length := by
  induction growth with
  | nil next =>
      simp [enumerateFrom]
  | @seen next final code rest smaller restGrowth induction =>
      simp only [List.length_cons, enumerateFrom, List.mem_append]
      apply Or.inl
      apply List.mem_flatMap.mpr
      refine ⟨code, List.mem_range.mpr smaller, ?_⟩
      exact List.mem_map.mpr ⟨rest, induction, rfl⟩
  | @fresh next final rest restGrowth induction =>
      simp only [List.length_cons, enumerateFrom, List.mem_append]
      apply Or.inr
      exact List.mem_map.mpr ⟨rest, induction, rfl⟩

/-- Restricted-growth rows together with the number of available variable
names after the row.  This has the same row order as `enumerateFrom`, but
retaining the final state lets a following constrained suffix be generated
without enumerating and filtering every unrestricted continuation. -/
def enumerateFromWithFinal :
    (next length : Nat) → List (List Nat × Nat)
  | next, 0 => [([], next)]
  | next, length + 1 =>
      ((List.range next).flatMap fun code =>
        (enumerateFromWithFinal next length).map fun row =>
          (code :: row.1, row.2)) ++
        (enumerateFromWithFinal (next + 1) length).map fun row =>
          (next :: row.1, row.2)

/-- Every restricted-growth sequence occurs in the state-retaining
enumerator with its exact final state. -/
theorem mem_enumerateFromWithFinal
    {next final : Nat} {codes : List Nat}
    (growth : RestrictedGrowthFrom next codes final) :
    (codes, final) ∈ enumerateFromWithFinal next codes.length := by
  induction growth with
  | nil next =>
      simp [enumerateFromWithFinal]
  | @seen next final code rest smaller restGrowth induction =>
      simp only [List.length_cons, enumerateFromWithFinal, List.mem_append]
      apply Or.inl
      apply List.mem_flatMap.mpr
      refine ⟨code, List.mem_range.mpr smaller, ?_⟩
      exact List.mem_map.mpr ⟨(rest, final), induction, rfl⟩
  | @fresh next final rest restGrowth induction =>
      simp only [List.length_cons, enumerateFromWithFinal, List.mem_append]
      apply Or.inr
      exact List.mem_map.mpr ⟨(rest, final), induction, rfl⟩

/-- Enumerate restricted-growth suffixes while pruning a branch as soon as it
reuses a code already seen in this suffix.  On calls whose `used` entries are
all below `next`, the order is exactly the order obtained by filtering
`enumerateFrom` for duplicate-free rows. -/
def enumerateNodupFrom :
    (next length : Nat) → List Nat → List (List Nat)
  | _, 0, _ => [[]]
  | next, length + 1, used =>
      (((List.range next).filter fun code => decide (code ∉ used)).flatMap
        fun code =>
          (enumerateNodupFrom next length (code :: used)).map
            (List.cons code)) ++
        (enumerateNodupFrom (next + 1) length (next :: used)).map
          (List.cons next)

/-- Every duplicate-free restricted-growth suffix occurs in the pruned
enumerator, provided it is disjoint from the already-used suffix codes. -/
theorem mem_enumerateNodupFrom
    {next final : Nat} {codes used : List Nat}
    (growth : RestrictedGrowthFrom next codes final)
    (nodup : codes.Nodup)
    (disjoint : ∀ code, code ∈ codes → code ∉ used) :
    codes ∈ enumerateNodupFrom next codes.length used := by
  induction growth generalizing used with
  | nil next =>
      simp [enumerateNodupFrom]
  | @seen next final code rest smaller restGrowth induction =>
      have headNotMem := (List.nodup_cons.mp nodup).1
      have restNodup := (List.nodup_cons.mp nodup).2
      simp only [List.length_cons, enumerateNodupFrom, List.mem_append]
      apply Or.inl
      apply List.mem_flatMap.mpr
      refine ⟨code, ?_, ?_⟩
      · apply List.mem_filter.mpr
        exact ⟨List.mem_range.mpr smaller,
          decide_eq_true (disjoint code (by simp))⟩
      · apply List.mem_map.mpr
        refine ⟨rest, ?_, rfl⟩
        apply induction restNodup
        intro value member inUsed
        rcases List.mem_cons.mp inUsed with equals | inUsed
        · apply headNotMem
          simpa only [equals] using member
        · exact disjoint value (List.mem_cons_of_mem code member) inUsed
  | @fresh next final rest restGrowth induction =>
      have headNotMem := (List.nodup_cons.mp nodup).1
      have restNodup := (List.nodup_cons.mp nodup).2
      simp only [List.length_cons, enumerateNodupFrom, List.mem_append]
      apply Or.inr
      apply List.mem_map.mpr
      refine ⟨rest, ?_, rfl⟩
      apply induction restNodup
      intro value member inUsed
      rcases List.mem_cons.mp inUsed with equals | inUsed
      · apply headNotMem
        simpa only [equals] using member
      · exact disjoint value (List.mem_cons_of_mem next member) inUsed

/-- Convert a list to a nonempty word.  The fallback is unreachable in the
positive-length candidate domains but keeps the enumerator total. -/
def wordOfList : List Nat → Word Nat
  | [] => Word.singleton 0
  | head :: tail => ⟨head, tail⟩

private theorem wordOfList_toList (word : Word Nat) :
    wordOfList word.toList = word := by
  cases word
  rfl

/-- Split a restricted-growth row at the requested left length. -/
def splitIdentity (leftLength : Nat) (codes : List Nat) : Identity Nat :=
  ⟨wordOfList (codes.take leftLength),
    wordOfList (codes.drop leftLength)⟩

private theorem splitIdentity_append (left right : Word Nat) :
    splitIdentity left.toList.length (left.toList ++ right.toList) =
      (⟨left, right⟩ : Identity Nat) := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only [splitIdentity, Word.toList]
          rw [List.take_append_of_le_length (Nat.le_refl _),
            List.take_length,
            List.drop_append_of_le_length (Nat.le_refl _),
            List.drop_length, List.nil_append]
          rfl

/-- All normalized pairs with these two positive side lengths. -/
def identitiesAtLengths (leftLength rightLength : Nat) :
    List (Identity Nat) :=
  (enumerateFrom 0 (leftLength + rightLength)).map
    (splitIdentity leftLength)

/-- Cardinality of a fixed side-length block without materializing its
restricted-growth identities. -/
theorem length_identitiesAtLengths (leftLength rightLength : Nat) :
    (identitiesAtLengths leftLength rightLength).length =
      enumerateFromCount 0 (leftLength + rightLength) := by
  simp [identitiesAtLengths, length_enumerateFrom]

private theorem mem_identitiesAtLengths
    (left right : Word Nat) {final : Nat}
    (growth :
      RestrictedGrowthFrom 0 (left.toList ++ right.toList) final) :
    (⟨left, right⟩ : Identity Nat) ∈
      identitiesAtLengths left.toList.length right.toList.length := by
  apply List.mem_map.mpr
  refine ⟨left.toList ++ right.toList, ?_, ?_⟩
  · have member := mem_enumerateFrom growth
    simpa only [List.length_append] using member
  · exact splitIdentity_append left right

/-- Positive lengths strictly below a cutoff. -/
def positiveBelow (cutoff : Nat) : List Nat :=
  (List.range (cutoff - 1)).map Nat.succ

private theorem mem_positiveBelow {length cutoff : Nat}
    (positive : 0 < length) (short : length < cutoff) :
    length ∈ positiveBelow cutoff := by
  cases length with
  | zero => omega
  | succ predecessor =>
      simp [positiveBelow]
      omega

/-- Ordered normalized short--short candidates. -/
def shortPairDomain (cutoff : Nat) : List (Identity Nat) :=
  (positiveBelow cutoff).flatMap fun leftLength =>
    (positiveBelow cutoff).flatMap fun rightLength =>
      identitiesAtLengths leftLength rightLength

private theorem restrictedGrowthFrom_append_split
    {next final : Nat} {left right : List Nat}
    (growth : RestrictedGrowthFrom next (left ++ right) final) :
    ∃ middle,
      RestrictedGrowthFrom next left middle ∧
        RestrictedGrowthFrom middle right final := by
  induction left generalizing next final with
  | nil =>
      exact ⟨next, RestrictedGrowthFrom.nil next, by simpa using growth⟩
  | cons code left induction =>
      cases growth with
      | seen smaller restGrowth =>
          rcases induction restGrowth with
            ⟨middle, leftGrowth, rightGrowth⟩
          exact ⟨middle,
            RestrictedGrowthFrom.seen smaller leftGrowth, rightGrowth⟩
      | fresh restGrowth =>
          rcases induction restGrowth with
            ⟨middle, leftGrowth, rightGrowth⟩
          exact ⟨middle,
            RestrictedGrowthFrom.fresh leftGrowth, rightGrowth⟩

/-- Ordered normalized candidates with fixed side lengths and a duplicate-free
right side.  Invalid right-side branches are pruned during generation rather
than constructed and discarded afterward. -/
def exactCommonIdentitiesAtLengths
    (leftLength rightLength : Nat) : List (Identity Nat) :=
  (enumerateFromWithFinal 0 leftLength).flatMap fun leftRow =>
    (enumerateNodupFrom leftRow.2 rightLength []).map fun rightCodes =>
      (⟨wordOfList leftRow.1, wordOfList rightCodes⟩ : Identity Nat)

private theorem mem_exactCommonIdentitiesAtLengths
    (left right : Word Nat) {final : Nat}
    (growth :
      RestrictedGrowthFrom 0 (left.toList ++ right.toList) final)
    (rightNodup : right.toList.Nodup) :
    (⟨left, right⟩ : Identity Nat) ∈
      exactCommonIdentitiesAtLengths
        left.toList.length right.toList.length := by
  rcases restrictedGrowthFrom_append_split growth with
    ⟨middle, leftGrowth, rightGrowth⟩
  apply List.mem_flatMap.mpr
  refine ⟨(left.toList, middle),
    mem_enumerateFromWithFinal leftGrowth, ?_⟩
  apply List.mem_map.mpr
  refine ⟨right.toList, ?_, ?_⟩
  · apply mem_enumerateNodupFrom rightGrowth rightNodup
    intro code member
    simp
  · simp only [wordOfList_toList]

/-- Ordered normalized short--common candidates.  The pruned generator has
the same order as filtering all restricted-growth rows, but its work is
proportional to the retained exact-common domain. -/
def exactCommonDomain (cutoff : Nat) : List (Identity Nat) :=
  (positiveBelow cutoff).flatMap fun leftLength =>
    exactCommonIdentitiesAtLengths leftLength cutoff

/-- The finite exact-common candidate domain used by class certificates. -/
def candidateDomain (cutoff : Nat) : List (Identity Nat) :=
  shortPairDomain cutoff ++ exactCommonDomain cutoff

private theorem word_length_positive (word : Word Nat) :
    0 < word.toList.length := by
  cases word
  simp [Word.toList]

private theorem mem_shortPairDomain
    (left right : Word Nat) {cutoff final : Nat}
    (leftShort : left.toList.length < cutoff)
    (rightShort : right.toList.length < cutoff)
    (growth :
      RestrictedGrowthFrom 0 (left.toList ++ right.toList) final) :
    (⟨left, right⟩ : Identity Nat) ∈ shortPairDomain cutoff := by
  apply List.mem_flatMap.mpr
  refine ⟨left.toList.length,
    mem_positiveBelow (word_length_positive left) leftShort, ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨right.toList.length,
    mem_positiveBelow (word_length_positive right) rightShort,
    mem_identitiesAtLengths left right growth⟩

private theorem mem_exactCommonDomain
    (left right : Word Nat) {cutoff final : Nat}
    (leftShort : left.toList.length < cutoff)
    (rightLength : right.toList.length = cutoff)
    (rightNodup : right.toList.Nodup)
    (growth :
      RestrictedGrowthFrom 0 (left.toList ++ right.toList) final) :
    (⟨left, right⟩ : Identity Nat) ∈ exactCommonDomain cutoff := by
  apply List.mem_flatMap.mpr
  refine ⟨left.toList.length,
    mem_positiveBelow (word_length_positive left) leftShort, ?_⟩
  rw [← rightLength]
  exact mem_exactCommonIdentitiesAtLengths left right growth rightNodup

private theorem nodup_of_map_nodup (values : List α) (rename : α → β)
    (mapped : (values.map rename).Nodup) : values.Nodup := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at mapped ⊢
      refine ⟨?_, induction mapped.2⟩
      intro member
      exact mapped.1 (List.mem_map.mpr ⟨head, member, rfl⟩)

/-- Normalizing either finite nilpotent short shape lands in the recomputed
candidate domain.  The common word must have exactly the cutoff length and
distinct letters, as required by the disjoint universal law. -/
theorem normalize_mem_candidateDomain
    {cutoff : Nat} {common left right : Word Nat}
    (commonLength : common.toList.length = cutoff)
    (commonNodup : common.toList.Nodup)
    (shape :
      FiniteNilpotentCertificate.ShortShape cutoff common left right) :
    FiniteVariableRenaming.normalizeIdentity left right ∈
      candidateDomain cutoff := by
  let result := FiniteVariableRenaming.normalize left right
  change (⟨result.left, result.right⟩ : Identity Nat) ∈
    candidateDomain cutoff
  have normalizes :=
    FiniteVariableRenaming.normalize_normalizes left right
  change left.map result.forward = result.left ∧
    right.map result.forward = result.right at normalizes
  have reconstructs :=
    FiniteVariableRenaming.normalize_reconstructs left right
  change result.left.map result.inverse = left ∧
    result.right.map result.inverse = right at reconstructs
  have restricted :=
    FiniteVariableRenaming.normalize_isRestrictedGrowth left right
  change IsRestrictedGrowth
    (result.left.toList ++ result.right.toList) at restricted
  rcases restricted with ⟨final, growth⟩
  have leftLength :
      result.left.toList.length = left.toList.length := by
    have lengths := congrArg (fun word : Word Nat => word.toList.length)
      normalizes.1
    simpa [Word.map, Word.toList] using lengths.symm
  have rightLength :
      result.right.toList.length = right.toList.length := by
    have lengths := congrArg (fun word : Word Nat => word.toList.length)
      normalizes.2
    simpa [Word.map, Word.toList] using lengths.symm
  rcases shape with shortShort | shortCommon
  · apply List.mem_append.mpr
    apply Or.inl
    apply mem_shortPairDomain result.left result.right
    · simpa only [leftLength] using shortShort.1
    · simpa only [rightLength] using shortShort.2
    · exact growth
  · apply List.mem_append.mpr
    apply Or.inr
    have rightMapped :
        result.right.toList.map result.inverse = right.toList := by
      have words := congrArg Word.toList reconstructs.2
      simpa [Word.map, Word.toList] using words
    have resultRightNodup : result.right.toList.Nodup := by
      apply nodup_of_map_nodup result.right.toList result.inverse
      rw [rightMapped, shortCommon.2]
      exact commonNodup
    apply mem_exactCommonDomain result.left result.right
    · simpa only [leftLength] using shortCommon.1
    · rw [rightLength, shortCommon.2]
      exact commonLength
    · exact resultRightNodup
    · exact growth

end FiniteNilpotentRestrictedGrowthEnumerator
end SemigroupBasis
