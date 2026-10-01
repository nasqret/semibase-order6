import SemigroupBasis.CoRoots.S5_107Basis
import SemigroupBasis.CoRoots.S5_848
import SemigroupBasis.CoRoots.S5_402SignatureBridge
import SemigroupBasis.Generated.S2_4

namespace SemigroupBasis

namespace CoRoots

namespace Order6S5_107InitialIntersection

open SemigroupBasis

/-- The head-preserving intersection basis. -/
def basis : List (Identity Nat) :=
  [S5_107.powerLaw,
    S5_107.leftEndpointLaw,
    S5_107.rightEndpointLaw,
    S5_107.squareInterleaveLaw,
    S5_107.squareFinalLaw,
    S5_107.attachmentXXZYYLaw,
    S5_107.attachmentXYXZYLaw,
    S5_107.attachmentXYYZXLaw,
    S5_107.attachmentXYZXYLaw,
    S5_107.attachmentXYZYXLaw,
    S5_107.attachmentXZXYYLaw,
    S5_107.attachmentXZYXYLaw,
    S5_107.attachmentXZYYXLaw,
    S5_107.blockSwapLaw,
    S5_848.tailSquarePromotionLaw]

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem derivesTailSquarePromotion
    (guard u v : Word Nat) :
    Derives basis
      ((((guard ++ u) ++ u) ++ v) ++ v)
      ((((guard ++ v) ++ u) ++ u) ++ v) := by
  have base :=
    Derives.fromBasis (basis := basis)
      (e := S5_848.tailSquarePromotionLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords guard u v)
  change Derives basis
    ((((guard ++ u) ++ u) ++ v) ++ v)
    ((((guard ++ v) ++ u) ++ u) ++ v) at substituted
  exact substituted

private theorem derivesPrefixedSquareInitial
    (guard u v : Word Nat) :
    Derives basis
      (guard ++ ((u ++ u) ++ (v ++ v)))
      (guard ++ (((v ++ u) ++ u) ++ v)) := by
  simpa [Word.append_assoc] using
    derivesTailSquarePromotion guard u v

private theorem derivesLeftEndpointExpansion
    (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      (((u ++ u) ++ v) ++ u) := by
  have base :=
    Derives.fromBasis (basis := basis)
      (e := S5_107.leftEndpointLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  change Derives basis
    ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) at substituted
  exact substituted

private theorem derivesSquareFinal
    (u v : Word Nat) :
    Derives basis
      ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ v) ++ u) := by
  have base : Derives basis S5_107.xxyy S5_107.xyyx :=
    Derives.fromBasis (e := S5_107.squareFinalLaw) (by simp [basis])
  have leftShape : S5_107.xxyy = ⟨0, [0, 1, 1]⟩ := by decide
  have rightShape : S5_107.xyyx = ⟨0, [1, 1, 0]⟩ := by decide
  rw [leftShape, rightShape] at base
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesPrefixedAttachmentYXXZY
    (guard x y z : Word Nat) :
    Derives basis
      (guard ++ ((((x ++ x) ++ y) ++ z) ++ y))
      (guard ++ ((((y ++ x) ++ x) ++ z) ++ y)) := by
  have first :=
    Derives.prepend (guard ++ (x ++ x))
      (derivesLeftEndpointExpansion y z)
  have first' :
      Derives basis
        (guard ++ (x ++ (x ++ (y ++ (z ++ y)))))
        (guard ++ (x ++ (x ++ (y ++ (y ++ (z ++ y)))))) := by
    simpa [Word.append_assoc] using first
  have second :=
    Derives.appendRight
      (Derives.prepend guard (derivesSquareFinal x y)) (z ++ y)
  have second' :
      Derives basis
        (guard ++ (x ++ (x ++ (y ++ (y ++ (z ++ y))))))
        (guard ++ (x ++ (y ++ (y ++ (x ++ (z ++ y)))))) := by
    simpa [Word.append_assoc] using second
  have third :=
    Derives.appendRight
      (Derives.symm (derivesTailSquarePromotion guard y x)) (z ++ y)
  have third' :
      Derives basis
        (guard ++ (x ++ (y ++ (y ++ (x ++ (z ++ y))))))
        (guard ++ (y ++ (y ++ (x ++ (x ++ (z ++ y)))))) := by
    simpa [Word.append_assoc] using third
  have fourth :=
    Derives.prepend guard
      (Derives.symm
        (derivesLeftEndpointExpansion y ((x ++ x) ++ z)))
  have fourth' :
      Derives basis
        (guard ++ (y ++ (y ++ (x ++ (x ++ (z ++ y))))))
        (guard ++ (y ++ (x ++ (x ++ (z ++ y))))) := by
    simpa [Word.append_assoc] using fourth
  simpa [Word.append_assoc] using
    first'.trans (second'.trans (third'.trans fourth'))

private theorem bindAppend
    (left right : Word Nat) (sigma : Nat → Word Nat) :
    (left ++ right).bind sigma = left.bind sigma ++ right.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bindBind
    (word : Word Nat) (tau sigma : Nat → Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bindSingleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem prefixedS5AxiomDerivesAfterBind
    (guard : Word Nat) (sigma : Nat → Word Nat)
    (e : Identity Nat) (member : e ∈ S5_107.basis) :
    Derives basis
      (guard ++ e.lhs.bind sigma) (guard ++ e.rhs.bind sigma) := by
  simp only [S5_107.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.powerLaw) (by simp [basis])) sigma
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.leftEndpointLaw) (by simp [basis])) sigma
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.rightEndpointLaw) (by simp [basis])) sigma
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.squareInterleaveLaw) (by simp [basis])) sigma
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.squareFinalLaw) (by simp [basis])) sigma
  · have leftShape : S5_107.xxyy = ⟨0, [0, 1, 1]⟩ := by decide
    have rightShape : S5_107.yxxy = ⟨1, [0, 0, 1]⟩ := by decide
    simp [S5_107.squareInitialLaw, leftShape, rightShape,
      Word.bind, Word.append_assoc]
    simpa [Word.append_assoc] using
      derivesPrefixedSquareInitial guard (sigma 0) (sigma 1)
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.attachmentXXZYYLaw) (by simp [basis])) sigma
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.attachmentXYXZYLaw) (by simp [basis])) sigma
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.attachmentXYYZXLaw) (by simp [basis])) sigma
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.attachmentXYZXYLaw) (by simp [basis])) sigma
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.attachmentXYZYXLaw) (by simp [basis])) sigma
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.attachmentXZXYYLaw) (by simp [basis])) sigma
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.attachmentXZYXYLaw) (by simp [basis])) sigma
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.attachmentXZYYXLaw) (by simp [basis])) sigma
  · have leftShape : S5_107.xxyzy = ⟨0, [0, 1, 2, 1]⟩ := by decide
    have rightShape : S5_107.yxxzy = ⟨1, [0, 0, 2, 1]⟩ := by decide
    simp [S5_107.attachmentYXXZYLaw, leftShape, rightShape,
      Word.bind, Word.append_assoc]
    simpa [Word.append_assoc] using
      derivesPrefixedAttachmentYXXZY guard (sigma 0) (sigma 1) (sigma 2)
  · exact Derives.prepend guard <| Derives.subst
      (Derives.fromBasis (e := S5_107.blockSwapLaw) (by simp [basis])) sigma

private theorem liftS5DerivationUnderPrefix
    {left right : Word Nat}
    (derivation : Derives S5_107.basis left right)
    (guard : Word Nat) (sigma : Nat → Word Nat) :
    Derives basis
      (guard ++ left.bind sigma) (guard ++ right.bind sigma) := by
  induction derivation generalizing guard sigma with
  | fromBasis member =>
      exact prefixedS5AxiomDerivesAfterBind guard sigma _ member
  | refl word => exact Derives.refl _
  | symm derivation ih => exact Derives.symm (ih guard sigma)
  | trans first second ihFirst ihSecond =>
      exact Derives.trans (ihFirst guard sigma) (ihSecond guard sigma)
  | prepend pre derivation ih =>
      simpa [bindAppend, Word.append_assoc] using
        ih (guard ++ pre.bind sigma) sigma
  | appendRight derivation post ih =>
      simpa [bindAppend, Word.append_assoc] using
        Derives.appendRight (ih guard sigma) (post.bind sigma)
  | subst derivation tau ih =>
      simpa [bindBind] using
        ih guard (fun letter => (tau letter).bind sigma)

private theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base :=
    Derives.fromBasis (basis := basis)
      (e := S5_107.powerLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u u u)
  change Derives basis (u ++ u) ((u ++ u) ++ u) at substituted
  exact substituted

private theorem listDerivesDuplicateInitial
    (head : Nat) {tail : List Nat} (member : head ∈ tail) :
    S5_107.ListDerives basis
      (head :: tail) (head :: head :: tail) := by
  rcases List.append_of_mem member with ⟨before, after, rfl⟩
  cases before with
  | nil =>
      have expanded := S5_107.ListDerives.ofWord
        (derivesPowerExpansion (Word.singleton head))
      simpa [Word.toList_append, List.append_assoc] using
        S5_107.ListDerives.append expanded after
  | cons middleHead middleTail =>
      let middle := S5_107.listWordOfCons middleHead middleTail
      have expanded := S5_107.ListDerives.ofWord
        (derivesLeftEndpointExpansion (Word.singleton head) middle)
      simpa [middle, S5_107.listWordOfCons,
        Word.toList_append, List.append_assoc] using
        S5_107.ListDerives.append expanded after

private theorem derivesDuplicateInitial
    (word : Word Nat) (member : word.head ∈ word.tail) :
    Derives basis word (Word.singleton word.head ++ word) := by
  cases word with
  | mk head tail =>
      have listDerivation := listDerivesDuplicateInitial head member
      simpa [S5_107.listWordOfCons, Word.singleton, Word.append] using
        S5_107.ListDerives.toWord listDerivation

private theorem suffixCappedOfSimpleCommonHead
    {left right leftSuffix rightSuffix : Word Nat}
    (same : S5_107.SameSimpleAdjacencySignature left right)
    (heads : left.head = right.head)
    (leftShape : left = Word.singleton left.head ++ leftSuffix)
    (rightShape : right = Word.singleton right.head ++ rightSuffix)
    (leftSimple : left.toList.count left.head = 1)
    (rightSimple : right.toList.count right.head = 1) :
    ∀ letter, S5_107.cappedMultiplicity leftSuffix letter =
      S5_107.cappedMultiplicity rightSuffix letter := by
  intro letter
  by_cases h : letter = left.head
  · subst letter
    rw [leftShape] at leftSimple
    rw [rightShape] at rightSimple
    simp [heads, Word.toList] at leftSimple rightSimple
    unfold S5_107.cappedMultiplicity
    rw [heads]
    change Nat.min 2 (leftSuffix.toList.count right.head) =
      Nat.min 2 (rightSuffix.toList.count right.head)
    have leftZero : leftSuffix.toList.count right.head = 0 := by
      simpa [Word.toList] using leftSimple
    have rightZero : rightSuffix.toList.count right.head = 0 := by
      simpa [Word.toList] using rightSimple
    rw [leftZero, rightZero]
  · have hright : letter ≠ right.head := by
      rw [← heads]
      exact h
    have capped := same.capped letter
    rw [leftShape, rightShape] at capped
    unfold S5_107.cappedMultiplicity at capped ⊢
    change Nat.min 2 (leftSuffix.toList.count letter) =
      Nat.min 2 (rightSuffix.toList.count letter)
    change Nat.min 2 ((left.head :: leftSuffix.toList).count letter) =
      Nat.min 2 ((right.head :: rightSuffix.toList).count letter) at capped
    simpa [h, hright, Ne.symm h, Ne.symm hright] using capped

private theorem adjacent_from_absent_source_is_first
    (head source target : Nat) (tail : List Nat)
    (absent : tail.count source = 0)
    (edge : (source, target) ∈ Word.adjacentPairsFrom head tail) :
    source = head ∧ target = tail.headD head := by
  induction tail generalizing head with
  | nil => simp [Word.adjacentPairsFrom] at edge
  | cons next rest ih =>
      simp only [Word.adjacentPairsFrom, List.mem_cons] at edge
      rcases edge with edge | edge
      · injection edge with sourceEq targetEq
        exact ⟨sourceEq, by simpa using targetEq⟩
      · have absentRest : rest.count source = 0 := by
          simp only [List.count_cons] at absent
          omega
        have found := ih next absentRest edge
        have nextNe : next ≠ source := by
          intro equal
          subst next
          simp at absent
        exact False.elim (nextNe found.1.symm)

private theorem simpleInitial_iff_prefixedAdjacent
    (head letter : Nat) (suffix : Word Nat)
    (absent : suffix.toList.count head = 0) :
    S5_107.SimpleInitial suffix letter ↔
      S5_107.SimpleAdjacent
        (Word.singleton head ++ suffix) head letter := by
  cases suffix with
  | mk suffixHead suffixTail =>
      unfold S5_107.SimpleInitial S5_107.SimpleAdjacent S5_107.SimpleIn
      change
        (List.count letter (suffixHead :: suffixTail) = 1 ∧
          suffixHead = letter) ↔
        (List.count head (head :: suffixHead :: suffixTail) = 1 ∧
          List.count letter (head :: suffixHead :: suffixTail) = 1 ∧
          (head, letter) ∈
            Word.adjacentPairsFrom head (suffixHead :: suffixTail))
      have different : head ≠ suffixHead := by
        intro equal
        subst suffixHead
        change List.count head (head :: suffixTail) = 0 at absent
        simp at absent
      constructor
      · rintro ⟨simple, rfl⟩
        refine ⟨?_, ?_, ?_⟩
        · simpa [different] using absent
        · simpa [different] using simple
        · simp [Word.adjacentPairsFrom]
      · rintro ⟨_, simple, edge⟩
        have first := adjacent_from_absent_source_is_first
          head head letter (suffixHead :: suffixTail) absent edge
        have letterNe : head ≠ letter := by
          intro equal
          subst letter
          have : head = suffixHead := by simpa using first.2
          exact different this
        exact ⟨by simpa [letterNe] using simple, by simpa using first.2.symm⟩

private theorem suffixInitialOfSimpleCommonHead
    {left right leftSuffix rightSuffix : Word Nat}
    (same : S5_107.SameSimpleAdjacencySignature left right)
    (heads : left.head = right.head)
    (leftShape : left = Word.singleton left.head ++ leftSuffix)
    (rightShape : right = Word.singleton right.head ++ rightSuffix)
    (leftSimple : left.toList.count left.head = 1)
    (rightSimple : right.toList.count right.head = 1) :
    ∀ letter, S5_107.SimpleInitial leftSuffix letter ↔
      S5_107.SimpleInitial rightSuffix letter := by
  have leftAbsent : leftSuffix.toList.count left.head = 0 := by
    rw [leftShape] at leftSimple
    simpa [Word.toList] using leftSimple
  have rightAbsent : rightSuffix.toList.count right.head = 0 := by
    rw [rightShape] at rightSimple
    simpa [Word.toList] using rightSimple
  intro letter
  rw [simpleInitial_iff_prefixedAdjacent left.head letter leftSuffix leftAbsent,
    simpleInitial_iff_prefixedAdjacent right.head letter rightSuffix rightAbsent]
  rw [← leftShape, ← rightShape, heads]
  exact same.adjacent right.head letter

private theorem simpleFinal_iff_prefixed
    (head letter : Nat) (suffix : Word Nat)
    (absent : suffix.toList.count head = 0) :
    S5_107.SimpleFinal suffix letter ↔
      S5_107.SimpleFinal (Word.singleton head ++ suffix) letter := by
  unfold S5_107.SimpleFinal S5_107.SimpleIn
  rw [Word.final_append]
  change
    (suffix.toList.count letter = 1 ∧ suffix.final = letter) ↔
      ((head :: suffix.toList).count letter = 1 ∧ suffix.final = letter)
  by_cases equal : head = letter
  · subst letter
    have finalMember : suffix.final ∈ suffix.toList := by
      cases suffix with
      | mk suffixHead suffixTail =>
          simpa [Word.final, Word.toList] using
            (List.getLastD_mem_cons (l := suffixTail) (a := suffixHead))
    have finalNe : suffix.final ≠ head := by
      intro equal
      exact (List.count_eq_zero.mp absent) (equal ▸ finalMember)
    simp [absent, finalNe]
  · simp [equal]

private theorem suffixFinalOfSimpleCommonHead
    {left right leftSuffix rightSuffix : Word Nat}
    (same : S5_107.SameSimpleAdjacencySignature left right)
    (leftShape : left = Word.singleton left.head ++ leftSuffix)
    (rightShape : right = Word.singleton right.head ++ rightSuffix)
    (leftSimple : left.toList.count left.head = 1)
    (rightSimple : right.toList.count right.head = 1) :
    ∀ letter, S5_107.SimpleFinal leftSuffix letter ↔
      S5_107.SimpleFinal rightSuffix letter := by
  have leftAbsent : leftSuffix.toList.count left.head = 0 := by
    rw [leftShape] at leftSimple
    simpa [Word.toList] using leftSimple
  have rightAbsent : rightSuffix.toList.count right.head = 0 := by
    rw [rightShape] at rightSimple
    simpa [Word.toList] using rightSimple
  intro letter
  rw [simpleFinal_iff_prefixed left.head letter leftSuffix leftAbsent,
    simpleFinal_iff_prefixed right.head letter rightSuffix rightAbsent]
  rw [← leftShape, ← rightShape]
  exact same.final letter

private theorem suffixAdjacentOfSimpleCommonHead
    {left right leftSuffix rightSuffix : Word Nat}
    (same : S5_107.SameSimpleAdjacencySignature left right)
    (heads : left.head = right.head)
    (leftShape : left = Word.singleton left.head ++ leftSuffix)
    (rightShape : right = Word.singleton right.head ++ rightSuffix)
    (leftSimple : left.toList.count left.head = 1)
    (rightSimple : right.toList.count right.head = 1) :
    ∀ source target, S5_107.SimpleAdjacent leftSuffix source target ↔
      S5_107.SimpleAdjacent rightSuffix source target := by
  intro source target
  by_cases hsource : source = left.head
  · subst source
    have leftAbsent : leftSuffix.toList.count left.head = 0 := by
      rw [leftShape] at leftSimple
      simpa [Word.toList] using leftSimple
    have rightAbsent : rightSuffix.toList.count right.head = 0 := by
      rw [rightShape] at rightSimple
      simpa [Word.toList] using rightSimple
    unfold S5_107.SimpleAdjacent S5_107.SimpleIn
    have leftAbsent' : leftSuffix.toList.count left.head = 0 := by
      simpa [heads] using leftAbsent
    have rightAbsent' : rightSuffix.toList.count left.head = 0 := by
      simpa [heads] using rightAbsent
    constructor
    · rintro ⟨simple, _⟩
      exact False.elim (by rw [leftAbsent'] at simple; omega)
    · rintro ⟨simple, _⟩
      exact False.elim (by rw [rightAbsent'] at simple; omega)
  · have h_adjacency : S5_107.SimpleAdjacent left source target ↔ S5_107.SimpleAdjacent right source target :=
      same.adjacent source target
    rw [S5_107.SimpleAdjacent, S5_107.SimpleAdjacent] at *;
    rw [leftShape] at h_adjacency; rw [rightShape] at h_adjacency; simp +decide [S5_107.SimpleIn, Word.adjacentPairs] at h_adjacency ⊢;
    simp +decide [ Word.toList, Word.adjacentPairsFrom ] at *;
    grind

private theorem suffixSignatureOfSimpleCommonHead
    {left right leftSuffix rightSuffix : Word Nat}
    (same : S5_107.SameSimpleAdjacencySignature left right)
    (heads : left.head = right.head)
    (leftShape : left = Word.singleton left.head ++ leftSuffix)
    (rightShape : right = Word.singleton right.head ++ rightSuffix)
    (leftSimple : left.toList.count left.head = 1)
    (rightSimple : right.toList.count right.head = 1) :
    S5_107.SameSimpleAdjacencySignature leftSuffix rightSuffix := by
  exact
    { capped := suffixCappedOfSimpleCommonHead same heads leftShape
        rightShape leftSimple rightSimple
      initial := suffixInitialOfSimpleCommonHead same heads leftShape
        rightShape leftSimple rightSimple
      final := suffixFinalOfSimpleCommonHead same leftShape
        rightShape leftSimple rightSimple
      adjacent := suffixAdjacentOfSimpleCommonHead same heads leftShape
        rightShape leftSimple rightSimple }

private theorem s5DerivesOfSignature
    {left right : Word Nat}
    (same : S5_107.SameSimpleAdjacencySignature left right) :
    Derives S5_107.basis left right := by
  have leftNormal := S5_107.derivesCanonicalUnrestricted left
  have rightNormal := S5_107.derivesCanonicalUnrestricted right
  rw [same.canonicalWord_eq] at leftNormal
  exact leftNormal.trans rightNormal.symm

private theorem derivesOfSignatureAndHead
    {left right : Word Nat}
    (same : S5_107.SameSimpleAdjacencySignature left right)
    (heads : left.head = right.head) :
    Derives basis left right := by
  have simpleIff := same.simple left.head
  by_cases leftHeadSimple : left.toList.count left.head = 1
  · have rightHeadSimple : right.toList.count right.head = 1 := by
      have := simpleIff.mp leftHeadSimple
      simpa [heads] using this
    cases left with
    | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
        change leftHead = rightHead at heads
        subst rightHead
        cases leftTail with
        | nil =>
          cases rightTail with
          | nil => exact Derives.refl _
          | cons rightSuffixHead rightSuffixTail =>
            have rightHeadNe : rightSuffixHead ≠ leftHead := by
              intro equal
              subst rightSuffixHead
              simp [Word.toList] at rightHeadSimple
            have leftZero : S5_107.cappedMultiplicity
                (Word.mk leftHead []) rightSuffixHead = 0 := by
              rw [S5_107.cappedMultiplicity_eq_zero_iff]
              simp [Word.toList, Ne.symm rightHeadNe]
            have rightNonzero : S5_107.cappedMultiplicity
                (Word.mk leftHead (rightSuffixHead :: rightSuffixTail))
                rightSuffixHead ≠ 0 := by
              intro zero
              have countZero := (S5_107.cappedMultiplicity_eq_zero_iff _ _).mp zero
              change List.count rightSuffixHead
                (leftHead :: rightSuffixHead :: rightSuffixTail) = 0 at countZero
              have positive : 0 < List.count rightSuffixHead
                  (leftHead :: rightSuffixHead :: rightSuffixTail) :=
                List.count_pos_iff.mpr (by simp)
              omega
            have transferred : S5_107.cappedMultiplicity
                (Word.mk leftHead (rightSuffixHead :: rightSuffixTail))
                rightSuffixHead = 0 := by
              rw [← same.capped rightSuffixHead]
              exact leftZero
            exact False.elim (rightNonzero transferred)
        | cons leftSuffixHead leftSuffixTail =>
          cases rightTail with
          | nil =>
            have leftHeadNe : leftSuffixHead ≠ leftHead := by
              intro equal
              subst leftSuffixHead
              simp [Word.toList] at leftHeadSimple
            have leftNonzero : S5_107.cappedMultiplicity
                (Word.mk leftHead (leftSuffixHead :: leftSuffixTail))
                leftSuffixHead ≠ 0 := by
              intro zero
              have countZero := (S5_107.cappedMultiplicity_eq_zero_iff _ _).mp zero
              change List.count leftSuffixHead
                (leftHead :: leftSuffixHead :: leftSuffixTail) = 0 at countZero
              have positive : 0 < List.count leftSuffixHead
                  (leftHead :: leftSuffixHead :: leftSuffixTail) :=
                List.count_pos_iff.mpr (by simp)
              omega
            have rightZero : S5_107.cappedMultiplicity
                (Word.mk leftHead []) leftSuffixHead = 0 := by
              rw [S5_107.cappedMultiplicity_eq_zero_iff]
              simp [Word.toList, Ne.symm leftHeadNe]
            exact False.elim (leftNonzero (same.capped leftSuffixHead ▸ rightZero))
          | cons rightSuffixHead rightSuffixTail =>
            let leftSuffix : Word Nat := ⟨leftSuffixHead, leftSuffixTail⟩
            let rightSuffix : Word Nat := ⟨rightSuffixHead, rightSuffixTail⟩
            have suffixSame := suffixSignatureOfSimpleCommonHead same rfl
              (leftSuffix := leftSuffix) (rightSuffix := rightSuffix)
              (by rfl) (by rfl)
              leftHeadSimple rightHeadSimple
            have suffixDerivation := s5DerivesOfSignature suffixSame
            have lifted := liftS5DerivationUnderPrefix suffixDerivation
              (Word.singleton leftHead) Word.singleton
            rw [bindSingleton, bindSingleton] at lifted
            simpa [leftSuffix, rightSuffix, Word.singleton, Word.append] using lifted
  · have rightHeadNotSimple : right.toList.count right.head ≠ 1 := by
      intro simple
      apply leftHeadSimple
      have := simpleIff.mpr (by simpa [heads] using simple)
      exact this
    have leftHeadInTail : left.head ∈ left.tail := by
      cases left with
      | mk head tail =>
          simp only [Word.toList, List.count_cons_self] at leftHeadSimple
          apply List.count_pos_iff.mp
          show 0 < tail.count head
          omega
    have rightHeadInTail : right.head ∈ right.tail := by
      cases right with
      | mk head tail =>
          simp only [Word.toList, List.count_cons_self] at rightHeadNotSimple
          apply List.count_pos_iff.mp
          show 0 < tail.count head
          omega
    have leftDuplicate := derivesDuplicateInitial left leftHeadInTail
    have rightDuplicate := derivesDuplicateInitial right rightHeadInTail
    have rootDerivation := s5DerivesOfSignature same
    have lifted := liftS5DerivationUnderPrefix rootDerivation
      (Word.singleton left.head) Word.singleton
    rw [bindSingleton, bindSingleton] at lifted
    have guarded : Derives basis
        (Word.singleton left.head ++ left)
        (Word.singleton right.head ++ right) := by
      simpa [heads] using lifted
    simpa [heads] using
      leftDuplicate.trans (guarded.trans rightDuplicate.symm)

theorem intersection_complete_aristotle (identity : Identity Nat) (initialValid : identity.SatisfiedBy SemigroupBasis.Generated.S2_4.table.semigroup) (s5Valid : identity.SatisfiedBy SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup) : Derives basis identity.lhs identity.rhs
:= by
  have heads : identity.lhs.head = identity.rhs.head := by
    apply Decidable.byContradiction
    intro different
    let valuation : Nat → Fin 2 := fun letter =>
      if letter = identity.lhs.head then 0 else 1
    have evaluated := initialValid valuation
    have evaluated' :
        SemigroupBasis.Examples.leftZeroTwo.semigroup.eval valuation identity.lhs =
          SemigroupBasis.Examples.leftZeroTwo.semigroup.eval valuation identity.rhs :=
      evaluated
    rw [SemigroupBasis.Examples.leftZeroTwo_eval,
      SemigroupBasis.Examples.leftZeroTwo_eval] at evaluated'
    simp [valuation, Ne.symm different] at evaluated'
  exact derivesOfSignatureAndHead
    (S5_107.valid_sameSimpleAdjacencySignature identity s5Valid) heads

end Order6S5_107InitialIntersection

end CoRoots

end SemigroupBasis