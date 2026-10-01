import SemigroupBasis.CoRoots.S5_415EndpointConnectivity
import SemigroupBasis.CoRoots.S5_415RepeatedWords

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-! ## The endpoint coloring at an isolated letter -/

private def IsolatedTransition
    (leadingLetters : List Nat) (marker source target : Nat) : Prop :=
  source ∈ leadingLetters ↔ target ∈ leadingLetters ∨ target = marker

private def IsolatedTransitionsFrom
    (leadingLetters : List Nat) (marker : Nat) (previous : Nat) :
    List Nat → Prop
  | [] => True
  | next :: rest =>
      IsolatedTransition leadingLetters marker previous next ∧
        IsolatedTransitionsFrom leadingLetters marker next rest

private def IsolatedTransitions
    (leadingLetters : List Nat) (marker : Nat) : List Nat → Prop
  | [] => True
  | first :: rest =>
      IsolatedTransitionsFrom leadingLetters marker first rest

/-- Prefix endpoints have color `0`, suffix endpoints have color `1`, and the
isolated marker changes from incoming color `0` to outgoing color `1`. -/
private def isolatedEndpointAssignment
    (leadingLetters : List Nat) (marker : Nat) : EndpointAssignment :=
  fun letter =>
    (if letter ∈ leadingLetters ∨ letter = marker then (0 : Fin 2) else 1,
      if letter ∈ leadingLetters then (0 : Fin 2) else 1)

private theorem isolatedEndpointAssignment_edge_iff
    (leadingLetters : List Nat) (marker source target : Nat) :
    (isolatedEndpointAssignment leadingLetters marker source).2 =
        (isolatedEndpointAssignment leadingLetters marker target).1 ↔
      IsolatedTransition leadingLetters marker source target := by
  by_cases sourceMem : source ∈ leadingLetters
  <;> by_cases targetSide : target ∈ leadingLetters ∨ target = marker
  <;> simp [isolatedEndpointAssignment, IsolatedTransition,
    sourceMem, targetSide]

private theorem isolatedTransitionsFrom_iff_edges
    (leadingLetters : List Nat) (marker previous : Nat) (letters : List Nat) :
    IsolatedTransitionsFrom leadingLetters marker previous letters ↔
      ∀ source target,
        (source, target) ∈ Word.adjacentPairsFrom previous letters →
          IsolatedTransition leadingLetters marker source target := by
  induction letters generalizing previous with
  | nil =>
      simp [IsolatedTransitionsFrom, Word.adjacentPairsFrom]
  | cons next rest ih =>
      constructor
      · intro transitions source target edge
        have first := transitions.1
        have remaining := transitions.2
        simp only [Word.adjacentPairsFrom, List.mem_cons] at edge
        rcases edge with edge | edge
        · cases edge
          exact first
        · exact (ih next).mp remaining source target edge
      · intro edges
        refine ⟨?_, ?_⟩
        · exact edges previous next (by
            simp [Word.adjacentPairsFrom])
        · apply (ih next).mpr
          intro source target edge
          exact edges source target (by
            simp [Word.adjacentPairsFrom, edge])

private theorem compatible_isolatedEndpointAssignment_iff
    (leadingLetters : List Nat) (marker : Nat) (word : Word Nat) :
    Compatible (isolatedEndpointAssignment leadingLetters marker) word ↔
      IsolatedTransitions leadingLetters marker word.toList := by
  cases word with
  | mk head tail =>
      rw [compatible_iff_adjacent_endpoint_eq]
      change
        (∀ source target,
            (source, target) ∈ Word.adjacentPairsFrom head tail →
              (isolatedEndpointAssignment leadingLetters marker source).2 =
                (isolatedEndpointAssignment leadingLetters marker target).1) ↔
          IsolatedTransitionsFrom leadingLetters marker head tail
      rw [isolatedTransitionsFrom_iff_edges]
      constructor
      · intro edges source target edge
        exact
          (isolatedEndpointAssignment_edge_iff
            leadingLetters marker source target).mp
            (edges source target edge)
      · intro transitions source target edge
        exact
          (isolatedEndpointAssignment_edge_iff
            leadingLetters marker source target).mpr
            (transitions source target edge)

private theorem isolatedTransitionsFrom_of_outside
    (leadingLetters : List Nat) (marker : Nat)
    {previous : Nat} {letters : List Nat}
    (previousOutside : previous ∉ leadingLetters)
    (lettersOutside :
      ∀ letter, letter ∈ letters →
        letter ∉ leadingLetters ∧ letter ≠ marker) :
    IsolatedTransitionsFrom leadingLetters marker previous letters := by
  induction letters generalizing previous with
  | nil =>
      trivial
  | cons next rest ih =>
      have nextOutside := lettersOutside next (by simp)
      refine ⟨?_, ?_⟩
      · simp [IsolatedTransition, previousOutside,
          nextOutside.1, nextOutside.2]
      · apply ih nextOutside.1
        intro letter member
        exact lettersOutside letter (by simp [member])

private theorem isolatedTransitionsFrom_prefix_marker_suffix
    (leadingLetters : List Nat) (marker : Nat)
    {previous : Nat} {middle suffix : List Nat}
    (previousMem : previous ∈ leadingLetters)
    (middleMem : ∀ letter, letter ∈ middle → letter ∈ leadingLetters)
    (markerNotPrefix : marker ∉ leadingLetters)
    (suffixOutside :
      ∀ letter, letter ∈ suffix →
        letter ∉ leadingLetters ∧ letter ≠ marker) :
    IsolatedTransitionsFrom leadingLetters marker previous
      (middle ++ marker :: suffix) := by
  induction middle generalizing previous with
  | nil =>
      simp only [List.nil_append, IsolatedTransitionsFrom]
      refine ⟨?_, ?_⟩
      · simp [IsolatedTransition, previousMem]
      · exact isolatedTransitionsFrom_of_outside
          leadingLetters marker markerNotPrefix suffixOutside
  | cons next rest ih =>
      simp only [List.cons_append, IsolatedTransitionsFrom]
      have nextMem : next ∈ leadingLetters :=
        middleMem next (by simp)
      refine ⟨?_, ?_⟩
      · simp [IsolatedTransition, previousMem, nextMem]
      · apply ih nextMem
        intro letter member
        exact middleMem letter (by simp [member])

private theorem isolatedTransitions_of_isolated_split
    (leadingLetters : List Nat) (marker : Nat) (suffix : List Nat)
    (markerNotPrefix : marker ∉ leadingLetters)
    (markerNotSuffix : marker ∉ suffix)
    (disjoint : ∀ letter, letter ∈ leadingLetters → letter ∉ suffix) :
    IsolatedTransitions leadingLetters marker
      (leadingLetters ++ [marker] ++ suffix) := by
  have suffixOutside :
      ∀ letter, letter ∈ suffix →
        letter ∉ leadingLetters ∧ letter ≠ marker := by
    intro letter member
    refine ⟨?_, ?_⟩
    · intro prefixMem
      exact disjoint letter prefixMem member
    · intro equality
      subst letter
      exact markerNotSuffix member
  cases leadingLetters with
  | nil =>
      simpa [IsolatedTransitions] using
        (isolatedTransitionsFrom_of_outside
          ([] : List Nat) marker (by simp) suffixOutside)
  | cons first rest =>
      have transitions :=
        isolatedTransitionsFrom_prefix_marker_suffix
          (first :: rest) marker
          (previous := first) (middle := rest) (suffix := suffix)
          (by simp)
          (by
            intro letter member
            simp [member])
          markerNotPrefix suffixOutside
      simpa [IsolatedTransitions, List.append_assoc] using transitions

private theorem all_outside_of_isolatedTransitionsFrom
    (leadingLetters : List Nat) (marker : Nat)
    {previous : Nat} {letters : List Nat}
    (previousOutside : previous ∉ leadingLetters)
    (transitions :
      IsolatedTransitionsFrom leadingLetters marker previous letters) :
    ∀ letter, letter ∈ letters →
      letter ∉ leadingLetters ∧ letter ≠ marker := by
  induction letters generalizing previous with
  | nil =>
      simp
  | cons next rest ih =>
      have nextOutside : next ∉ leadingLetters ∧ next ≠ marker := by
        have noTargetSide :
            ¬(next ∈ leadingLetters ∨ next = marker) := by
          intro targetSide
          exact previousOutside (transitions.1.mpr targetSide)
        exact ⟨
          fun member => noTargetSide (Or.inl member),
          fun equality => noTargetSide (Or.inr equality)⟩
      intro letter member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact nextOutside
      · exact ih nextOutside.1 transitions.2 letter member

private theorem exists_ordered_split_of_isolatedTransitions
    (leadingLetters : List Nat) (marker : Nat) (letters : List Nat)
    (markerNotPrefix : marker ∉ leadingLetters)
    (markerMem : marker ∈ letters)
    (transitions : IsolatedTransitions leadingLetters marker letters) :
    ∃ before after,
      letters = before ++ [marker] ++ after ∧
        (∀ letter, letter ∈ before → letter ∈ leadingLetters) ∧
        (∀ letter, letter ∈ after →
          letter ∉ leadingLetters ∧ letter ≠ marker) := by
  induction letters with
  | nil =>
      simp at markerMem
  | cons first rest ih =>
      by_cases firstMarker : first = marker
      · subst first
        refine ⟨[], rest, by simp, ?_, ?_⟩
        · simp
        · exact all_outside_of_isolatedTransitionsFrom
            leadingLetters marker markerNotPrefix transitions
      · have markerMemRest : marker ∈ rest := by
          exact (List.mem_cons.mp markerMem).resolve_left
            (Ne.symm firstMarker)
        cases rest with
        | nil =>
            simp at markerMemRest
        | cons second tail =>
            have tailTransitions :
                IsolatedTransitions leadingLetters marker (second :: tail) :=
              transitions.2
            obtain ⟨before, after, shape, beforeMem, afterOutside⟩ :=
              ih markerMemRest tailTransitions
            have secondSide : second ∈ leadingLetters ∨ second = marker := by
              cases before with
              | nil =>
                  simp only [List.nil_append, List.singleton_append] at shape
                  injection shape with equality _
                  exact Or.inr equality
              | cons next remaining =>
                  simp only [List.cons_append] at shape
                  injection shape with equality _
                  subst second
                  exact Or.inl (beforeMem next (by simp))
            have firstMem : first ∈ leadingLetters :=
              transitions.1.mpr secondSide
            refine ⟨first :: before, after, ?_, ?_, afterOutside⟩
            · simp only [List.cons_append]
              rw [shape]
            · intro letter member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact firstMem
              · exact beforeMem letter member

/-! ## Public split certificate -/

/-- The right-hand split forced by the endpoint coloring.  The certificate
records support equality, not literal equality or positional gap alignment. -/
structure CorrespondingIsolatedSplit
    (leftPrefix : List Nat) (marker : Nat) (leftSuffix : List Nat)
    (right : Word Nat) where
  rightPrefix : List Nat
  rightSuffix : List Nat
  factorization :
    right.toList = rightPrefix ++ [marker] ++ rightSuffix
  marker_not_prefix : marker ∉ rightPrefix
  marker_not_suffix : marker ∉ rightSuffix
  supports_disjoint :
    ∀ letter, letter ∈ rightPrefix → letter ∉ rightSuffix
  prefix_support :
    ∀ letter, letter ∈ leftPrefix ↔ letter ∈ rightPrefix
  suffix_support :
    ∀ letter, letter ∈ leftSuffix ↔ letter ∈ rightSuffix

/-- Equal Brandt signatures transport an isolated occurrence across an
identity.  This is the endpoint-valuation part of Volkov's split argument. -/
noncomputable def correspondingIsolatedSplit_of_sameBrandtSignature
    {left right : Word Nat}
    {leftPrefix leftSuffix : List Nat} {marker : Nat}
    (same : SameBrandtSignature left right)
    (leftFactorization :
      left.toList = leftPrefix ++ [marker] ++ leftSuffix)
    (markerNotPrefix : marker ∉ leftPrefix)
    (markerNotSuffix : marker ∉ leftSuffix)
    (supportsDisjoint :
      ∀ letter, letter ∈ leftPrefix → letter ∉ leftSuffix) :
    CorrespondingIsolatedSplit leftPrefix marker leftSuffix right := by
  let assignment := isolatedEndpointAssignment leftPrefix marker
  have leftTransitions :
      IsolatedTransitions leftPrefix marker left.toList := by
    rw [leftFactorization]
    exact isolatedTransitions_of_isolated_split
      leftPrefix marker leftSuffix markerNotPrefix markerNotSuffix
        supportsDisjoint
  have leftCompatible : Compatible assignment left :=
    (compatible_isolatedEndpointAssignment_iff
      leftPrefix marker left).mpr leftTransitions
  have rightCompatible : Compatible assignment right :=
    ((same.2 assignment).1).mp leftCompatible
  have rightTransitions :
      IsolatedTransitions leftPrefix marker right.toList :=
    (compatible_isolatedEndpointAssignment_iff
      leftPrefix marker right).mp rightCompatible
  have markerMemLeft : marker ∈ left.toList := by
    rw [leftFactorization]
    simp
  have markerMemRight : marker ∈ right.toList :=
    (same.1 marker).mp markerMemLeft
  let splitExistence :=
    exists_ordered_split_of_isolatedTransitions
      leftPrefix marker right.toList markerNotPrefix
        markerMemRight rightTransitions
  let rightPrefix := Classical.choose splitExistence
  let suffixExistence := Classical.choose_spec splitExistence
  let rightSuffix := Classical.choose suffixExistence
  have splitProperties := Classical.choose_spec suffixExistence
  have rightFactorization :
      right.toList = rightPrefix ++ [marker] ++ rightSuffix :=
    splitProperties.1
  have rightPrefixMem :
      ∀ letter, letter ∈ rightPrefix → letter ∈ leftPrefix :=
    splitProperties.2.1
  have rightSuffixOutside :
      ∀ letter, letter ∈ rightSuffix →
        letter ∉ leftPrefix ∧ letter ≠ marker :=
    splitProperties.2.2
  have rightSuffixMem :
      ∀ letter, letter ∈ rightSuffix → letter ∈ leftSuffix := by
    intro letter member
    have rightMember : letter ∈ right.toList := by
      rw [rightFactorization]
      simp [member]
    have leftMember : letter ∈ left.toList :=
      (same.1 letter).mpr rightMember
    rw [leftFactorization] at leftMember
    simp only [List.mem_append, List.mem_singleton] at leftMember
    rcases leftMember with (prefixMember | markerEquality) | suffixMember
    · exact ((rightSuffixOutside letter member).1 prefixMember).elim
    · exact ((rightSuffixOutside letter member).2 markerEquality).elim
    · exact suffixMember
  have prefixSupport :
      ∀ letter, letter ∈ leftPrefix ↔ letter ∈ rightPrefix := by
    intro letter
    constructor
    · intro prefixMember
      have leftMember : letter ∈ left.toList := by
        rw [leftFactorization]
        simp [prefixMember]
      have rightMember : letter ∈ right.toList :=
        (same.1 letter).mp leftMember
      rw [rightFactorization] at rightMember
      simp only [List.mem_append, List.mem_singleton] at rightMember
      rcases rightMember with (rightPrefixMember | markerEquality) |
          rightSuffixMember
      · exact rightPrefixMember
      · subst letter
        exact False.elim (markerNotPrefix prefixMember)
      · exact False.elim
          ((rightSuffixOutside letter rightSuffixMember).1 prefixMember)
    · exact rightPrefixMem letter
  have suffixSupport :
      ∀ letter, letter ∈ leftSuffix ↔ letter ∈ rightSuffix := by
    intro letter
    constructor
    · intro suffixMember
      have leftMember : letter ∈ left.toList := by
        rw [leftFactorization]
        simp [suffixMember]
      have rightMember : letter ∈ right.toList :=
        (same.1 letter).mp leftMember
      rw [rightFactorization] at rightMember
      simp only [List.mem_append, List.mem_singleton] at rightMember
      rcases rightMember with (rightPrefixMember | markerEquality) |
          rightSuffixMember
      · exact False.elim
          (supportsDisjoint letter
            (rightPrefixMem letter rightPrefixMember) suffixMember)
      · subst letter
        exact False.elim (markerNotSuffix suffixMember)
      · exact rightSuffixMember
    · exact rightSuffixMem letter
  refine
    { rightPrefix := rightPrefix
      rightSuffix := rightSuffix
      factorization := rightFactorization
      marker_not_prefix := ?_
      marker_not_suffix := ?_
      supports_disjoint := ?_
      prefix_support := prefixSupport
      suffix_support := suffixSupport }
  · intro member
    exact markerNotPrefix ((prefixSupport marker).mpr member)
  · intro member
    exact (rightSuffixOutside marker member).2 rfl
  · intro letter prefixMember suffixMember
    exact supportsDisjoint letter
      ((prefixSupport letter).mpr prefixMember)
      ((suffixSupport letter).mpr suffixMember)

/-! ## Exact recursive semantic obligation -/

/-- Empty sides correspond only to empty sides; nonempty sides retain the full
Brandt signature required by recursive derivation. -/
inductive OptionalSameBrandtSignature :
    Option (Word Nat) → Option (Word Nat) → Prop
  | none : OptionalSameBrandtSignature none none
  | some {left right : Word Nat} :
      SameBrandtSignature left right →
        OptionalSameBrandtSignature (some left) (some right)

/-- The exact pair of subidentities needed after the split-shape theorem.
Keeping it attached to the certificate makes empty prefix and suffix cases
explicit and prevents an implicit choice of dummy semigroup words. -/
def CorrespondingIsolatedSplit.RecursiveSignatures
    {leftPrefix leftSuffix : List Nat} {marker : Nat} {right : Word Nat}
    (split :
      CorrespondingIsolatedSplit leftPrefix marker leftSuffix right) : Prop :=
  OptionalSameBrandtSignature
      (optionalWordOfList leftPrefix)
      (optionalWordOfList split.rightPrefix) ∧
    OptionalSameBrandtSignature
      (optionalWordOfList leftSuffix)
      (optionalWordOfList split.rightSuffix)

end SemigroupBasis.CoRoots.S5_415
