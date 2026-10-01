import SemigroupBasis.CoRoots.Order6LeeLiProposition8ASemantics

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiProposition8A

open SemigroupBasis

namespace SemanticTransfer

/-!
# Semantic complete-precedence transfers

This module contains the generic list and pair-projection facts used by the
Proposition 8 canonical adapter.  It deliberately does not import or mention
the canonical representation itself.
-/

/-! ## Transitivity of complete precedence -/

private def precedenceStep
    (x y : Nat) (state : S5_841.PrecedenceState) (letter : Nat) :
    S5_841.PrecedenceState :=
  if letter = x then
    match state with
    | .neither => .onlyX
    | .onlyX => .onlyX
    | .onlyY | .ordered | .violated => .violated
  else if letter = y then
    match state with
    | .neither => .onlyY
    | .onlyX => .ordered
    | .onlyY => .onlyY
    | .ordered => .ordered
    | .violated => .violated
  else state

private theorem precedenceScanList_eq_fold
    (letters : List Nat) (x y : Nat) :
    S5_841.precedenceScanList letters x y =
      letters.foldl (precedenceStep x y) .neither := by
  rfl

private def firstSeen : S5_841.PrecedenceState → Bool
  | .neither | .onlyY => false
  | .onlyX | .ordered | .violated => true

private def secondSeen : S5_841.PrecedenceState → Bool
  | .neither | .onlyX => false
  | .onlyY | .ordered | .violated => true

/-- The three pair scans agree on which shared letters have appeared.  The
last clause records the only way an `x,z` inversion can coexist with scans of
`x,y` and `y,z`: one of those scans is already violated, or `y` has not yet
appeared. -/
private def PrecedenceTransitivityInvariant
    (xy yz xz : S5_841.PrecedenceState) : Prop :=
  firstSeen xy = firstSeen xz ∧
    secondSeen xy = firstSeen yz ∧
    secondSeen yz = secondSeen xz ∧
    (xz = .violated →
      xy = .violated ∨ yz = .violated ∨ firstSeen yz = false)

private theorem precedenceTransitivityInvariant_step
    {x y z letter : Nat}
    (differentXY : x ≠ y)
    (differentYZ : y ≠ z)
    (differentXZ : x ≠ z)
    {xy yz xz : S5_841.PrecedenceState}
    (invariant : PrecedenceTransitivityInvariant xy yz xz) :
    PrecedenceTransitivityInvariant
      (precedenceStep x y xy letter)
      (precedenceStep y z yz letter)
      (precedenceStep x z xz letter) := by
  by_cases isX : letter = x
  · subst letter
    cases xy <;> cases yz <;> cases xz <;>
      simp_all [PrecedenceTransitivityInvariant, firstSeen, secondSeen,
        precedenceStep, Ne.symm differentXY, Ne.symm differentYZ,
        Ne.symm differentXZ]
  · by_cases isY : letter = y
    · subst letter
      cases xy <;> cases yz <;> cases xz <;>
        simp_all [PrecedenceTransitivityInvariant, firstSeen, secondSeen,
          precedenceStep, Ne.symm differentXY, Ne.symm differentYZ,
          Ne.symm differentXZ]
    · by_cases isZ : letter = z
      · subst letter
        cases xy <;> cases yz <;> cases xz <;>
          simp_all [PrecedenceTransitivityInvariant, firstSeen, secondSeen,
            precedenceStep, Ne.symm differentXY, Ne.symm differentYZ,
            Ne.symm differentXZ]
      · cases xy <;> cases yz <;> cases xz <;>
          simp_all [PrecedenceTransitivityInvariant, firstSeen, secondSeen,
            precedenceStep, Ne.symm differentXY, Ne.symm differentYZ,
            Ne.symm differentXZ]

private theorem precedenceTransitivityInvariant_fold
    (x y z : Nat)
    (differentXY : x ≠ y)
    (differentYZ : y ≠ z)
    (differentXZ : x ≠ z) :
    ∀ (letters : List Nat) (xy yz xz : S5_841.PrecedenceState),
      PrecedenceTransitivityInvariant xy yz xz →
        PrecedenceTransitivityInvariant
          (letters.foldl (precedenceStep x y) xy)
          (letters.foldl (precedenceStep y z) yz)
          (letters.foldl (precedenceStep x z) xz)
  | [], _, _, _, invariant => invariant
  | letter :: rest, xy, yz, xz, invariant => by
      simp only [List.foldl_cons]
      exact precedenceTransitivityInvariant_fold x y z
        differentXY differentYZ differentXZ rest
        (precedenceStep x y xy letter)
        (precedenceStep y z yz letter)
        (precedenceStep x z xz letter)
        (precedenceTransitivityInvariant_step
          differentXY differentYZ differentXZ invariant)

/-- Complete precedence on one list is transitive.  Distinctness of the
outer pair is the only extra premise; the other two inequalities are already
part of the two complete-precedence hypotheses. -/
theorem completePrecedenceList_trans
    {letters : List Nat} {x y z : Nat}
    (differentXZ : x ≠ z)
    (xy : S5_841.CompletePrecedenceList letters x y)
    (yz : S5_841.CompletePrecedenceList letters y z) :
    S5_841.CompletePrecedenceList letters x z := by
  refine ⟨differentXZ, ?_⟩
  have invariant :
      PrecedenceTransitivityInvariant
        (S5_841.precedenceScanList letters x y)
        (S5_841.precedenceScanList letters y z)
        (S5_841.precedenceScanList letters x z) := by
    simpa only [precedenceScanList_eq_fold] using
      precedenceTransitivityInvariant_fold x y z
        xy.1 yz.1 differentXZ letters .neither .neither .neither (by
          simp [PrecedenceTransitivityInvariant, firstSeen, secondSeen])
  rw [xy.2, yz.2] at invariant
  generalize stateEquality :
      S5_841.precedenceScanList letters x z = stateXZ at invariant ⊢
  cases stateXZ <;>
    simp_all [PrecedenceTransitivityInvariant, firstSeen, secondSeen]

/-! ## Pair-projection multiplicities -/

/-- Binary zero records exactly the occurrences of the first selected
letter.  This remains true when the displayed variables coincide because
`pairProjection` tests the first variable first. -/
theorem pairProjection_count_zero
    (letters : List Nat) (x y : Nat) :
    (Semantics.pairProjection letters x y).count 0 = letters.count x := by
  induction letters with
  | nil => rfl
  | cons letter rest induction =>
      simp only [Semantics.pairProjection] at induction ⊢
      by_cases isX : letter = x
      · subst letter
        simp [Semantics.pairProjection, induction]
      · by_cases isY : letter = y
        · subst letter
          simp [Semantics.pairProjection, isX, induction]
        · simp [Semantics.pairProjection, isX, isY, induction]

/-- For distinct selected letters, binary one records exactly the
occurrences of the second selected letter. -/
theorem pairProjection_count_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y) :
    (Semantics.pairProjection letters x y).count 1 = letters.count y := by
  induction letters with
  | nil => rfl
  | cons letter rest induction =>
      simp only [Semantics.pairProjection] at induction ⊢
      by_cases isX : letter = x
      · subst letter
        simp [Semantics.pairProjection, different, induction]
      · by_cases isY : letter = y
        · subst letter
          simp [Semantics.pairProjection, isX, induction]
        · simp [Semantics.pairProjection, isX, isY, induction]

/-! ## Nonexceptional semantic transfer -/

private theorem binaryExceptionalPair_count_one_eq_three
    {left right : List (Fin 2)}
    (exceptional : Semantics.BinaryExceptionalPair left right) :
    left.count 1 = 3 ∧ right.count 1 = 3 := by
  unfold Semantics.BinaryExceptionalPair Semantics.binaryPairMatches at exceptional
  rcases exceptional with firstFamily | secondFamily
  · rcases firstFamily with direct | reversed
    · rcases direct with ⟨rfl, rfl⟩
      decide
    · rcases reversed with ⟨rfl, rfl⟩
      decide
  · rcases secondFamily with direct | reversed
    · rcases direct with ⟨rfl, rfl⟩
      decide
    · rcases reversed with ⟨rfl, rfl⟩
      decide

private theorem binaryExceptionalPair_impossible_of_second_count_le_two
    {left right : List Nat} {x z : Nat}
    (different : x ≠ z)
    (small : left.count z ≤ 2 ∨ right.count z ≤ 2) :
    ¬ Semantics.BinaryExceptionalPair
      (Semantics.pairProjection left x z)
      (Semantics.pairProjection right x z) := by
  intro exceptional
  have projectedCounts :=
    binaryExceptionalPair_count_one_eq_three exceptional
  rcases small with leftSmall | rightSmall
  · have countBridge := pairProjection_count_one left different
    omega
  · have countBridge := pairProjection_count_one right different
    omega

/-- For a valid identity between projection-ready sides, complete precedence
of `x` over `z` transfers whenever `z` has multiplicity at most two on at
least one side.  Both finite exceptional families have second multiplicity
three, so this theorem invokes the classifier without circularly assuming
the target complete-precedence equivalence. -/
theorem validCP_iff_of_second_count_le_two
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup)
    (leftReady :
      Semantics.CanonicalProjectionReady identity.lhs.toList)
    (rightReady :
      Semantics.CanonicalProjectionReady identity.rhs.toList)
    {x z : Nat}
    (different : x ≠ z)
    (small :
      identity.lhs.toList.count z ≤ 2 ∨
        identity.rhs.toList.count z ≤ 2) :
    S5_841.CompletePrecedenceList identity.lhs.toList x z ↔
      S5_841.CompletePrecedenceList identity.rhs.toList x z := by
  have termEquivalent :=
    Semantics.valid_pairProjectionTermEquivalent identity valid x z
  have classified :=
    Semantics.binaryTermClassifier
      (leftReady x z different)
      (rightReady x z different)
      termEquivalent
  rcases classified with preserved | exceptional
  · exact
      (Semantics.completePrecedenceList_iff_binaryProjection
        (letters := identity.lhs.toList) different).trans <|
        preserved.trans <|
          (Semantics.completePrecedenceList_iff_binaryProjection
            (letters := identity.rhs.toList) different).symm
  · exact False.elim <|
      (binaryExceptionalPair_impossible_of_second_count_le_two
        different small) exceptional

end SemanticTransfer

end SemigroupBasis.CoRoots.Order6LeeLiProposition8A
