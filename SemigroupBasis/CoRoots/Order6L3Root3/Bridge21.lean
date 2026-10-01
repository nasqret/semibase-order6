import SemigroupBasis.CoRoots.Order6L3Root3.GeneratedFresh21
import SemigroupBasis.CoRoots.Order6L3Root3.GeneratedSecond21
import SemigroupBasis.CoRoots.Order6GenericCASShortTwo
import SemigroupBasis.Subdirect

/-!
# Derivation bridge and complete intersection basis for `S3_4 × S4_21`

The complete `S4_21` derivation is transported one constructor at a time.
Only a bare unary square is protected; every endpoint in the long stratum
is therefore fixed by the bridge.  The short-factor classifier reduces the
remaining completeness proof to literal, quadratic, and long cases.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6L3Root3

open SemigroupBasis
open SemigroupBasis.Examples

private def word21 (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-! ## Descriptor uniqueness and derivation transport -/

/-- The oracle-validated structural descriptor determines one rendered
canonical representative. -/
theorem descriptorInjectivity21
    {left right : Word Nat}
    (same : jointSignature21 left = jointSignature21 right) :
    canonicalize21 left = canonicalize21 right :=
  canonicalize21_eq_of_signature_eq same

/-- Lift every constructor of a complete `S4_21` derivation through an
arbitrary nonempty substitution and optional nonempty contexts. -/
theorem lift21Derivation
    {left right : Word Nat}
    (derivation :
      Derives edmundsFourTwentyOneBasis left right)
    (pre suf : Option (Word Nat))
    (substitution : Nat → Word Nat) :
    Derives basis21
      (protect21
        (surround pre (left.bind substitution) suf))
      (protect21
        (surround pre (right.bind substitution) suf)) := by
  induction derivation generalizing pre suf substitution with
  | fromBasis member =>
      simp only [edmundsFourTwentyOneBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · simpa [edmundsFourTwentyOnePrefixCommutationLaw,
          edmundsFourTwentyOneXYZ, edmundsFourTwentyOneYXZ,
          Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          lift21ContextPrefixSwap pre suf
            (substitution 0) (substitution 1) (substitution 2)
      · simpa [edmundsFourTwentyOnePowerLaw,
          edmundsFourTwentyOneXX, edmundsFourTwentyOneXXX,
          Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          lift21ContextPower pre suf (substitution 0)
      · simpa [edmundsFourTwentyOneSquareCommutationLaw,
          edmundsFourTwentyOneXXYY, edmundsFourTwentyOneYYXX,
          Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          lift21ContextSquareSwitch pre suf
            (substitution 0) (substitution 1)
  | refl => exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm (induction pre suf substitution)
  | trans _ _ first second =>
      exact Derives.trans
        (first pre suf substitution)
        (second pre suf substitution)
  | prepend stem _ induction =>
      simpa only [bind_append, surround_prepend] using
        induction
          (addPrefix pre (stem.bind substitution))
          suf substitution
  | appendRight _ ending induction =>
      simpa only [bind_append, surround_append] using
        induction pre
          (addSuffix (ending.bind substitution) suf)
          substitution
  | subst _ first induction =>
      simpa only [bind_bind] using
        induction pre suf
          (fun letter => (first letter).bind substitution)

/-- Long endpoints of an `S4_21` derivation pass unchanged through the
protected intersection bridge. -/
theorem derivationBridge21
    {left right : Word Nat}
    (derivation :
      Derives edmundsFourTwentyOneBasis left right)
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length) :
    Derives basis21 left right := by
  have lifted :=
    lift21Derivation derivation none none Word.singleton
  have leftProtected := protect21_of_long left leftLong
  have rightProtected := protect21_of_long right rightLong
  simpa [surround, bind_singleton, leftProtected, rightProtected] using lifted

/-- Explicit derivation-to-canonical interface: once the complete factor
normalizer supplies a derivation to the structural canonical word, the
intersection bridge transports it without changing long endpoints. -/
theorem derivationToCanonicalBridge21
    (value : Word Nat)
    (factorDerivation :
      Derives edmundsFourTwentyOneBasis
        value (canonicalize21 value))
    (valueLong : 3 ≤ value.toList.length)
    (canonicalLong :
      3 ≤ (canonicalize21 value).toList.length) :
    Derives basis21 value (canonicalize21 value) :=
  derivationBridge21 factorDerivation valueLong canonicalLong

/-! ## The quadratic separator -/

private def orderedPairSeparator21
    (first second : Nat) : Nat → Fin 4 :=
  fun tested =>
    if tested = first then 1 else
      if tested = second then 3 else 0

private theorem swappedQuadraticImpossible21
    {first second : Nat} (different : first ≠ second)
    (valid :
      (Identity.mk (word21 first [second])
        (word21 second [first])).SatisfiedBy
        SemigroupBasis.Generated.S4_21.table.semigroup) :
    False := by
  have evaluated := valid (orderedPairSeparator21 first second)
  change
    edmundsFourTwentyOneMul
        (orderedPairSeparator21 first second first)
        (orderedPairSeparator21 first second second) =
      edmundsFourTwentyOneMul
        (orderedPairSeparator21 first second second)
        (orderedPairSeparator21 first second first) at evaluated
  have impossible : (0 : Fin 4) = 1 := by
    simpa [orderedPairSeparator21, different, different.symm,
      edmundsFourTwentyOneMul] using evaluated
  exact (by decide : (0 : Fin 4) ≠ 1) impossible

private theorem quadraticWordsEqual21
    (first second third fourth : Nat)
    (permutation : [first, second].Perm [third, fourth])
    (valid :
      (Identity.mk (word21 first [second])
        (word21 third [fourth])).SatisfiedBy
        SemigroupBasis.Generated.S4_21.table.semigroup) :
    word21 first [second] = word21 third [fourth] := by
  have support (tested : Nat) :
      (first = tested ∨ second = tested) ↔
        (third = tested ∨ fourth = tested) := by
    have membership :
        tested ∈ [first, second] ↔
          tested ∈ [third, fourth] :=
      permutation.mem_iff
    simpa [eq_comm] using membership
  have thirdSource : third = first ∨ third = second := by
    have member := (support third).mpr (Or.inl rfl)
    exact member.imp Eq.symm Eq.symm
  have fourthSource : fourth = first ∨ fourth = second := by
    have member := (support fourth).mpr (Or.inr rfl)
    exact member.imp Eq.symm Eq.symm
  rcases thirdSource with thirdFirst | thirdSecond
  · rcases fourthSource with fourthFirst | fourthSecond
    · subst third
      subst fourth
      by_cases same : first = second
      · subst second
        rfl
      · have missing := (support second).mp (Or.inr rfl)
        have forced : first = second := missing.elim id id
        exact False.elim (same forced)
    · subst third
      subst fourth
      rfl
  · rcases fourthSource with fourthFirst | fourthSecond
    · subst third
      subst fourth
      by_cases same : first = second
      · subst second
        rfl
      · exact False.elim
          (swappedQuadraticImpossible21 same valid)
    · subst third
      subst fourth
      by_cases same : first = second
      · subst second
        rfl
      · have missing := (support first).mp (Or.inl rfl)
        have forced : second = first := missing.elim id id
        exact False.elim (same forced.symm)

private theorem quadraticIdentityLiteral21
    (identity : Identity Nat)
    (leftTwo : identity.lhs.toList.length = 2)
    (rightTwo : identity.rhs.toList.length = 2)
    (permutation :
      identity.lhs.toList.Perm identity.rhs.toList)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_21.table.semigroup) :
    identity.lhs = identity.rhs := by
  cases identity with
  | mk left right =>
      cases left with
      | mk leftFirst leftTail =>
          cases leftTail with
          | nil => simp [Word.toList] at leftTwo
          | cons leftSecond leftRest =>
              have leftRestNil : leftRest = [] := by
                simp [Word.toList] at leftTwo
                omega
              subst leftRest
              cases right with
              | mk rightFirst rightTail =>
                  cases rightTail with
                  | nil => simp [Word.toList] at rightTwo
                  | cons rightSecond rightRest =>
                      have rightRestNil : rightRest = [] := by
                        simp [Word.toList] at rightTwo
                        omega
                      subst rightRest
                      exact quadraticWordsEqual21
                        leftFirst leftSecond
                        rightFirst rightSecond
                        (by
                          simpa [word21, Word.toList] using
                            permutation)
                        (by simpa [word21] using valid)

/-! ## Unrestricted completeness -/

theorem derivesOfFactorValid21
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_4.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_21.table.semigroup) :
    Derives basis21 identity.lhs identity.rhs := by
  have shortValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.Order6GenericCASShortTwo.shortFactor := by
    change identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S3_4.table.semigroup
    rw [SemigroupBasis.CoRoots.Order6GenericCASShortTwo.shortFactorTable_eq_projectionQuadraticThree]
    rw [← SemigroupBasis.Generated.S3_4.table_eq_catalogue_model]
    exact s3Valid
  rcases
      SemigroupBasis.CoRoots.Order6GenericCASShortTwo.classifyValidIdentity
        identity shortValid with
    literal | quadratic | long
  · rw [literal]
    exact Derives.refl _
  · rcases quadratic with
      ⟨leftTwo, rightTwo, permutation⟩
    have literal :=
      quadraticIdentityLiteral21
        identity leftTwo rightTwo permutation s4Valid
    rw [literal]
    exact Derives.refl _
  · have factorDerivation :=
      SemigroupBasis.Generated.S4_21.representative_basis.2
        identity s4Valid
    exact derivationBridge21
      factorDerivation long.1 long.2

/-- The six msg-0601 laws are the exact unrestricted identity basis of
`S3_4 × S4_21`. -/
def intersectionBasis21 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_4.table.semigroup
      SemigroupBasis.Generated.S4_21.table.semigroup
      basis21 where
  leftModels := basis21_s3_4_models
  rightModels := basis21_s4_21_models
  complete := derivesOfFactorValid21

end SemigroupBasis.CoRoots.Order6L3Root3
