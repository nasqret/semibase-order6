import SemigroupBasis.CoRoots.Order6L3Root3.GeneratedFresh60
import SemigroupBasis.CoRoots.Order6L3Root3.GeneratedSecond60
import SemigroupBasis.CoRoots.Order6GenericCASShortTwo
import SemigroupBasis.Subdirect

/-!
# Derivation bridge and complete intersection basis for `S3_4 × S4_60`

The complete `S4_60` derivation is transported one constructor at a time.
Every bare quadratic is protected by inserting its initial letter; all
endpoints in the long stratum are unchanged.  The short-factor classifier
again leaves only a concrete noncommutative quadratic separator.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6L3Root3

open SemigroupBasis
open SemigroupBasis.Examples

private def word60 (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-! ## Descriptor uniqueness and derivation transport -/

/-- The oracle-validated structural descriptor determines one rendered
canonical representative. -/
theorem descriptorInjectivity60
    {left right : Word Nat}
    (same : jointSignature60 left = jointSignature60 right) :
    canonicalize60 left = canonicalize60 right :=
  canonicalize60_eq_of_signature_eq same

/-- Lift every constructor of a complete `S4_60` derivation through an
arbitrary nonempty substitution and optional nonempty contexts. -/
theorem lift60Derivation
    {left right : Word Nat}
    (derivation :
      Derives edmundsFourSixtyBasis left right)
    (pre suf : Option (Word Nat))
    (substitution : Nat → Word Nat) :
    Derives basis60
      (protect60
        (surround pre (left.bind substitution) suf))
      (protect60
        (surround pre (right.bind substitution) suf)) := by
  induction derivation generalizing pre suf substitution with
  | fromBasis member =>
      simp only [edmundsFourSixtyBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · simpa [edmundsFourSixtyInitialGatherLaw,
          edmundsFourSixtyXYXZ, edmundsFourSixtyXXYZ,
          Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          lift60ContextInitialGather pre suf
            (substitution 0) (substitution 1) (substitution 2)
      · simpa [edmundsFourSixtyFinalGatherLaw,
          edmundsFourSixtyXYZY, edmundsFourSixtyXZYY,
          Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          lift60ContextFinalGather pre suf
            (substitution 0) (substitution 1) (substitution 2)
      · simpa [edmundsFourSixtyLeftContractionLaw,
          edmundsFourSixtyXXY, edmundsFourSixtyXY,
          Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          lift60ContextLeftContraction pre suf
            (substitution 0) (substitution 1)
      · simpa [edmundsFourSixtyFinalSwitchLaw,
          edmundsFourSixtyXYZZ, edmundsFourSixtyXZYY,
          Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          lift60ContextFinalSwitch pre suf
            (substitution 0) (substitution 1) (substitution 2)
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

/-- Long endpoints of an `S4_60` derivation pass unchanged through the
protected intersection bridge. -/
theorem derivationBridge60
    {left right : Word Nat}
    (derivation :
      Derives edmundsFourSixtyBasis left right)
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length) :
    Derives basis60 left right := by
  have lifted :=
    lift60Derivation derivation none none Word.singleton
  have leftProtected := protect60_of_long left leftLong
  have rightProtected := protect60_of_long right rightLong
  simpa [surround, bind_singleton, leftProtected, rightProtected] using lifted

/-- Explicit derivation-to-canonical interface: once the complete factor
normalizer supplies a derivation to the structural canonical word, the
intersection bridge transports it without changing long endpoints. -/
theorem derivationToCanonicalBridge60
    (value : Word Nat)
    (factorDerivation :
      Derives edmundsFourSixtyBasis
        value (canonicalize60 value))
    (valueLong : 3 ≤ value.toList.length)
    (canonicalLong :
      3 ≤ (canonicalize60 value).toList.length) :
    Derives basis60 value (canonicalize60 value) :=
  derivationBridge60 factorDerivation valueLong canonicalLong

/-! ## The quadratic separator -/

private def orderedPairSeparator60
    (first second : Nat) : Nat → Fin 4 :=
  fun tested =>
    if tested = first then 1 else
      if tested = second then 2 else 0

private theorem swappedQuadraticImpossible60
    {first second : Nat} (different : first ≠ second)
    (valid :
      (Identity.mk (word60 first [second])
        (word60 second [first])).SatisfiedBy
        SemigroupBasis.Generated.S4_60.table.semigroup) :
    False := by
  have evaluated := valid (orderedPairSeparator60 first second)
  change
    edmundsFourSixtyMul
        (orderedPairSeparator60 first second first)
        (orderedPairSeparator60 first second second) =
      edmundsFourSixtyMul
        (orderedPairSeparator60 first second second)
        (orderedPairSeparator60 first second first) at evaluated
  have impossible : (0 : Fin 4) = 1 := by
    simpa [orderedPairSeparator60, different, different.symm,
      edmundsFourSixtyMul] using evaluated
  exact (by decide : (0 : Fin 4) ≠ 1) impossible

private theorem quadraticWordsEqual60
    (first second third fourth : Nat)
    (permutation : [first, second].Perm [third, fourth])
    (valid :
      (Identity.mk (word60 first [second])
        (word60 third [fourth])).SatisfiedBy
        SemigroupBasis.Generated.S4_60.table.semigroup) :
    word60 first [second] = word60 third [fourth] := by
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
          (swappedQuadraticImpossible60 same valid)
    · subst third
      subst fourth
      by_cases same : first = second
      · subst second
        rfl
      · have missing := (support first).mp (Or.inl rfl)
        have forced : second = first := missing.elim id id
        exact False.elim (same forced.symm)

private theorem quadraticIdentityLiteral60
    (identity : Identity Nat)
    (leftTwo : identity.lhs.toList.length = 2)
    (rightTwo : identity.rhs.toList.length = 2)
    (permutation :
      identity.lhs.toList.Perm identity.rhs.toList)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_60.table.semigroup) :
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
                      exact quadraticWordsEqual60
                        leftFirst leftSecond
                        rightFirst rightSecond
                        (by
                          simpa [word60, Word.toList] using
                            permutation)
                        (by simpa [word60] using valid)

/-! ## Unrestricted completeness -/

theorem derivesOfFactorValid60
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_4.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_60.table.semigroup) :
    Derives basis60 identity.lhs identity.rhs := by
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
      quadraticIdentityLiteral60
        identity leftTwo rightTwo permutation s4Valid
    rw [literal]
    exact Derives.refl _
  · have factorDerivation :=
      SemigroupBasis.Generated.S4_60.representative_basis.2
        identity s4Valid
    exact derivationBridge60
      factorDerivation long.1 long.2

/-- The seven msg-0619 laws are the exact unrestricted identity basis of
`S3_4 × S4_60`. -/
def intersectionBasis60 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_4.table.semigroup
      SemigroupBasis.Generated.S4_60.table.semigroup
      basis60 where
  leftModels := basis60_s3_4_models
  rightModels := basis60_s4_60_models
  complete := derivesOfFactorValid60

end SemigroupBasis.CoRoots.Order6L3Root3
