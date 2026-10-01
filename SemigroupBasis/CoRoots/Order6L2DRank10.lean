import SemigroupBasis.CoRoots.Order6GenericCASShortTwo
import SemigroupBasis.CoRoots.Order6L3Root3.Common
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma
import SemigroupBasis.Generated.S3_4
import SemigroupBasis.Generated.S4_64
import SemigroupBasis.Subdirect

/-!
# Unrestricted L2D rank-10 root: `S3_4 × S4_64`

The exact six-law system is the rank-10 design packet with SHA-256
`799d6f5645f1ae36b4d5bd499508e51dadf1e4283a5810270c32da815caa87d7`.
It is also the six-law prefix of the kernel-verified L3 `S4_60` pilot.  The
same quadratic protection is used here, but only the two complete `S4_64`
factor laws are transported.  No bounded closure statement enters the
unrestricted completeness proof.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6L2DRank10

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6L3Root3

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma.Sigma_799d6f5645f1ae36.basis

def displayedBasisSHA256 : String :=
  SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma.Sigma_799d6f5645f1ae36.sha256

theorem basis_is_l3_pilot_prefix :
    basis = SemigroupBasis.CoRoots.Order6L3Root3.basis60.take 6 := by
  decide

private def word (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-! ## Exact-system block laws -/

theorem derivesRightCollapse (block suffix : Word Nat) :
    Derives basis
      (((block ++ block) ++ block) ++ suffix)
      ((block ++ block) ++ suffix) := by
  have base :
      Derives basis (word 0 [0, 0, 1]) (word 0 [0, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 0, 1]) (word 0 [0, 1])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords block suffix suffix)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesTerminalCollapse (block middle : Word Nat) :
    Derives basis
      (((block ++ block) ++ middle) ++ block)
      ((block ++ middle) ++ block) := by
  have base :
      Derives basis (word 0 [0, 1, 0]) (word 0 [1, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 1, 0]) (word 0 [1, 0])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords block middle middle)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesOpenContraction
    (block middle suffix : Word Nat) :
    Derives basis
      (((block ++ block) ++ middle) ++ suffix)
      ((block ++ middle) ++ suffix) := by
  have base :
      Derives basis (word 0 [0, 1, 2]) (word 0 [1, 2]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 1, 2]) (word 0 [1, 2])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords block middle suffix)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesFinalDuplicateSwitch
    (first second : Word Nat) :
    Derives basis
      ((first ++ second) ++ first)
      ((first ++ second) ++ second) := by
  have base :
      Derives basis (word 0 [1, 0]) (word 0 [1, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [1, 0]) (word 0 [1, 1])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords first second second)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesAnchoredContraction
    (first middle suffix : Word Nat) :
    Derives basis
      (((first ++ middle) ++ first) ++ suffix)
      ((first ++ middle) ++ suffix) := by
  have base :
      Derives basis (word 0 [1, 0, 2]) (word 0 [1, 2]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [1, 0, 2]) (word 0 [1, 2])) (by decide)
  have substituted :=
    Derives.subst base
      (instantiateThreeWords first middle suffix)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-! ## Protected transport of the complete `S4_64` basis -/

/-- A bare quadratic word is represented by duplicating its initial letter.
Long words are unchanged. -/
def protect (value : Word Nat) : Word Nat :=
  match value.tail with
  | [last] => Word.mk value.head [value.head, last]
  | _ => value

theorem protect_of_long
    (value : Word Nat) (long : 3 ≤ value.toList.length) :
    protect value = value := by
  cases value with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third extra => rfl

theorem liftContextLeftContraction
    (pre suf : Option (Word Nat))
    (block suffix : Word Nat) :
    Derives basis
      (protect
        (surround pre ((block ++ block) ++ suffix) suf))
      (protect
        (surround pre (block ++ suffix) suf)) := by
  cases suf with
  | some right =>
      have sourceLong :
          3 ≤
            (surround pre ((block ++ block) ++ suffix)
              (some right)).toList.length :=
        surroundLong pre (some right) _
          (threeBlocksLong block block suffix)
      have targetCoreLong :
          3 ≤ ((block ++ suffix) ++ right).toList.length :=
        threeBlocksLong block suffix right
      have targetLong :
          3 ≤
            (surround pre (block ++ suffix)
              (some right)).toList.length := by
        have contextual :=
          surroundLong pre none
            ((block ++ suffix) ++ right) targetCoreLong
        have targetEq :
            surround pre ((block ++ suffix) ++ right) none =
              surround pre (block ++ suffix) (some right) := by
          simpa [addSuffix] using
            surround_append pre none (block ++ suffix) right
        rw [← targetEq]
        exact contextual
      rw [protect_of_long _ sourceLong,
        protect_of_long _ targetLong]
      have contextual :=
        surroundDerives pre none
          (derivesOpenContraction block suffix right)
      have sourceEq :
          surround pre
              (((block ++ block) ++ suffix) ++ right) none =
            surround pre ((block ++ block) ++ suffix)
              (some right) := by
        simpa [addSuffix] using
          surround_append pre none
            ((block ++ block) ++ suffix) right
      have targetEq :
          surround pre ((block ++ suffix) ++ right) none =
            surround pre (block ++ suffix) (some right) := by
        simpa [addSuffix] using
          surround_append pre none (block ++ suffix) right
      rw [← sourceEq, ← targetEq]
      exact contextual
  | none =>
      cases pre with
      | some left =>
          have leftPositive := wordLengthPositive left
          have blockPositive := wordLengthPositive block
          have suffixPositive := wordLengthPositive suffix
          have sourceLong :
              3 ≤
                (surround (some left)
                  ((block ++ block) ++ suffix) none).toList.length := by
            simp [surround, Word.toList_append]
            omega
          have targetLong :
              3 ≤
                (surround (some left)
                  (block ++ suffix) none).toList.length := by
            simp [surround, Word.toList_append]
            omega
          rw [protect_of_long _ sourceLong,
            protect_of_long _ targetLong]
          have expose :=
            Derives.appendRight
              (Derives.symm
                (derivesFinalDuplicateSwitch left block))
              suffix
          have contract :=
            derivesAnchoredContraction left block suffix
          exact by
            simpa [surround, Word.append_assoc] using
              expose.trans contract
      | none =>
          simp only [surround]
          cases block with
          | mk head tail =>
              cases tail with
              | nil =>
                  cases suffix with
                  | mk final suffixTail =>
                      cases suffixTail with
                      | nil =>
                          simpa [protect, word, Word.append] using
                            (Derives.refl
                              (word head [head, final]) :
                              Derives basis
                                (word head [head, final])
                                (word head [head, final]))
                      | cons second rest =>
                          let firstSuffix := Word.singleton final
                          let remaining := Word.mk second rest
                          have sourceLong :
                              3 ≤
                                (((Word.mk head [] ++
                                    Word.mk head []) ++
                                  Word.mk final (second :: rest))).toList.length := by
                            simp [Word.toList_append, Word.toList]
                          have targetLong :
                              3 ≤
                                ((Word.mk head [] ++
                                  Word.mk final (second :: rest))).toList.length := by
                            simp [Word.toList_append, Word.toList]
                          rw [protect_of_long _ sourceLong,
                            protect_of_long _ targetLong]
                          have contraction :=
                            derivesOpenContraction
                              (Word.mk head [])
                              firstSuffix remaining
                          simpa [firstSuffix, remaining,
                            Word.singleton, Word.append,
                            Word.append_assoc] using contraction
              | cons second rest =>
                  let first := Word.singleton head
                  let remaining := Word.mk second rest
                  have sourceLong :
                      3 ≤
                        (((Word.mk head (second :: rest) ++
                            Word.mk head (second :: rest)) ++
                          suffix).toList.length) :=
                    threeBlocksLong
                      (Word.mk head (second :: rest))
                      (Word.mk head (second :: rest)) suffix
                  have targetLong :
                      3 ≤
                        ((Word.mk head (second :: rest) ++
                          suffix).toList.length) :=
                    threeBlocksLong first remaining suffix
                  rw [protect_of_long _ sourceLong,
                    protect_of_long _ targetLong]
                  have firstStep :=
                    Derives.prepend first
                      (derivesAnchoredContraction
                        remaining first suffix)
                  have secondStep :=
                    derivesAnchoredContraction
                      first remaining suffix
                  exact by
                    simpa [first, remaining, Word.singleton,
                      Word.append, Word.append_assoc] using
                      firstStep.trans secondStep

theorem liftContextEndpoint
    (pre suf : Option (Word Nat))
    (first second : Word Nat) :
    Derives basis
      (protect
        (surround pre ((first ++ second) ++ second) suf))
      (protect
        (surround pre ((first ++ second) ++ first) suf)) := by
  rw [protect_of_long _
      (surroundLong pre suf _
        (threeBlocksLong first second second)),
    protect_of_long _
      (surroundLong pre suf _
        (threeBlocksLong first second first))]
  exact surroundDerives pre suf
    (Derives.symm (derivesFinalDuplicateSwitch first second))

/-- Transport every constructor of a complete `S4_64` derivation while
protecting only the forbidden quadratic stratum. -/
theorem liftS4_64Derivation
    {left right : Word Nat}
    (derivation :
      Derives edmundsFourSixtyFourBasis left right)
    (pre suf : Option (Word Nat))
    (substitution : Nat → Word Nat) :
    Derives basis
      (protect
        (surround pre (left.bind substitution) suf))
      (protect
        (surround pre (right.bind substitution) suf)) := by
  induction derivation generalizing pre suf substitution with
  | fromBasis member =>
      simp only [edmundsFourSixtyFourBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [edmundsFourSixtyFourLeftContractionLaw,
          edmundsFourSixtyFourXXY, edmundsFourSixtyFourXY,
          Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          liftContextLeftContraction pre suf
            (substitution 0) (substitution 1)
      · simpa [edmundsFourSixtyFourEndpointLaw,
          edmundsFourSixtyFourXYY, edmundsFourSixtyFourXYX,
          Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          liftContextEndpoint pre suf
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

theorem derivationBridge
    {left right : Word Nat}
    (derivation :
      Derives edmundsFourSixtyFourBasis left right)
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length) :
    Derives basis left right := by
  have lifted :=
    liftS4_64Derivation derivation none none Word.singleton
  have leftProtected := protect_of_long left leftLong
  have rightProtected := protect_of_long right rightLong
  simpa [surround, bind_singleton, leftProtected,
    rightProtected] using lifted

/-! ## Short-stratum separation -/

private def orderedPairSeparator
    (first second : Nat) : Nat → Fin 4 :=
  fun tested =>
    if tested = first then 1 else
      if tested = second then 2 else 0

private theorem swappedQuadraticImpossible
    {first second : Nat} (different : first ≠ second)
    (valid :
      (Identity.mk (word first [second])
        (word second [first])).SatisfiedBy
        SemigroupBasis.Generated.S4_64.table.semigroup) :
    False := by
  have evaluated := valid (orderedPairSeparator first second)
  change
    edmundsFourSixtyFourMul
        (orderedPairSeparator first second first)
        (orderedPairSeparator first second second) =
      edmundsFourSixtyFourMul
        (orderedPairSeparator first second second)
        (orderedPairSeparator first second first) at evaluated
  have impossible : (0 : Fin 4) = 1 := by
    simpa [orderedPairSeparator, different, different.symm,
      edmundsFourSixtyFourMul] using evaluated
  exact (by decide : (0 : Fin 4) ≠ 1) impossible

private theorem quadraticWordsEqual
    (first second third fourth : Nat)
    (permutation : [first, second].Perm [third, fourth])
    (valid :
      (Identity.mk (word first [second])
        (word third [fourth])).SatisfiedBy
        SemigroupBasis.Generated.S4_64.table.semigroup) :
    word first [second] = word third [fourth] := by
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
          (swappedQuadraticImpossible same valid)
    · subst third
      subst fourth
      by_cases same : first = second
      · subst second
        rfl
      · have missing := (support first).mp (Or.inl rfl)
        have forced : second = first := missing.elim id id
        exact False.elim (same forced.symm)

private theorem quadraticIdentityLiteral
    (identity : Identity Nat)
    (leftTwo : identity.lhs.toList.length = 2)
    (rightTwo : identity.rhs.toList.length = 2)
    (permutation :
      identity.lhs.toList.Perm identity.rhs.toList)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_64.table.semigroup) :
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
                      exact quadraticWordsEqual
                        leftFirst leftSecond
                        rightFirst rightSecond
                        (by
                          simpa [word, Word.toList] using
                            permutation)
                        (by simpa [word] using valid)

/-! ## Unrestricted factor intersection -/

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem s3_4_models :
    Models SemigroupBasis.Generated.S3_4.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_4.table basis toFinThree (by decide)

theorem s4_64_models :
    Models SemigroupBasis.Generated.S4_64.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_64.table basis toFinThree (by decide)

theorem derivesOfFactorValid
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_4.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_64.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
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
      quadraticIdentityLiteral
        identity leftTwo rightTwo permutation s4Valid
    rw [literal]
    exact Derives.refl _
  · have factorDerivation :=
      SemigroupBasis.Generated.S4_64.representative_basis.2
        identity s4Valid
    exact derivationBridge
      factorDerivation long.1 long.2

/-- The six exact rank-10 laws form the unrestricted identity basis of
`S3_4 × S4_64`. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_4.table.semigroup
      SemigroupBasis.Generated.S4_64.table.semigroup
      basis where
  leftModels := s3_4_models
  rightModels := s4_64_models
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6L2DRank10
