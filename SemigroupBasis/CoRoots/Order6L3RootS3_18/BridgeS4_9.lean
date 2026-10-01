import SemigroupBasis.CoRoots.Order6L3RootS3_18.Common
import SemigroupBasis.Subdirect

/-!
# Complete guarded bridge for `S3_18 × S4_9`

Every cyclic-three derivation is interpreted before a frozen trailing cube.
Optional contexts are explicit so `prepend`, `appendRight`, and `subst` are
transported constructor by constructor.  The complete `S4_9` basis proves
that a valid endpoint pair is either literal or long.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6L3RootS3_18

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6L3Root3

def suffixWithGuard9
    (middle : Option (Word Nat)) (guard : Word Nat) : Word Nat :=
  match middle with
  | none => cube guard
  | some value => value ++ cube guard

def guarded9
    (pre middle : Option (Word Nat))
    (core guard : Word Nat) : Word Nat :=
  surround pre core (some (suffixWithGuard9 middle guard))

theorem guarded9_prepend
    (pre middle : Option (Word Nat))
    (left core guard : Word Nat) :
    guarded9 pre middle (left ++ core) guard =
      guarded9 (addPrefix pre left) middle core guard := by
  exact surround_prepend pre (some (suffixWithGuard9 middle guard))
    left core

theorem guarded9_append
    (pre middle : Option (Word Nat))
    (core right guard : Word Nat) :
    guarded9 pre middle (core ++ right) guard =
      guarded9 pre (addSuffix right middle) core guard := by
  cases pre <;> cases middle <;>
    simp [guarded9, suffixWithGuard9, surround, addSuffix,
      Word.append_assoc]

theorem surroundEmbeddedSuffix9
    (pre : Option (Word Nat)) (suffix : Word Nat)
    {left right : Word Nat}
    (derivation :
      Derives basisS4_9 (left ++ suffix) (right ++ suffix)) :
    Derives basisS4_9
      (surround pre left (some suffix))
      (surround pre right (some suffix)) := by
  cases pre with
  | none =>
      simpa [surround] using derivation
  | some prefixWord =>
      have contextual := Derives.prepend prefixWord derivation
      simpa [surround, Word.append_assoc] using contextual

theorem guarded9_middle_to_core
    (pre : Option (Word Nat))
    (middle core guard : Word Nat) :
    guarded9 pre (some middle) core guard =
      guarded9 pre none (core ++ middle) guard := by
  symm
  simpa [guarded9, suffixWithGuard9, addSuffix] using
    surround_append pre (some (cube guard)) core middle

theorem lift9Commutativity
    (pre middle : Option (Word Nat))
    (guard left right : Word Nat) :
    Derives basisS4_9
      (guarded9 pre middle (left ++ right) guard)
      (guarded9 pre middle (right ++ left) guard) := by
  have direct :=
    derives9Law04 (suffixWithGuard9 middle guard) right left
  have embedded :
      Derives basisS4_9
        ((left ++ right) ++ suffixWithGuard9 middle guard)
        ((right ++ left) ++ suffixWithGuard9 middle guard) := by
    simpa only [Word.append_assoc] using direct
  simpa only [guarded9] using
    surroundEmbeddedSuffix9 pre
      (suffixWithGuard9 middle guard) embedded

theorem lift9CancelCube
    (pre middle : Option (Word Nat))
    (guard repeated remainder : Word Nat) :
    Derives basisS4_9
      (guarded9 pre middle (cube repeated ++ remainder) guard)
      (guarded9 pre middle remainder guard) := by
  cases middle with
  | none =>
      have firstCore :=
        derives9Law04 (cube guard) remainder (cube repeated)
      have firstEmbedded :
          Derives basisS4_9
            ((cube repeated ++ remainder) ++ cube guard)
            ((remainder ++ cube repeated) ++ cube guard) := by
        simpa only [Word.append_assoc] using firstCore
      have first :
          Derives basisS4_9
            (guarded9 pre none (cube repeated ++ remainder) guard)
            (guarded9 pre none (remainder ++ cube repeated) guard) := by
        simpa only [guarded9, suffixWithGuard9] using
          surroundEmbeddedSuffix9 pre (cube guard) firstEmbedded
      have secondCore := derives9Law00 repeated guard
      have secondEmbedded :
          Derives basisS4_9
            (cube repeated ++ cube guard)
            (cube guard ++ cube guard) := by
        simpa [cube, Word.append_assoc] using
          Derives.appendRight secondCore (cube guard)
      have secondPrefixed := Derives.prepend remainder secondEmbedded
      have secondFull :
          Derives basisS4_9
            ((remainder ++ cube repeated) ++ cube guard)
            ((remainder ++ cube guard) ++ cube guard) := by
        simpa only [Word.append_assoc] using secondPrefixed
      have second :
          Derives basisS4_9
            (guarded9 pre none (remainder ++ cube repeated) guard)
            (guarded9 pre none (remainder ++ cube guard) guard) := by
        simpa only [guarded9, suffixWithGuard9] using
          surroundEmbeddedSuffix9 pre (cube guard) secondFull
      have thirdCore :=
        derives9Law01 guard (remainder ++ guard) guard guard
      have thirdEmbedded :
          Derives basisS4_9
            ((remainder ++ cube guard) ++ cube guard)
            (remainder ++ cube guard) := by
        simpa [cube, Word.append_assoc] using thirdCore
      have third :
          Derives basisS4_9
            (guarded9 pre none (remainder ++ cube guard) guard)
            (guarded9 pre none remainder guard) := by
        simpa only [guarded9, suffixWithGuard9] using
          surroundEmbeddedSuffix9 pre (cube guard) thirdEmbedded
      exact Derives.trans first (Derives.trans second third)
  | some middleWord =>
      have firstCore :=
        derives9Law04 (middleWord ++ cube guard)
          remainder (cube repeated)
      have firstEmbedded :
          Derives basisS4_9
            ((cube repeated ++ remainder) ++
              (middleWord ++ cube guard))
            ((remainder ++ cube repeated) ++
              (middleWord ++ cube guard)) := by
        simpa only [Word.append_assoc] using firstCore
      have first :
          Derives basisS4_9
            (guarded9 pre (some middleWord)
              (cube repeated ++ remainder) guard)
            (guarded9 pre (some middleWord)
              (remainder ++ cube repeated) guard) := by
        simpa only [guarded9, suffixWithGuard9] using
          surroundEmbeddedSuffix9 pre
            (middleWord ++ cube guard) firstEmbedded
      have swapCore :=
        derives9Law05 middleWord (cube repeated) remainder
      have swappedGuard := Derives.appendRight swapCore (cube guard)
      have swappedEmbedded :
          Derives basisS4_9
            (((remainder ++ cube repeated) ++ middleWord) ++ cube guard)
            (((remainder ++ middleWord) ++ cube repeated) ++ cube guard) := by
        simpa only [Word.append_assoc] using swappedGuard
      have swappedContext :=
        surroundEmbeddedSuffix9 pre (cube guard) swappedEmbedded
      have swapped :
          Derives basisS4_9
            (guarded9 pre (some middleWord)
              (remainder ++ cube repeated) guard)
            (guarded9 pre none
              ((remainder ++ middleWord) ++ cube repeated) guard) := by
        rw [guarded9_middle_to_core]
        simpa only [guarded9, suffixWithGuard9] using swappedContext
      have secondCore := derives9Law00 repeated guard
      have secondEmbedded :
          Derives basisS4_9
            (cube repeated ++ cube guard)
            (cube guard ++ cube guard) := by
        simpa [cube, Word.append_assoc] using
          Derives.appendRight secondCore (cube guard)
      have secondPrefixed :=
        Derives.prepend (remainder ++ middleWord) secondEmbedded
      have secondFull :
          Derives basisS4_9
            (((remainder ++ middleWord) ++ cube repeated) ++ cube guard)
            (((remainder ++ middleWord) ++ cube guard) ++ cube guard) := by
        simpa only [Word.append_assoc] using secondPrefixed
      have second :
          Derives basisS4_9
            (guarded9 pre none
              ((remainder ++ middleWord) ++ cube repeated) guard)
            (guarded9 pre none
              ((remainder ++ middleWord) ++ cube guard) guard) := by
        simpa only [guarded9, suffixWithGuard9] using
          surroundEmbeddedSuffix9 pre (cube guard) secondFull
      have thirdCore :=
        derives9Law01 guard
          ((remainder ++ middleWord) ++ guard) guard guard
      have thirdEmbedded :
          Derives basisS4_9
            ((((remainder ++ middleWord) ++ cube guard) ++ cube guard))
            ((remainder ++ middleWord) ++ cube guard) := by
        simpa [cube, Word.append_assoc] using thirdCore
      have thirdContext :=
        surroundEmbeddedSuffix9 pre (cube guard) thirdEmbedded
      have third :
          Derives basisS4_9
            (guarded9 pre none
              ((remainder ++ middleWord) ++ cube guard) guard)
            (guarded9 pre (some middleWord) remainder guard) := by
        rw [guarded9_middle_to_core]
        simpa only [guarded9, suffixWithGuard9] using thirdContext
      exact Derives.trans first <|
        Derives.trans swapped <|
          Derives.trans second third

theorem liftCyclicDerivation9
    {left right : Word Nat}
    (derivation : Derives cyclicThreeBasis left right)
    (pre middle : Option (Word Nat))
    (guard : Word Nat)
    (substitution : Nat → Word Nat) :
    Derives basisS4_9
      (guarded9 pre middle (left.bind substitution) guard)
      (guarded9 pre middle (right.bind substitution) guard) := by
  induction derivation generalizing pre middle substitution with
  | fromBasis member =>
      simp only [cyclicThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [cyclicThreeCommutativityLaw, cyclicThreeXY,
          cyclicThreeYX, Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          lift9Commutativity pre middle guard
            (substitution 0) (substitution 1)
      · simpa [cyclicThreeCancellationLaw, cyclicThreeXXXY,
          cyclicThreeY, cube, Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          lift9CancelCube pre middle guard
            (substitution 0) (substitution 1)
  | refl => exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm (induction pre middle substitution)
  | trans _ _ first second =>
      exact Derives.trans
        (first pre middle substitution)
        (second pre middle substitution)
  | prepend stem _ induction =>
      simpa only [bind_append, guarded9_prepend] using
        induction (addPrefix pre (stem.bind substitution))
          middle substitution
  | appendRight _ suffix induction =>
      simpa only [bind_append, guarded9_append] using
        induction pre (addSuffix (suffix.bind substitution) middle)
          substitution
  | subst _ inner induction =>
      simpa only [bind_bind] using
        induction pre middle
          (fun letter => (inner letter).bind substitution)

theorem derivesOfFactorValidS4_9
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_18.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_9.table.semigroup) :
    Derives basisS4_9 identity.lhs identity.rhs := by
  have shortDerivation :=
    SemigroupBasis.Generated.S4_9.representative_basis.2
      identity s4Valid
  rcases threeNilpotentDerivationClass shortDerivation with
    equal | ⟨leftEligible, rightEligible⟩
  · rw [equal]
    exact Derives.refl _
  · let guard := Word.singleton 0
    have cyclicDerivation :=
      SemigroupBasis.Generated.S3_18.representative_basis.2
        identity s3Valid
    have lifted :=
      liftCyclicDerivation9 cyclicDerivation none none guard
        Word.singleton
    have leftExpansion :=
      appendGuardOfEligibleS4_9 guard identity.lhs leftEligible
    have rightExpansion :=
      appendGuardOfEligibleS4_9 guard identity.rhs rightEligible
    exact Derives.trans leftExpansion <|
      Derives.trans
        (by
          simpa [guarded9, suffixWithGuard9, surround,
            bind_singleton, guard] using lifted)
        (Derives.symm rightExpansion)

def intersectionBasisS4_9 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_18.table.semigroup
      SemigroupBasis.Generated.S4_9.table.semigroup
      basisS4_9 where
  leftModels := basisS4_9_s3_18_models
  rightModels := basisS4_9_s4_9_models
  complete := derivesOfFactorValidS4_9

end SemigroupBasis.CoRoots.Order6L3RootS3_18
