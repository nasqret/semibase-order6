import SemigroupBasis.CoRoots.Order6L3RootS3_18.Common
import SemigroupBasis.Subdirect

/-!
# Complete guarded bridge for `S3_18 × S4_2`

Every cyclic-three derivation is interpreted after a frozen leading cube.
The complete common-square/three-nilpotent basis shows that valid endpoints
are either literally equal or both belong to the square-or-long bulk stratum.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6L3RootS3_18

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6L3Root3

def prefixWithGuard2
    (guard : Word Nat) (middle : Option (Word Nat)) : Word Nat :=
  match middle with
  | none => cube guard
  | some value => cube guard ++ value

def guarded2
    (middle suf : Option (Word Nat))
    (core guard : Word Nat) : Word Nat :=
  surround (some (prefixWithGuard2 guard middle)) core suf

theorem guarded2_prepend
    (middle suf : Option (Word Nat))
    (left core guard : Word Nat) :
    guarded2 middle suf (left ++ core) guard =
      guarded2 (addPrefix middle left) suf core guard := by
  cases middle <;> cases suf <;>
    simp [guarded2, prefixWithGuard2, surround, addPrefix,
      Word.append_assoc]

theorem guarded2_append
    (middle suf : Option (Word Nat))
    (core right guard : Word Nat) :
    guarded2 middle suf (core ++ right) guard =
      guarded2 middle (addSuffix right suf) core guard := by
  exact surround_append
    (some (prefixWithGuard2 guard middle)) suf core right

theorem surroundEmbeddedPrefix2
    (leading : Word Nat) (suf : Option (Word Nat))
    {left right : Word Nat}
    (derivation :
      Derives basisS4_2 (leading ++ left) (leading ++ right)) :
    Derives basisS4_2
      (surround (some leading) left suf)
      (surround (some leading) right suf) := by
  cases suf with
  | none =>
      simpa [surround] using derivation
  | some suffix =>
      have contextual := Derives.appendRight derivation suffix
      simpa [surround] using contextual

theorem guarded2_middle_to_core
    (suf : Option (Word Nat))
    (middle core guard : Word Nat) :
    guarded2 (some middle) suf core guard =
      guarded2 none suf (middle ++ core) guard := by
  symm
  simpa [guarded2, prefixWithGuard2, addPrefix] using
    surround_prepend (some (cube guard)) suf middle core

theorem lift2Commutativity
    (middle suf : Option (Word Nat))
    (guard left right : Word Nat) :
    Derives basisS4_2
      (guarded2 middle suf (left ++ right) guard)
      (guarded2 middle suf (right ++ left) guard) := by
  have direct :=
    derives2Law15 right left (prefixWithGuard2 guard middle)
  simpa only [guarded2] using
    surroundEmbeddedPrefix2
      (prefixWithGuard2 guard middle) suf direct

theorem lift2CancelCube
    (middle suf : Option (Word Nat))
    (guard repeated remainder : Word Nat) :
    Derives basisS4_2
      (guarded2 middle suf (cube repeated ++ remainder) guard)
      (guarded2 middle suf remainder guard) := by
  cases middle with
  | none =>
      have commonCore := derives2Law11 repeated guard
      have commonCube :
          Derives basisS4_2 (cube repeated) (cube guard) := by
        simpa [cube, Word.append_assoc] using commonCore
      have commonContext :=
        Derives.appendRight
          (Derives.prepend (cube guard) commonCube) remainder
      have commonFull :
          Derives basisS4_2
            (cube guard ++ (cube repeated ++ remainder))
            (cube guard ++ (cube guard ++ remainder)) := by
        simpa only [Word.append_assoc] using commonContext
      have common :
          Derives basisS4_2
            (guarded2 none suf (cube repeated ++ remainder) guard)
            (guarded2 none suf (cube guard ++ remainder) guard) := by
        simpa only [guarded2, prefixWithGuard2] using
          surroundEmbeddedPrefix2 (cube guard) suf commonFull
      have cancelCore :=
        derives2Law16 guard guard (guard ++ remainder)
      have cancelFull :
          Derives basisS4_2
            (cube guard ++ (cube guard ++ remainder))
            (cube guard ++ remainder) := by
        simpa [cube, Word.append_assoc] using cancelCore
      have cancelled :
          Derives basisS4_2
            (guarded2 none suf (cube guard ++ remainder) guard)
            (guarded2 none suf remainder guard) := by
        simpa only [guarded2, prefixWithGuard2] using
          surroundEmbeddedPrefix2 (cube guard) suf cancelFull
      exact Derives.trans common cancelled
  | some middleWord =>
      have swapCore :=
        derives2Law15 (cube repeated) middleWord (cube guard)
      have swapContext := Derives.appendRight swapCore remainder
      have swapFull :
          Derives basisS4_2
            (cube guard ++
              (middleWord ++ (cube repeated ++ remainder)))
            (cube guard ++
              (cube repeated ++ (middleWord ++ remainder))) := by
        simpa only [Word.append_assoc] using swapContext
      have swappedContext :=
        surroundEmbeddedPrefix2 (cube guard) suf swapFull
      have swapped :
          Derives basisS4_2
            (guarded2 (some middleWord) suf
              (cube repeated ++ remainder) guard)
            (guarded2 none suf
              (cube repeated ++ (middleWord ++ remainder)) guard) := by
        rw [guarded2_middle_to_core]
        simpa only [guarded2, prefixWithGuard2] using swappedContext
      have commonCore := derives2Law11 repeated guard
      have commonCube :
          Derives basisS4_2 (cube repeated) (cube guard) := by
        simpa [cube, Word.append_assoc] using commonCore
      have commonContext :=
        Derives.appendRight
          (Derives.prepend (cube guard) commonCube)
          (middleWord ++ remainder)
      have commonFull :
          Derives basisS4_2
            (cube guard ++
              (cube repeated ++ (middleWord ++ remainder)))
            (cube guard ++
              (cube guard ++ (middleWord ++ remainder))) := by
        simpa only [Word.append_assoc] using commonContext
      have common :
          Derives basisS4_2
            (guarded2 none suf
              (cube repeated ++ (middleWord ++ remainder)) guard)
            (guarded2 none suf
              (cube guard ++ (middleWord ++ remainder)) guard) := by
        simpa only [guarded2, prefixWithGuard2] using
          surroundEmbeddedPrefix2 (cube guard) suf commonFull
      have cancelCore :=
        derives2Law16 guard guard
          (guard ++ (middleWord ++ remainder))
      have cancelFull :
          Derives basisS4_2
            (cube guard ++
              (cube guard ++ (middleWord ++ remainder)))
            (cube guard ++ (middleWord ++ remainder)) := by
        simpa [cube, Word.append_assoc] using cancelCore
      have cancelledContext :=
        surroundEmbeddedPrefix2 (cube guard) suf cancelFull
      have cancelled :
          Derives basisS4_2
            (guarded2 none suf
              (cube guard ++ (middleWord ++ remainder)) guard)
            (guarded2 (some middleWord) suf remainder guard) := by
        rw [guarded2_middle_to_core]
        simpa only [guarded2, prefixWithGuard2] using cancelledContext
      exact Derives.trans swapped <|
        Derives.trans common cancelled

theorem liftCyclicDerivation2
    {left right : Word Nat}
    (derivation : Derives cyclicThreeBasis left right)
    (middle suf : Option (Word Nat))
    (guard : Word Nat)
    (substitution : Nat → Word Nat) :
    Derives basisS4_2
      (guarded2 middle suf (left.bind substitution) guard)
      (guarded2 middle suf (right.bind substitution) guard) := by
  induction derivation generalizing middle suf substitution with
  | fromBasis member =>
      simp only [cyclicThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [cyclicThreeCommutativityLaw, cyclicThreeXY,
          cyclicThreeYX, Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          lift2Commutativity middle suf guard
            (substitution 0) (substitution 1)
      · simpa [cyclicThreeCancellationLaw, cyclicThreeXXXY,
          cyclicThreeY, cube, Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          lift2CancelCube middle suf guard
            (substitution 0) (substitution 1)
  | refl => exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm (induction middle suf substitution)
  | trans _ _ first second =>
      exact Derives.trans
        (first middle suf substitution)
        (second middle suf substitution)
  | prepend stem _ induction =>
      simpa only [bind_append, guarded2_prepend] using
        induction (addPrefix middle (stem.bind substitution))
          suf substitution
  | appendRight _ suffix induction =>
      simpa only [bind_append, guarded2_append] using
        induction middle (addSuffix (suffix.bind substitution) suf)
          substitution
  | subst _ inner induction =>
      simpa only [bind_bind] using
        induction middle suf
          (fun letter => (inner letter).bind substitution)

theorem derivesOfFactorValidS4_2
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_18.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_2.table.semigroup) :
    Derives basisS4_2 identity.lhs identity.rhs := by
  have shortDerivation :=
    SemigroupBasis.Generated.S4_2.representative_basis.2
      identity s4Valid
  rcases commonSquareDerivationClass shortDerivation with
    equal | ⟨leftEligible, rightEligible⟩
  · rw [equal]
    exact Derives.refl _
  · let guard := Word.singleton 0
    have cyclicDerivation :=
      SemigroupBasis.Generated.S3_18.representative_basis.2
        identity s3Valid
    have lifted :=
      liftCyclicDerivation2 cyclicDerivation none none guard
        Word.singleton
    have leftExpansion :=
      prependGuardOfEligibleS4_2 guard identity.lhs leftEligible
    have rightExpansion :=
      prependGuardOfEligibleS4_2 guard identity.rhs rightEligible
    exact Derives.trans leftExpansion <|
      Derives.trans
        (by
          simpa [guarded2, prefixWithGuard2, surround,
            bind_singleton, guard] using lifted)
        (Derives.symm rightExpansion)

def intersectionBasisS4_2 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_18.table.semigroup
      SemigroupBasis.Generated.S4_2.table.semigroup
      basisS4_2 where
  leftModels := basisS4_2_s3_18_models
  rightModels := basisS4_2_s4_2_models
  complete := derivesOfFactorValidS4_2

end SemigroupBasis.CoRoots.Order6L3RootS3_18
