import SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank012
import SemigroupBasis.Generated.S4_71

/-!
# Protected long-word lift for the frozen S3_4 × S4_71 rank-012 basis

The complete lower `S4_71` calculus contains the naked square law `xx = xxx`,
which is false in `S3_4`.  The structural lift therefore replaces only a bare
unary square with its cube, leaving every word of length at least three fixed.
All three lower laws are proved under arbitrary substitutions and contexts
from the exact five-law frozen envelope.

The nontrivial derived paths are the four-step prefixed-square expansion, the
three-step composite-square expansion, and the two-step square commutation.
Every displayed-law use is an explicit `Derives.fromBasis` kernel witness.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_71

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank012.basis

private abbrev lowerBasis : List (Identity Nat) :=
  edmundsFourSeventyOneBasis

private def instantiateTwo
    (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | letter + 2 => Word.singleton (letter + 2)

/-- The frozen gather law `xyx = yxx` in arbitrary nonempty blocks. -/
theorem derivesGather (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ first)
      ((second ++ first) ++ first) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [1, 0]) (Word.mk 1 [0, 0]) :=
    Derives.fromBasis (e := Rank012.law04)
      (show Rank012.law04 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateTwo first second)
  simpa [instantiateTwo, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The frozen anchored contraction `xxyx = xyx`. -/
theorem derivesAnchoredContraction (first second : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ second) ++ first)
      ((first ++ second) ++ first) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0]) :=
    Derives.fromBasis (e := Rank012.law02)
      (show Rank012.law02 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateTwo first second)
  simpa [instantiateTwo, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The reversed frozen law `xxy -> xxxy` with a nonempty suffix. -/
theorem derivesPrefixPowerExpansion
    (first suffix : Word Nat) :
    Derives targetBasis
      ((first ++ first) ++ suffix)
      (((first ++ first) ++ first) ++ suffix) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 0, 1]) (Word.mk 0 [0, 1]) :=
    Derives.fromBasis (e := Rank012.law01)
      (show Rank012.law01 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive.symm (instantiateTwo first suffix)
  simpa [instantiateTwo, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The frozen square-step law `xxyy = xyyx`. -/
theorem derivesSquareStep (first second : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ second) ++ second)
      (((first ++ second) ++ second) ++ first) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]) :=
    Derives.fromBasis (e := Rank012.law03)
      (show Rank012.law03 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateTwo first second)
  simpa [instantiateTwo, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Four exact frozen rewrites derive `yxx -> yxxx`. -/
theorem derivesSuffixPowerExpansion
    (pre block : Word Nat) :
    Derives targetBasis
      ((pre ++ block) ++ block)
      (((pre ++ block) ++ block) ++ block) := by
  have first :
      Derives targetBasis
        ((pre ++ block) ++ block)
        ((block ++ pre) ++ block) :=
    (derivesGather block pre).symm
  have second :
      Derives targetBasis
        ((block ++ pre) ++ block)
        (((block ++ block) ++ pre) ++ block) :=
    (derivesAnchoredContraction block pre).symm
  have third :
      Derives targetBasis
        (((block ++ block) ++ pre) ++ block)
        (((block ++ pre) ++ block) ++ block) := by
    simpa [Word.append_assoc] using
      Derives.prepend block (derivesGather block pre)
  have fourth :
      Derives targetBasis
        (((block ++ pre) ++ block) ++ block)
        (((pre ++ block) ++ block) ++ block) :=
    Derives.appendRight (derivesGather block pre) block
  exact first.trans <| second.trans <| third.trans fourth

/-- Three exact frozen rewrites derive `(xy)² -> (xy)³`. -/
theorem derivesCompositePowerExpansion
    (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ (first ++ second))
      (((first ++ second) ++ (first ++ second)) ++
        (first ++ second)) := by
  have stepOne :
      Derives targetBasis
        (((first ++ second) ++ first) ++ second)
        ((((first ++ first) ++ second) ++ first) ++ second) :=
    Derives.appendRight
      (derivesAnchoredContraction first second).symm second
  have stepTwo :
      Derives targetBasis
        ((((first ++ first) ++ second) ++ first) ++ second)
        (((((first ++ first) ++ second) ++ second) ++ first) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend (first ++ first)
        (derivesAnchoredContraction second first).symm
  have stepThree :
      Derives targetBasis
        (((((first ++ first) ++ second) ++ second) ++ first) ++ second)
        (((((first ++ second) ++ first) ++ second) ++ first) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend first <|
        Derives.appendRight
          (derivesGather second first).symm (first ++ second)
  simpa [Word.append_assoc] using
    stepOne.trans (stepTwo.trans stepThree)

/-- Two exact frozen rewrites derive the complete lower square commutation. -/
theorem derivesSquareCommutation (first second : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ second) ++ second)
      (((second ++ second) ++ first) ++ first) := by
  have gathered :
      Derives targetBasis
        (((first ++ second) ++ second) ++ first)
        (((second ++ second) ++ first) ++ first) := by
    simpa [Word.append_assoc] using
      derivesGather first (second ++ second)
  exact (derivesSquareStep first second).trans gathered

private def protect (value : Word Nat) : Word Nat :=
  match value.tail with
  | [last] =>
      if value.head = last then
        value ++ Word.singleton last
      else
        value
  | _ => value

private theorem protect_of_long
    (value : Word Nat) (long : 3 ≤ value.toList.length) :
    protect value = value := by
  cases value with
  | mk first tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third extra => rfl

private def surround
    (pre : Option (Word Nat)) (core : Word Nat)
    (suffix : Option (Word Nat)) : Word Nat :=
  match pre, suffix with
  | none, none => core
  | some left, none => left ++ core
  | none, some right => core ++ right
  | some left, some right => (left ++ core) ++ right

private def addPrefix
    (pre : Option (Word Nat)) (next : Word Nat) : Option (Word Nat) :=
  match pre with
  | none => some next
  | some current => some (current ++ next)

private def addSuffix
    (next : Word Nat) (suffix : Option (Word Nat)) : Option (Word Nat) :=
  match suffix with
  | none => some next
  | some current => some (next ++ current)

private theorem surround_prepend
    (pre suffix : Option (Word Nat)) (left core : Word Nat) :
    surround pre (left ++ core) suffix =
      surround (addPrefix pre left) core suffix := by
  cases pre <;> cases suffix <;>
    simp [surround, addPrefix, Word.append_assoc]

private theorem surround_append
    (pre suffix : Option (Word Nat)) (core right : Word Nat) :
    surround pre (core ++ right) suffix =
      surround pre core (addSuffix right suffix) := by
  cases pre <;> cases suffix <;>
    simp [surround, addSuffix, Word.append_assoc]

private theorem surroundDerives
    {left right : Word Nat}
    (pre suffix : Option (Word Nat))
    (derivation : Derives targetBasis left right) :
    Derives targetBasis
      (surround pre left suffix)
      (surround pre right suffix) := by
  cases pre with
  | none =>
      cases suffix with
      | none => exact derivation
      | some ending => exact Derives.appendRight derivation ending
  | some beginning =>
      cases suffix with
      | none => exact Derives.prepend beginning derivation
      | some ending =>
          exact Derives.appendRight
            (Derives.prepend beginning derivation) ending

private theorem wordLengthPositive (value : Word Nat) :
    0 < value.toList.length := by
  cases value
  simp [Word.toList]

private theorem threeBlocksLong
    (first second third : Word Nat) :
    3 ≤ ((first ++ second) ++ third).toList.length := by
  rw [Word.toList_append, Word.toList_append,
    List.length_append, List.length_append]
  have firstPositive := wordLengthPositive first
  have secondPositive := wordLengthPositive second
  have thirdPositive := wordLengthPositive third
  omega

private theorem fourBlocksLong
    (first second third fourth : Word Nat) :
    3 ≤ (((first ++ second) ++ third) ++ fourth).toList.length := by
  rw [Word.toList_append, Word.toList_append, Word.toList_append,
    List.length_append, List.length_append, List.length_append]
  have firstPositive := wordLengthPositive first
  have secondPositive := wordLengthPositive second
  have thirdPositive := wordLengthPositive third
  have fourthPositive := wordLengthPositive fourth
  omega

private theorem surroundLong
    (pre suffix : Option (Word Nat)) (core : Word Nat)
    (long : 3 ≤ core.toList.length) :
    3 ≤ (surround pre core suffix).toList.length := by
  cases pre with
  | none =>
      cases suffix with
      | none => exact long
      | some ending =>
          rw [surround, Word.toList_append, List.length_append]
          omega
  | some beginning =>
      cases suffix with
      | none =>
          rw [surround, Word.toList_append, List.length_append]
          omega
      | some ending =>
          rw [surround, Word.toList_append, Word.toList_append,
            List.length_append, List.length_append]
          omega

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (value : Word Nat)
    (first second : Nat → Word Nat) :
    (value.bind first).bind second =
      value.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (value : Word Nat) :
    value.bind Word.singleton = value := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem derivesPowerExpansionOfLengthAtLeastTwo
    (block : Word Nat) (long : 2 ≤ block.toList.length) :
    Derives targetBasis
      (block ++ block)
      ((block ++ block) ++ block) := by
  cases block with
  | mk first tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          let beginning := Word.singleton first
          let ending := Word.mk second rest
          simpa [beginning, ending, Word.singleton, Word.append,
            Word.append_assoc] using
            derivesCompositePowerExpansion beginning ending

private theorem liftContextGather
    (pre suffix : Option (Word Nat))
    (first second : Word Nat) :
    Derives targetBasis
      (protect (surround pre ((first ++ second) ++ first) suffix))
      (protect (surround pre ((second ++ first) ++ first) suffix)) := by
  rw [protect_of_long _
      (surroundLong pre suffix _ (threeBlocksLong first second first)),
    protect_of_long _
      (surroundLong pre suffix _ (threeBlocksLong second first first))]
  exact surroundDerives pre suffix (derivesGather first second)

private theorem liftContextSquareCommutation
    (pre suffix : Option (Word Nat))
    (first second : Word Nat) :
    Derives targetBasis
      (protect (surround pre
        (((first ++ first) ++ second) ++ second) suffix))
      (protect (surround pre
        (((second ++ second) ++ first) ++ first) suffix)) := by
  rw [protect_of_long _
      (surroundLong pre suffix _
        (fourBlocksLong first first second second)),
    protect_of_long _
      (surroundLong pre suffix _
        (fourBlocksLong second second first first))]
  exact surroundDerives pre suffix
    (derivesSquareCommutation first second)

private theorem liftContextPower
    (pre suffix : Option (Word Nat)) (block : Word Nat) :
    Derives targetBasis
      (protect (surround pre (block ++ block) suffix))
      (protect (surround pre ((block ++ block) ++ block) suffix)) := by
  cases pre with
  | some beginning =>
      have beginningPositive := wordLengthPositive beginning
      have blockPositive := wordLengthPositive block
      have sourceLong :
          3 ≤
            (surround (some beginning) (block ++ block) suffix).toList.length := by
        cases suffix <;>
          simp [surround, Word.toList_append] <;> omega
      have targetLong :
          3 ≤
            (surround (some beginning)
              ((block ++ block) ++ block) suffix).toList.length := by
        cases suffix <;>
          simp [surround, Word.toList_append] <;> omega
      rw [protect_of_long _ sourceLong, protect_of_long _ targetLong]
      cases suffix with
      | none =>
          simpa [surround, Word.append_assoc] using
            derivesSuffixPowerExpansion beginning block
      | some ending =>
          simpa [surround, Word.append_assoc] using
            Derives.appendRight
              (derivesSuffixPowerExpansion beginning block) ending
  | none =>
      cases suffix with
      | some ending =>
          have blockPositive := wordLengthPositive block
          have endingPositive := wordLengthPositive ending
          have sourceLong :
              3 ≤
                (surround none (block ++ block)
                  (some ending)).toList.length := by
            simp [surround, Word.toList_append]
            omega
          have targetLong :
              3 ≤
                (surround none ((block ++ block) ++ block)
                  (some ending)).toList.length := by
            simp [surround, Word.toList_append]
            omega
          rw [protect_of_long _ sourceLong, protect_of_long _ targetLong]
          simpa [surround, Word.append_assoc] using
            derivesPrefixPowerExpansion block ending
      | none =>
          cases block with
          | mk first tail =>
              cases tail with
              | nil =>
                  simpa [surround, protect, Word.singleton, Word.append] using
                    (Derives.refl (Word.mk first [first, first]) :
                      Derives targetBasis
                        (Word.mk first [first, first])
                        (Word.mk first [first, first]))
              | cons second rest =>
                  have sourceLong :
                      3 ≤
                        ((Word.mk first (second :: rest) ++
                          Word.mk first (second :: rest))).toList.length := by
                    simp [Word.toList] <;> omega
                  have targetLong :
                      3 ≤
                        (((Word.mk first (second :: rest) ++
                            Word.mk first (second :: rest)) ++
                          Word.mk first (second :: rest))).toList.length := by
                    simp [Word.toList] <;> omega
                  simp only [surround]
                  rw [protect_of_long _ sourceLong,
                    protect_of_long _ targetLong]
                  exact derivesPowerExpansionOfLengthAtLeastTwo
                    (Word.mk first (second :: rest)) (by simp [Word.toList])

/-- Lift all three complete S4_71 laws through contexts and substitutions. -/
theorem liftLowerDerivation
    {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (pre suffix : Option (Word Nat))
    (substitution : Nat → Word Nat) :
    Derives targetBasis
      (protect (surround pre (left.bind substitution) suffix))
      (protect (surround pre (right.bind substitution) suffix)) := by
  induction derivation generalizing pre suffix substitution with
  | fromBasis member =>
      simp only [edmundsFourSeventyOneBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · simpa [edmundsFourSeventyOnePowerLaw,
          edmundsFourSeventyOneXX, edmundsFourSeventyOneXXX,
          Word.bind, Word.singleton, Word.append, Word.append_assoc] using
          liftContextPower pre suffix (substitution 0)
      · simpa [edmundsFourSeventyOneGatherLaw,
          edmundsFourSeventyOneXYX, edmundsFourSeventyOneYXX,
          Word.bind, Word.singleton, Word.append, Word.append_assoc] using
          liftContextGather pre suffix
            (substitution 0) (substitution 1)
      · simpa [edmundsFourSeventyOneSquareCommutationLaw,
          edmundsFourSeventyOneXXYY, edmundsFourSeventyOneYYXX,
          Word.bind, Word.singleton, Word.append, Word.append_assoc] using
          liftContextSquareCommutation pre suffix
            (substitution 0) (substitution 1)
  | refl => exact Derives.refl _
  | symm _ induction =>
      exact (induction pre suffix substitution).symm
  | trans _ _ first second =>
      exact
        (first pre suffix substitution).trans
          (second pre suffix substitution)
  | prepend stem _ induction =>
      simpa only [bind_append, surround_prepend] using
        induction
          (addPrefix pre (stem.bind substitution))
          suffix substitution
  | appendRight _ ending induction =>
      simpa only [bind_append, surround_append] using
        induction pre
          (addSuffix (ending.bind substitution) suffix)
          substitution
  | subst _ next induction =>
      simpa only [bind_bind] using
        induction pre suffix
          (fun letter => (next letter).bind substitution)

/-- Long endpoints are fixed by protection, yielding genuine unrestricted lift. -/
theorem liftLowerDerivationOfLong
    {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length) :
    Derives targetBasis left right := by
  have lifted := liftLowerDerivation derivation none none Word.singleton
  have leftProtected := protect_of_long left leftLong
  have rightProtected := protect_of_long right rightLong
  simpa [surround, bind_singleton, leftProtected, rightProtected] using lifted

end SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_71
