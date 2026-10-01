import SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank011
import SemigroupBasis.Generated.S4_69

/-!
# Protected unrestricted S3_4 × S4_69 rank-011 lower-theory lift

The independently complete `S4_69` calculus has seven axioms.  Its naked
square axiom is false in `S3_4`, so only a bare unary square is protected;
every word of length at least three remains unchanged.  Exact frozen
rank-011 derivations produce middle duplication in three steps, right
duplication in two, alternation in two, and composite-square expansion in
three.  All seven lower laws then lift through arbitrary substitutions and
both optional nonempty contexts.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_69

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank011.basis

private abbrev lowerBasis : List (Identity Nat) := uniqueSeparatorFourBasis

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- The frozen anchored contraction `xxyx = xyx`. -/
theorem derivesAnchoredContraction (first second : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ second) ++ first)
      ((first ++ second) ++ first) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0]) :=
    Derives.fromBasis (e := Rank011.law02)
      (show Rank011.law02 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The reversed frozen initial-square law `xxy -> xxxy`. -/
theorem derivesPrefixPowerExpansion (first suffix : Word Nat) :
    Derives targetBasis
      ((first ++ first) ++ suffix)
      (((first ++ first) ++ first) ++ suffix) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 0, 1]) (Word.mk 0 [0, 1]) :=
    Derives.fromBasis (e := Rank011.law01)
      (show Rank011.law01 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive.symm (instantiateThree first suffix suffix)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The frozen terminal-square expansion `xyy -> xyyy`. -/
theorem derivesSuffixPowerExpansion (pre block : Word Nat) :
    Derives targetBasis
      ((pre ++ block) ++ block)
      (((pre ++ block) ++ block) ++ block) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [1, 1]) (Word.mk 0 [1, 1, 1]) :=
    Derives.fromBasis (e := Rank011.law08)
      (show Rank011.law08 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree pre block block)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The frozen contraction `xxyy = xyx`. -/
theorem derivesSquareContraction (first second : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ second) ++ second)
      ((first ++ second) ++ first) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 0]) :=
    Derives.fromBasis (e := Rank011.law03)
      (show Rank011.law03 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The frozen lower rotation `xyx = yxy`. -/
theorem derivesRotation (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ first)
      ((second ++ first) ++ second) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [1, 0]) (Word.mk 1 [0, 1]) :=
    Derives.fromBasis (e := Rank011.law05)
      (show Rank011.law05 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The frozen internal interchange `xyzx = xzyx`. -/
theorem derivesInsideSwap
    (first second third : Word Nat) :
    Derives targetBasis
      (((first ++ second) ++ third) ++ first)
      (((first ++ third) ++ second) ++ first) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) :=
    Derives.fromBasis (e := Rank011.law10)
      (show Rank011.law10 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The frozen retargeted last-duplication law `xyzy = xyzzy`. -/
theorem derivesLastDuplication
    (first second third : Word Nat) :
    Derives targetBasis
      (((first ++ second) ++ third) ++ second)
      ((((first ++ second) ++ third) ++ third) ++ second) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [1, 2, 1]) (Word.mk 0 [1, 2, 2, 1]) :=
    Derives.fromBasis (e := Rank011.law11)
      (show Rank011.law11 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Three exact frozen rewrites derive `xyx -> xyyx`. -/
theorem derivesMiddleDuplication (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ first)
      (((first ++ second) ++ second) ++ first) := by
  have one := (derivesAnchoredContraction first second).symm
  have two := derivesLastDuplication first first second
  have three :
      Derives targetBasis
        ((((first ++ first) ++ second) ++ second) ++ first)
        (((first ++ second) ++ second) ++ first) := by
    simpa [Word.append_assoc] using
      derivesAnchoredContraction first (second ++ second)
  exact one.trans (two.trans three)

/-- Two exact frozen rewrites derive `xyx -> xyxx`. -/
theorem derivesRightDuplication (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ first)
      (((first ++ second) ++ first) ++ first) := by
  have one := (derivesAnchoredContraction first second).symm
  have two := derivesInsideSwap first first second
  exact one.trans two

/-- Two exact frozen rewrites derive `xyx -> xyxy`. -/
theorem derivesAlternating (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ first)
      (((first ++ second) ++ first) ++ second) := by
  have one := (derivesAnchoredContraction first second).symm
  have two :
      Derives targetBasis
        (((first ++ first) ++ second) ++ first)
        (((first ++ second) ++ first) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend first (derivesRotation first second)
  exact one.trans two

/-- Three exact frozen rewrites derive `(xy)² -> (xy)³`. -/
theorem derivesCompositePowerExpansion
    (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ (first ++ second))
      (((first ++ second) ++ (first ++ second)) ++
        (first ++ second)) := by
  have one :
      Derives targetBasis
        (((first ++ second) ++ first) ++ second)
        ((((first ++ first) ++ second) ++ first) ++ second) :=
    Derives.appendRight
      (derivesAnchoredContraction first second).symm second
  have two :
      Derives targetBasis
        ((((first ++ first) ++ second) ++ first) ++ second)
        (((((first ++ first) ++ second) ++ second) ++ first) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend (first ++ first)
        (derivesAnchoredContraction second first).symm
  have three :
      Derives targetBasis
        (((((first ++ first) ++ second) ++ second) ++ first) ++ second)
        (((((first ++ second) ++ first) ++ second) ++ first) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesInsideSwap first second (first ++ second)).symm second
  simpa [Word.append_assoc] using one.trans (two.trans three)

private def protect (value : Word Nat) : Word Nat :=
  match value.tail with
  | [last] =>
      if value.head = last then value ++ Word.singleton last else value
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
  | some first, none => first ++ core
  | none, some last => core ++ last
  | some first, some last => (first ++ core) ++ last

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
    (pre suffix : Option (Word Nat)) (first core : Word Nat) :
    surround pre (first ++ core) suffix =
      surround (addPrefix pre first) core suffix := by
  cases pre <;> cases suffix <;>
    simp [surround, addPrefix, Word.append_assoc]

private theorem surround_append
    (pre suffix : Option (Word Nat)) (core last : Word Nat) :
    surround pre (core ++ last) suffix =
      surround pre core (addSuffix last suffix) := by
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
      | some last => exact Derives.appendRight derivation last
  | some first =>
      cases suffix with
      | none => exact Derives.prepend first derivation
      | some last =>
          exact Derives.appendRight
            (Derives.prepend first derivation) last

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
      | some last =>
          rw [surround, Word.toList_append, List.length_append]
          omega
  | some first =>
      cases suffix with
      | none =>
          rw [surround, Word.toList_append, List.length_append]
          omega
      | some last =>
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

private theorem liftContextLong
    {left right : Word Nat}
    (pre suffix : Option (Word Nat))
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length)
    (derivation : Derives targetBasis left right) :
    Derives targetBasis
      (protect (surround pre left suffix))
      (protect (surround pre right suffix)) := by
  rw [protect_of_long _ (surroundLong pre suffix left leftLong),
    protect_of_long _ (surroundLong pre suffix right rightLong)]
  exact surroundDerives pre suffix derivation

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
            (surround (some beginning)
              (block ++ block) suffix).toList.length := by
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

/-- Lift all seven complete S4_69 laws structurally under arbitrary contexts. -/
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
      simp only [uniqueSeparatorFourBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [uniqueSeparatorPowerLaw, uniqueSeparatorXX,
          uniqueSeparatorXXX, Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          liftContextPower pre suffix (substitution 0)
      · simpa [uniqueSeparatorLeftDuplicationLaw,
          uniqueSeparatorXYX, uniqueSeparatorXXYX,
          Word.bind, Word.singleton, Word.append, Word.append_assoc] using
          liftContextLong pre suffix
            (threeBlocksLong (substitution 0) (substitution 1)
              (substitution 0))
            (fourBlocksLong (substitution 0) (substitution 0)
              (substitution 1) (substitution 0))
            (derivesAnchoredContraction
              (substitution 0) (substitution 1)).symm
      · simpa [uniqueSeparatorMiddleDuplicationLaw,
          uniqueSeparatorXYX, uniqueSeparatorXYYX,
          Word.bind, Word.singleton, Word.append, Word.append_assoc] using
          liftContextLong pre suffix
            (threeBlocksLong (substitution 0) (substitution 1)
              (substitution 0))
            (fourBlocksLong (substitution 0) (substitution 1)
              (substitution 1) (substitution 0))
            (derivesMiddleDuplication
              (substitution 0) (substitution 1))
      · simpa [uniqueSeparatorRightDuplicationLaw,
          uniqueSeparatorXYX, uniqueSeparatorXYXX,
          Word.bind, Word.singleton, Word.append, Word.append_assoc] using
          liftContextLong pre suffix
            (threeBlocksLong (substitution 0) (substitution 1)
              (substitution 0))
            (fourBlocksLong (substitution 0) (substitution 1)
              (substitution 0) (substitution 0))
            (derivesRightDuplication
              (substitution 0) (substitution 1))
      · simpa [uniqueSeparatorAlternatingLaw,
          uniqueSeparatorXYX, uniqueSeparatorXYXY,
          Word.bind, Word.singleton, Word.append, Word.append_assoc] using
          liftContextLong pre suffix
            (threeBlocksLong (substitution 0) (substitution 1)
              (substitution 0))
            (fourBlocksLong (substitution 0) (substitution 1)
              (substitution 0) (substitution 1))
            (derivesAlternating
              (substitution 0) (substitution 1))
      · simpa [uniqueSeparatorSquaresLaw,
          uniqueSeparatorXYX, uniqueSeparatorXXYY,
          Word.bind, Word.singleton, Word.append, Word.append_assoc] using
          liftContextLong pre suffix
            (threeBlocksLong (substitution 0) (substitution 1)
              (substitution 0))
            (fourBlocksLong (substitution 0) (substitution 0)
              (substitution 1) (substitution 1))
            (derivesSquareContraction
              (substitution 0) (substitution 1)).symm
      · simpa [uniqueSeparatorRotationLaw,
          uniqueSeparatorXYX, uniqueSeparatorYXY,
          Word.bind, Word.singleton, Word.append, Word.append_assoc] using
          liftContextLong pre suffix
            (threeBlocksLong (substitution 0) (substitution 1)
              (substitution 0))
            (threeBlocksLong (substitution 1) (substitution 0)
              (substitution 1))
            (derivesRotation (substitution 0) (substitution 1))
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

/-- Long endpoints are fixed by protection, yielding unrestricted derivations. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_69
