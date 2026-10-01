import SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank085
import SemigroupBasis.CoRoots.S5_240Completeness

/-!
# Complete protected S5_240 lift for the final authenticated S3_4 seed

The exact complete S5_240 lower basis is `xx = xxx`, `xyy = yxx`, and
`xyz = xxyz`. Its square axiom is false on `S3_4`, so protect precisely bare
unary squares and structurally lift all three lower laws under arbitrary
nonempty substitutions and optional left/right contexts.

The prefixed square macro has the exact four-edge displayed-law route
`xyy -> yxx -> yyxx -> xyyyy -> xyyy`; composite-square expansion is a
single frozen long-insertion instance. Every edge is an explicit
`Derives.fromBasis` witness for the immutable fifteen-law rank-085 envelope.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS5_240

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank085.basis

private abbrev lowerBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.S5_240.basis

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Exact frozen `xyy = yxx` for arbitrary nonempty substituted blocks. -/
theorem derivesMarkerSwitch (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ second)
      ((second ++ first) ++ first) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [1, 1]) (Word.mk 1 [0, 0]) :=
    Derives.fromBasis (e := Rank085.law08)
      (show Rank085.law08 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Reverse frozen `xxyy = xyy` to duplicate an initial block. -/
theorem derivesSquaresExpansion (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ second)
      (((first ++ first) ++ second) ++ second) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1]) :=
    Derives.fromBasis (e := Rank085.law03)
      (show Rank085.law03 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive.symm (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Reverse frozen `xxx = xxxx` to contract a fourth copy to three. -/
theorem derivesCubicContraction (block : Word Nat) :
    Derives targetBasis
      (((block ++ block) ++ block) ++ block)
      ((block ++ block) ++ block) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 0]) (Word.mk 0 [0, 0, 0]) :=
    Derives.fromBasis (e := Rank085.law00)
      (show Rank085.law00 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive.symm (instantiateThree block block block)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Reverse frozen `xxxy = xxy` in a nonempty right context. -/
theorem derivesPrefixPowerExpansion
    (first suffix : Word Nat) :
    Derives targetBasis
      ((first ++ first) ++ suffix)
      (((first ++ first) ++ first) ++ suffix) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 0, 1]) (Word.mk 0 [0, 1]) :=
    Derives.fromBasis (e := Rank085.law01)
      (show Rank085.law01 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive.symm (instantiateThree first suffix suffix)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Reverse frozen `xxyz = xyz` for the complete lower insertion axiom. -/
theorem derivesLongInsertion
    (first second third : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ third)
      (((first ++ first) ++ second) ++ third) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 1, 2]) (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := Rank085.law04)
      (show Rank085.law04 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive.symm (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Four exact frozen displayed rewrites derive `yxx -> yxxx`. -/
theorem derivesSuffixPowerExpansion
    (pre block : Word Nat) :
    Derives targetBasis
      ((pre ++ block) ++ block)
      (((pre ++ block) ++ block) ++ block) := by
  have stepOne :
      Derives targetBasis
        ((pre ++ block) ++ block)
        ((block ++ pre) ++ pre) :=
    derivesMarkerSwitch pre block
  have stepTwo :
      Derives targetBasis
        ((block ++ pre) ++ pre)
        (((block ++ block) ++ pre) ++ pre) :=
    derivesSquaresExpansion block pre
  have stepThree :
      Derives targetBasis
        (((block ++ block) ++ pre) ++ pre)
        ((pre ++ (block ++ block)) ++ (block ++ block)) := by
    simpa [Word.append_assoc] using
      derivesMarkerSwitch (block ++ block) pre
  have stepFour :
      Derives targetBasis
        ((pre ++ (block ++ block)) ++ (block ++ block))
        (((pre ++ block) ++ block) ++ block) := by
    simpa [Word.append_assoc] using
      Derives.prepend pre (derivesCubicContraction block)
  exact stepOne.trans <| stepTwo.trans <| stepThree.trans stepFour

/-- One exact long-insertion edge derives `(xy)² -> (xy)³`. -/
theorem derivesCompositePowerExpansion
    (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ (first ++ second))
      (((first ++ second) ++ (first ++ second)) ++
        (first ++ second)) := by
  simpa [Word.append_assoc] using
    derivesLongInsertion (first ++ second) first second

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

/-- Structurally lift all three axioms of the complete S5_240 lower basis. -/
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
      simp only [SemigroupBasis.CoRoots.S5_240.basis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · change
          Derives targetBasis
            (protect (surround pre
              (substitution 0 ++ substitution 0) suffix))
            (protect (surround pre
              ((substitution 0 ++ substitution 0) ++ substitution 0)
              suffix))
        exact liftContextPower pre suffix (substitution 0)
      · change
          Derives targetBasis
            (protect (surround pre
              ((substitution 0 ++ substitution 1) ++ substitution 1)
              suffix))
            (protect (surround pre
              ((substitution 1 ++ substitution 0) ++ substitution 0)
              suffix))
        exact liftContextLong pre suffix
          (threeBlocksLong (substitution 0) (substitution 1)
            (substitution 1))
          (threeBlocksLong (substitution 1) (substitution 0)
            (substitution 0))
          (derivesMarkerSwitch (substitution 0) (substitution 1))
      · change
          Derives targetBasis
            (protect (surround pre
              ((substitution 0 ++ substitution 1) ++ substitution 2)
              suffix))
            (protect (surround pre
              (((substitution 0 ++ substitution 0) ++ substitution 1) ++
                substitution 2) suffix))
        exact liftContextLong pre suffix
          (threeBlocksLong (substitution 0) (substitution 1)
            (substitution 2))
          (fourBlocksLong (substitution 0) (substitution 0)
            (substitution 1) (substitution 2))
          (derivesLongInsertion (substitution 0) (substitution 1)
            (substitution 2))
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

/-- Long endpoints are fixed by protection and lift fully unrestrictedly. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS5_240
