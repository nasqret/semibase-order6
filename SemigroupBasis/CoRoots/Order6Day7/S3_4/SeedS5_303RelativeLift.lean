import SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank079
import SemigroupBasis.CoRoots.S5_303Completeness

/-!
# Complete all-quadratic protected S5_303 lift for authenticated rank 079

The exact complete lower basis has `xy = xxy`, `xyx = yxx`, and
`xyzx = xzyx`.  Unlike the previously solved S3_4 seeds, its first axiom
changes EVERY quadratic word, not merely bare unary squares.  Protect each
quadratic word by duplicating its first letter, fix all long words, and lift
all three lower axioms under arbitrary nonempty substitutions and contexts.

The only nonprimitive macro is the exact three-edge composite-prefix
duplication `xyz -> xxyz -> xxyxyz -> xyxyz`; every edge is an actual
instance of a frozen displayed rank-079 law.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS5_303

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank079.basis

private abbrev lowerBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.S5_303.basis

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- The exact frozen rank-079 rotation `xyx = yxx`. -/
theorem derivesRotate (first second : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ first)
      ((second ++ first) ++ first) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [1, 0]) (Word.mk 1 [0, 0]) :=
    Derives.fromBasis (e := Rank079.law05)
      (show Rank079.law05 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The exact frozen anchored contraction `xxyx = xyx`. -/
theorem derivesAnchoredContraction (first second : Word Nat) :
    Derives targetBasis
      (((first ++ first) ++ second) ++ first)
      ((first ++ second) ++ first) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0]) :=
    Derives.fromBasis (e := Rank079.law02)
      (show Rank079.law02 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Reverse frozen `xxyz = xyz` in a nonempty right context. -/
theorem derivesPrefixDuplication
    (first second third : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ third)
      (((first ++ first) ++ second) ++ third) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [0, 1, 2]) (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := Rank079.law03)
      (show Rank079.law03 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive.symm (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Reverse frozen `xyyz = xyz` in a nonempty left context. -/
theorem derivesMiddleDuplication
    (first second third : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ third)
      (((first ++ second) ++ second) ++ third) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [1, 1, 2]) (Word.mk 0 [1, 2]) :=
    Derives.fromBasis (e := Rank079.law06)
      (show Rank079.law06 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive.symm (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The exact frozen rank-079 interior interchange `xyzx = xzyx`. -/
theorem derivesInteriorSwap
    (first second third : Word Nat) :
    Derives targetBasis
      (((first ++ second) ++ third) ++ first)
      (((first ++ third) ++ second) ++ first) := by
  have primitive :
      Derives targetBasis
        (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) :=
    Derives.fromBasis (e := Rank079.law07)
      (show Rank079.law07 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Three exact displayed-law edges duplicate an arbitrary composite prefix. -/
theorem derivesCompositePrefixDuplication
    (first second ending : Word Nat) :
    Derives targetBasis
      ((first ++ second) ++ ending)
      (((first ++ second) ++ (first ++ second)) ++ ending) := by
  have stepOne :
      Derives targetBasis
        ((first ++ second) ++ ending)
        (((first ++ first) ++ second) ++ ending) :=
    derivesPrefixDuplication first second ending
  have stepTwo :
      Derives targetBasis
        (((first ++ first) ++ second) ++ ending)
        (((first ++ (first ++ second)) ++ (first ++ second)) ++ ending) := by
    simpa [Word.append_assoc] using
      derivesMiddleDuplication first (first ++ second) ending
  have stepThree :
      Derives targetBasis
        (((first ++ (first ++ second)) ++ (first ++ second)) ++ ending)
        (((first ++ second) ++ (first ++ second)) ++ ending) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesAnchoredContraction first second) (second ++ ending)
  exact stepOne.trans (stepTwo.trans stepThree)

/-- Every quadratic word, including words with two distinct letters, is guarded. -/
private def protect (value : Word Nat) : Word Nat :=
  match value.tail with
  | [_] => Word.singleton value.head ++ value
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

private theorem liftContextPrefixDuplication
    (pre suffix : Option (Word Nat)) (first second : Word Nat) :
    Derives targetBasis
      (protect (surround pre (first ++ second) suffix))
      (protect (surround pre ((first ++ first) ++ second) suffix)) := by
  cases pre with
  | some beginning =>
      have beginningPositive := wordLengthPositive beginning
      have firstPositive := wordLengthPositive first
      have secondPositive := wordLengthPositive second
      have sourceLong :
          3 ≤
            (surround (some beginning)
              (first ++ second) suffix).toList.length := by
        cases suffix <;>
          simp [surround, Word.toList_append] <;> omega
      have targetLong :
          3 ≤
            (surround (some beginning)
              ((first ++ first) ++ second) suffix).toList.length := by
        cases suffix <;>
          simp [surround, Word.toList_append] <;> omega
      rw [protect_of_long _ sourceLong, protect_of_long _ targetLong]
      cases suffix with
      | none =>
          simpa [surround, Word.append_assoc] using
            derivesMiddleDuplication beginning first second
      | some ending =>
          simpa [surround, Word.append_assoc] using
            Derives.appendRight
              (derivesMiddleDuplication beginning first second) ending
  | none =>
      cases suffix with
      | some ending =>
          have firstPositive := wordLengthPositive first
          have secondPositive := wordLengthPositive second
          have endingPositive := wordLengthPositive ending
          have sourceLong :
              3 ≤
                (surround none (first ++ second)
                  (some ending)).toList.length := by
            simp [surround, Word.toList_append]
            omega
          have targetLong :
              3 ≤
                (surround none ((first ++ first) ++ second)
                  (some ending)).toList.length := by
            simp [surround, Word.toList_append]
            omega
          rw [protect_of_long _ sourceLong, protect_of_long _ targetLong]
          simpa [surround, Word.append_assoc] using
            derivesPrefixDuplication first second ending
      | none =>
          cases first with
          | mk firstLetter firstTail =>
              cases firstTail with
              | nil =>
                  cases second with
                  | mk secondLetter secondTail =>
                      cases secondTail with
                      | nil =>
                          simpa [surround, protect, Word.singleton,
                            Word.append] using
                            (Derives.refl
                              (Word.mk firstLetter
                                [firstLetter, secondLetter]) :
                              Derives targetBasis
                                (Word.mk firstLetter
                                  [firstLetter, secondLetter])
                                (Word.mk firstLetter
                                  [firstLetter, secondLetter]))
                      | cons thirdLetter extra =>
                          let starting := Word.singleton firstLetter
                          let middle := Word.singleton secondLetter
                          let ending := Word.mk thirdLetter extra
                          have sourceLong :
                              3 ≤
                                (Word.mk firstLetter [] ++
                                  Word.mk secondLetter
                                    (thirdLetter :: extra)).toList.length := by
                            simp [Word.toList]
                          have targetLong :
                              3 ≤
                                ((Word.mk firstLetter [] ++
                                    Word.mk firstLetter []) ++
                                  Word.mk secondLetter
                                    (thirdLetter :: extra)).toList.length := by
                            simp [Word.toList]
                          simp only [surround]
                          rw [protect_of_long _ sourceLong,
                            protect_of_long _ targetLong]
                          simpa [starting, middle, ending, Word.singleton,
                            Word.append, Word.append_assoc] using
                            derivesPrefixDuplication starting middle ending
              | cons next extra =>
                  let starting := Word.singleton firstLetter
                  let remainder := Word.mk next extra
                  have secondPositive := wordLengthPositive second
                  have sourceLong :
                      3 ≤
                        (Word.mk firstLetter (next :: extra) ++
                          second).toList.length := by
                    simp [Word.toList]
                    omega
                  have targetLong :
                      3 ≤
                        ((Word.mk firstLetter (next :: extra) ++
                            Word.mk firstLetter (next :: extra)) ++
                          second).toList.length := by
                    simp [Word.toList]
                    omega
                  simp only [surround]
                  rw [protect_of_long _ sourceLong,
                    protect_of_long _ targetLong]
                  simpa [starting, remainder, Word.singleton,
                    Word.append, Word.append_assoc] using
                    derivesCompositePrefixDuplication starting remainder second

/-- Structurally lift every exact axiom of the complete S5_303 lower basis. -/
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
      simp only [SemigroupBasis.CoRoots.S5_303.basis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · change
          Derives targetBasis
            (protect (surround pre
              (substitution 0 ++ substitution 1) suffix))
            (protect (surround pre
              ((substitution 0 ++ substitution 0) ++ substitution 1)
              suffix))
        exact liftContextPrefixDuplication
          pre suffix (substitution 0) (substitution 1)
      · change
          Derives targetBasis
            (protect (surround pre
              ((substitution 0 ++ substitution 1) ++ substitution 0)
              suffix))
            (protect (surround pre
              ((substitution 1 ++ substitution 0) ++ substitution 0)
              suffix))
        exact liftContextLong pre suffix
          (threeBlocksLong (substitution 0) (substitution 1)
            (substitution 0))
          (threeBlocksLong (substitution 1) (substitution 0)
            (substitution 0))
          (derivesRotate (substitution 0) (substitution 1))
      · change
          Derives targetBasis
            (protect (surround pre
              (((substitution 0 ++ substitution 1) ++ substitution 2) ++
                substitution 0) suffix))
            (protect (surround pre
              (((substitution 0 ++ substitution 2) ++ substitution 1) ++
                substitution 0) suffix))
        exact liftContextLong pre suffix
          (fourBlocksLong (substitution 0) (substitution 1)
            (substitution 2) (substitution 0))
          (fourBlocksLong (substitution 0) (substitution 2)
            (substitution 1) (substitution 0))
          (derivesInteriorSwap (substitution 0) (substitution 1)
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

/-- All endpoints of length at least three lift fully unrestrictedly. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS5_303
