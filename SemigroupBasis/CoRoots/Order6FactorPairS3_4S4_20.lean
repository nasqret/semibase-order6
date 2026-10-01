import SemigroupBasis.CoRoots.Order6FactorPairS3_4S4_20Prelude
import SemigroupBasis.CoRoots.Order6GenericCASShortTwo
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_4S4_20

open SemigroupBasis
open SemigroupBasis.Examples

private def word (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def instantiateTwoWords
    (x y : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | n + 2 => Word.singleton (n + 2)

private def instantiateThreeWords
    (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem wordLengthPositive (value : Word Nat) :
    0 < value.toList.length := by
  cases value
  simp [Word.toList]

private theorem threeBlocksLong (x y z : Word Nat) :
    3 ≤ ((x ++ y) ++ z).toList.length := by
  rw [Word.toList_append, Word.toList_append,
    List.length_append, List.length_append]
  have hx := wordLengthPositive x
  have hy := wordLengthPositive y
  have hz := wordLengthPositive z
  omega

private theorem fourBlocksLong (x y z t : Word Nat) :
    3 ≤ (((x ++ y) ++ z) ++ t).toList.length := by
  rw [Word.toList_append, Word.toList_append, Word.toList_append,
    List.length_append, List.length_append, List.length_append]
  have hx := wordLengthPositive x
  have hy := wordLengthPositive y
  have hz := wordLengthPositive z
  have ht := wordLengthPositive t
  omega

/-! ## Consequences of the displayed basis -/

/-- The ninth displayed law, with nonempty blocks substituted for `x,y`. -/
private theorem derivesSuffixPowerExpansion (pre block : Word Nat) :
    Derives basis
      ((pre ++ block) ++ block)
      (((pre ++ block) ++ block) ++ block) := by
  have base :
      Derives basis (word 0 [1, 1]) (word 0 [1, 1, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [1, 1]) (word 0 [1, 1, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateTwoWords pre block)
  simpa [word, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The reverse of the second displayed law. -/
private theorem derivesPrefixPowerExpansion (block suf : Word Nat) :
    Derives basis
      ((block ++ block) ++ suf)
      (((block ++ block) ++ block) ++ suf) := by
  have base :
      Derives basis (word 0 [0, 0, 1]) (word 0 [0, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 0, 1]) (word 0 [0, 1])) (by decide)
  have substituted :=
    Derives.subst (Derives.symm base) (instantiateTwoWords block suf)
  simpa [word, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The tenth displayed law in block form. -/
private theorem derivesContraction (pre block suf : Word Nat) :
    Derives basis
      (((pre ++ block) ++ block) ++ suf)
      ((pre ++ block) ++ suf) := by
  have base :
      Derives basis (word 0 [1, 1, 2]) (word 0 [1, 2]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [1, 1, 2]) (word 0 [1, 2])) (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords pre block suf)
  simpa [word, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

private theorem derivesInteriorDuplication
    (pre block suf : Word Nat) :
    Derives basis
      ((pre ++ block) ++ suf)
      (((pre ++ block) ++ block) ++ suf) :=
  Derives.symm (derivesContraction pre block suf)

/-- The seventh displayed law in block form. -/
private theorem derivesRotation (x y : Word Nat) :
    Derives basis ((x ++ y) ++ x) ((y ++ x) ++ y) := by
  have base :
      Derives basis (word 0 [1, 0]) (word 1 [0, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [1, 0]) (word 1 [0, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateTwoWords x y)
  simpa [word, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- If a nonempty block already has at least two letters, the tenth law
duplicates the middle block in its square and hence gives `u² = u³`. -/
private theorem derivesPowerExpansionOfLengthAtLeastTwo
    (u : Word Nat) (long : 2 ≤ u.toList.length) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  cases u with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          let first := Word.singleton head
          let remaining := word second rest
          have expanded :=
            derivesInteriorDuplication
              first (remaining ++ first) remaining
          simpa [first, remaining, word, Word.singleton, Word.append,
            Word.append_assoc] using expanded

/-! ## Long lift of the `S4_20` derivation -/

/-- Replace only a bare unary square by its cube. All words of length at
least three are fixed. -/
private def liftSquare (value : Word Nat) : Word Nat :=
  match value.tail with
  | [last] =>
      if value.head = last then value ++ Word.singleton last else value
  | _ => value

private theorem liftSquare_of_long
    (value : Word Nat) (long : 3 ≤ value.toList.length) :
    liftSquare value = value := by
  cases value with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third extra => rfl

private def surround
    (pre : Option (Word Nat)) (core : Word Nat)
    (suf : Option (Word Nat)) : Word Nat :=
  match pre, suf with
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
    (next : Word Nat) (suf : Option (Word Nat)) : Option (Word Nat) :=
  match suf with
  | none => some next
  | some current => some (next ++ current)

private theorem surround_prepend
    (pre suf : Option (Word Nat)) (left core : Word Nat) :
    surround pre (left ++ core) suf =
      surround (addPrefix pre left) core suf := by
  cases pre <;> cases suf <;>
    simp [surround, addPrefix, Word.append_assoc]

private theorem surround_append
    (pre suf : Option (Word Nat)) (core right : Word Nat) :
    surround pre (core ++ right) suf =
      surround pre core (addSuffix right suf) := by
  cases pre <;> cases suf <;>
    simp [surround, addSuffix, Word.append_assoc]

private theorem surroundLong
    (pre suf : Option (Word Nat)) (core : Word Nat)
    (long : 3 ≤ core.toList.length) :
    3 ≤ (surround pre core suf).toList.length := by
  cases pre with
  | none =>
      cases suf with
      | none => exact long
      | some right =>
          rw [surround, Word.toList_append, List.length_append]
          omega
  | some left =>
      cases suf with
      | none =>
          rw [surround, Word.toList_append, List.length_append]
          omega
      | some right =>
          rw [surround, Word.toList_append, Word.toList_append,
            List.length_append, List.length_append]
          omega

private theorem surroundDerives
    {left right : Word Nat}
    (pre suf : Option (Word Nat))
    (derivation : Derives basis left right) :
    Derives basis
      (surround pre left suf)
      (surround pre right suf) := by
  cases pre with
  | none =>
      cases suf with
      | none => exact derivation
      | some suf => exact Derives.appendRight derivation suf
  | some pre =>
      cases suf with
      | none => exact Derives.prepend pre derivation
      | some suf =>
          exact Derives.appendRight (Derives.prepend pre derivation) suf

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
      value.bind (fun x => (first x).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (value : Word Nat) :
    value.bind Word.singleton = value := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem liftContextContraction
    (pre suf : Option (Word Nat)) (x y z : Word Nat) :
    Derives basis
      (liftSquare (surround pre (((x ++ y) ++ y) ++ z) suf))
      (liftSquare (surround pre ((x ++ y) ++ z) suf)) := by
  rw [liftSquare_of_long _
      (surroundLong pre suf _ (fourBlocksLong x y y z)),
    liftSquare_of_long _
      (surroundLong pre suf _ (threeBlocksLong x y z))]
  exact surroundDerives pre suf (derivesContraction x y z)

private theorem liftContextRotation
    (pre suf : Option (Word Nat)) (x y : Word Nat) :
    Derives basis
      (liftSquare (surround pre ((x ++ y) ++ x) suf))
      (liftSquare (surround pre ((y ++ x) ++ y) suf)) := by
  rw [liftSquare_of_long _
      (surroundLong pre suf _ (threeBlocksLong x y x)),
    liftSquare_of_long _
      (surroundLong pre suf _ (threeBlocksLong y x y))]
  exact surroundDerives pre suf (derivesRotation x y)

private theorem liftContextPower
    (pre suf : Option (Word Nat)) (block : Word Nat) :
    Derives basis
      (liftSquare (surround pre (block ++ block) suf))
      (liftSquare (surround pre ((block ++ block) ++ block) suf)) := by
  cases pre with
  | some pre =>
      have prePositive := wordLengthPositive pre
      have blockPositive := wordLengthPositive block
      have sourceLong :
          3 ≤ (surround (some pre) (block ++ block) suf).toList.length := by
        cases suf <;>
          simp [surround, Word.toList_append] <;> omega
      have targetLong :
          3 ≤
            (surround (some pre) ((block ++ block) ++ block) suf).toList.length := by
        cases suf <;>
          simp [surround, Word.toList_append] <;> omega
      rw [liftSquare_of_long _ sourceLong,
        liftSquare_of_long _ targetLong]
      cases suf with
      | none =>
          simpa [surround, Word.append_assoc] using
            derivesSuffixPowerExpansion pre block
      | some suf =>
          simpa [surround, Word.append_assoc] using
            Derives.appendRight
              (derivesSuffixPowerExpansion pre block) suf
  | none =>
      cases suf with
      | some suf =>
          have blockPositive := wordLengthPositive block
          have sufPositive := wordLengthPositive suf
          have sourceLong :
              3 ≤
                (surround none (block ++ block) (some suf)).toList.length := by
            simp [surround, Word.toList_append]
            omega
          have targetLong :
              3 ≤
                (surround none ((block ++ block) ++ block)
                  (some suf)).toList.length := by
            simp [surround, Word.toList_append]
            omega
          rw [liftSquare_of_long _ sourceLong,
            liftSquare_of_long _ targetLong]
          simpa [surround, Word.append_assoc] using
            derivesPrefixPowerExpansion block suf
      | none =>
          cases block with
          | mk head tail =>
              cases tail with
              | nil =>
                  simpa [surround, liftSquare, Word.singleton,
                    Word.append] using
                    (Derives.refl (word head [head, head]) :
                      Derives basis
                        (word head [head, head])
                        (word head [head, head]))
              | cons second rest =>
                  have sourceLong :
                      3 ≤
                        ((Word.mk head (second :: rest) ++
                          Word.mk head (second :: rest))).toList.length := by
                    simp [Word.toList_append, Word.toList] <;> omega
                  have targetLong :
                      3 ≤
                        (((Word.mk head (second :: rest) ++
                            Word.mk head (second :: rest)) ++
                          Word.mk head (second :: rest))).toList.length := by
                    simp [Word.toList_append, Word.toList] <;> omega
                  simp only [surround]
                  rw [liftSquare_of_long _ sourceLong,
                    liftSquare_of_long _ targetLong]
                  exact derivesPowerExpansionOfLengthAtLeastTwo
                    (Word.mk head (second :: rest)) (by simp [Word.toList])

/-- Lift an arbitrary derivation from the complete `S4_20` basis. The two
optional contexts and the substitution are carried through the induction, so
the only short intermediate that needs changing is a bare unary square. -/
private theorem liftSimpleEndpointsDerivation
    {left right : Word Nat}
    (derivation : Derives simpleEndpointsBasis left right)
    (pre suf : Option (Word Nat))
    (substitution : Nat → Word Nat) :
    Derives basis
      (liftSquare (surround pre (left.bind substitution) suf))
      (liftSquare (surround pre (right.bind substitution) suf)) := by
  induction derivation generalizing pre suf substitution with
  | fromBasis member =>
      simp only [simpleEndpointsBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · simpa [simpleEndpointsContractionLaw, simpleEndpointsXYYZ,
          simpleEndpointsXYZ, Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          liftContextContraction pre suf
            (substitution 0) (substitution 1) (substitution 2)
      · simpa [simpleEndpointsRotationLaw, simpleEndpointsXYX,
          simpleEndpointsYXY, Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          liftContextRotation pre suf
            (substitution 0) (substitution 1)
      · simpa [simpleEndpointsPowerLaw, simpleEndpointsXX,
          simpleEndpointsXXX, Word.bind, Word.singleton, Word.append,
          Word.append_assoc] using
          liftContextPower pre suf (substitution 0)
  | refl => exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm (induction pre suf substitution)
  | trans _ _ first second =>
      exact Derives.trans
        (first pre suf substitution)
        (second pre suf substitution)
  | prepend stem _ induction =>
      simpa only [bind_append, surround_prepend] using
        induction (addPrefix pre (stem.bind substitution))
          suf substitution
  | appendRight _ ending induction =>
      simpa only [bind_append, surround_append] using
        induction pre (addSuffix (ending.bind substitution) suf)
          substitution
  | subst _ first induction =>
      simpa only [bind_bind] using
        induction pre suf
          (fun x => (first x).bind substitution)

/-! ## Soundness and the short strata -/

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem s3_4_models :
    Models SemigroupBasis.Generated.S3_4.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_4.table basis toFinThree (by decide)

theorem s4_20_models :
    Models SemigroupBasis.Generated.S4_20.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_20.table basis toFinThree (by decide)

private def orderedPairSeparator
    (first second : Nat) : Nat → Fin 4 :=
  fun tested =>
    if tested = first then 2 else if tested = second then 3 else 0

private theorem swappedQuadraticImpossible
    {first second : Nat} (different : first ≠ second)
    (valid :
      (Identity.mk (word first [second])
        (word second [first])).SatisfiedBy
        SemigroupBasis.Generated.S4_20.table.semigroup) :
    False := by
  have evaluated := valid (orderedPairSeparator first second)
  change
    simpleEndpointsFourMul
        (orderedPairSeparator first second first)
        (orderedPairSeparator first second second) =
      simpleEndpointsFourMul
        (orderedPairSeparator first second second)
        (orderedPairSeparator first second first) at evaluated
  have impossible : (2 : Fin 4) = 0 := by
    simpa [orderedPairSeparator, different, different.symm,
      simpleEndpointsFourMul] using evaluated
  exact (by decide : (2 : Fin 4) ≠ 0) impossible

private theorem quadraticWordsEqual
    (first second third fourth : Nat)
    (permutation : [first, second].Perm [third, fourth])
    (valid :
      (Identity.mk (word first [second])
        (word third [fourth])).SatisfiedBy
        SemigroupBasis.Generated.S4_20.table.semigroup) :
    word first [second] = word third [fourth] := by
  have support (tested : Nat) :
      (first = tested ∨ second = tested) ↔
        (third = tested ∨ fourth = tested) := by
    have membership :
        tested ∈ [first, second] ↔ tested ∈ [third, fourth] :=
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
      · exact False.elim (swappedQuadraticImpossible same valid)
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
    (permutation : identity.lhs.toList.Perm identity.rhs.toList)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S4_20.table.semigroup) :
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
                        leftFirst leftSecond rightFirst rightSecond
                        (by simpa [word, Word.toList] using permutation)
                        (by simpa [word] using valid)

/-- Unrestricted completeness of the exact `S3_4`/`S4_20` identity-theory
intersection. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy SemigroupBasis.Generated.S3_4.table.semigroup)
    (s4Valid :
      identity.SatisfiedBy SemigroupBasis.Generated.S4_20.table.semigroup) :
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
  · rcases quadratic with ⟨leftTwo, rightTwo, permutation⟩
    have literal :=
      quadraticIdentityLiteral identity leftTwo rightTwo permutation s4Valid
    rw [literal]
    exact Derives.refl _
  · have lowerDerivation :=
      SemigroupBasis.Generated.S4_20.representative_basis.2
        identity s4Valid
    have lifted :=
      liftSimpleEndpointsDerivation lowerDerivation none none Word.singleton
    have leftLift := liftSquare_of_long identity.lhs long.1
    have rightLift := liftSquare_of_long identity.rhs long.2
    simpa [surround, bind_singleton, leftLift, rightLift] using lifted

/-- The displayed eleven laws are the exact basis of the intersection. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_4.table.semigroup
      SemigroupBasis.Generated.S4_20.table.semigroup basis where
  leftModels := s3_4_models
  rightModels := s4_20_models
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6FactorPairS3_4S4_20
