import SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangCondition8Completeness

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions

private abbrev B : List (Identity Nat) := Condition8.basis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def zyxxx : Word Nat := w 2 [1, 0, 0, 0]
private def zyx : Word Nat := w 2 [1, 0]
private def yxxx : Word Nat := w 1 [0, 0, 0]
private def yyyx : Word Nat := w 1 [1, 1, 0]
private def xxyx : Word Nat := w 0 [0, 1, 0]
private def yxyx : Word Nat := w 1 [0, 1, 0]
private def xyyx : Word Nat := w 0 [1, 1, 0]

private def suffixPowerLaw : Identity Nat := ⟨zyxxx, zyx⟩
private def powerTransferLaw : Identity Nat := ⟨yxxx, yyyx⟩
private def squareReturnLaw : Identity Nat := ⟨xxyx, yxxx⟩
private def middleSquareLaw : Identity Nat := ⟨yxyx, xyyx⟩

private theorem basisSuffixPower :
    Derives B zyxxx zyx := by
  apply Derives.fromBasis (e := suffixPowerLaw)
  decide

private theorem basisPowerTransfer :
    Derives B yxxx yyyx := by
  apply Derives.fromBasis (e := powerTransferLaw)
  decide

private theorem basisSquareReturn :
    Derives B xxyx yxxx := by
  apply Derives.fromBasis (e := squareReturnLaw)
  decide

private theorem basisMiddleSquare :
    Derives B yxyx xyyx := by
  apply Derives.fromBasis (e := middleSquareLaw)
  decide

private def instantiateThreeWords
    (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private def triple (word : Word Nat) : Word Nat :=
  (word ++ word) ++ word

/-- The reversed form of Lee--Zhang (6.1a): a cube may be deleted after
two nonempty blocks. -/
private theorem derivesSuffixTripleContraction
    (z y x : Word Nat) :
    Derives B ((z ++ y) ++ triple x) ((z ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSuffixPower (instantiateThreeWords x y z)
  simpa [suffixPowerLaw, zyxxx, zyx, w, triple,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Lee--Zhang (6.1b) moves a cube across one neighboring block. -/
private theorem derivesPowerTransfer (y x : Word Nat) :
    Derives B (y ++ triple x) (triple y ++ x) := by
  have substituted :=
    Derives.subst basisPowerTransfer (instantiateThreeWords x y y)
  simpa [powerTransferLaw, yxxx, yyyx, w, triple,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The thresholded affine square-return law. -/
private theorem derivesSquareReturn (x y : Word Nat) :
    Derives B (((x ++ x) ++ y) ++ x) (y ++ triple x) := by
  have substituted :=
    Derives.subst basisSquareReturn (instantiateThreeWords x y y)
  simpa [squareReturnLaw, xxyx, yxxx, w, triple,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The affine middle-square law in the orientation stored by Condition 8. -/
private theorem derivesMiddleSquare (x y : Word Nat) :
    Derives B (((y ++ x) ++ y) ++ x)
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisMiddleSquare (instantiateThreeWords x y y)
  simpa [middleSquareLaw, yxyx, xyyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private theorem word_length_positive (word : Word Nat) :
    0 < word.toList.length := by
  cases word
  simp [Word.toList]

/-! ## Threshold-three transport of the affine theory -/

/-- Preserve words of length at least three, replace a singleton by its
cube, and replace a pair `xy` by `xy^3`.  These are exactly the representatives
for which the three affine axioms become Condition 8 derivations. -/
private def threshold (word : Word Nat) : Word Nat :=
  match word.tail with
  | [] => triple word
  | [last] => Word.singleton word.head ++ triple (Word.singleton last)
  | _ :: _ :: _ => word

private theorem threshold_of_long
    (word : Word Nat) (long : 3 ≤ word.toList.length) :
    threshold word = word := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third extra => rfl

private theorem threshold_long (word : Word Nat) :
    3 ≤ (threshold word).toList.length := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => simp [threshold, triple, Word.toList]
      | cons second rest =>
          cases rest with
          | nil =>
              simp [threshold, triple, Word.toList, Word.singleton]
          | cons third extra =>
              simp [threshold, Word.toList]

/-- A cube of a three-block word contracts to the word.  This is the
four-step calculation behind Lee--Zhang (6.2a), formulated for arbitrary
nonempty blocks. -/
private theorem derivesLongCubeBlocks (a b c : Word Nat) :
    Derives B (triple ((a ++ b) ++ c)) ((a ++ b) ++ c) := by
  let whole := (a ++ b) ++ c
  have first :=
    Derives.prepend whole
      (Derives.symm (derivesSuffixTripleContraction whole (a ++ b) c))
  have second :=
    Derives.appendRight
      (Derives.symm (derivesPowerTransfer whole c)) c
  have third :=
    Derives.appendRight (derivesSuffixTripleContraction a b c) (c ++ c)
  have fourth := derivesSuffixTripleContraction a b c
  simp [whole, triple, Word.append_assoc] at first second third fourth ⊢
  exact first.trans (second.trans (third.trans fourth))

/-- A cube of a pair contracts to the threshold representative `xy^3`. -/
private theorem derivesPairCubeToThreshold (a b : Word Nat) :
    Derives B (triple (a ++ b)) (a ++ triple b) := by
  let pair := a ++ b
  have first :=
    Derives.prepend pair
      (Derives.symm (derivesSuffixTripleContraction pair a b))
  have second :=
    Derives.appendRight
      (Derives.symm (derivesPowerTransfer pair b)) b
  have third :=
    Derives.appendRight (derivesSuffixTripleContraction a b b) b
  simp [pair, triple, Word.append_assoc] at first second third ⊢
  exact first.trans (second.trans third)

private theorem derivesTripleToThreshold (word : Word Nat) :
    Derives B (triple word) (threshold word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          exact Derives.refl _
      | cons second rest =>
          cases rest with
          | nil =>
              simpa [threshold, triple, Word.singleton, Word.append,
                Word.append_assoc] using
                derivesPairCubeToThreshold
                  (Word.singleton head) (Word.singleton second)
          | cons third extra =>
              simpa [threshold, triple, wordOfCons, Word.singleton,
                Word.append, Word.append_assoc] using
                derivesLongCubeBlocks
                  (Word.singleton head) (Word.singleton second)
                  (wordOfCons third extra)

/-- Thresholding commutes with adding a nonempty prefix, modulo Condition 8. -/
private theorem derivesPrependThreshold
    (pre word : Word Nat) :
    Derives B (threshold (pre ++ word))
      (pre ++ threshold word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          cases pre with
          | mk prefixHead prefixTail =>
              cases prefixTail with
              | nil =>
                  exact Derives.refl _
              | cons next rest =>
                  have sourceLong :
                      3 ≤
                        (Word.mk prefixHead (next :: rest) ++
                          Word.mk head []).toList.length := by
                    simp [Word.toList]
                  rw [threshold_of_long _ sourceLong]
                  simpa [threshold, triple, wordOfCons, Word.singleton,
                    Word.append, Word.append_assoc] using
                    Derives.symm
                      (derivesSuffixTripleContraction
                        (Word.singleton prefixHead)
                        (wordOfCons next rest)
                        (Word.singleton head))
      | cons second rest =>
          cases rest with
          | nil =>
              have sourceLong :
                  3 ≤
                    (pre ++ Word.mk head [second]).toList.length := by
                simp [Word.toList]
              rw [threshold_of_long _ sourceLong]
              simpa [threshold, triple, wordOfCons, Word.singleton,
                Word.append, Word.append_assoc] using
                Derives.symm
                  (derivesSuffixTripleContraction pre
                    (Word.singleton head) (Word.singleton second))
          | cons third extra =>
              have wordLong :
                  3 ≤ (Word.mk head (second :: third :: extra)).toList.length := by
                simp [Word.toList]
              have sourceLong :
                  3 ≤
                    (pre ++
                      Word.mk head (second :: third :: extra)).toList.length := by
                simp [Word.toList]
                omega
              rw [threshold_of_long _ sourceLong,
                threshold_of_long _ wordLong]
              exact Derives.refl _

/-- Thresholding commutes with adding a nonempty suffix, modulo Condition 8. -/
private theorem derivesAppendThreshold
    (word suffix : Word Nat) :
    Derives B (threshold (word ++ suffix))
      (threshold word ++ suffix) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          cases suffix with
          | mk suffixHead suffixTail =>
              cases suffixTail with
              | nil =>
                  simpa [threshold, triple, Word.singleton, Word.append,
                    Word.append_assoc] using
                    derivesPowerTransfer
                      (Word.singleton head) (Word.singleton suffixHead)
              | cons next rest =>
                  let suffixRest := wordOfCons next rest
                  have sourceLong :
                      3 ≤
                        (Word.mk head [] ++
                          Word.mk suffixHead (next :: rest)).toList.length := by
                    simp [Word.toList]
                  rw [threshold_of_long _ sourceLong]
                  have first :=
                    Derives.symm
                      (derivesSuffixTripleContraction
                        (Word.singleton head)
                        (Word.singleton suffixHead) suffixRest)
                  have second :=
                    Derives.prepend (Word.singleton head)
                      (derivesPowerTransfer
                        (Word.singleton suffixHead) suffixRest)
                  have third :=
                    Derives.appendRight
                      (derivesPowerTransfer
                        (Word.singleton head)
                        (Word.singleton suffixHead)) suffixRest
                  simp [threshold, triple, suffixRest, wordOfCons,
                    Word.singleton, Word.append_assoc]
                    at first second third ⊢
                  exact first.trans (second.trans third)
      | cons second rest =>
          cases rest with
          | nil =>
              have sourceLong :
                  3 ≤
                    (Word.mk head [second] ++ suffix).toList.length := by
                simp [Word.toList]
              rw [threshold_of_long _ sourceLong]
              have first :=
                Derives.symm
                  (derivesSuffixTripleContraction
                    (Word.singleton head) (Word.singleton second) suffix)
              have second :=
                Derives.prepend (Word.singleton head)
                  (derivesPowerTransfer (Word.singleton second) suffix)
              simp [threshold, triple, Word.singleton,
                Word.append_assoc] at first second ⊢
              exact first.trans second
          | cons third extra =>
              have wordLong :
                  3 ≤ (Word.mk head (second :: third :: extra)).toList.length := by
                simp [Word.toList]
              have sourceLong :
                  3 ≤
                    (Word.mk head (second :: third :: extra) ++
                      suffix).toList.length := by
                simp [Word.toList]
              rw [threshold_of_long _ sourceLong,
                threshold_of_long _ wordLong]
              exact Derives.refl _

private theorem derivesPairBindThreshold (left right : Word Nat) :
    Derives B (left ++ triple right) (threshold (left ++ right)) := by
  cases right with
  | mk rightHead rightTail =>
      cases rightTail with
      | nil =>
          cases left with
          | mk leftHead leftTail =>
              cases leftTail with
              | nil =>
                  exact Derives.refl _
              | cons next rest =>
                  have targetLong :
                      3 ≤
                        (Word.mk leftHead (next :: rest) ++
                          Word.mk rightHead []).toList.length := by
                    simp [Word.toList]
                  rw [threshold_of_long _ targetLong]
                  simpa [triple, wordOfCons, Word.singleton, Word.append,
                    Word.append_assoc] using
                    derivesSuffixTripleContraction
                      (Word.singleton leftHead)
                      (wordOfCons next rest)
                      (Word.singleton rightHead)
      | cons second rest =>
          cases rest with
          | nil =>
              have targetLong :
                  3 ≤
                    (left ++ Word.mk rightHead [second]).toList.length := by
                simp [Word.toList]
              rw [threshold_of_long _ targetLong]
              have first :=
                Derives.prepend left
                  (derivesPairCubeToThreshold
                    (Word.singleton rightHead) (Word.singleton second))
              have secondDerivation :=
                derivesSuffixTripleContraction left
                  (Word.singleton rightHead) (Word.singleton second)
              simp [triple, Word.singleton, Word.append_assoc]
                at first secondDerivation ⊢
              exact first.trans secondDerivation
          | cons third extra =>
              have targetLong :
                  3 ≤
                    (left ++
                      Word.mk rightHead (second :: third :: extra)).toList.length := by
                simp [Word.toList]
                omega
              rw [threshold_of_long _ targetLong]
              simpa [triple, wordOfCons, Word.singleton, Word.append,
                Word.append_assoc] using
                Derives.prepend left
                  (derivesLongCubeBlocks
                    (Word.singleton rightHead) (Word.singleton second)
                    (wordOfCons third extra))

private theorem list_length_le_flatMap_words
    (letters : List Nat) (substitution : Nat → Word Nat) :
    letters.length ≤
      (letters.flatMap fun letter => (substitution letter).toList).length := by
  induction letters with
  | nil => simp
  | cons letter rest induction =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have positive : 1 ≤ (substitution letter).toList.length := by
        exact word_length_positive (substitution letter)
      omega

private theorem bind_long
    (word : Word Nat) (substitution : Nat → Word Nat)
    (long : 3 ≤ word.toList.length) :
    3 ≤ (word.bind substitution).toList.length := by
  rw [Word.toList_bind]
  exact Nat.le_trans long
    (list_length_le_flatMap_words word.toList substitution)

private theorem derivesBindThreshold
    (word : Word Nat) (substitution : Nat → Word Nat) :
    Derives B ((threshold word).bind substitution)
      (threshold (word.bind substitution)) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simpa [threshold, triple, Word.bind, Word.append,
            Word.singleton, Word.append_assoc] using
            derivesTripleToThreshold (substitution head)
      | cons second rest =>
          cases rest with
          | nil =>
              simpa [threshold, triple, Word.bind, Word.append,
                Word.singleton, Word.append_assoc] using
                derivesPairBindThreshold
                  (substitution head) (substitution second)
          | cons third extra =>
              have sourceLong :
                  3 ≤
                    (Word.mk head (second :: third :: extra)).toList.length := by
                simp [Word.toList]
              have targetLong :=
                bind_long (Word.mk head (second :: third :: extra))
                  substitution sourceLong
              rw [threshold_of_long _ targetLong]
              exact Derives.refl _

/-- Every affine-parity derivation lifts through the threshold-three
representatives.  This is the reusable content of the Lee--Zhang Section 6
normal-form argument. -/
private theorem derivesThresholded
    {left right : Word Nat}
    (derivation : Derives affineParityFourBasis left right) :
    Derives B (threshold left) (threshold right) := by
  induction derivation with
  | fromBasis member =>
      simp only [affineParityFourBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact Derives.refl _
      · simpa [threshold, affineParitySquareReturnLaw,
          affineParityXXYX, affineParityYX, triple, xxyx, yxxx, w,
          Word.singleton, Word.append, Word.append_assoc] using
          basisSquareReturn
      · simpa [threshold, affineParityMiddleSquareLaw,
          affineParityXYYX, affineParityYXYX, triple, xyyx, yxyx, w,
          Word.singleton, Word.append, Word.append_assoc] using
          Derives.symm basisMiddleSquare
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm induction
  | trans _ _ first second =>
      exact first.trans second
  | prepend pre _ induction =>
      exact
        (derivesPrependThreshold pre _).trans <|
          (Derives.prepend pre induction).trans <|
            Derives.symm (derivesPrependThreshold pre _)
  | appendRight _ suffix induction =>
      exact
        (derivesAppendThreshold _ suffix).trans <|
          (Derives.appendRight induction suffix).trans <|
            Derives.symm (derivesAppendThreshold _ suffix)
  | subst _ substitution induction =>
      exact
        (Derives.symm (derivesBindThreshold _ substitution)).trans <|
          (Derives.subst induction substitution).trans <|
            derivesBindThreshold _ substitution

/-! ## The `S3_4 = N_3` length strata -/

private def projectionLengthState (length : Nat) : Fin 3 :=
  if length = 1 then 2 else if length = 2 then 1 else 0

private def projectionLengthValuation : Nat → Fin 3 :=
  fun _ => 2

private theorem projectionEval_length (word : Word Nat) :
    projectionQuadraticThree.semigroup.eval
        projectionLengthValuation word =
      projectionLengthState word.toList.length := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third extra =>
              have evaluated :
                  projectionQuadraticThree.semigroup.eval
                      projectionLengthValuation
                      (Word.mk head (second :: third :: extra)) =
                    (0 : Fin 3) := by
                simpa only [] using
                  projectionQuadraticEval_long projectionLengthValuation
                    head second third extra
              rw [evaluated]
              simp [projectionLengthState, Word.toList]

private theorem projectionLengthState_capped_injective
    {leftLength rightLength : Nat}
    (leftPositive : 0 < leftLength)
    (rightPositive : 0 < rightLength)
    (equal :
      projectionLengthState leftLength =
        projectionLengthState rightLength) :
    min leftLength 3 = min rightLength 3 := by
  have values := congrArg Fin.val equal
  by_cases leftOne : leftLength = 1
  · subst leftLength
    by_cases rightOne : rightLength = 1
    · subst rightLength
      rfl
    · by_cases rightTwo : rightLength = 2
      · subst rightLength
        simp [projectionLengthState] at values
      · have rightLong : 3 ≤ rightLength := by omega
        simp [projectionLengthState, rightOne, rightTwo] at values
  · by_cases leftTwo : leftLength = 2
    · subst leftLength
      by_cases rightOne : rightLength = 1
      · subst rightLength
        simp [projectionLengthState, leftOne] at values
      · by_cases rightTwo : rightLength = 2
        · subst rightLength
          rfl
        · have rightLong : 3 ≤ rightLength := by omega
          simp [projectionLengthState, rightOne, rightTwo] at values
    · have leftLong : 3 ≤ leftLength := by omega
      by_cases rightOne : rightLength = 1
      · subst rightLength
        simp [projectionLengthState, leftOne, leftTwo] at values
      · by_cases rightTwo : rightLength = 2
        · subst rightLength
          simp [projectionLengthState, leftOne, leftTwo] at values
        · have rightLong : 3 ≤ rightLength := by omega
          simp [Nat.min_eq_right leftLong,
            Nat.min_eq_right rightLong]

private theorem projectionValid_cappedLength
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy projectionQuadraticThree.semigroup) :
    min identity.lhs.toList.length 3 =
      min identity.rhs.toList.length 3 := by
  have evaluated := valid projectionLengthValuation
  rw [projectionEval_length, projectionEval_length] at evaluated
  exact projectionLengthState_capped_injective
    (word_length_positive identity.lhs)
    (word_length_positive identity.rhs) evaluated

private def projectionSeparator (selected : Nat) : Nat → Fin 3 :=
  fun tested => if tested = selected then 2 else 0

private theorem valid_projection_eq {left right : Nat}
    (valid :
      (Identity.mk (Word.singleton left) (Word.singleton right)).SatisfiedBy
        projectionQuadraticThree.semigroup) :
    left = right := by
  have evaluated := valid (projectionSeparator left)
  change projectionSeparator left left = projectionSeparator left right
    at evaluated
  by_cases equal : left = right
  · exact equal
  · exfalso
    simp [projectionSeparator] at evaluated
    exact equal evaluated.symm

private def quadraticSeparator (selected : Nat) : Nat → Fin 3 :=
  fun tested => if tested = selected then 0 else 2

private theorem quadraticSeparator_eval
    (selected left right : Nat) :
    projectionQuadraticThree.semigroup.eval
        (quadraticSeparator selected) (wordOfCons left [right]) =
      if left = selected ∨ right = selected then (0 : Fin 3)
      else (1 : Fin 3) := by
  change
    projectionQuadraticThreeMul
        (quadraticSeparator selected left)
        (quadraticSeparator selected right) =
      if left = selected ∨ right = selected then 0 else 1
  by_cases leftSelected : left = selected <;>
    by_cases rightSelected : right = selected <;>
      simp [projectionQuadraticThreeMul, quadraticSeparator,
        leftSelected, rightSelected]

private theorem valid_quadratic_support_iff
    {leftFirst leftSecond rightFirst rightSecond selected : Nat}
    (valid :
      (Identity.mk
        (wordOfCons leftFirst [leftSecond])
        (wordOfCons rightFirst [rightSecond])).SatisfiedBy
        projectionQuadraticThree.semigroup) :
    (leftFirst = selected ∨ leftSecond = selected) ↔
      (rightFirst = selected ∨ rightSecond = selected) := by
  have evaluated := valid (quadraticSeparator selected)
  rw [quadraticSeparator_eval, quadraticSeparator_eval] at evaluated
  constructor
  · intro leftMember
    by_cases rightMember :
        rightFirst = selected ∨ rightSecond = selected
    · exact rightMember
    · exfalso
      simp [leftMember, rightMember] at evaluated
  · intro rightMember
    by_cases leftMember : leftFirst = selected ∨ leftSecond = selected
    · exact leftMember
    · exfalso
      simp [leftMember, rightMember] at evaluated

private def affineSwapSeparator
    (left right : Nat) : Nat → Fin 4 :=
  fun tested =>
    if tested = left then 1 else if tested = right then 2 else 0

private theorem affine_swap_impossible
    {left right : Nat} (different : left ≠ right)
    (valid :
      (Identity.mk
        (wordOfCons left [right])
        (wordOfCons right [left])).SatisfiedBy
        affineParityFour.semigroup) :
    False := by
  have evaluated := valid (affineSwapSeparator left right)
  change
    SemigroupBasis.Generated.Catalogue.S4_96.mul
        (affineSwapSeparator left right left)
        (affineSwapSeparator left right right) =
      SemigroupBasis.Generated.Catalogue.S4_96.mul
        (affineSwapSeparator left right right)
        (affineSwapSeparator left right left) at evaluated
  have impossible : (2 : Fin 4) = 3 := by
    simp [affineSwapSeparator, different, different.symm,
      SemigroupBasis.Generated.Catalogue.S4_96.mul] at evaluated
  exact (by decide : (2 : Fin 4) ≠ 3) impossible

private theorem valid_pair_eq
    {leftFirst leftSecond rightFirst rightSecond : Nat}
    (projectionValid :
      (Identity.mk
        (wordOfCons leftFirst [leftSecond])
        (wordOfCons rightFirst [rightSecond])).SatisfiedBy
        projectionQuadraticThree.semigroup)
    (affineValid :
      (Identity.mk
        (wordOfCons leftFirst [leftSecond])
        (wordOfCons rightFirst [rightSecond])).SatisfiedBy
        affineParityFour.semigroup) :
    wordOfCons leftFirst [leftSecond] =
      wordOfCons rightFirst [rightSecond] := by
  have support (selected : Nat) :
      (leftFirst = selected ∨ leftSecond = selected) ↔
        (rightFirst = selected ∨ rightSecond = selected) :=
    valid_quadratic_support_iff projectionValid
  have rightFirstMember :
      rightFirst = leftFirst ∨ rightFirst = leftSecond := by
    have member := (support rightFirst).mpr (Or.inl rfl)
    exact member.imp Eq.symm Eq.symm
  have rightSecondMember :
      rightSecond = leftFirst ∨ rightSecond = leftSecond := by
    have member := (support rightSecond).mpr (Or.inr rfl)
    exact member.imp Eq.symm Eq.symm
  rcases rightFirstMember with firstLeft | firstRight
  · rcases rightSecondMember with secondLeft | secondRight
    · subst rightFirst
      subst rightSecond
      by_cases equal : leftFirst = leftSecond
      · subst leftSecond
        rfl
      · have missing := (support leftSecond).mp (Or.inr rfl)
        have forced : leftFirst = leftSecond := missing.elim id id
        exact False.elim (equal forced)
    · subst rightFirst
      subst rightSecond
      rfl
  · rcases rightSecondMember with secondLeft | secondRight
    · subst rightFirst
      subst rightSecond
      by_cases equal : leftFirst = leftSecond
      · subst leftSecond
        rfl
      · exact False.elim (affine_swap_impossible equal affineValid)
    · subst rightFirst
      subst rightSecond
      by_cases equal : leftFirst = leftSecond
      · subst leftSecond
        rfl
      · have missing := (support leftFirst).mp (Or.inl rfl)
        have forced : leftSecond = leftFirst := missing.elim id id
        exact False.elim (equal forced.symm)

private theorem lengthOne_eq_of_projectionValid
    (left right : Word Nat)
    (leftLength : left.toList.length = 1)
    (rightLength : right.toList.length = 1)
    (valid : (Identity.mk left right).SatisfiedBy
      projectionQuadraticThree.semigroup) :
    left = right := by
  cases left with
  | mk leftHead leftTail =>
      cases leftTail with
      | nil =>
          cases right with
          | mk rightHead rightTail =>
              cases rightTail with
              | nil =>
                  have heads : leftHead = rightHead :=
                    valid_projection_eq valid
                  subst rightHead
                  rfl
              | cons rightSecond rightRest =>
                  simp [Word.toList] at rightLength
      | cons leftSecond leftRest =>
          simp [Word.toList] at leftLength

private theorem lengthTwo_eq_of_factorValid
    (left right : Word Nat)
    (leftLength : left.toList.length = 2)
    (rightLength : right.toList.length = 2)
    (projectionValid : (Identity.mk left right).SatisfiedBy
      projectionQuadraticThree.semigroup)
    (affineValid : (Identity.mk left right).SatisfiedBy
      affineParityFour.semigroup) :
    left = right := by
  cases left with
  | mk leftHead leftTail =>
      cases leftTail with
      | nil => simp [Word.toList] at leftLength
      | cons leftSecond leftRest =>
          cases leftRest with
          | nil =>
              cases right with
              | mk rightHead rightTail =>
                  cases rightTail with
                  | nil => simp [Word.toList] at rightLength
                  | cons rightSecond rightRest =>
                      cases rightRest with
                      | nil =>
                          exact valid_pair_eq projectionValid affineValid
                      | cons rightThird rightExtra =>
                          simp [Word.toList] at rightLength
          | cons leftThird leftExtra =>
              simp [Word.toList] at leftLength

/-! ## Unrestricted completeness -/

/-- Unrestricted derivational completeness for the exact Condition 8 basis.
The long stratum is the threshold lift of the complete affine theory; the
`N_3` factor separates singleton, pair, and long words, and the two short
strata are separated directly by the checked factors. -/
theorem complete : Condition8.DerivationalObligation := by
  intro identity firstValid affineValid
  have projectionValid :
      identity.SatisfiedBy projectionQuadraticThree.semigroup := by
    simpa [Condition8.firstFactor, Condition8.firstTable,
      SemigroupBasis.Generated.S3_4.table,
      projectionQuadraticThree] using firstValid
  have affineValid' :
      identity.SatisfiedBy affineParityFour.semigroup := by
    simpa [Condition8.affineFactor, Condition8.affineTable,
      SemigroupBasis.Generated.S4_96.table] using affineValid
  have capped := projectionValid_cappedLength identity projectionValid
  by_cases leftOne : identity.lhs.toList.length = 1
  · have rightOne : identity.rhs.toList.length = 1 := by
      omega
    rw [lengthOne_eq_of_projectionValid identity.lhs identity.rhs
      leftOne rightOne projectionValid]
    exact Derives.refl _
  · by_cases leftTwo : identity.lhs.toList.length = 2
    · have rightTwo : identity.rhs.toList.length = 2 := by
        omega
      rw [lengthTwo_eq_of_factorValid identity.lhs identity.rhs
        leftTwo rightTwo projectionValid affineValid']
      exact Derives.refl _
    · have leftLong : 3 ≤ identity.lhs.toList.length := by
        have positive := word_length_positive identity.lhs
        omega
      have rightLong : 3 ≤ identity.rhs.toList.length := by
        have positive := word_length_positive identity.rhs
        omega
      have affineDerivation :=
        affineParityFourBasis_complete.2 identity affineValid'
      have lifted := derivesThresholded affineDerivation
      rw [threshold_of_long identity.lhs leftLong,
        threshold_of_long identity.rhs rightLong] at lifted
      exact lifted

end SemigroupBasis.CoRoots.Order6LeeZhangCondition8Completeness
