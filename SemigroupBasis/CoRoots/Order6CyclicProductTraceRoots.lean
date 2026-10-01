import SemigroupBasis.Examples.CyclicFive
import SemigroupBasis.Examples.NullTwo
import SemigroupBasis.Subdirect

namespace SemigroupBasis.CoRoots.Order6CyclicProductTraceRoots

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Packet basis and provenance

The authenticated packet is opposite-oriented and displays
`yx = xy`, `xxxxx = yyyyy`, and `zyxxxxx = zy`.  Both catalogue
representatives are commutative one-point inflations of `C5`: their common
identity theory is the intersection of the theories of `C5` and the
two-element null semigroup.
-/

def packetRecordType : String :=
  "order6_power_productized_inflation_population"

def packetProofRoute : String :=
  "cyclic-group-product-only-normal-forms"

def packetSourceOrientation : String := "opposite"

def packetSHA256 : String :=
  "6600b82d1dfb18a6ad6ec71cabc13716029d748c4ff3f23d168df88eee7ddd69"

def packetPopulationSHA256 : String :=
  "dbc72b10a727bd45ee575ec6c84c856aebb85d15d5878ae6278546c406ed3401"

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def yx : Word Nat := w 1 [0]
def xy : Word Nat := w 0 [1]
def xxxxx : Word Nat := w 0 [0, 0, 0, 0]
def yyyyy : Word Nat := w 1 [1, 1, 1, 1]
def zyxxxxx : Word Nat := w 2 [1, 0, 0, 0, 0, 0]
def zy : Word Nat := w 2 [1]

def commutativityLaw : Identity Nat := ⟨yx, xy⟩
def commonFifthLaw : Identity Nat := ⟨xxxxx, yyyyy⟩
def productCancellationLaw : Identity Nat := ⟨zyxxxxx, zy⟩

/-- The exact three-law basis displayed by the authenticated packet. -/
def basis : List (Identity Nat) :=
  [commutativityLaw, commonFifthLaw, productCancellationLaw]

private def fifthPower (word : Word Nat) : Word Nat :=
  ((((word ++ word) ++ word) ++ word) ++ word)

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def instantiateThreeWords
    (xWord yWord zWord : Word Nat) : Nat → Word Nat
  | 0 => xWord
  | 1 => yWord
  | 2 => zWord
  | n + 3 => Word.singleton (n + 3)

theorem derivesCommutativity (left right : Word Nat) :
    Derives basis (left ++ right) (right ++ left) := by
  have base : Derives basis yx xy :=
    Derives.fromBasis (e := commutativityLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords right left (Word.singleton 2))
  simpa [commutativityLaw, yx, xy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton] using substituted

theorem derivesCommonFifth (left right : Word Nat) :
    Derives basis (fifthPower left) (fifthPower right) := by
  have base : Derives basis xxxxx yyyyy :=
    Derives.fromBasis (e := commonFifthLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords left right (Word.singleton 2))
  simpa [commonFifthLaw, xxxxx, yyyyy, w, fifthPower,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Remove a fifth power after two nonempty product blocks. -/
theorem derivesStripFifth
    (power front suffix : Word Nat) :
    Derives basis
      ((front ++ suffix) ++ fifthPower power)
      (front ++ suffix) := by
  have base : Derives basis zyxxxxx zy :=
    Derives.fromBasis (e := productCancellationLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords power suffix front)
  simpa [productCancellationLaw, zyxxxxx, zy, w, fifthPower,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The packet cancellation law simulates the `C5` cancellation axiom after
a fixed nonempty prefix and a nonempty suffix. -/
theorem derivesContextualCancelFifth
    (power front suffix : Word Nat) :
    Derives basis
      (front ++ (fifthPower power ++ suffix))
      (front ++ suffix) := by
  have commute :=
    Derives.prepend front
      (derivesCommutativity (fifthPower power) suffix)
  have cancel := derivesStripFifth power front suffix
  exact Derives.trans
    (by simpa [Word.append_assoc] using commute)
    (by simpa [Word.append_assoc] using cancel)

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay any derivation for `C5` after a fixed product of two nonempty
words.  The fixed product is precisely the residual context required by
`zyxxxxx = zy`. -/
theorem liftCyclicFive
    {left right : Word Nat}
    (derivation : Derives cyclicFiveBasis left right)
    (first second : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      ((first ++ second) ++ left.bind substitution)
      ((first ++ second) ++ right.bind substitution) := by
  induction derivation generalizing first second substitution with
  | fromBasis member =>
      simp only [cyclicFiveBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · have commute :=
          derivesCommutativity (substitution 0) (substitution 1)
        simpa [cyclicFiveCommutativityLaw, cyclicFiveXY,
          cyclicFiveYX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            Derives.prepend (first ++ second) commute
      · have cancel :=
          derivesContextualCancelFifth (substitution 0)
            (first ++ second) (substitution 1)
        simpa [cyclicFiveCancellationLaw, cyclicFiveXXXXXY,
          cyclicFiveY, fifthPower, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using cancel
  | refl =>
      exact Derives.refl _
  | symm _ inductionHypothesis =>
      exact Derives.symm
        (inductionHypothesis first second substitution)
  | trans _ _ firstHypothesis secondHypothesis =>
      exact Derives.trans
        (firstHypothesis first second substitution)
        (secondHypothesis first second substitution)
  | prepend front _ inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        inductionHypothesis first
          (second ++ front.bind substitution) substitution
  | appendRight _ suffix inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis first second substitution)
          (suffix.bind substitution)
  | subst _ next inductionHypothesis =>
      simpa [bind_bind] using
        inductionHypothesis first second
          (fun letter => (next letter).bind substitution)

private def marker : Word Nat := Word.singleton 0

private def markerTriple : Word Nat :=
  (marker ++ marker) ++ marker

private theorem derivesMarkerExpansion
    (word : Word Nat) (long : 2 ≤ word.toList.length) :
    Derives basis word (fifthPower marker ++ word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at long
      | cons next rest =>
          let current := wordOfCons head (next :: rest)
          let suffix := wordOfCons next rest
          have inserted :=
            (derivesStripFifth marker (Word.singleton head) suffix).symm
          have rotated :=
            derivesCommutativity current (fifthPower marker)
          exact Derives.trans
            (by
              simpa [current, suffix, wordOfCons, Word.singleton,
                Word.append, Word.append_assoc] using inserted)
            (by simpa [current] using rotated)

/-- Long identities valid in `C5` are derivable from the packet basis. -/
theorem derivesLongCyclicFive
    {left right : Word Nat}
    (derivation : Derives cyclicFiveBasis left right)
    (leftLong : 2 ≤ left.toList.length)
    (rightLong : 2 ≤ right.toList.length) :
    Derives basis left right := by
  have expandedLeft := derivesMarkerExpansion left leftLong
  have expandedRight := derivesMarkerExpansion right rightLong
  have marked := Derives.prepend markerTriple derivation
  have lifted := liftCyclicFive marked marker marker Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  exact Derives.trans expandedLeft <|
    Derives.trans
      (by
        simpa [markerTriple, fifthPower, Word.append_assoc] using lifted)
      (Derives.symm expandedRight)

/-! ## Factor-intersection completeness -/

private theorem cyclicFiveModels :
    Models cyclicFive.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · have derivation : Derives cyclicFiveBasis yx xy := by
      simpa [yx, xy, w, Word.singleton, Word.append] using
        cyclicFiveDerivesCommutativity
          (Word.singleton 1) (Word.singleton 0)
    exact fun valuation =>
      derivation.sound cyclicFiveBasis_models valuation
  · have derivation : Derives cyclicFiveBasis xxxxx yyyyy := by
      simpa [xxxxx, yyyyy, w, Word.singleton, Word.append,
        Word.append_assoc] using
          cyclicFiveDerivesCommonFifth
            (Word.singleton 0) (Word.singleton 1)
    exact fun valuation =>
      derivation.sound cyclicFiveBasis_models valuation
  · have swap :=
      cyclicFiveDerivesCommutativity zy
        (fifthPower (Word.singleton 0))
    have cancel :=
      cyclicFiveDerivesCancelFifth (Word.singleton 0) zy
    have derivation : Derives cyclicFiveBasis zyxxxxx zy :=
      Derives.trans
        (by
          simpa [zyxxxxx, zy, w, fifthPower, Word.singleton,
            Word.append, Word.append_assoc] using swap)
        (by
          simpa [zy, w, fifthPower, Word.singleton, Word.append,
            Word.append_assoc] using cancel)
    exact fun valuation =>
      derivation.sound cyclicFiveBasis_models valuation

private theorem nullTwoModels :
    Models nullTwo.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    intro valuation <;> rfl

private theorem nullValid_eq_or_long
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy nullTwo.semigroup) :
    identity.lhs = identity.rhs ∨
      (2 ≤ identity.lhs.toList.length ∧
        2 ≤ identity.rhs.toList.length) := by
  cases identity with
  | mk left right =>
      cases left with
      | mk leftHead leftTail =>
          cases leftTail with
          | nil =>
              cases right with
              | mk rightHead rightTail =>
                  cases rightTail with
                  | nil =>
                      have heads : leftHead = rightHead := by
                        apply Decidable.byContradiction
                        intro different
                        let valuation : Nat → Fin 2 := fun letter =>
                          if letter = leftHead then 1 else 0
                        have evaluated := valid valuation
                        simp [Semigroup.eval, valuation,
                          Ne.symm different] at evaluated
                      left
                      cases heads
                      rfl
                  | cons rightNext rightRest =>
                      let valuation : Nat → Fin 2 := fun _ => 1
                      have evaluated := valid valuation
                      rw [nullTwo_eval_product] at evaluated
                      simp [Semigroup.eval, valuation] at evaluated
          | cons leftNext leftRest =>
              cases right with
              | mk rightHead rightTail =>
                  cases rightTail with
                  | nil =>
                      let valuation : Nat → Fin 2 := fun _ => 1
                      have evaluated := valid valuation
                      rw [nullTwo_eval_product] at evaluated
                      simp [Semigroup.eval, valuation] at evaluated
                  | cons rightNext rightRest =>
                      right
                      constructor <;> simp [Word.toList]

/-- Complete basis for the intersection of the cyclic-group and null-semigroup
identity theories. -/
theorem intersectionBasis :
    IntersectionBasis cyclicFive.semigroup nullTwo.semigroup basis where
  leftModels := cyclicFiveModels
  rightModels := nullTwoModels
  complete := by
    intro identity cyclicValid nullValid
    rcases nullValid_eq_or_long identity nullValid with equal | long
    · rw [equal]
      exact Derives.refl _
    · exact derivesLongCyclicFive
        (cyclicFiveBasis_complete.2 identity cyclicValid)
        long.1 long.2

/-! ## Exact order-six tables and subdirect endpoint proofs -/

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

namespace S6_14999

/-- Exact one-based catalogue table:
`[[1,1,3,4,5,6],[1,1,3,4,5,6],[3,3,4,6,1,5],
  [4,4,6,5,3,1],[5,5,1,3,6,4],[6,6,5,1,4,3]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 3 4 5 right else
    if left = 1 then row6 0 0 2 3 4 5 right else
      if left = 2 then row6 2 2 3 5 0 4 right else
        if left = 3 then row6 3 3 5 4 2 0 right else
          if left = 4 then row6 4 4 0 2 5 3 right else
            row6 5 5 4 0 3 2 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8d72e5b7a6de359edb1095423fc4965234b39c38f97fdb12be168ff03b3eb0b0"

def packetCaseSHA256 : String :=
  "da03c8bf4bbb6bae24745fb5457f5bdb79f143fcfa61948cf45a89ceaf5ac259"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 3, 4, 5, 6], [1, 1, 3, 4, 5, 6],
        [3, 3, 4, 6, 1, 5], [4, 4, 6, 5, 3, 1],
        [5, 5, 1, 3, 6, 4], [6, 6, 5, 1, 4, 3]] := by
  decide

def cyclicMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0 else
    if value = 1 then 0 else
      if value = 2 then 1 else
        if value = 3 then 2 else
          if value = 4 then 3 else 4

def cyclicPreimage (value : Fin 5) : Fin 6 :=
  if value = 0 then 0 else
    if value = 1 then 2 else
      if value = 2 then 3 else
        if value = 3 then 4 else 5

def cyclicQuotient :
    SplitSurjection table.semigroup cyclicFive.semigroup where
  toFun := cyclicMap
  map_mul := by
    intro left right
    exact by decide +revert
  preimage := cyclicPreimage
  right_inverse := by
    intro value
    exact by decide +revert

def nullMap (value : Fin 6) : Fin 2 :=
  if value = 1 then 1 else 0

def nullPreimage (value : Fin 2) : Fin 6 :=
  if value = 0 then 0 else 1

def nullQuotient :
    SplitSurjection table.semigroup nullTwo.semigroup where
  toFun := nullMap
  map_mul := by
    intro left right
    exact by decide +revert
  preimage := nullPreimage
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup cyclicFive.semigroup
      nullTwo.semigroup where
  left := cyclicQuotient
  right := nullQuotient
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis :
    BasisFor table.semigroup basis :=
  intersectionBasis.basisFor subdirectPair

/-- The source orientation recorded in the packet. -/
def sourceMul (left right : Fin 6) : Fin 6 := mul right left

def sourceTable : FiniteTable where
  order := 6
  mul := sourceMul
  assoc := by decide

theorem tableOpposite_eq_source :
    table.semigroup.opposite = sourceTable.semigroup := by
  unfold table sourceTable sourceMul FiniteTable.semigroup
    Semigroup.opposite
  rfl

def sourceCyclicQuotient :
    SplitSurjection sourceTable.semigroup cyclicFive.semigroup where
  toFun := cyclicMap
  map_mul := by
    intro left right
    exact by decide +revert
  preimage := cyclicPreimage
  right_inverse := by
    intro value
    exact by decide +revert

def sourceNullQuotient :
    SplitSurjection sourceTable.semigroup nullTwo.semigroup where
  toFun := nullMap
  map_mul := by
    intro left right
    exact by decide +revert
  preimage := nullPreimage
  right_inverse := by
    intro value
    exact by decide +revert

def sourceSubdirectPair :
    SubdirectPair sourceTable.semigroup cyclicFive.semigroup
      nullTwo.semigroup where
  left := sourceCyclicQuotient
  right := sourceNullQuotient
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

/-- Unconditional endpoint on the packet's opposite source orientation. -/
theorem source_basis :
    BasisFor sourceTable.semigroup basis :=
  intersectionBasis.basisFor sourceSubdirectPair

end S6_14999

namespace S6_15973

/-- Exact one-based catalogue table:
`[[1,2,3,4,5,5],[2,3,5,1,4,4],[3,5,4,2,1,1],
  [4,1,2,5,3,3],[5,4,1,3,2,2],[5,4,1,3,2,2]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 2 3 4 4 right else
    if left = 1 then row6 1 2 4 0 3 3 right else
      if left = 2 then row6 2 4 3 1 0 0 right else
        if left = 3 then row6 3 0 1 4 2 2 right else
          if left = 4 then row6 4 3 0 2 1 1 right else
            row6 4 3 0 2 1 1 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ad9a2b75e89814140870f213e3db363df17f845d2ddce6770f26942dd9e5dae2"

def packetCaseSHA256 : String :=
  "ab47939d5f2fcc3303ef5bdb27c75cc448175dfceb55df0495b06940c2d3a1bc"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 2, 3, 4, 5, 5], [2, 3, 5, 1, 4, 4],
        [3, 5, 4, 2, 1, 1], [4, 1, 2, 5, 3, 3],
        [5, 4, 1, 3, 2, 2], [5, 4, 1, 3, 2, 2]] := by
  decide

def cyclicMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 2 else
        if value = 3 then 3 else 4

def cyclicPreimage (value : Fin 5) : Fin 6 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 2 else
        if value = 3 then 3 else 4

def cyclicQuotient :
    SplitSurjection table.semigroup cyclicFive.semigroup where
  toFun := cyclicMap
  map_mul := by
    intro left right
    exact by decide +revert
  preimage := cyclicPreimage
  right_inverse := by
    intro value
    exact by decide +revert

def nullMap (value : Fin 6) : Fin 2 :=
  if value = 5 then 1 else 0

def nullPreimage (value : Fin 2) : Fin 6 :=
  if value = 0 then 0 else 5

def nullQuotient :
    SplitSurjection table.semigroup nullTwo.semigroup where
  toFun := nullMap
  map_mul := by
    intro left right
    exact by decide +revert
  preimage := nullPreimage
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup cyclicFive.semigroup
      nullTwo.semigroup where
  left := cyclicQuotient
  right := nullQuotient
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis :
    BasisFor table.semigroup basis :=
  intersectionBasis.basisFor subdirectPair

/-- The source orientation recorded in the packet. -/
def sourceMul (left right : Fin 6) : Fin 6 := mul right left

def sourceTable : FiniteTable where
  order := 6
  mul := sourceMul
  assoc := by decide

theorem tableOpposite_eq_source :
    table.semigroup.opposite = sourceTable.semigroup := by
  unfold table sourceTable sourceMul FiniteTable.semigroup
    Semigroup.opposite
  rfl

def sourceCyclicQuotient :
    SplitSurjection sourceTable.semigroup cyclicFive.semigroup where
  toFun := cyclicMap
  map_mul := by
    intro left right
    exact by decide +revert
  preimage := cyclicPreimage
  right_inverse := by
    intro value
    exact by decide +revert

def sourceNullQuotient :
    SplitSurjection sourceTable.semigroup nullTwo.semigroup where
  toFun := nullMap
  map_mul := by
    intro left right
    exact by decide +revert
  preimage := nullPreimage
  right_inverse := by
    intro value
    exact by decide +revert

def sourceSubdirectPair :
    SubdirectPair sourceTable.semigroup cyclicFive.semigroup
      nullTwo.semigroup where
  left := sourceCyclicQuotient
  right := sourceNullQuotient
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

/-- Unconditional endpoint on the packet's opposite source orientation. -/
theorem source_basis :
    BasisFor sourceTable.semigroup basis :=
  intersectionBasis.basisFor sourceSubdirectPair

end S6_15973

end SemigroupBasis.CoRoots.Order6CyclicProductTraceRoots
