import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.CoRoots.S5_505Family
import SemigroupBasis.Generated.S3_16

namespace SemigroupBasis.CoRoots.S6_9503

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_107
open SemigroupBasis.Examples

universe u

/-! ## Exact packet presentation -/

private def word (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def x : Word Nat := word 0 []
def xxxxx : Word Nat := word 0 [0, 0, 0, 0]
def xxy : Word Nat := word 0 [0, 1]
def xyx : Word Nat := word 0 [1, 0]
def yxx : Word Nat := word 1 [0, 0]

def powerLaw : Identity Nat := ⟨x, xxxxx⟩
def gatherLaw : Identity Nat := ⟨xxy, xyx⟩

/-- The packet basis in the canonical table orientation. -/
def basis : List (Identity Nat) :=
  [powerLaw, gatherLaw]

/-- The packet-source orientation, obtained by reversing every word. -/
def oppositeBasis : List (Identity Nat) :=
  [powerLaw, ⟨yxx, xyx⟩]

theorem reversedBasis_basis :
    reversedBasis basis = oppositeBasis := by
  decide

/-! ## Exact canonical table -/

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table:
`[[1,2,3,4,5,6],[2,1,4,3,5,6],[3,4,2,1,5,6],
  [4,3,1,2,5,6],[5,5,5,5,5,5],[6,6,6,6,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 2 3 4 5 right else
    if left = 1 then row6 1 0 3 2 4 5 right else
      if left = 2 then row6 2 3 1 0 4 5 right else
        if left = 3 then row6 3 2 0 1 4 5 right else
          if left = 4 then row6 4 4 4 4 4 4 right else
            row6 5 5 5 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- SHA-256 of the compact one-based JSON table above. -/
def tableSHA256 : String :=
  "dd52437ed2c838cb34cbf67bfd770fd3a5b9d45155d91aa0fd28ae0b40d783d9"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 2, 3, 4, 5, 6], [2, 1, 4, 3, 5, 6],
        [3, 4, 2, 1, 5, 6], [4, 3, 1, 2, 5, 6],
        [5, 5, 5, 5, 5, 5], [6, 6, 6, 6, 6, 6]] := by
  decide

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0, 0, 0]⟩⟩

def finiteGatherLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem finiteGatherLaw_map :
    finiteGatherLaw.map Fin.val = gatherLaw := rfl

/-- Direct finite verification of both packet laws on the exact table. -/
theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteGatherLaw_map]
    exact table.checkIdentityNat_sound finiteGatherLaw (by decide)

/-! ## Specialized positive-period-four normalizer -/

/-- Zero is retained as zero. Every positive multiplicity is represented by
one, two, three, or four copies according to its residue modulo four, with
four copies representing residue zero. -/
def retainedExponent (n : Nat) : Nat :=
  if n = 0 then 0 else if n % 4 = 0 then 4 else n % 4

@[simp]
theorem retainedExponent_zero : retainedExponent 0 = 0 := rfl

@[simp]
theorem retainedExponent_one : retainedExponent 1 = 1 := by
  simp [retainedExponent]

theorem retainedExponent_pos {n : Nat} (positive : 0 < n) :
    0 < retainedExponent n := by
  unfold retainedExponent
  split
  · omega
  · split <;> omega

theorem retainedExponent_le_four (n : Nat) :
    retainedExponent n ≤ 4 := by
  unfold retainedExponent
  split
  · omega
  · split <;> omega

/-- A gathered occurrence advances `1,2,3,4` cyclically, with the fifth
copy contracted back to one by `x = xxxxx`. -/
theorem retainedExponent_succ (n : Nat) :
    retainedExponent (n + 1) =
      if retainedExponent n < 4 then retainedExponent n + 1 else 1 := by
  by_cases hn0 : n = 0
  · subst n
    simp [retainedExponent]
  · by_cases h0 : n % 4 = 0
    · have hnext : (n + 1) % 4 = 1 := by omega
      simp [retainedExponent, hn0, h0, hnext]
    · by_cases h1 : n % 4 = 1
      · have hnext : (n + 1) % 4 = 2 := by omega
        simp [retainedExponent, hn0, h0, h1, hnext]
      · by_cases h2 : n % 4 = 2
        · have hnext : (n + 1) % 4 = 3 := by omega
          simp [retainedExponent, hn0, h0, h1, h2, hnext]
        · have h3 : n % 4 = 3 := by omega
          have hnext : (n + 1) % 4 = 0 := by omega
          simp [retainedExponent, hn0, h0, h1, h2, h3, hnext]

private def renameTwo (first second : Nat) : Nat → Nat
  | 0 => first
  | 1 => second
  | n + 2 => n + 2

/-- Five adjacent copies contract to one copy. -/
theorem derivesFiveToOne (letter : Nat) :
    ListDerives basis (List.replicate 5 letter) [letter] := by
  have base : Derives basis xxxxx x :=
    (Derives.fromBasis (e := powerLaw) (by
      simp [basis])).symm
  have substituted := Derives.subst base (fun _ => Word.singleton letter)
  simpa [powerLaw, x, xxxxx, word, Word.bind, Word.singleton] using
    ListDerives.ofWord substituted

private theorem derivesGatherWords (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have base : Derives basis xyx xxy :=
    (Derives.fromBasis (e := gatherLaw) (by
      simp [basis])).symm
  have substituted := Derives.subst base (fun
    | 0 => u
    | 1 => v
    | n + 2 => Word.singleton (n + 2))
  simpa [gatherLaw, xxy, xyx, word, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- One later occurrence can be gathered across an arbitrary middle while
preserving an arbitrary suffix. -/
theorem gatherOneDerivable
    (letter : Nat) (middle suffix : List Nat) :
    ListDerives basis
      (letter :: middle ++ letter :: suffix)
      (letter :: letter :: middle ++ suffix) := by
  cases middle with
  | nil =>
      exact ListDerives.refl _
  | cons next rest =>
      let middleWord := listWordOfCons next rest
      have core :=
        derivesGatherWords (Word.singleton letter) middleWord
      have coreList := ListDerives.ofWord core
      simpa [middleWord, listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using coreList.append suffix

def GatherStepDerivable : Prop :=
  ∀ seen : Nat, 0 < seen →
    ∀ (letter : Nat) (middle suffix : List Nat),
      ListDerives basis
        (List.replicate (retainedExponent seen) letter ++
          middle ++ letter :: suffix)
        (List.replicate (retainedExponent (seen + 1)) letter ++
          middle ++ suffix)

/-- The gather law supplies the transitions through states one to four; the
power law supplies the wrap from five adjacent copies back to one. -/
theorem gatherStepDerivable : GatherStepDerivable := by
  intro seen positive letter middle suffix
  let retained := retainedExponent seen
  have retainedPositive : 0 < retained :=
    retainedExponent_pos positive
  have retainedBound : retained ≤ 4 :=
    retainedExponent_le_four seen
  have retainedCases :
      retained = 1 ∨ retained = 2 ∨
        retained = 3 ∨ retained = 4 := by
    omega
  have moved :
      ListDerives basis
        (List.replicate retained letter ++
          middle ++ letter :: suffix)
        (List.replicate (retained + 1) letter ++
          middle ++ suffix) := by
    rcases retainedCases with h | h | h | h
    · rw [h]
      simpa [List.append_assoc] using
        gatherOneDerivable letter middle suffix
    · rw [h]
      simpa [List.append_assoc] using
        (gatherOneDerivable letter middle suffix).prepend [letter]
    · rw [h]
      simpa [List.append_assoc] using
        (gatherOneDerivable letter middle suffix).prepend
          [letter, letter]
    · rw [h]
      simpa [List.append_assoc] using
        (gatherOneDerivable letter middle suffix).prepend
          [letter, letter, letter]
  rw [retainedExponent_succ seen]
  by_cases below : retained < 4
  · rw [if_pos below]
    exact moved
  · rw [if_neg below]
    have retainedEq : retained = 4 := by omega
    have reduced :=
      (derivesFiveToOne letter).append (middle ++ suffix)
    rw [retainedEq] at moved
    have movedReduced := moved.trans <| by
      simpa [List.append_assoc] using reduced
    simpa [retained, retainedEq, List.append_assoc] using movedReduced

/-- Scan a suffix and gather every later copy of `letter` into its retained
front block. Other letters retain their relative order. -/
theorem gatherAll
    (step : GatherStepDerivable) :
    ∀ (seen : Nat), 0 < seen →
      ∀ (letter : Nat) (middle rest : List Nat),
        ListDerives basis
          (List.replicate (retainedExponent seen) letter ++ middle ++ rest)
          (List.replicate
              (retainedExponent (seen + rest.count letter)) letter ++
            middle ++ rest.filter (fun value => decide (value ≠ letter)))
  | seen, _, letter, middle, [] => by
      simp
      exact ListDerives.refl _
  | seen, positive, letter, middle, next :: rest => by
      by_cases equal : next = letter
      · subst next
        have first := step seen positive letter middle rest
        have remaining :=
          gatherAll step (seen + 1) (by omega) letter middle rest
        have countEq :
            seen + (letter :: rest).count letter =
              (seen + 1) + rest.count letter := by
          simp
          omega
        apply first.trans
        rw [countEq]
        simpa using remaining
      · have remaining :=
          gatherAll step seen positive letter (middle ++ [next]) rest
        simpa [equal, List.count_cons_of_ne equal,
          List.append_assoc] using remaining
termination_by
  _ _ _ _ rest => rest.length

private theorem filter_ne_length_lt_cons (letter : Nat) (rest : List Nat) :
    (rest.filter (fun value => decide (value ≠ letter))).length <
      (letter :: rest).length := by
  have bound :
      (rest.filter (fun value => decide (value ≠ letter))).length ≤
        rest.length :=
    List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le bound

/-- The flattened first-occurrence block normal form. Each first occurrence
starts one block, all later copies of that label are removed, and the block
length is its retained positive residue modulo four. -/
def normalList : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      List.replicate
          (retainedExponent ((letter :: rest).count letter)) letter ++
        normalList
          (rest.filter (fun value => decide (value ≠ letter)))
termination_by letters => letters.length
decreasing_by
  have bound :
      (rest.attach.filter
          (fun value => decide (value.val ≠ letter))).length ≤
        rest.attach.length :=
    List.filter_sublist.length_le
  simpa using Nat.lt_succ_of_le bound

/-- Every list derives to its positive-period-four first-occurrence block
normal form. -/
theorem derivesNormalize :
    ∀ letters : List Nat,
      ListDerives basis letters (normalList letters)
  | [] => by
      rw [normalList]
      exact ListDerives.refl []
  | letter :: rest => by
      have gathered :=
        gatherAll gatherStepDerivable 1 (by omega) letter [] rest
      have countEq :
          1 + rest.count letter =
            (letter :: rest).count letter := by
        simp
        omega
      have gathered' :
          ListDerives basis (letter :: rest)
            (List.replicate
                (retainedExponent
                  ((letter :: rest).count letter)) letter ++
              rest.filter (fun value => decide (value ≠ letter))) := by
        simpa [countEq] using gathered
      have tailNormal :=
        derivesNormalize
          (rest.filter (fun value => decide (value ≠ letter)))
      have prefixed :=
        tailNormal.prepend
          (List.replicate
            (retainedExponent
              ((letter :: rest).count letter)) letter)
      rw [normalList]
      exact gathered'.trans <| by
        simpa using prefixed
termination_by letters => letters.length
decreasing_by
  all_goals exact filter_ne_length_lt_cons letter rest

private theorem count_replicate_of_ne
    {letter selected : Nat} (different : selected ≠ letter) :
    ∀ n : Nat, (List.replicate n letter).count selected = 0
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm different),
        count_replicate_of_ne different n]

private theorem count_filter_ne_self
    (letter : Nat) (letters : List Nat) :
    (letters.filter
      (fun value => decide (value ≠ letter))).count letter = 0 := by
  apply List.count_eq_zero.mpr
  simp

private theorem count_filter_ne_of_ne
    {letter selected : Nat} (different : selected ≠ letter)
    (letters : List Nat) :
    (letters.filter
      (fun value => decide (value ≠ letter))).count selected =
        letters.count selected := by
  induction letters with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      by_cases equal : value = letter
      · subst value
        rw [List.filter_cons_of_neg (by simp),
          List.count_cons_of_ne (Ne.symm different)]
        exact inductionHypothesis
      · rw [List.filter_cons_of_pos (by simpa)]
        simp only [List.count_cons]
        rw [inductionHypothesis]

/-- Normalization retains exactly the specialized exponent of every source
multiplicity. -/
theorem normalList_count (selected : Nat) :
    ∀ letters : List Nat,
      (normalList letters).count selected =
        retainedExponent (letters.count selected)
  | [] => by
      simp [normalList]
  | letter :: rest => by
      simp only [normalList, List.count_append]
      by_cases equal : selected = letter
      · subst selected
        rw [List.count_replicate_self,
          normalList_count letter,
          count_filter_ne_self,
          retainedExponent_zero,
          Nat.add_zero]
      · rw [count_replicate_of_ne equal,
          normalList_count selected,
          count_filter_ne_of_ne equal,
          List.count_cons_of_ne (Ne.symm equal),
          Nat.zero_add]
termination_by letters => letters.length
decreasing_by
  all_goals exact filter_ne_length_lt_cons letter rest

private theorem filter_filter_ne_comm
    (keep : Nat → Bool) (selected : Nat) (letters : List Nat) :
    (letters.filter keep).filter
        (fun letter => decide (letter ≠ selected)) =
      (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro letter _
  exact Bool.and_comm _ _

private theorem filter_ne_then_keep_of_drop
    (keep : Nat → Bool) (selected : Nat)
    (dropped : ¬ keep selected) (letters : List Nat) :
    (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep =
      letters.filter keep := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro letter _
  by_cases equal : letter = selected
  · subst letter
    simp [dropped]
  · simp [equal]

theorem firstOccurrenceSequence_filter
    (keep : Nat → Bool) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters.filter keep) =
        (firstOccurrenceSequence letters).filter keep
  | [] => rfl
  | letter :: rest => by
      by_cases kept : keep letter
      · rw [List.filter_cons, if_pos kept,
          firstOccurrenceSequence, firstOccurrenceSequence,
          firstOccurrenceSequence_filter keep rest,
          List.filter_cons, if_pos kept]
        exact congrArg (List.cons letter) <|
          filter_filter_ne_comm keep letter
            (firstOccurrenceSequence rest)
      · rw [List.filter_cons, if_neg kept,
          firstOccurrenceSequence_filter keep rest,
          firstOccurrenceSequence,
          List.filter_cons, if_neg kept]
        exact
          (filter_ne_then_keep_of_drop
            keep letter kept (firstOccurrenceSequence rest)).symm

/-- First-occurrence order and retained multiplicities determine the normal
list literally. -/
theorem normalList_eq_of_invariants :
    ∀ (left right : List Nat),
      firstOccurrenceSequence left = firstOccurrenceSequence right →
      (∀ selected,
        retainedExponent (left.count selected) =
          retainedExponent (right.count selected)) →
      normalList left = normalList right
  | [], [], _, _ => rfl
  | [], _ :: _, order, _ => by
      simp [firstOccurrenceSequence] at order
  | _ :: _, [], order, _ => by
      simp [firstOccurrenceSequence] at order
  | letter :: rest, rightLetter :: rightRest, order, counts => by
      have heads : letter = rightLetter :=
        (List.cons.inj order).1
      subst rightLetter
      have tailOrder :
          firstOccurrenceSequence
              (rest.filter
                (fun value => decide (value ≠ letter))) =
            firstOccurrenceSequence
              (rightRest.filter
                (fun value => decide (value ≠ letter))) := by
        rw [firstOccurrenceSequence_filter,
          firstOccurrenceSequence_filter]
        exact (List.cons.inj order).2
      have tailCounts :
          ∀ selected,
            retainedExponent
                ((rest.filter
                  (fun value => decide (value ≠ letter))).count
                    selected) =
              retainedExponent
                ((rightRest.filter
                  (fun value => decide (value ≠ letter))).count
                    selected) := by
        intro selected
        by_cases equal : selected = letter
        · subst selected
          rw [count_filter_ne_self, count_filter_ne_self]
        · rw [count_filter_ne_of_ne equal,
            count_filter_ne_of_ne equal]
          simpa [List.count_cons_of_ne (Ne.symm equal)] using
            counts selected
      have tailsEqual :=
        normalList_eq_of_invariants
          (rest.filter (fun value => decide (value ≠ letter)))
          (rightRest.filter (fun value => decide (value ≠ letter)))
          tailOrder tailCounts
      simp only [normalList]
      rw [counts letter, tailsEqual]
termination_by left _ => left.length
decreasing_by
  exact filter_ne_length_lt_cons letter rest

/-- Complete syntactic invariant for the canonical two-law basis. -/
theorem derivesOfInvariants
    (left right : Word Nat)
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (counts : ∀ selected,
      retainedExponent (left.toList.count selected) =
        retainedExponent (right.toList.count selected)) :
    Derives basis left right := by
  have leftNormal := derivesNormalize left.toList
  have rightNormal := derivesNormalize right.toList
  have normalsEqual :=
    normalList_eq_of_invariants left.toList right.toList order counts
  rw [normalsEqual] at leftNormal
  have listed := leftNormal.trans rightNormal.symm
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact listed.toWord

/-- Generic completeness interface for models that separate first-occurrence
order and the specialized positive-period-four exponent. -/
theorem basisFor_of_invariants
    {S : Type u} (candidate : Semigroup S)
    (basisModels : Models candidate basis)
    (separatesOrder : ∀ identity : Identity Nat,
      identity.SatisfiedBy candidate →
        firstOccurrenceSequence identity.lhs.toList =
          firstOccurrenceSequence identity.rhs.toList)
    (separatesCounts : ∀ identity : Identity Nat,
      identity.SatisfiedBy candidate →
        ∀ selected,
          retainedExponent (identity.lhs.toList.count selected) =
            retainedExponent (identity.rhs.toList.count selected)) :
    BasisFor candidate basis := by
  refine ⟨basisModels, ?_⟩
  intro identity valid
  exact derivesOfInvariants identity.lhs identity.rhs
    (separatesOrder identity valid)
    (separatesCounts identity valid)

/-! ## Embedded completeness invariants -/

/-- Explorer embedding `S5_506 ↪ S6_9503`, one-based map
`[1,2,3,4,5]`. -/
def e4 :
    Embedding
      SemigroupBasis.CoRoots.S5_505Family.S5_506.table.semigroup
      table.semigroup where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else
        if value = 2 then (2 : Fin 6) else
          if value = 3 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def e4OutputsOneBased : List Nat :=
  List.ofFn fun value : Fin 5 => (e4.toFun value).val + 1

theorem e4OutputsOneBased_certificate :
    e4OutputsOneBased = [1, 2, 3, 4, 5] := by
  decide

/-- Explorer embedding `S3_16 ↪ S6_9503`, one-based map `[5,1,6]`. -/
def eFO :
    Embedding SemigroupBasis.Generated.S3_16.table.semigroup
      table.semigroup where
  toFun := fun value : Fin 3 =>
    if value = 0 then (4 : Fin 6) else
      if value = 1 then (0 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def eFOOutputsOneBased : List Nat :=
  List.ofFn fun value : Fin 3 => (eFO.toFun value).val + 1

theorem eFOOutputsOneBased_certificate :
    eFOOutputsOneBased = [5, 1, 6] := by
  decide

theorem retainedExponent_eq_of_samePositiveModFour
    {left right : Word Nat}
    (same : SamePositiveModFour left right) :
    ∀ selected,
      retainedExponent (left.toList.count selected) =
        retainedExponent (right.toList.count selected) := by
  intro selected
  by_cases leftZero : left.toList.count selected = 0
  · have leftNotMem : selected ∉ left.toList :=
      List.count_eq_zero.mp leftZero
    have rightNotMem : selected ∉ right.toList := by
      intro rightMem
      exact leftNotMem ((same.1 selected).mpr rightMem)
    have rightZero : right.toList.count selected = 0 :=
      List.count_eq_zero.mpr rightNotMem
    simp [leftZero, rightZero]
  · have leftMem : selected ∈ left.toList :=
      List.count_pos_iff.mp (Nat.pos_of_ne_zero leftZero)
    have rightMem : selected ∈ right.toList :=
      (same.1 selected).mp leftMem
    have rightNonzero : right.toList.count selected ≠ 0 :=
      Nat.ne_of_gt (List.count_pos_iff.mpr rightMem)
    simp [retainedExponent, leftZero, rightNonzero, same.2 selected]

theorem validRetainedExponents
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ selected,
      retainedExponent (identity.lhs.toList.count selected) =
        retainedExponent (identity.rhs.toList.count selected) :=
  retainedExponent_eq_of_samePositiveModFour <|
    SemigroupBasis.CoRoots.S5_505Family.S5_506.valid_samePositiveModFour
      identity (e4.pullback_identity identity valid)

theorem validFirstOccurrenceSequence
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList := by
  exact
    SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
        identity (by
          simpa [SemigroupBasis.Generated.S3_16.table,
            leftRegularBandThree] using
              (eFO.pullback_identity identity valid))

/-! ## Unconditional endpoints -/

theorem representative_basis :
    BasisFor table.semigroup basis :=
  basisFor_of_invariants table.semigroup models
    validFirstOccurrenceSequence validRetainedExponents

/-- The source packet is opposite-oriented; reversal transports the
canonical endpoint to its exact packet-source orientation. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  rw [← reversedBasis_basis]
  exact representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.S6_9503
