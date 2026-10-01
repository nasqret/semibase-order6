import SemigroupBasis.CoRoots.S5_841CompletenessBridge
import SemigroupBasis.CoRoots.S5_841QuadraticSwap
import SemigroupBasis.Examples.CommutativePeriodTwoFromTwo
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SemigroupBasis.CoRoots.S6_8874

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xhytxy : Word Nat := w 0 [1, 2, 3, 0, 2]
def xhytyx : Word Nat := w 0 [1, 2, 3, 2, 0]
def xhyxy : Word Nat := w 0 [1, 2, 0, 2]
def xhyyx : Word Nat := w 0 [1, 2, 2, 0]
def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyzx : Word Nat := w 0 [0, 1, 2, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xyhxty : Word Nat := w 0 [2, 1, 0, 3, 2]
def yxhxty : Word Nat := w 2 [0, 1, 0, 3, 2]
def xyhxy : Word Nat := w 0 [2, 1, 0, 2]
def yxhxy : Word Nat := w 2 [0, 1, 0, 2]
def xytxy : Word Nat := w 0 [2, 3, 0, 2]
def xytyx : Word Nat := w 0 [2, 3, 2, 0]
def xyxty : Word Nat := w 0 [2, 0, 3, 2]
def yxxty : Word Nat := w 2 [0, 0, 3, 2]
def xyxy : Word Nat := w 0 [2, 0, 2]
def xyyx : Word Nat := w 0 [2, 2, 0]
def yxxy : Word Nat := w 2 [0, 0, 2]

def sortGeneralRightLaw : Identity Nat := ⟨xhytxy, xhytyx⟩
def sortFinalGapRightLaw : Identity Nat := ⟨xhyxy, xhyyx⟩
def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def sandwichContractionLaw : Identity Nat := ⟨xxxyx, xyx⟩
def squareTransportLaw : Identity Nat := ⟨xxyx, xyxx⟩
def gatherGeneralLaw : Identity Nat := ⟨xxyzx, xyxzx⟩
def sortGeneralLeftLaw : Identity Nat := ⟨xyhxty, yxhxty⟩
def sortFinalGapLeftLaw : Identity Nat := ⟨xyhxy, yxhxy⟩
def sortInitialGapRightLaw : Identity Nat := ⟨xytxy, xytyx⟩
def sortInitialGapLeftLaw : Identity Nat := ⟨xyxty, yxxty⟩
def sortBothEmptyRightLaw : Identity Nat := ⟨xyxy, xyyx⟩
def sortBothEmptyLeftLaw : Identity Nat := ⟨xyxy, yxxy⟩

/-- Lee--Li Proposition 5.3 at `n = 2`, with every starred deletion
expanded and retained in the exact packet order for `S6_8874`. -/
def basis : List (Identity Nat) :=
  [sortGeneralRightLaw, sortFinalGapRightLaw, powerLaw,
    sandwichContractionLaw, squareTransportLaw, gatherGeneralLaw,
    sortGeneralLeftLaw, sortFinalGapLeftLaw, sortInitialGapRightLaw,
    sortInitialGapLeftLaw, sortBothEmptyRightLaw,
    sortBothEmptyLeftLaw]

def oppositeBasis : List (Identity Nat) := reversedBasis basis

def packetSHA256 : String :=
  "b9ace4eaa29046abaec59a3f6ecba5bf72bc6fa310c0121eb4d1989cb01fa960"

/-! ## Exact catalogue table -/

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 0 0 0 right else
    if left = 1 then row6 0 0 2 0 1 1 right else
      if left = 2 then row6 2 2 0 2 2 2 right else
        if left = 3 then row6 0 1 2 3 1 3 right else
          if left = 4 then row6 0 0 2 0 4 4 right else
            row6 0 1 2 3 4 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (table.mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 3, 1, 1, 1], [1, 1, 3, 1, 2, 2],
        [3, 3, 1, 3, 3, 3], [1, 2, 3, 4, 2, 4],
        [1, 1, 3, 1, 5, 5], [1, 2, 3, 4, 5, 6]] := by
  decide

def tableSHA256 : String :=
  "abb9e6fcd14abab35614ebe35d2e315172581e6b210b5d36d08c97cdb69d4ea7"

/-! ## Finite soundness -/

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

private theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

private theorem m20Models :
    Models SemigroupBasis.CoRoots.S5_841.table.semigroup basis :=
  models_of_finite_checks SemigroupBasis.CoRoots.S5_841.table (by decide)

private theorem cyclicModels : Models cyclicTwo.semigroup basis :=
  models_of_finite_checks cyclicTwo (by decide)

/-! ## Primitive Lee--Li substitutions -/

private abbrev ListDerives (left right : List Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis left right

private theorem publishedM20Models :
    Models S5_841.publishedM20Table.semigroup basis :=
  models_of_finite_checks S5_841.publishedM20Table (by decide)

private theorem publishedM20Mul_leftIdentity (value : Fin 5) :
    S5_841.publishedM20Mul 1 value = value := by
  decide +revert

private theorem m20ListEval_cons_eq_eval
    (valuation : Nat → Fin 5) (head : Nat) (tail : List Nat) :
    S5_841.m20ListEval valuation (head :: tail) =
      S5_841.publishedM20Table.semigroup.eval valuation
        (S5_107.listWordOfCons head tail) := by
  unfold S5_841.m20ListEval S5_107.listWordOfCons
  change
    tail.foldl
        (fun current letter =>
          S5_841.publishedM20Mul current (valuation letter))
        (S5_841.publishedM20Mul 1 (valuation head)) =
      tail.foldl
        (fun current letter =>
          S5_841.publishedM20Mul current (valuation letter))
        (valuation head)
  rw [publishedM20Mul_leftIdentity]

/-- Every Condition 6 list derivation is sound in the `M20` factor. -/
private theorem m20EquivalentOfListDerives
    {left right : List Nat} (derivation : ListDerives left right) :
    S5_841.M20ListEquivalent left right := by
  cases derivation with
  | empty => exact fun _ => rfl
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      intro valuation
      rw [m20ListEval_cons_eq_eval, m20ListEval_cons_eq_eval]
      exact wordDerivation.sound publishedM20Models valuation

private def instantiateFiveWords
    (x h y t z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => h
  | 2 => y
  | 3 => t
  | 4 => z
  | n + 5 => Word.singleton (n + 5)

private theorem basisSortGeneralRight :
    Derives basis xhytxy xhytyx :=
  Derives.fromBasis (e := sortGeneralRightLaw) (by simp [basis])

private theorem basisSortFinalGapRight :
    Derives basis xhyxy xhyyx :=
  Derives.fromBasis (e := sortFinalGapRightLaw) (by simp [basis])

private theorem basisSortGeneralLeft :
    Derives basis xyhxty yxhxty :=
  Derives.fromBasis (e := sortGeneralLeftLaw) (by simp [basis])

private theorem basisSortFinalGapLeft :
    Derives basis xyhxy yxhxy :=
  Derives.fromBasis (e := sortFinalGapLeftLaw) (by simp [basis])

private theorem basisSortInitialGapRight :
    Derives basis xytxy xytyx :=
  Derives.fromBasis (e := sortInitialGapRightLaw) (by simp [basis])

private theorem basisSortInitialGapLeft :
    Derives basis xyxty yxxty :=
  Derives.fromBasis (e := sortInitialGapLeftLaw) (by simp [basis])

private theorem basisSortBothEmptyRight :
    Derives basis xyxy xyyx :=
  Derives.fromBasis (e := sortBothEmptyRightLaw) (by simp [basis])

private theorem basisSortBothEmptyLeft :
    Derives basis xyxy yxxy :=
  Derives.fromBasis (e := sortBothEmptyLeftLaw) (by simp [basis])

private theorem basisPower : Derives basis xx xxxx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem basisSandwichContraction :
    Derives basis xxxyx xyx :=
  Derives.fromBasis (e := sandwichContractionLaw) (by simp [basis])

private theorem basisSquareTransport :
    Derives basis xxyx xyxx :=
  Derives.fromBasis (e := squareTransportLaw) (by simp [basis])

private theorem basisGatherGeneral :
    Derives basis xxyzx xyxzx :=
  Derives.fromBasis (e := gatherGeneralLaw) (by simp [basis])

private theorem derivesFourToTwo (x : Word Nat) :
    Derives basis (((x ++ x) ++ x) ++ x) (x ++ x) := by
  have substituted :=
    Derives.subst basisPower (instantiateFiveWords x x x x x)
  simpa [xx, xxxx, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

private theorem derivesSandwichContraction
    (x y : Word Nat) :
    Derives basis ((((x ++ x) ++ x) ++ y) ++ x)
      ((x ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSandwichContraction
      (instantiateFiveWords x y y y y)
  simpa [xxxyx, xyx, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesSquareTransport (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ x)
      (((x ++ y) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisSquareTransport
      (instantiateFiveWords x y y y y)
  simpa [xxyx, xyxx, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesGatherGeneral
    (x y z : Word Nat) :
    Derives basis ((((x ++ y) ++ x) ++ z) ++ x)
      ((((x ++ x) ++ y) ++ z) ++ x) := by
  have substituted :=
    Derives.subst basisGatherGeneral
      (instantiateFiveWords x y z y z)
  simpa [xxyzx, xyxzx, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

private theorem derivesSortGeneralLeft
    (x y h t : Word Nat) :
    Derives basis (((((x ++ y) ++ h) ++ x) ++ t) ++ y)
      (((((y ++ x) ++ h) ++ x) ++ t) ++ y) := by
  have substituted :=
    Derives.subst basisSortGeneralLeft
      (instantiateFiveWords x h y t t)
  simpa [xyhxty, yxhxty, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesSortFinalGapLeft
    (x y h : Word Nat) :
    Derives basis ((((x ++ y) ++ h) ++ x) ++ y)
      ((((y ++ x) ++ h) ++ x) ++ y) := by
  have substituted :=
    Derives.subst basisSortFinalGapLeft
      (instantiateFiveWords x h y h h)
  simpa [xyhxy, yxhxy, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesSortInitialGapLeft
    (x y t : Word Nat) :
    Derives basis ((((x ++ y) ++ x) ++ t) ++ y)
      ((((y ++ x) ++ x) ++ t) ++ y) := by
  have substituted :=
    Derives.subst basisSortInitialGapLeft
      (instantiateFiveWords x x y t t)
  simpa [xyxty, yxxty, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesSortBothEmptyLeft (x y : Word Nat) :
    Derives basis (((x ++ y) ++ x) ++ y)
      (((y ++ x) ++ x) ++ y) := by
  have substituted :=
    Derives.subst basisSortBothEmptyLeft
      (instantiateFiveWords x x y x y)
  simpa [xyxy, yxxy, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesSortGeneralRight
    (x h y t : Word Nat) :
    Derives basis (((((x ++ h) ++ y) ++ t) ++ x) ++ y)
      (((((x ++ h) ++ y) ++ t) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortGeneralRight
      (instantiateFiveWords x h y t t)
  simpa [xhytxy, xhytyx, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesSortFinalGapRight
    (x h y : Word Nat) :
    Derives basis ((((x ++ h) ++ y) ++ x) ++ y)
      ((((x ++ h) ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortFinalGapRight
      (instantiateFiveWords x h y h h)
  simpa [xhyxy, xhyyx, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesSortInitialGapRight
    (x y t : Word Nat) :
    Derives basis ((((x ++ y) ++ t) ++ x) ++ y)
      ((((x ++ y) ++ t) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortInitialGapRight
      (instantiateFiveWords x x y t t)
  simpa [xytxy, xytyx, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesSortBothEmptyRight (x y : Word Nat) :
    Derives basis (((x ++ y) ++ x) ++ y)
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSortBothEmptyRight
      (instantiateFiveWords x x y x y)
  simpa [xyxy, xyyx, w, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The four L6 deletion cases, with the two final witnesses to the right
of the adjacent pair being interchanged. -/
theorem listDerivesL6
    (x y : Nat) (middle tail : List Nat) :
    ListDerives
      ([x, y] ++ middle ++ [x] ++ tail ++ [y])
      ([y, x] ++ middle ++ [x] ++ tail ++ [y]) := by
  cases middle with
  | nil =>
      cases tail with
      | nil =>
          exact .words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
                derivesSortBothEmptyLeft
                  (Word.singleton x) (Word.singleton y)
      | cons t ts =>
          exact .words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
                derivesSortInitialGapLeft
                  (Word.singleton x) (Word.singleton y)
                  (S5_107.listWordOfCons t ts)
  | cons m ms =>
      cases tail with
      | nil =>
          exact .words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
                derivesSortFinalGapLeft
                  (Word.singleton x) (Word.singleton y)
                  (S5_107.listWordOfCons m ms)
      | cons t ts =>
          exact .words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
                derivesSortGeneralLeft
                  (Word.singleton x) (Word.singleton y)
                  (S5_107.listWordOfCons m ms)
                  (S5_107.listWordOfCons t ts)

/-- The four L8 deletion cases, with the two earlier witnesses to the left
of the adjacent pair being interchanged. -/
theorem listDerivesL8
    (x y : Nat) (left middle : List Nat) :
    ListDerives
      ([x] ++ left ++ [y] ++ middle ++ [x, y])
      ([x] ++ left ++ [y] ++ middle ++ [y, x]) := by
  cases left with
  | nil =>
      cases middle with
      | nil =>
          exact .words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
                derivesSortBothEmptyRight
                  (Word.singleton x) (Word.singleton y)
      | cons m ms =>
          exact .words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
                derivesSortInitialGapRight
                  (Word.singleton x) (Word.singleton y)
                  (S5_107.listWordOfCons m ms)
  | cons l ls =>
      cases middle with
      | nil =>
          exact .words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
                derivesSortFinalGapRight
                  (Word.singleton x)
                  (S5_107.listWordOfCons l ls)
                  (Word.singleton y)
      | cons m ms =>
          exact .words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
                derivesSortGeneralRight
                  (Word.singleton x)
                  (S5_107.listWordOfCons l ls)
                  (Word.singleton y)
                  (S5_107.listWordOfCons m ms)

/-! ## Edmunds repeated-block permutations -/

private def repeatedPrecedenceStep
    (x y : Nat) (state : S5_841.PrecedenceState) (letter : Nat) :
    S5_841.PrecedenceState :=
  if letter = x then
    match state with
    | .neither => .onlyX
    | .onlyX => .onlyX
    | .onlyY | .ordered | .violated => .violated
  else if letter = y then
    match state with
    | .neither => .onlyY
    | .onlyX => .ordered
    | .onlyY => .onlyY
    | .ordered => .ordered
    | .violated => .violated
  else state

private theorem precedenceScanList_eq_repeatedFold
    (letters : List Nat) (x y : Nat) :
    S5_841.precedenceScanList letters x y =
      letters.foldl (repeatedPrecedenceStep x y) .neither := by
  rfl

private def repeatedPairFree
    (x y : Nat) (letters : List Nat) : Prop :=
  x ∉ letters ∧ y ∉ letters

private theorem repeatedPrecedenceFold_pairFree
    (x y : Nat) :
    ∀ (letters : List Nat) (state : S5_841.PrecedenceState),
      repeatedPairFree x y letters →
      letters.foldl (repeatedPrecedenceStep x y) state = state
  | [], _, _ => rfl
  | letter :: rest, state, free => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact free.1 (List.Mem.head rest)
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact free.2 (List.Mem.head rest)
      have restFree : repeatedPairFree x y rest :=
        ⟨fun member => free.1 (List.Mem.tail letter member),
          fun member => free.2 (List.Mem.tail letter member)⟩
      simp only [List.foldl_cons]
      rw [show repeatedPrecedenceStep x y state letter = state by
        simp [repeatedPrecedenceStep, letterNeX, letterNeY]]
      exact repeatedPrecedenceFold_pairFree x y rest state restFree

private theorem repeatedPrecedenceFold_onlyX_of_y_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      y ∉ letters →
      letters.foldl (repeatedPrecedenceStep x y) .onlyX = .onlyX
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : y ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show repeatedPrecedenceStep x y .onlyX letter = .onlyX by
        by_cases isX : letter = x
        · simp [repeatedPrecedenceStep, isX]
        · simp [repeatedPrecedenceStep, isX, letterNeY]]
      exact repeatedPrecedenceFold_onlyX_of_y_absent x y rest restAbsent

private theorem repeatedPrecedenceFold_onlyY_of_x_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      letters.foldl (repeatedPrecedenceStep x y) .onlyY = .onlyY
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : x ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show repeatedPrecedenceStep x y .onlyY letter = .onlyY by
        simp [repeatedPrecedenceStep, letterNeX]]
      exact repeatedPrecedenceFold_onlyY_of_x_absent x y rest restAbsent

private theorem repeatedPrecedenceFold_ordered_of_x_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      letters.foldl (repeatedPrecedenceStep x y) .ordered = .ordered
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : x ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show repeatedPrecedenceStep x y .ordered letter = .ordered by
        simp [repeatedPrecedenceStep, letterNeX]]
      exact repeatedPrecedenceFold_ordered_of_x_absent x y rest restAbsent

private theorem repeatedPrecedenceFold_violated
    (x y : Nat) :
    ∀ letters : List Nat,
      letters.foldl (repeatedPrecedenceStep x y) .violated = .violated
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show repeatedPrecedenceStep x y .violated letter = .violated by
        simp [repeatedPrecedenceStep]]
      exact repeatedPrecedenceFold_violated x y rest

private theorem repeatedPrecedenceFold_onlyX_of_x_mem_y_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      y ∉ letters →
      letters.foldl (repeatedPrecedenceStep x y) .neither = .onlyX
  | [], member, _ => by simp at member
  | letter :: rest, xMember, yAbsent => by
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact yAbsent (List.Mem.head rest)
      have restYAbsent : y ∉ rest :=
        fun member => yAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show repeatedPrecedenceStep x y .neither letter = .onlyX by
          simp [repeatedPrecedenceStep, isX]]
        exact repeatedPrecedenceFold_onlyX_of_y_absent
          x y rest restYAbsent
      · have restXMember : x ∈ rest :=
          (List.mem_cons.mp xMember).resolve_left (Ne.symm isX)
        rw [show repeatedPrecedenceStep x y .neither letter = .neither by
          simp [repeatedPrecedenceStep, isX, letterNeY]]
        exact repeatedPrecedenceFold_onlyX_of_x_mem_y_absent
          x y rest restXMember restYAbsent

private theorem repeatedPrecedenceFold_onlyY_of_x_absent_y_mem
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      y ∈ letters →
      letters.foldl (repeatedPrecedenceStep x y) .neither = .onlyY
  | [], _, member => by simp at member
  | letter :: rest, xAbsent, yMember => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact xAbsent (List.Mem.head rest)
      have restXAbsent : x ∉ rest :=
        fun member => xAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isY : letter = y
      · have yNeX : y ≠ x := by
          intro equal
          exact letterNeX (isY.trans equal)
        rw [show repeatedPrecedenceStep x y .neither letter = .onlyY by
          simp [repeatedPrecedenceStep, isY, yNeX]]
        exact repeatedPrecedenceFold_onlyY_of_x_absent
          x y rest restXAbsent
      · have restYMember : y ∈ rest :=
          (List.mem_cons.mp yMember).resolve_left (Ne.symm isY)
        rw [show repeatedPrecedenceStep x y .neither letter = .neither by
          simp [repeatedPrecedenceStep, letterNeX, isY]]
        exact repeatedPrecedenceFold_onlyY_of_x_absent_y_mem
          x y rest restXAbsent restYMember

private theorem repeatedPrecedenceFold_ordered_of_x_absent_y_mem
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      y ∈ letters →
      letters.foldl (repeatedPrecedenceStep x y) .onlyX = .ordered
  | [], _, member => by simp at member
  | letter :: rest, xAbsent, yMember => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact xAbsent (List.Mem.head rest)
      have restXAbsent : x ∉ rest :=
        fun member => xAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isY : letter = y
      · rw [show repeatedPrecedenceStep x y .onlyX letter = .ordered by
          have yNeX : y ≠ x := fun equal => letterNeX (isY.trans equal)
          simp [repeatedPrecedenceStep, isY, yNeX]]
        exact repeatedPrecedenceFold_ordered_of_x_absent
          x y rest restXAbsent
      · have restYMember : y ∈ rest :=
          (List.mem_cons.mp yMember).resolve_left (Ne.symm isY)
        rw [show repeatedPrecedenceStep x y .onlyX letter = .onlyX by
          simp [repeatedPrecedenceStep, letterNeX, isY]]
        exact repeatedPrecedenceFold_ordered_of_x_absent_y_mem
          x y rest restXAbsent restYMember

private theorem repeatedPrecedenceFold_violated_of_x_mem_from_onlyY
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      letters.foldl (repeatedPrecedenceStep x y) .onlyY = .violated
  | [], member => by simp at member
  | letter :: rest, member => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show repeatedPrecedenceStep x y .onlyY letter = .violated by
          simp [repeatedPrecedenceStep, isX]]
        exact repeatedPrecedenceFold_violated x y rest
      · have restMember : x ∈ rest :=
          (List.mem_cons.mp member).resolve_left (Ne.symm isX)
        rw [show repeatedPrecedenceStep x y .onlyY letter = .onlyY by
          simp [repeatedPrecedenceStep, isX]]
        exact repeatedPrecedenceFold_violated_of_x_mem_from_onlyY
          x y rest restMember

private theorem repeatedPrecedenceFold_violated_of_x_mem_from_ordered
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      letters.foldl (repeatedPrecedenceStep x y) .ordered = .violated
  | [], member => by simp at member
  | letter :: rest, member => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show repeatedPrecedenceStep x y .ordered letter = .violated by
          simp [repeatedPrecedenceStep, isX]]
        exact repeatedPrecedenceFold_violated x y rest
      · have restMember : x ∈ rest :=
          (List.mem_cons.mp member).resolve_left (Ne.symm isX)
        rw [show repeatedPrecedenceStep x y .ordered letter = .ordered by
          simp [repeatedPrecedenceStep, isX]]
        exact repeatedPrecedenceFold_violated_of_x_mem_from_ordered
          x y rest restMember

private theorem precedenceScan_ordered_of_repeatedSplit
    {x y : Nat} (different : x ≠ y)
    (before after : List Nat)
    (xInBefore : x ∈ before)
    (yAbsentBefore : y ∉ before)
    (xAbsentAfter : x ∉ after)
    (yInAfter : y ∈ after) :
    S5_841.precedenceScanList (before ++ x :: after) x y = .ordered := by
  rw [precedenceScanList_eq_repeatedFold, List.foldl_append]
  rw [repeatedPrecedenceFold_onlyX_of_x_mem_y_absent
    x y before xInBefore yAbsentBefore]
  simp only [List.foldl_cons]
  rw [show repeatedPrecedenceStep x y .onlyX x = .onlyX by
    simp [repeatedPrecedenceStep]]
  exact repeatedPrecedenceFold_ordered_of_x_absent_y_mem
    x y after xAbsentAfter yInAfter

private theorem precedenceScan_violated_of_repeatedInversion
    {x y : Nat} (different : x ≠ y)
    (before after : List Nat)
    (yAbsentBefore : y ∉ before)
    (xInAfter : x ∈ after) :
    S5_841.precedenceScanList (before ++ y :: after) x y = .violated := by
  rw [precedenceScanList_eq_repeatedFold, List.foldl_append]
  by_cases xInBefore : x ∈ before
  · rw [repeatedPrecedenceFold_onlyX_of_x_mem_y_absent
      x y before xInBefore yAbsentBefore]
    simp only [List.foldl_cons]
    rw [show repeatedPrecedenceStep x y .onlyX y = .ordered by
      simp [repeatedPrecedenceStep, Ne.symm different]]
    exact repeatedPrecedenceFold_violated_of_x_mem_from_ordered
      x y after xInAfter
  · rw [repeatedPrecedenceFold_pairFree x y before .neither
      ⟨xInBefore, yAbsentBefore⟩]
    simp only [List.foldl_cons]
    rw [show repeatedPrecedenceStep x y .neither y = .onlyY by
      simp [repeatedPrecedenceStep, Ne.symm different]]
    exact repeatedPrecedenceFold_violated_of_x_mem_from_onlyY
      x y after xInAfter

private theorem precedenceScan_ordered_before_separator
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xInBefore : x ∈ before)
    (separatorAbsentBefore : separator ∉ before)
    (xAbsentAfter : x ∉ after) :
    S5_841.precedenceScanList
        (before ++ separator :: after) x separator = .ordered := by
  rw [precedenceScanList_eq_repeatedFold, List.foldl_append]
  rw [repeatedPrecedenceFold_onlyX_of_x_mem_y_absent
    x separator before xInBefore separatorAbsentBefore]
  simp only [List.foldl_cons]
  rw [show repeatedPrecedenceStep x separator .onlyX separator =
      .ordered by
    simp [repeatedPrecedenceStep, Ne.symm different]]
  exact repeatedPrecedenceFold_ordered_of_x_absent
    x separator after xAbsentAfter

private theorem precedenceScan_ordered_after_separator
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xAbsentBefore : x ∉ before)
    (separatorAbsentBefore : separator ∉ before)
    (xInAfter : x ∈ after)
    (separatorAbsentAfter : separator ∉ after) :
    S5_841.precedenceScanList
        (before ++ separator :: after) separator x = .ordered := by
  rw [precedenceScanList_eq_repeatedFold, List.foldl_append]
  rw [repeatedPrecedenceFold_pairFree separator x before .neither
    ⟨separatorAbsentBefore, xAbsentBefore⟩]
  simp only [List.foldl_cons]
  rw [show repeatedPrecedenceStep separator x .neither separator =
      .onlyX by
    simp [repeatedPrecedenceStep]]
  exact repeatedPrecedenceFold_ordered_of_x_absent_y_mem
    separator x after separatorAbsentAfter xInAfter

private theorem precedenceScan_violated_before_separator
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xInBefore : x ∈ before)
    (separatorAbsentBefore : separator ∉ before) :
    S5_841.precedenceScanList
        (before ++ separator :: after) separator x = .violated := by
  rw [precedenceScanList_eq_repeatedFold, List.foldl_append]
  rw [repeatedPrecedenceFold_onlyY_of_x_absent_y_mem
    separator x before separatorAbsentBefore xInBefore]
  simp only [List.foldl_cons]
  rw [show repeatedPrecedenceStep separator x .onlyY separator =
      .violated by
    simp [repeatedPrecedenceStep]]
  exact repeatedPrecedenceFold_violated separator x after

private theorem precedenceState_violated_ne_ordered :
    (S5_841.PrecedenceState.violated : S5_841.PrecedenceState) ≠ .ordered := by
  decide

private theorem completePrecedence_before_separator_iff
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xPositive : 0 < (before ++ separator :: after).count x)
    (separatorSimple :
      (before ++ separator :: after).count separator = 1) :
    S5_841.CompletePrecedenceList
        (before ++ separator :: after) x separator ↔
      before.count x = (before ++ separator :: after).count x := by
  have xSplit :
      (before ++ separator :: after).count x =
        before.count x + after.count x := by
    simp [different, Ne.symm different, List.count_append]
  have separatorSplit := separatorSimple
  simp only [List.count_append, List.count_cons_self] at separatorSplit
  have separatorBeforeZero : before.count separator = 0 := by omega
  have separatorAbsentBefore : separator ∉ before :=
    List.count_eq_zero.mp separatorBeforeZero
  constructor
  · intro complete
    have xAfterZero : after.count x = 0 := by
      apply Decidable.byContradiction
      intro nonzero
      have xInAfter : x ∈ after :=
        List.one_le_count_iff.mp (by omega)
      have violated :=
        precedenceScan_violated_of_repeatedInversion
          different before after separatorAbsentBefore xInAfter
      exact precedenceState_violated_ne_ordered
        (violated.symm.trans complete.2)
    omega
  · intro beforeTotal
    have xInBefore : x ∈ before :=
      List.one_le_count_iff.mp (by omega)
    have xAfterZero : after.count x = 0 := by omega
    have xAbsentAfter : x ∉ after :=
      List.count_eq_zero.mp xAfterZero
    exact ⟨different,
      precedenceScan_ordered_before_separator different before after
        xInBefore separatorAbsentBefore xAbsentAfter⟩

private theorem completePrecedence_after_separator_iff
    {x separator : Nat} (different : x ≠ separator)
    (before after : List Nat)
    (xPositive : 0 < (before ++ separator :: after).count x)
    (separatorSimple :
      (before ++ separator :: after).count separator = 1) :
    S5_841.CompletePrecedenceList
        (before ++ separator :: after) separator x ↔
      before.count x = 0 := by
  have xSplit :
      (before ++ separator :: after).count x =
        before.count x + after.count x := by
    simp [different, Ne.symm different, List.count_append]
  have separatorSplit := separatorSimple
  simp only [List.count_append, List.count_cons_self] at separatorSplit
  have separatorBeforeZero : before.count separator = 0 := by omega
  have separatorAfterZero : after.count separator = 0 := by omega
  have separatorAbsentBefore : separator ∉ before :=
    List.count_eq_zero.mp separatorBeforeZero
  have separatorAbsentAfter : separator ∉ after :=
    List.count_eq_zero.mp separatorAfterZero
  constructor
  · intro complete
    apply Decidable.byContradiction
    intro nonzero
    have xInBefore : x ∈ before :=
      List.one_le_count_iff.mp (by omega)
    have violated := precedenceScan_violated_before_separator
      different before after xInBefore separatorAbsentBefore
    exact precedenceState_violated_ne_ordered
      (violated.symm.trans complete.2)
  · intro beforeZero
    have xInAfter : x ∈ after :=
      List.one_le_count_iff.mp (by omega)
    have xAbsentBefore : x ∉ before :=
      List.count_eq_zero.mp beforeZero
    exact ⟨Ne.symm different,
      precedenceScan_ordered_after_separator different before after
        xAbsentBefore separatorAbsentBefore xInAfter
        separatorAbsentAfter⟩

private theorem repeatedWitnesses
    {x y : Nat} {pre post : List Nat}
    (different : x ≠ y)
    (xRepeated : 2 ≤ (pre ++ x :: y :: post).count x)
    (yRepeated : 2 ≤ (pre ++ x :: y :: post).count y) :
    (x ∈ pre ∨ x ∈ post) ∧ (y ∈ pre ∨ y ∈ post) := by
  constructor
  · by_cases inPre : x ∈ pre
    · exact Or.inl inPre
    · right
      apply Decidable.byContradiction
      intro inPost
      have preZero := List.count_eq_zero.mpr inPre
      have postZero := List.count_eq_zero.mpr inPost
      simp [List.count_append, preZero, postZero, different,
        Ne.symm different] at xRepeated
  · by_cases inPre : y ∈ pre
    · exact Or.inl inPre
    · right
      apply Decidable.byContradiction
      intro inPost
      have preZero := List.count_eq_zero.mpr inPre
      have postZero := List.count_eq_zero.mpr inPost
      simp [List.count_append, preZero, postZero, different,
        Ne.symm different] at yRepeated

private theorem listDerivesAdjacentWithFutureWitnesses
    (x y : Nat) (pre post : List Nat)
    (different : x ≠ y) (xFuture : x ∈ post) (yFuture : y ∈ post) :
    ListDerives (pre ++ x :: y :: post) (pre ++ y :: x :: post) := by
  rcases uniqueSeparatorDistinctOccurrencesOrdered
      different xFuture yFuture with orderedXY | orderedYX
  · obtain ⟨before, middle, after, shape⟩ := orderedXY
    rw [shape]
    simpa [List.append_assoc] using
      (listDerivesL6 x y before middle).context pre after
  · obtain ⟨before, middle, after, shape⟩ := orderedYX
    rw [shape]
    simpa [List.append_assoc] using
      (listDerivesL6 y x before middle).symm.context pre after

private theorem listDerivesAdjacentWithPastWitnesses
    (x y : Nat) (pre post : List Nat)
    (different : x ≠ y) (xPast : x ∈ pre) (yPast : y ∈ pre) :
    ListDerives (pre ++ x :: y :: post) (pre ++ y :: x :: post) := by
  rcases uniqueSeparatorDistinctOccurrencesOrdered
      different xPast yPast with orderedXY | orderedYX
  · obtain ⟨before, middle, after, shape⟩ := orderedXY
    rw [shape]
    simpa [List.append_assoc] using
      (listDerivesL8 x y middle after).context before post
  · obtain ⟨before, middle, after, shape⟩ := orderedYX
    rw [shape]
    simpa [List.append_assoc] using
      (listDerivesL8 y x middle after).symm.context before post

private theorem listDerivesMoveRepeatedMemberToFront
    (fixedPrefix targetTail sourcePost targetPost : List Nat)
    (selected : Nat) :
    ∀ (crossed source : List Nat),
      selected ∉ crossed →
      (crossed ++ source).Perm (selected :: targetTail) →
      (∀ letter, letter ∈ crossed ++ source →
        2 ≤
          (fixedPrefix ++ crossed ++ source ++ sourcePost).count letter) →
      (∀ letter,
        (fixedPrefix ++ crossed ++ source ++ sourcePost).count letter =
          (fixedPrefix ++ (selected :: targetTail) ++ targetPost).count
            letter) →
      S5_841.M20ListEquivalent
        (fixedPrefix ++ crossed ++ source ++ sourcePost)
        (fixedPrefix ++ (selected :: targetTail) ++ targetPost) →
      ListDerives
        (fixedPrefix ++ crossed ++ source ++ sourcePost)
        (fixedPrefix ++ crossed ++
          (selected :: source.erase selected) ++ sourcePost)
  | crossed, [], selectedAbsent, permutation, _, _, _ => by
      have selectedInCrossed : selected ∈ crossed := by
        simpa using permutation.mem_iff.mpr (List.Mem.head targetTail)
      exact False.elim (selectedAbsent selectedInCrossed)
  | crossed, head :: tail, selectedAbsent, permutation,
      sourceRepeated, exactCounts, equivalent => by
      by_cases equal : head = selected
      · subst head
        simpa [List.append_assoc] using
          S5_107.ListDerives.refl (basis := basis)
            (fixedPrefix ++ crossed ++ selected :: tail ++ sourcePost)
      · have selectedInBlock : selected ∈ crossed ++ head :: tail :=
          permutation.mem_iff.mpr (List.Mem.head targetTail)
        have selectedInSource : selected ∈ head :: tail :=
          (List.mem_append.mp selectedInBlock).resolve_left selectedAbsent
        have selectedInTail : selected ∈ tail := by
          simpa [Ne.symm equal] using selectedInSource
        have nextSelectedAbsent : selected ∉ crossed ++ [head] := by
          simp [selectedAbsent, Ne.symm equal]
        have nextPermutation :
            ((crossed ++ [head]) ++ tail).Perm
              (selected :: targetTail) := by
          simpa [List.append_assoc] using permutation
        have nextRepeated :
            ∀ letter, letter ∈ (crossed ++ [head]) ++ tail →
              2 ≤
                (fixedPrefix ++ (crossed ++ [head]) ++ tail ++
                  sourcePost).count letter := by
          intro letter member
          have oldMember : letter ∈ crossed ++ head :: tail := by
            simpa [List.append_assoc] using member
          simpa [List.append_assoc] using
            sourceRepeated letter oldMember
        have nextCounts :
            ∀ letter,
              (fixedPrefix ++ (crossed ++ [head]) ++ tail ++
                  sourcePost).count letter =
                (fixedPrefix ++ (selected :: targetTail) ++
                  targetPost).count letter := by
          intro letter
          simpa [List.append_assoc] using exactCounts letter
        have nextEquivalent :
            S5_841.M20ListEquivalent
              (fixedPrefix ++ (crossed ++ [head]) ++ tail ++ sourcePost)
              (fixedPrefix ++ (selected :: targetTail) ++ targetPost) := by
          simpa [List.append_assoc] using equivalent
        have moveTail :=
          listDerivesMoveRepeatedMemberToFront
            fixedPrefix targetTail sourcePost targetPost selected
            (crossed ++ [head]) tail nextSelectedAbsent
            nextPermutation nextRepeated nextCounts nextEquivalent
        have movedEquivalent :
            S5_841.M20ListEquivalent
              ((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost)))
              (fixedPrefix ++ (selected :: targetTail) ++ targetPost) := by
          have moveSound := m20EquivalentOfListDerives moveTail
          exact by
            simpa [List.append_assoc] using
              moveSound.symm.trans nextEquivalent
        have tailExpose :
            tail.Perm (selected :: tail.erase selected) :=
          List.perm_cons_erase selectedInTail
        have sourceExpose :
            (head :: tail).Perm
              (head :: selected :: tail.erase selected) :=
          List.Perm.cons head tailExpose
        have fullExpose :
            (fixedPrefix ++ crossed ++ head :: tail ++ sourcePost).Perm
              ((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost))) := by
          simpa [List.append_assoc] using
            List.Perm.append
              (List.Perm.append
                (List.Perm.refl (fixedPrefix ++ crossed)) sourceExpose)
              (List.Perm.refl sourcePost)
        have movedCounts : ∀ letter,
            (((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost))).count letter) =
              (fixedPrefix ++ (selected :: targetTail) ++
                targetPost).count letter := by
          intro letter
          calc
            (((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost))).count letter) =
                (fixedPrefix ++ crossed ++ head :: tail ++
                  sourcePost).count letter :=
              (fullExpose.count letter).symm
            _ = _ := exactCounts letter
        have headRepeated :
            2 ≤
              (((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost))).count head) := by
          calc
            2 ≤
                (fixedPrefix ++ crossed ++ head :: tail ++
                  sourcePost).count head :=
              sourceRepeated head (by simp)
            _ = _ := fullExpose.count head
        have selectedRepeated :
            2 ≤
              (((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost))).count selected) := by
          calc
            2 ≤
                (fixedPrefix ++ crossed ++ head :: tail ++
                  sourcePost).count selected :=
              sourceRepeated selected (by simp [selectedInTail])
            _ = _ := fullExpose.count selected
        have headInTargetTail : head ∈ targetTail := by
          have headInTarget : head ∈ selected :: targetTail :=
            permutation.mem_iff.mp (by simp)
          simpa [equal] using headInTarget
        let currentPrefix := fixedPrefix ++ crossed
        let currentPost := tail.erase selected ++ sourcePost
        have witnesses := repeatedWitnesses
          (pre := currentPrefix) (post := currentPost)
          equal headRepeated selectedRepeated
        have swap :
            ListDerives
              (currentPrefix ++ head :: selected :: currentPost)
              (currentPrefix ++ selected :: head :: currentPost) := by
          by_cases headPast : head ∈ currentPrefix
          · by_cases selectedPast : selected ∈ currentPrefix
            · exact listDerivesAdjacentWithPastWitnesses
                head selected currentPrefix currentPost equal
                headPast selectedPast
            · have selectedFuture : selected ∈ currentPost :=
                witnesses.2.resolve_left selectedPast
              by_cases headFuture : head ∈ currentPost
              · exact listDerivesAdjacentWithFutureWitnesses
                  head selected currentPrefix currentPost equal
                  headFuture selectedFuture
              · have sourcePrecedence :
                    S5_841.CompletePrecedenceList
                      (currentPrefix ++ head :: selected :: currentPost)
                      head selected :=
                  ⟨equal, by
                    exact precedenceScan_ordered_of_repeatedSplit equal
                      currentPrefix (selected :: currentPost)
                      headPast selectedPast
                      (by simpa [equal] using headFuture) (by simp)⟩
                have selectedAbsentFixedPrefix :
                    selected ∉ fixedPrefix := by
                  intro member
                  exact selectedPast (List.mem_append_left crossed member)
                have targetNotPrecedence :
                    ¬ S5_841.CompletePrecedenceList
                      (fixedPrefix ++ selected :: targetTail ++ targetPost)
                      head selected := by
                  intro targetPrecedence
                  have targetScan :
                      S5_841.precedenceScanList
                          (fixedPrefix ++ selected :: targetTail ++ targetPost)
                          head selected = .violated := by
                    simpa [List.append_assoc] using
                      precedenceScan_violated_of_repeatedInversion equal
                        fixedPrefix (targetTail ++ targetPost)
                        selectedAbsentFixedPrefix
                        (List.mem_append_left targetPost headInTargetTail)
                  exact precedenceState_violated_ne_ordered
                    (targetScan.symm.trans targetPrecedence.2)
                have preserved :=
                  S5_841.m20ListEquivalent_completePrecedenceList
                    movedEquivalent head selected
                exact False.elim
                  (targetNotPrecedence (preserved.mp sourcePrecedence))
          · have headFuture : head ∈ currentPost :=
              witnesses.1.resolve_left headPast
            by_cases selectedFuture : selected ∈ currentPost
            · exact listDerivesAdjacentWithFutureWitnesses
                head selected currentPrefix currentPost equal
                headFuture selectedFuture
            · have selectedPast : selected ∈ currentPrefix :=
                witnesses.2.resolve_right selectedFuture
              have headAbsentFixedPrefix : head ∉ fixedPrefix := by
                intro member
                exact headPast (List.mem_append_left crossed member)
              have selectedInFixedPrefix : selected ∈ fixedPrefix := by
                rcases List.mem_append.mp selectedPast with
                  inFixed | inCrossed
                · exact inFixed
                · exact False.elim (selectedAbsent inCrossed)
              have selectedAbsentTargetAfter :
                  selected ∉ targetTail ++ targetPost := by
                apply List.count_eq_zero.mp
                have countEq := movedCounts selected
                have crossedZero : crossed.count selected = 0 :=
                  List.count_eq_zero.mpr selectedAbsent
                have currentPostZero : currentPost.count selected = 0 :=
                  List.count_eq_zero.mpr selectedFuture
                have sourceCountShape :
                    (currentPrefix ++ head :: selected :: currentPost).count
                        selected =
                      fixedPrefix.count selected + 1 := by
                  simp [currentPrefix, List.count_append, equal,
                    crossedZero, currentPostZero]
                have targetCountShape :
                    (fixedPrefix ++ selected :: targetTail ++ targetPost).count
                        selected =
                      fixedPrefix.count selected + 1 +
                        (targetTail ++ targetPost).count selected := by
                  simp [List.count_append, Nat.add_assoc, Nat.add_comm,
                    Nat.add_left_comm]
                change
                  (currentPrefix ++ head :: selected :: currentPost).count
                      selected =
                    (fixedPrefix ++ selected :: targetTail ++ targetPost).count
                      selected at countEq
                rw [sourceCountShape, targetCountShape] at countEq
                omega
              have sourceNotPrecedence :
                  ¬ S5_841.CompletePrecedenceList
                    (currentPrefix ++ head :: selected :: currentPost)
                    selected head := by
                intro sourcePrecedence
                have sourceScan :
                    S5_841.precedenceScanList
                        (currentPrefix ++ head :: selected :: currentPost)
                        selected head = .violated := by
                  exact precedenceScan_violated_of_repeatedInversion
                    (Ne.symm equal) currentPrefix
                    (selected :: currentPost) headPast (by simp)
                exact precedenceState_violated_ne_ordered
                  (sourceScan.symm.trans sourcePrecedence.2)
              have targetPrecedence :
                  S5_841.CompletePrecedenceList
                    (fixedPrefix ++ selected :: targetTail ++ targetPost)
                    selected head :=
                ⟨Ne.symm equal, by
                  simpa [List.append_assoc] using
                    precedenceScan_ordered_of_repeatedSplit
                      (Ne.symm equal) fixedPrefix
                      (targetTail ++ targetPost)
                      selectedInFixedPrefix headAbsentFixedPrefix
                      selectedAbsentTargetAfter
                      (List.mem_append_left targetPost headInTargetTail)⟩
              have preserved :=
                S5_841.m20ListEquivalent_completePrecedenceList
                  movedEquivalent selected head
              exact False.elim
                (sourceNotPrecedence (preserved.mpr targetPrecedence))
        have complete := moveTail.trans <| by
          simpa [currentPrefix, currentPost, List.append_assoc] using swap
        simpa [equal, List.append_assoc] using complete
termination_by
  _ source => source.length

/-- Edmunds' block-permutation lemma for a block consisting entirely of
globally repeated letters. Exact full-word counts are retained separately;
no quadratic restriction is imposed. -/
private theorem listDerivesRepeatedBlockPermutationAgainst :
    ∀ (target source pre sourcePost targetPost : List Nat),
      source.Perm target →
      (∀ letter, letter ∈ source →
        2 ≤ (pre ++ source ++ sourcePost).count letter) →
      (∀ letter,
        (pre ++ source ++ sourcePost).count letter =
          (pre ++ target ++ targetPost).count letter) →
      S5_841.M20ListEquivalent
        (pre ++ source ++ sourcePost)
        (pre ++ target ++ targetPost) →
      ListDerives
        (pre ++ source ++ sourcePost)
        (pre ++ target ++ sourcePost)
  | [], source, pre, sourcePost, _, permutation, _, _, _ => by
      have sourceEmpty : source = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using permutation.length_eq
      subst source
      simpa [List.append_assoc] using
        S5_107.ListDerives.refl (basis := basis) (pre ++ sourcePost)
  | selected :: targetTail, source, pre, sourcePost, targetPost,
      permutation, sourceRepeated, exactCounts, equivalent => by
      have moveRaw :=
        listDerivesMoveRepeatedMemberToFront
          pre targetTail sourcePost targetPost selected [] source
          (by simp) (by simpa using permutation)
          (by simpa [List.append_assoc] using sourceRepeated)
          (by simpa [List.append_assoc] using exactCounts)
          (by simpa [List.append_assoc] using equivalent)
      have move :
          ListDerives
            (pre ++ source ++ sourcePost)
            ((pre ++ [selected]) ++ source.erase selected ++
              sourcePost) := by
        simpa [List.append_assoc] using moveRaw
      have selectedInSource : selected ∈ source :=
        permutation.mem_iff.mpr (by simp)
      have sourceExpose :
          source.Perm (selected :: source.erase selected) :=
        List.perm_cons_erase selectedInSource
      have erasedPermutation :
          (source.erase selected).Perm targetTail := by
        simpa using permutation.erase selected
      have fullExpose :
          (pre ++ source ++ sourcePost).Perm
            ((pre ++ [selected]) ++ source.erase selected ++
              sourcePost) := by
        simpa [List.append_assoc] using
          List.Perm.append
            (List.Perm.append (List.Perm.refl pre) sourceExpose)
            (List.Perm.refl sourcePost)
      have erasedRepeated :
          ∀ letter, letter ∈ source.erase selected →
            2 ≤
              ((pre ++ [selected]) ++ source.erase selected ++
                sourcePost).count letter := by
        intro letter member
        have sourceMember : letter ∈ source :=
          List.mem_of_mem_erase member
        calc
          2 ≤ (pre ++ source ++ sourcePost).count letter :=
            sourceRepeated letter sourceMember
          _ = _ := fullExpose.count letter
      have erasedCounts : ∀ letter,
          ((pre ++ [selected]) ++ source.erase selected ++
              sourcePost).count letter =
            ((pre ++ [selected]) ++ targetTail ++ targetPost).count
              letter := by
        intro letter
        calc
          ((pre ++ [selected]) ++ source.erase selected ++
              sourcePost).count letter =
              (pre ++ source ++ sourcePost).count letter :=
            (fullExpose.count letter).symm
          _ = (pre ++ (selected :: targetTail) ++ targetPost).count
              letter := exactCounts letter
          _ = _ := by simp [List.append_assoc]
      have exposedEquivalent :
          S5_841.M20ListEquivalent
            ((pre ++ [selected]) ++ source.erase selected ++ sourcePost)
            ((pre ++ [selected]) ++ targetTail ++ targetPost) := by
        have moveSound := m20EquivalentOfListDerives move
        have exposedToTarget := moveSound.symm.trans equivalent
        simpa [List.append_assoc] using exposedToTarget
      have rest :=
        listDerivesRepeatedBlockPermutationAgainst
          targetTail (source.erase selected) (pre ++ [selected])
          sourcePost targetPost erasedPermutation erasedRepeated
          erasedCounts exposedEquivalent
      exact move.trans <| by
        simpa [List.append_assoc] using rest
termination_by
  target _ _ _ _ => target.length

/-! ## Precedence-preserving exponent normalization -/

/-- Pull one displayed interior copy next to the first copy while retaining
the final copy as the M20 complete-precedence witness. -/
private theorem listDerivesGatherMiddleToFirst
    (letter : Nat) (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
        [letter] ++ after)
      (before ++ [letter, letter] ++ firstGap ++ secondGap ++
        [letter] ++ after) := by
  cases firstGap with
  | nil =>
      simpa [List.append_assoc] using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++ [letter, letter] ++ secondGap ++ [letter] ++ after))
  | cons firstHead firstTail =>
      let firstWord := S5_107.listWordOfCons firstHead firstTail
      cases secondGap with
      | nil =>
          have moved := S5_107.ListDerives.ofWord
            (derivesSquareTransport
              (Word.singleton letter) firstWord).symm
          simpa [firstWord, S5_107.listWordOfCons, Word.singleton,
            Word.append, Word.append_assoc, List.append_assoc] using
              S5_107.ListDerives.context before after moved
      | cons secondHead secondTail =>
          let secondWord :=
            S5_107.listWordOfCons secondHead secondTail
          have gathered := S5_107.ListDerives.ofWord
            (derivesGatherGeneral
              (Word.singleton letter) firstWord secondWord)
          simpa [firstWord, secondWord, S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.append_assoc,
            List.append_assoc] using
              S5_107.ListDerives.context before after gathered

/-- Delete two copies from a displayed front block while retaining a final
copy. The empty middle is exactly `x^4 = x^2`; the nonempty middle is
`x^3 y x = x y x`. -/
private theorem listDerivesContractFrontPair
    (letter : Nat) (before middle after : List Nat) :
    ListDerives
      (before ++ [letter, letter, letter] ++ middle ++ [letter] ++ after)
      (before ++ [letter] ++ middle ++ [letter] ++ after) := by
  cases middle with
  | nil =>
      have contracted := S5_107.ListDerives.ofWord
        (derivesFourToTwo (Word.singleton letter))
      simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
        Word.append_assoc, List.append_assoc] using
          S5_107.ListDerives.context before after contracted
  | cons middleHead middleTail =>
      let middleWord :=
        S5_107.listWordOfCons middleHead middleTail
      have contracted := S5_107.ListDerives.ofWord
        (derivesSandwichContraction
          (Word.singleton letter) middleWord)
      simpa [middleWord, S5_107.listWordOfCons, Word.singleton,
        Word.append, Word.append_assoc, List.append_assoc] using
          S5_107.ListDerives.context before after contracted

/-- Delete the second and third of four displayed copies while retaining
the first and fourth. This is the parity-preserving Condition 6 reduction;
unlike an arbitrary pair deletion it preserves all first/last precedence
data seen by `M20`. -/
theorem listDerivesDeleteSecondAndThird
    (letter : Nat)
    (before firstGap secondGap thirdGap after : List Nat) :
    ListDerives
      (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
        [letter] ++ thirdGap ++ [letter] ++ after)
      (before ++ [letter] ++ firstGap ++ secondGap ++ thirdGap ++
        [letter] ++ after) := by
  have gatherSecond :=
    listDerivesGatherMiddleToFirst letter before firstGap secondGap
      (thirdGap ++ [letter] ++ after)
  have gatherThird :=
    listDerivesGatherMiddleToFirst letter (before ++ [letter])
      (firstGap ++ secondGap) thirdGap after
  have contract :=
    listDerivesContractFrontPair letter before
      (firstGap ++ secondGap ++ thirdGap) after
  have first :
      ListDerives
        (before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++
          [letter] ++ thirdGap ++ [letter] ++ after)
        (before ++ [letter, letter] ++ firstGap ++ secondGap ++
          [letter] ++ thirdGap ++ [letter] ++ after) := by
    simpa [List.append_assoc] using gatherSecond
  have second :
      ListDerives
        (before ++ [letter, letter] ++ firstGap ++ secondGap ++
          [letter] ++ thirdGap ++ [letter] ++ after)
        (before ++ [letter, letter, letter] ++ firstGap ++ secondGap ++
          thirdGap ++ [letter] ++ after) := by
    simpa [List.append_assoc] using gatherThird
  have third :
      ListDerives
        (before ++ [letter, letter, letter] ++ firstGap ++ secondGap ++
          thirdGap ++ [letter] ++ after)
        (before ++ [letter] ++ firstGap ++ secondGap ++ thirdGap ++
          [letter] ++ after) := by
    simpa [List.append_assoc] using contract
  exact first.trans (second.trans third)

private theorem existsTwoOccurrenceSplit
    (letter : Nat) :
    ∀ {letters : List Nat},
      2 ≤ letters.count letter →
        ∃ before middle after,
          letters = before ++ letter :: middle ++ letter :: after
  | [], count => by
      simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        have restPositive : 0 < rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        have restMember : letter ∈ rest :=
          List.count_pos_iff.mp restPositive
        obtain ⟨middle, after, split⟩ :=
          List.mem_iff_append.mp restMember
        exact ⟨[], middle, after, by simp [split, List.append_assoc]⟩
      · have restCount : 2 ≤ rest.count letter := by
          simpa [equality] using count
        obtain ⟨before, middle, after, split⟩ :=
          existsTwoOccurrenceSplit letter restCount
        exact ⟨first :: before, middle, after,
          by simp [split, List.append_assoc]⟩

private theorem existsThreeOccurrenceSplit
    (letter : Nat) :
    ∀ {letters : List Nat},
      3 ≤ letters.count letter →
        ∃ before firstGap secondGap after,
          letters = before ++ letter :: firstGap ++ letter ::
            secondGap ++ letter :: after
  | [], count => by
      simp at count
  | first :: rest, count => by
      by_cases equality : first = letter
      · subst first
        have restCount : 2 ≤ rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        obtain ⟨firstGap, secondGap, after, split⟩ :=
          existsTwoOccurrenceSplit letter restCount
        exact ⟨[], firstGap, secondGap, after,
          by simp [split, List.append_assoc]⟩
      · have restCount : 3 ≤ rest.count letter := by
          simpa [equality] using count
        obtain ⟨before, firstGap, secondGap, after, split⟩ :=
          existsThreeOccurrenceSplit letter restCount
        exact ⟨first :: before, firstGap, secondGap, after,
          by simp [split, List.append_assoc]⟩

private theorem periodExponentEqSelfOfLeThree
    {count : Nat} (bound : count ≤ 3) :
    periodTwoFromTwoExponent count = count := by
  unfold periodTwoFromTwoExponent
  split <;> omega

private theorem periodExponentAddTwo
    {count : Nat} (atLeastTwo : 2 ≤ count) :
    periodTwoFromTwoExponent (count + 2) =
      periodTwoFromTwoExponent count := by
  unfold periodTwoFromTwoExponent
  simp only [show ¬count + 2 < 2 by omega,
    show ¬count < 2 by omega, if_false]
  omega

/-- Reduce all multiplicities to the states `0,1,2,3`, deleting copies only
in precedence-preserving pairs. -/
private theorem existsPeriodReductionFrom :
    ∀ (remaining kept : List Nat),
      (∀ tested, kept.count tested ≤ 3) →
        ∃ reduced : List Nat,
          (∀ tested, reduced.count tested ≤ 3) ∧
          (∀ tested,
            periodTwoFromTwoExponent
                ((kept ++ remaining).count tested) =
              reduced.count tested) ∧
          ListDerives (kept ++ remaining) reduced
  | [], kept, keptBound => by
      refine ⟨kept, keptBound, ?_, ?_⟩
      · intro tested
        simpa using periodExponentEqSelfOfLeThree (keptBound tested)
      · simpa using S5_107.ListDerives.refl (basis := basis) kept
  | letter :: rest, kept, keptBound => by
      by_cases room : kept.count letter < 3
      · have nextBound :
            ∀ tested, (kept ++ [letter]).count tested ≤ 3 := by
          intro tested
          rw [List.count_append]
          by_cases equality : letter = tested
          · subst letter
            simp only [List.count_cons_self, List.count_nil]
            omega
          · have singletonZero : [letter].count tested = 0 := by
              simp [equality]
            rw [singletonZero, Nat.add_zero]
            exact keptBound tested
        obtain ⟨reduced, reducedBound, counts, derivation⟩ :=
          existsPeriodReductionFrom rest (kept ++ [letter]) nextBound
        refine ⟨reduced, reducedBound, ?_, ?_⟩
        · simpa [List.append_assoc] using counts
        · simpa [List.append_assoc] using derivation
      · have full : kept.count letter = 3 := by
          have bound := keptBound letter
          omega
        obtain ⟨before, firstGap, secondGap, after, split⟩ :=
          existsThreeOccurrenceSplit letter (letters := kept) (by omega)
        let nextKept :=
          before ++ [letter] ++ firstGap ++ secondGap ++ after ++ [letter]
        have nextBound :
            ∀ tested, nextKept.count tested ≤ 3 := by
          intro tested
          by_cases equality : tested = letter
          · subst tested
            simp only [nextKept, List.count_append,
              List.count_cons_self, List.count_nil]
            have splitCount := congrArg (List.count letter) split
            simp only [List.count_append, List.count_cons_self] at splitCount
            omega
          · have countEq : nextKept.count tested = kept.count tested := by
              rw [split]
              simp [nextKept, List.count_append, equality,
                Ne.symm equality]
            rw [countEq]
            exact keptBound tested
        have stateCounts :
            ∀ tested,
              periodTwoFromTwoExponent
                  ((kept ++ letter :: rest).count tested) =
                periodTwoFromTwoExponent
                  ((nextKept ++ rest).count tested) := by
          intro tested
          by_cases equality : tested = letter
          · subst tested
            have splitCount := congrArg (List.count letter) split
            simp only [List.count_append, List.count_cons_self] at splitCount
            have sourceShape :
                (kept ++ letter :: rest).count letter =
                  (nextKept ++ rest).count letter + 2 := by
              simp only [List.count_append, List.count_cons_self, nextKept,
                List.count_nil]
              omega
            rw [sourceShape]
            apply periodExponentAddTwo
            rw [List.count_append]
            have nextLetterCount : nextKept.count letter = 2 := by
              simp only [nextKept, List.count_append,
                List.count_cons_self, List.count_nil]
              omega
            omega
          · have countEq :
                (kept ++ letter :: rest).count tested =
                  (nextKept ++ rest).count tested := by
              rw [split]
              simp [nextKept, List.count_append, equality,
                Ne.symm equality]
            rw [countEq]
        obtain ⟨reduced, reducedBound, counts, recurse⟩ :=
          existsPeriodReductionFrom rest nextKept nextBound
        have deletePair :
            ListDerives (kept ++ letter :: rest)
              (nextKept ++ rest) := by
          rw [split]
          simpa [nextKept, List.append_assoc] using
            listDerivesDeleteSecondAndThird letter before firstGap
              secondGap after rest
        refine ⟨reduced, reducedBound, ?_, deletePair.trans recurse⟩
        intro tested
        exact (stateCounts tested).trans (counts tested)

theorem existsPeriodReduction (letters : List Nat) :
    ∃ reduced : List Nat,
      (∀ tested, reduced.count tested ≤ 3) ∧
      (∀ tested,
        periodTwoFromTwoExponent (letters.count tested) =
          reduced.count tested) ∧
      ListDerives letters reduced := by
  simpa using existsPeriodReductionFrom letters [] (by simp)

/-! ## Lee--Li canonical multiplicity placement -/

/-- A reduced Condition 6 word in Lee--Li canonical placement. A variable
occurring three times has its first two copies adjacent and one remaining
copy in the recursively normalized tail. -/
private inductive LeeLiCanonical : List Nat → Prop
  | nil : LeeLiCanonical []
  | single (letter : Nat) (tail : List Nat) :
      LeeLiCanonical tail →
      tail.count letter = 0 →
      LeeLiCanonical (letter :: tail)
  | double (letter : Nat) (tail : List Nat) :
      LeeLiCanonical tail →
      tail.count letter = 1 →
      LeeLiCanonical (letter :: tail)
  | triple (letter : Nat) (tail : List Nat) :
      LeeLiCanonical tail →
      tail.count letter = 1 →
      LeeLiCanonical (letter :: letter :: tail)

private theorem LeeLiCanonical.firstPairOfCountThree
    {letters : List Nat} (canonical : LeeLiCanonical letters)
    (tested : Nat) (count : letters.count tested = 3) :
    ∃ before after,
      letters = before ++ tested :: tested :: after ∧
        tested ∉ before := by
  induction canonical with
  | nil => simp at count
  | single letter tail tailCanonical letterZero induction =>
      by_cases equality : tested = letter
      · subst tested
        simp only [List.count_cons_self, letterZero] at count
        omega
      · have tailCount : tail.count tested = 3 := by
          simpa [equality, Ne.symm equality] using count
        obtain ⟨before, after, shape, absent⟩ :=
          induction tailCount
        exact ⟨letter :: before, after, by simp [shape], by
          simp [equality, Ne.symm equality, absent]⟩
  | double letter tail tailCanonical letterOne induction =>
      by_cases equality : tested = letter
      · subst tested
        simp only [List.count_cons_self, letterOne] at count
        omega
      · have tailCount : tail.count tested = 3 := by
          simpa [equality, Ne.symm equality] using count
        obtain ⟨before, after, shape, absent⟩ :=
          induction tailCount
        exact ⟨letter :: before, after, by simp [shape], by
          simp [equality, Ne.symm equality, absent]⟩
  | triple letter tail tailCanonical letterOne induction =>
      by_cases equality : tested = letter
      · subst tested
        exact ⟨[], tail, rfl, by simp⟩
      · have tailCount : tail.count tested = 3 := by
          simpa [equality, Ne.symm equality] using count
        obtain ⟨before, after, shape, absent⟩ :=
          induction tailCount
        exact ⟨letter :: letter :: before, after,
          by simp [shape], by
            simp [equality, Ne.symm equality, absent]⟩

private theorem prefixCount_ne_one_of_firstPairAux
    (tested separator : Nat) (pairAfter suffix : List Nat)
    (different : tested ≠ separator) :
    ∀ (pairBefore preWords : List Nat),
      tested ∉ pairBefore →
      pairBefore ++ tested :: tested :: pairAfter =
        preWords ++ separator :: suffix →
      preWords.count tested ≠ 1
  | [], [], _, _ => by simp
  | [], first :: rest, _, shape => by
      simp only [List.nil_append, List.cons_append] at shape
      injection shape with firstEq tailEq
      subst first
      intro countOne
      cases rest with
      | nil =>
          simp only [List.nil_append] at tailEq
          injection tailEq with equality
          exact different equality
      | cons next more =>
          simp only [List.cons_append] at tailEq
          injection tailEq with equality
          subst next
          simp only [List.count_cons_self] at countOne
          omega
  | first :: rest, [], _, _ => by simp
  | first :: rest, next :: preWords, absent, shape => by
      have firstDifferent : first ≠ tested := by
        intro equality
        subst first
        exact absent (List.Mem.head rest)
      have restAbsent : tested ∉ rest :=
        fun member => absent (List.Mem.tail first member)
      simp only [List.cons_append] at shape
      injection shape with headEq tailEq
      subst next
      have recurse :=
        prefixCount_ne_one_of_firstPairAux tested separator
          pairAfter suffix different rest preWords restAbsent tailEq
      simpa [firstDifferent] using recurse

/-- The only extra placement datum needed at a simple separator: a variable
with three copies never has exactly one copy before that separator. -/
private def SimpleSplitCanonical (whole : List Nat) : Prop :=
  ∀ tested separator before after,
    whole = before ++ separator :: after →
    whole.count tested = 3 →
    whole.count separator = 1 →
    tested ≠ separator →
    before.count tested ≠ 1

private theorem LeeLiCanonical.simpleSplitCanonical
    {letters : List Nat} (canonical : LeeLiCanonical letters) :
    SimpleSplitCanonical letters := by
  intro tested separator before after split testedThree _separatorSimple
    different
  obtain ⟨pairBefore, pairAfter, pairShape, pairBeforeAbsent⟩ :=
    canonical.firstPairOfCountThree tested testedThree
  exact prefixCount_ne_one_of_firstPairAux tested separator
    pairAfter after different pairBefore before pairBeforeAbsent
    (pairShape.symm.trans split)

private theorem prefixCount_eq_of_canonicalPrecedence
    {x separator : Nat} (different : x ≠ separator)
    (leftPrefix leftRest rightPrefix rightRest : List Nat)
    (counts :
      (leftPrefix ++ separator :: leftRest).count x =
        (rightPrefix ++ separator :: rightRest).count x)
    (leftPositive :
      0 < (leftPrefix ++ separator :: leftRest).count x)
    (leftBound :
      (leftPrefix ++ separator :: leftRest).count x ≤ 3)
    (leftSeparator :
      (leftPrefix ++ separator :: leftRest).count separator = 1)
    (rightSeparator :
      (rightPrefix ++ separator :: rightRest).count separator = 1)
    (leftCanonical :
      SimpleSplitCanonical (leftPrefix ++ separator :: leftRest))
    (rightCanonical :
      SimpleSplitCanonical (rightPrefix ++ separator :: rightRest))
    (precedence : ∀ a b,
      S5_841.CompletePrecedenceList
          (leftPrefix ++ separator :: leftRest) a b ↔
        S5_841.CompletePrecedenceList
          (rightPrefix ++ separator :: rightRest) a b) :
    leftPrefix.count x = rightPrefix.count x := by
  have rightPositive :
      0 < (rightPrefix ++ separator :: rightRest).count x := by
    omega
  have leftBefore := completePrecedence_before_separator_iff
    different leftPrefix leftRest leftPositive leftSeparator
  have rightBefore := completePrecedence_before_separator_iff
    different rightPrefix rightRest rightPositive rightSeparator
  have leftAfter := completePrecedence_after_separator_iff
    different leftPrefix leftRest leftPositive leftSeparator
  have rightAfter := completePrecedence_after_separator_iff
    different rightPrefix rightRest rightPositive rightSeparator
  by_cases before :
      S5_841.CompletePrecedenceList
        (leftPrefix ++ separator :: leftRest) x separator
  · have rightValue := (precedence x separator).mp before
    calc
      leftPrefix.count x =
          (leftPrefix ++ separator :: leftRest).count x :=
        leftBefore.mp before
      _ = (rightPrefix ++ separator :: rightRest).count x := counts
      _ = rightPrefix.count x := (rightBefore.mp rightValue).symm
  · have rightNotBefore :
        ¬ S5_841.CompletePrecedenceList
          (rightPrefix ++ separator :: rightRest) x separator := by
      intro rightValue
      exact before ((precedence x separator).mpr rightValue)
    by_cases after :
        S5_841.CompletePrecedenceList
          (leftPrefix ++ separator :: leftRest) separator x
    · have rightValue := (precedence separator x).mp after
      rw [leftAfter.mp after, rightAfter.mp rightValue]
    · have rightNotAfter :
          ¬ S5_841.CompletePrecedenceList
            (rightPrefix ++ separator :: rightRest) separator x := by
        intro rightValue
        exact after ((precedence separator x).mpr rightValue)
      have leftNotTotal :
          leftPrefix.count x ≠
            (leftPrefix ++ separator :: leftRest).count x :=
        fun equal => before (leftBefore.mpr equal)
      have rightNotTotal :
          rightPrefix.count x ≠
            (rightPrefix ++ separator :: rightRest).count x :=
        fun equal => rightNotBefore (rightBefore.mpr equal)
      have leftNotZero : leftPrefix.count x ≠ 0 :=
        fun equal => after (leftAfter.mpr equal)
      have rightNotZero : rightPrefix.count x ≠ 0 :=
        fun equal => rightNotAfter (rightAfter.mpr equal)
      have leftSplit :
          (leftPrefix ++ separator :: leftRest).count x =
            leftPrefix.count x + leftRest.count x := by
        simp [different, Ne.symm different, List.count_append]
      have rightSplit :
          (rightPrefix ++ separator :: rightRest).count x =
            rightPrefix.count x + rightRest.count x := by
        simp [different, Ne.symm different, List.count_append]
      by_cases leftThree :
          (leftPrefix ++ separator :: leftRest).count x = 3
      · have rightThree :
            (rightPrefix ++ separator :: rightRest).count x = 3 := by
          omega
        have leftNotOne : leftPrefix.count x ≠ 1 :=
          leftCanonical x separator leftPrefix leftRest rfl leftThree
            leftSeparator different
        have rightNotOne : rightPrefix.count x ≠ 1 :=
          rightCanonical x separator rightPrefix rightRest rfl rightThree
            rightSeparator different
        omega
      · omega

/-! ## Globally simple separator order -/

private def simpleProjection
    (whole letters : List Nat) : List Nat :=
  letters.filter fun letter => decide (whole.count letter = 1)

private theorem simpleProjection_cons_split
    (pre tail : List Nat) (separator : Nat) (remaining : List Nat)
    (projection :
      simpleProjection (pre ++ tail) tail = separator :: remaining) :
    ∃ before after,
      tail = before ++ separator :: after ∧
      (∀ letter, letter ∈ before →
        (pre ++ tail).count letter ≠ 1) ∧
      simpleProjection (pre ++ tail) after = remaining ∧
      (pre ++ tail).count separator = 1 := by
  have separatorProjected :
      separator ∈ simpleProjection (pre ++ tail) tail := by
    rw [projection]
    simp
  have separatorData := List.mem_filter.mp separatorProjected
  have separatorInTail : separator ∈ tail := separatorData.1
  have separatorSimple : (pre ++ tail).count separator = 1 := by
    simpa [simpleProjection] using separatorData.2
  obtain ⟨before, after, tailShape⟩ :=
    List.append_of_mem separatorInTail
  have separatorSimpleShaped :
      (pre ++ (before ++ separator :: after)).count separator = 1 := by
    simpa [tailShape] using separatorSimple
  have separatorNotBefore : separator ∉ before := by
    intro member
    have positive : 1 ≤ before.count separator :=
      List.one_le_count_iff.mpr member
    simp only [List.count_append, List.count_cons_self] at separatorSimpleShaped
    omega
  have expanded :
      simpleProjection (pre ++ tail) before ++
        separator :: simpleProjection (pre ++ tail) after =
      separator :: remaining := by
    have expandedProjection := projection
    rw [tailShape] at expandedProjection
    unfold simpleProjection at expandedProjection
    rw [List.filter_append] at expandedProjection
    have separatorKept :
        decide
            ((pre ++ (before ++ separator :: after)).count separator = 1) =
          true := by
      simp [separatorSimpleShaped]
    rw [List.filter_cons, if_pos separatorKept] at expandedProjection
    simpa [simpleProjection, tailShape, List.append_assoc] using
      expandedProjection
  have beforeEmpty : simpleProjection (pre ++ tail) before = [] := by
    cases beforeProjection : simpleProjection (pre ++ tail) before with
    | nil => rfl
    | cons first rest =>
        rw [beforeProjection] at expanded
        simp only [List.cons_append] at expanded
        have firstEqual : first = separator := by injection expanded
        subst first
        have separatorProjectedBefore :
            separator ∈ simpleProjection (pre ++ tail) before := by
          rw [beforeProjection]
          simp
        have separatorBefore : separator ∈ before :=
          (List.mem_filter.mp separatorProjectedBefore).1
        exact False.elim (separatorNotBefore separatorBefore)
  have afterProjection :
      simpleProjection (pre ++ tail) after = remaining := by
    rw [beforeEmpty] at expanded
    simpa using expanded
  have beforeNonlinear :
      ∀ letter, letter ∈ before →
        (pre ++ tail).count letter ≠ 1 := by
    intro letter member countOne
    have projected : letter ∈ simpleProjection (pre ++ tail) before :=
      List.mem_filter.mpr ⟨member, by simp [countOne]⟩
    rw [beforeEmpty] at projected
    simp at projected
  exact ⟨before, after, tailShape, beforeNonlinear,
    afterProjection, separatorSimple⟩

private theorem nonlinear_of_simpleProjection_nil
    (whole letters : List Nat)
    (projection : simpleProjection whole letters = []) :
    ∀ letter, letter ∈ letters → whole.count letter ≠ 1 := by
  intro letter member countOne
  have projected : letter ∈ simpleProjection whole letters :=
    List.mem_filter.mpr ⟨member, by simp [countOne]⟩
  rw [projection] at projected
  simp at projected

private theorem completePrecedence_of_uniqueOrderedSplit
    {whole : List Nat} {x y : Nat}
    (different : x ≠ y) (before middle after : List Nat)
    (shape : whole = before ++ x :: middle ++ y :: after)
    (xSimple : whole.count x = 1)
    (ySimple : whole.count y = 1) :
    S5_841.CompletePrecedenceList whole x y := by
  have xData := xSimple
  have yData := ySimple
  rw [shape] at xData yData
  simp only [List.count_append, List.count_cons] at xData yData
  simp [different, Ne.symm different] at xData yData
  have xBeforeZero : before.count x = 0 := by omega
  have xMiddleZero : middle.count x = 0 := by omega
  have xAfterZero : after.count x = 0 := by omega
  have yBeforeZero : before.count y = 0 := by omega
  have yMiddleZero : middle.count y = 0 := by omega
  have xAbsentBefore : x ∉ before := List.count_eq_zero.mp xBeforeZero
  have yAbsentBefore : y ∉ before := List.count_eq_zero.mp yBeforeZero
  have xAbsentMiddle : x ∉ middle := List.count_eq_zero.mp xMiddleZero
  have yAbsentMiddle : y ∉ middle := List.count_eq_zero.mp yMiddleZero
  have xAbsentAfter : x ∉ after := List.count_eq_zero.mp xAfterZero
  refine ⟨different, ?_⟩
  rw [shape, precedenceScanList_eq_repeatedFold]
  have folded :
      (before ++ [x] ++ middle ++ [y] ++ after).foldl
          (repeatedPrecedenceStep x y) .neither = .ordered := by
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [repeatedPrecedenceFold_pairFree x y before .neither
      ⟨xAbsentBefore, yAbsentBefore⟩]
    rw [show repeatedPrecedenceStep x y .neither x = .onlyX by
      simp [repeatedPrecedenceStep]]
    rw [repeatedPrecedenceFold_pairFree x y middle .onlyX
      ⟨xAbsentMiddle, yAbsentMiddle⟩]
    rw [show repeatedPrecedenceStep x y .onlyX y = .ordered by
      simp [repeatedPrecedenceStep, Ne.symm different]]
    exact repeatedPrecedenceFold_ordered_of_x_absent
      x y after xAbsentAfter
  simpa [List.append_assoc] using folded

private theorem simpleCompletePrecedence_antisymm
    {whole : List Nat} {x y : Nat}
    (xSimple : whole.count x = 1)
    (ySimple : whole.count y = 1)
    (xy : S5_841.CompletePrecedenceList whole x y)
    (yx : S5_841.CompletePrecedenceList whole y x) :
    x = y := by
  by_cases different : x ≠ y
  · have xMember : x ∈ whole :=
      List.count_pos_iff.mp (by omega)
    have yMember : y ∈ whole :=
      List.count_pos_iff.mp (by omega)
    rcases uniqueSeparatorDistinctOccurrencesOrdered
        different xMember yMember with orderedXY | orderedYX
    · obtain ⟨before, middle, after, shape⟩ := orderedXY
      have xData := xSimple
      rw [shape] at xData
      simp only [List.count_append, List.count_cons] at xData
      simp [different, Ne.symm different] at xData
      have xBeforeZero : before.count x = 0 := by omega
      have xAbsentBefore : x ∉ before :=
        List.count_eq_zero.mp xBeforeZero
      have violated :
          S5_841.precedenceScanList whole y x = .violated := by
        rw [shape]
        simpa [List.append_assoc] using
          precedenceScan_violated_of_repeatedInversion
            (Ne.symm different) before (middle ++ y :: after)
            xAbsentBefore (by simp)
      exact False.elim <| precedenceState_violated_ne_ordered
        (violated.symm.trans yx.2)
    · obtain ⟨before, middle, after, shape⟩ := orderedYX
      have yData := ySimple
      rw [shape] at yData
      simp only [List.count_append, List.count_cons] at yData
      simp [different, Ne.symm different] at yData
      have yBeforeZero : before.count y = 0 := by omega
      have yAbsentBefore : y ∉ before :=
        List.count_eq_zero.mp yBeforeZero
      have violated :
          S5_841.precedenceScanList whole x y = .violated := by
        rw [shape]
        simpa [List.append_assoc] using
          precedenceScan_violated_of_repeatedInversion
            different before (middle ++ x :: after)
            yAbsentBefore (by simp)
      exact False.elim <| precedenceState_violated_ne_ordered
        (violated.symm.trans xy.2)
  · exact Decidable.not_not.mp different

private theorem simpleProjection_pairwiseAux
    (whole : List Nat) :
    ∀ (preWords remaining : List Nat),
      whole = preWords ++ remaining →
      (simpleProjection whole remaining).Pairwise
        (S5_841.CompletePrecedenceList whole)
  | preWords, [], _ => by simp [simpleProjection]
  | preWords, letter :: rest, shape => by
      by_cases letterSimple : whole.count letter = 1
      · have tailPairwise :=
          simpleProjection_pairwiseAux whole
            (preWords ++ [letter]) rest (by
              simpa [List.append_assoc] using shape)
        have related : ∀ tested,
            tested ∈ simpleProjection whole rest →
              S5_841.CompletePrecedenceList whole letter tested := by
          intro tested member
          have filtered := List.mem_filter.mp member
          have testedSimple : whole.count tested = 1 := by
            simpa using of_decide_eq_true filtered.2
          have different : letter ≠ tested := by
            intro equality
            subst tested
            have restPositive : 1 ≤ rest.count letter :=
              List.one_le_count_iff.mpr filtered.1
            rw [shape] at letterSimple
            simp only [List.count_append, List.count_cons_self] at letterSimple
            omega
          obtain ⟨middle, after, restShape⟩ :=
            List.mem_iff_append.mp filtered.1
          exact completePrecedence_of_uniqueOrderedSplit
            different preWords middle after (by
              rw [shape, restShape]
              simp [List.append_assoc]) letterSimple testedSimple
        simpa [simpleProjection, letterSimple] using
          List.Pairwise.cons related tailPairwise
      · have tailPairwise :=
          simpleProjection_pairwiseAux whole
            (preWords ++ [letter]) rest (by
              simpa [List.append_assoc] using shape)
        simpa [simpleProjection, letterSimple] using tailPairwise
termination_by
  _ remaining => remaining.length

private theorem simpleProjection_pairwise (letters : List Nat) :
    (simpleProjection letters letters).Pairwise
      (S5_841.CompletePrecedenceList letters) := by
  simpa using simpleProjection_pairwiseAux letters [] letters (by simp)

private theorem nodup_of_count_le_one
    {letters : List Nat}
    (bounded : ∀ tested, letters.count tested ≤ 1) :
    letters.Nodup := by
  induction letters with
  | nil => simp
  | cons first rest induction =>
      simp only [List.nodup_cons]
      constructor
      · intro member
        have positive : 1 ≤ rest.count first :=
          List.one_le_count_iff.mpr member
        have bound := bounded first
        simp only [List.count_cons_self] at bound
        omega
      · apply induction
        intro tested
        have bound := bounded tested
        by_cases equality : first = tested
        · subst first
          simp only [List.count_cons_self] at bound
          omega
        · simpa [equality] using bound

private theorem simpleProjection_nodup (letters : List Nat) :
    (simpleProjection letters letters).Nodup := by
  apply nodup_of_count_le_one
  intro tested
  by_cases simple : letters.count tested = 1
  · exact Nat.le_trans
      (List.filter_sublist.count_le tested) (by omega)
  · have absent : tested ∉ simpleProjection letters letters := by
      intro member
      have kept := (List.mem_filter.mp member).2
      simp [simpleProjection, simple] at kept
    rw [List.count_eq_zero.mpr absent]
    omega

private theorem simpleProjection_eq_of_counts_precedence
    {left right : List Nat}
    (counts : ∀ tested, left.count tested = right.count tested)
    (precedence : ∀ x y,
      S5_841.CompletePrecedenceList left x y ↔
        S5_841.CompletePrecedenceList right x y) :
    simpleProjection left left = simpleProjection right right := by
  have leftNodup := simpleProjection_nodup left
  have rightNodup := simpleProjection_nodup right
  have support : ∀ tested,
      tested ∈ simpleProjection left left ↔
        tested ∈ simpleProjection right right := by
    intro tested
    constructor
    · intro member
      have filtered := List.mem_filter.mp member
      have leftOne : left.count tested = 1 := by
        simpa using of_decide_eq_true filtered.2
      have rightOne : right.count tested = 1 := by
        rw [← counts tested]
        exact leftOne
      exact List.mem_filter.mpr
        ⟨List.count_pos_iff.mp (by omega), decide_eq_true rightOne⟩
    · intro member
      have filtered := List.mem_filter.mp member
      have rightOne : right.count tested = 1 := by
        simpa using of_decide_eq_true filtered.2
      have leftOne : left.count tested = 1 := by
        rw [counts tested]
        exact rightOne
      exact List.mem_filter.mpr
        ⟨List.count_pos_iff.mp (by omega), decide_eq_true leftOne⟩
  have permutation :
      (simpleProjection left left).Perm
        (simpleProjection right right) := by
    rw [List.perm_iff_count]
    intro tested
    rw [leftNodup.count, rightNodup.count]
    simp [support tested]
  have rightPairwise :
      (simpleProjection right right).Pairwise
        (S5_841.CompletePrecedenceList left) :=
    (simpleProjection_pairwise right).imp fun relation =>
      (precedence _ _).mpr relation
  apply List.Perm.eq_of_pairwise
    (fun x y xMember yMember xy yx => by
      have xSimple : left.count x = 1 := by
        have kept := (List.mem_filter.mp xMember).2
        simpa [simpleProjection] using of_decide_eq_true kept
      have ySimple : left.count y = 1 := by
        have kept := (List.mem_filter.mp yMember).2
        have rightSimple : right.count y = 1 := by
          simpa [simpleProjection] using of_decide_eq_true kept
        rw [counts y]
        exact rightSimple
      exact simpleCompletePrecedence_antisymm xSimple ySimple xy yx)
    (simpleProjection_pairwise left) rightPairwise permutation

/-- Every three-limited list derives to Lee--Li canonical placement without
changing any multiplicity. -/
private theorem existsLeeLiCanonical :
    ∀ letters : List Nat,
      (∀ tested, letters.count tested ≤ 3) →
        ∃ normalized : List Nat,
          LeeLiCanonical normalized ∧
          (∀ tested, normalized.count tested = letters.count tested) ∧
          ListDerives letters normalized
  | [], _ => by
      exact ⟨[], .nil, by simp, S5_107.ListDerives.refl []⟩
  | letter :: rest, bounded => by
      have restBound : ∀ tested, rest.count tested ≤ 3 := by
        intro tested
        have wholeBound := bounded tested
        simp only [List.count_cons] at wholeBound
        omega
      by_cases twoLater : 2 ≤ rest.count letter
      · have restCount : rest.count letter = 2 := by
          have wholeBound := bounded letter
          simp only [List.count_cons_self] at wholeBound
          omega
        obtain ⟨firstGap, secondGap, after, split⟩ :=
          existsTwoOccurrenceSplit letter twoLater
        let remainder :=
          firstGap ++ secondGap ++ [letter] ++ after
        have exposedPermutation :
            (letter :: rest).Perm
              (letter :: letter :: remainder) := by
          rw [List.perm_iff_count]
          intro tested
          by_cases equality : tested = letter
          · subst tested
            simp [split, remainder, List.count_append, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm]
          · simp [split, remainder, List.count_append, equality,
              Ne.symm equality]
        have remainderBound :
            ∀ tested, remainder.count tested ≤ 3 := by
          intro tested
          have targetBound :
              (letter :: letter :: remainder).count tested ≤ 3 := by
            rw [← exposedPermutation.count tested]
            exact bounded tested
          simp only [List.count_cons] at targetBound
          omega
        have remainderShorter :
            remainder.length < (letter :: rest).length := by
          simp only [remainder, split, List.length_append,
            List.length_cons, List.length_nil]
          omega
        obtain ⟨normalizedTail, tailCanonical, tailCounts,
            tailDerivation⟩ :=
          existsLeeLiCanonical remainder remainderBound
        have remainderLetterCount : remainder.count letter = 1 := by
          rw [split] at restCount
          simp only [List.count_append, List.count_cons_self] at restCount
          simp only [remainder, List.count_append,
            List.count_cons_self, List.count_nil]
          omega
        have normalizedTailLetterCount :
            normalizedTail.count letter = 1 := by
          rw [tailCounts letter, remainderLetterCount]
        have gathered :=
          listDerivesGatherMiddleToFirst letter [] firstGap secondGap after
        have normalizedRest :=
          S5_107.ListDerives.prepend [letter, letter] tailDerivation
        refine ⟨letter :: letter :: normalizedTail,
          .triple letter normalizedTail tailCanonical
            normalizedTailLetterCount, ?_, ?_⟩
        · intro tested
          calc
            (letter :: letter :: normalizedTail).count tested =
                (letter :: letter :: remainder).count tested := by
              simp only [List.count_cons]
              rw [tailCounts tested]
            _ = (letter :: rest).count tested :=
              (exposedPermutation.count tested).symm
        · simpa [split, remainder, List.append_assoc] using
            gathered.trans normalizedRest
      · obtain ⟨normalizedTail, tailCanonical, tailCounts,
            tailDerivation⟩ :=
          existsLeeLiCanonical rest restBound
        have restSmall : rest.count letter ≤ 1 := by omega
        have normalizedCounts :
            ∀ tested,
              (letter :: normalizedTail).count tested =
                (letter :: rest).count tested := by
          intro tested
          simp only [List.count_cons]
          rw [tailCounts tested]
        have prefixed :
            ListDerives (letter :: rest)
              (letter :: normalizedTail) := by
          simpa using S5_107.ListDerives.prepend [letter] tailDerivation
        by_cases zero : rest.count letter = 0
        · have normalizedZero : normalizedTail.count letter = 0 := by
            rw [tailCounts letter, zero]
          exact ⟨letter :: normalizedTail,
            .single letter normalizedTail tailCanonical normalizedZero,
            normalizedCounts, prefixed⟩
        · have one : rest.count letter = 1 := by omega
          have normalizedOne : normalizedTail.count letter = 1 := by
            rw [tailCounts letter, one]
          exact ⟨letter :: normalizedTail,
            .double letter normalizedTail tailCanonical normalizedOne,
            normalizedCounts, prefixed⟩
termination_by letters => letters.length
decreasing_by
  · exact remainderShorter
  · simp

/-! ## Factor signatures after reduction -/

private theorem periodExponentEqOfCappedAndParity
    {left right : Nat}
    (capped : Nat.min left 2 = Nat.min right 2)
    (parity : left % 2 = right % 2) :
    periodTwoFromTwoExponent left =
      periodTwoFromTwoExponent right := by
  by_cases leftSmall : left < 2
  · have leftMin : left.min 2 = left :=
      Nat.min_eq_left (by omega)
    have rightSmall : right < 2 := by
      by_cases small : right < 2
      · exact small
      · have rightMin : right.min 2 = 2 :=
          Nat.min_eq_right (by omega)
        rw [leftMin, rightMin] at capped
        omega
    have rightMin : right.min 2 = right :=
      Nat.min_eq_left (by omega)
    have equal : left = right := by
      rw [leftMin, rightMin] at capped
      exact capped
    subst right
    rfl
  · have leftLarge : 2 ≤ left := by omega
    have rightLarge : 2 ≤ right := by
      by_cases large : 2 ≤ right
      · exact large
      · have leftMin : left.min 2 = 2 :=
          Nat.min_eq_right leftLarge
        have rightMin : right.min 2 = right :=
          Nat.min_eq_left (by omega)
        rw [leftMin, rightMin] at capped
        omega
    unfold periodTwoFromTwoExponent
    rw [if_neg leftSmall, if_neg (by omega : ¬ right < 2), parity]

private theorem factorValid_periodExponentEq
    (identity : Identity Nat)
    (m20Valid : identity.SatisfiedBy S5_841.table.semigroup)
    (cyclicValid : identity.SatisfiedBy cyclicTwo.semigroup) :
    ∀ tested,
      periodTwoFromTwoExponent (identity.lhs.toList.count tested) =
        periodTwoFromTwoExponent (identity.rhs.toList.count tested) := by
  intro tested
  have signature :=
    S5_841.catalogueValid_sameM20Signature identity m20Valid
  exact periodExponentEqOfCappedAndParity
    (by
      simpa [S5_841.CappedMultiplicity] using
        signature.cappedMultiplicity tested)
    (cyclicValid_parity_eq identity cyclicValid tested)

private theorem factorValid_m20Equivalent
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy S5_841.table.semigroup) :
    S5_841.M20ListEquivalent identity.lhs.toList identity.rhs.toList :=
  S5_841.M20ListEquivalent.of_valid identity
    (S5_841.publishedM20ToCatalogue.pullback_identity identity valid)

/-! ## Canonical block assembly -/

private theorem listDerivesCanonicalSegmented
    (sourceTail targetTail sourcePre pre : List Nat)
    (sourceCanonical :
      SimpleSplitCanonical (sourcePre ++ sourceTail))
    (targetCanonical :
      SimpleSplitCanonical (pre ++ targetTail))
    (sourceBound : ∀ letter,
      (sourcePre ++ sourceTail).count letter ≤ 3)
    (targetBound : ∀ letter,
      (pre ++ targetTail).count letter ≤ 3)
    (totalCounts : ∀ letter,
      (sourcePre ++ sourceTail).count letter =
        (pre ++ targetTail).count letter)
    (prefixCounts : ∀ letter,
      sourcePre.count letter = pre.count letter)
    (simpleEqual :
      simpleProjection (sourcePre ++ sourceTail) sourceTail =
        simpleProjection (pre ++ targetTail) targetTail)
    (precedence : ∀ x y,
      S5_841.CompletePrecedenceList
          (sourcePre ++ sourceTail) x y ↔
        S5_841.CompletePrecedenceList
          (pre ++ targetTail) x y)
    (currentCounts : ∀ letter,
      (pre ++ sourceTail).count letter =
        (pre ++ targetTail).count letter)
    (equivalent :
      S5_841.M20ListEquivalent
        (pre ++ sourceTail) (pre ++ targetTail)) :
    ListDerives (pre ++ sourceTail) (pre ++ targetTail) := by
  cases sourceProjection :
      simpleProjection (sourcePre ++ sourceTail) sourceTail with
  | nil =>
      have targetProjection :
          simpleProjection (pre ++ targetTail) targetTail = [] := by
        rw [← simpleEqual, sourceProjection]
      have sourceNonlinear := nonlinear_of_simpleProjection_nil
        (sourcePre ++ sourceTail) sourceTail sourceProjection
      have tailPermutation : sourceTail.Perm targetTail := by
        rw [List.perm_iff_count]
        intro letter
        have total := totalCounts letter
        have prefixEq := prefixCounts letter
        simp only [List.count_append] at total
        omega
      have sourceRepeated : ∀ letter, letter ∈ sourceTail →
          2 ≤ (pre ++ sourceTail ++ []).count letter := by
        intro letter member
        have originalPositive :
            0 < (sourcePre ++ sourceTail).count letter :=
          List.count_pos_iff.mpr (List.mem_append_right sourcePre member)
        have originalNotOne := sourceNonlinear letter member
        have currentToOriginal :
            (pre ++ sourceTail).count letter =
              (sourcePre ++ sourceTail).count letter :=
          (currentCounts letter).trans (totalCounts letter).symm
        simpa using (show 2 ≤ (pre ++ sourceTail).count letter by
          rw [currentToOriginal]
          omega)
      simpa using
        listDerivesRepeatedBlockPermutationAgainst
          targetTail sourceTail pre [] [] tailPermutation sourceRepeated
          (by simpa using currentCounts) (by simpa using equivalent)
  | cons separator remaining =>
      have targetProjection :
          simpleProjection (pre ++ targetTail) targetTail =
            separator :: remaining := by
        rw [← simpleEqual, sourceProjection]
      obtain ⟨sourceBlock, sourceRest, sourceShape,
          sourceBlockNonlinear, sourceRestProjection,
          sourceSeparator⟩ :=
        simpleProjection_cons_split sourcePre sourceTail separator
          remaining sourceProjection
      obtain ⟨targetBlock, targetRest, targetShape,
          _targetBlockNonlinear, targetRestProjection,
          targetSeparator⟩ :=
        simpleProjection_cons_split pre targetTail separator
          remaining targetProjection
      have sourceRestShorter : sourceRest.length < sourceTail.length := by
        rw [sourceShape]
        simp only [List.length_append, List.length_cons]
        omega
      have sourceCanonicalNorm :
          SimpleSplitCanonical
            (sourcePre ++ sourceBlock ++ separator :: sourceRest) := by
        simpa [sourceShape, List.append_assoc] using sourceCanonical
      have targetCanonicalNorm :
          SimpleSplitCanonical
            (pre ++ targetBlock ++ separator :: targetRest) := by
        simpa [targetShape, List.append_assoc] using targetCanonical
      have sourceBoundNorm : ∀ letter,
          (sourcePre ++ sourceBlock ++ separator :: sourceRest).count
              letter ≤ 3 := by
        intro letter
        simpa [sourceShape, List.append_assoc] using sourceBound letter
      have targetBoundNorm : ∀ letter,
          (pre ++ targetBlock ++ separator :: targetRest).count
              letter ≤ 3 := by
        intro letter
        simpa [targetShape, List.append_assoc] using targetBound letter
      have totalCountsNorm : ∀ letter,
          (sourcePre ++ sourceBlock ++ separator :: sourceRest).count
              letter =
            (pre ++ targetBlock ++ separator :: targetRest).count
              letter := by
        intro letter
        simpa [sourceShape, targetShape, List.append_assoc] using
          totalCounts letter
      have currentCountsNorm : ∀ letter,
          (pre ++ sourceBlock ++ separator :: sourceRest).count letter =
            (pre ++ targetBlock ++ separator :: targetRest).count
              letter := by
        intro letter
        simpa [sourceShape, targetShape, List.append_assoc] using
          currentCounts letter
      have precedenceNorm : ∀ x y,
          S5_841.CompletePrecedenceList
              (sourcePre ++ sourceBlock ++ separator :: sourceRest) x y ↔
            S5_841.CompletePrecedenceList
              (pre ++ targetBlock ++ separator :: targetRest) x y := by
        intro x y
        simpa [sourceShape, targetShape, List.append_assoc] using
          precedence x y
      have equivalentNorm :
          S5_841.M20ListEquivalent
            (pre ++ sourceBlock ++ separator :: sourceRest)
            (pre ++ targetBlock ++ separator :: targetRest) := by
        simpa [sourceShape, targetShape, List.append_assoc] using equivalent
      have sourceSeparatorNorm :
          (sourcePre ++ sourceBlock ++ separator :: sourceRest).count
              separator = 1 := by
        simpa [sourceShape, List.append_assoc] using sourceSeparator
      have targetSeparatorNorm :
          (pre ++ targetBlock ++ separator :: targetRest).count
              separator = 1 := by
        simpa [targetShape, List.append_assoc] using targetSeparator
      have blockPermutation : sourceBlock.Perm targetBlock := by
        rw [List.perm_iff_count]
        intro letter
        by_cases equalSeparator : letter = separator
        · subst letter
          have sourceData := sourceSeparatorNorm
          have targetData := targetSeparatorNorm
          simp only [List.count_append, List.count_cons_self] at sourceData targetData
          omega
        · by_cases positive :
              0 <
                (sourcePre ++ sourceBlock ++ separator :: sourceRest).count
                  letter
          · have cut := prefixCount_eq_of_canonicalPrecedence
              equalSeparator (sourcePre ++ sourceBlock) sourceRest
              (pre ++ targetBlock) targetRest
              (by simpa [List.append_assoc] using totalCountsNorm letter)
              (by simpa [List.append_assoc] using positive)
              (by simpa [List.append_assoc] using sourceBoundNorm letter)
              (by simpa [List.append_assoc] using sourceSeparatorNorm)
              (by simpa [List.append_assoc] using targetSeparatorNorm)
              (by simpa [List.append_assoc] using sourceCanonicalNorm)
              (by simpa [List.append_assoc] using targetCanonicalNorm)
              (by
                intro x y
                simpa [List.append_assoc] using precedenceNorm x y)
            have prefixEq := prefixCounts letter
            simp only [List.count_append] at cut
            omega
          · have sourceZero :
                (sourcePre ++ sourceBlock ++ separator :: sourceRest).count
                    letter = 0 := by
              omega
            have targetZero :
                (pre ++ targetBlock ++ separator :: targetRest).count
                    letter = 0 := by
              rw [← totalCountsNorm letter]
              exact sourceZero
            simp only [List.count_append, List.count_cons] at sourceZero targetZero
            simp [equalSeparator, Ne.symm equalSeparator] at sourceZero targetZero
            omega
      have sourceRepeated : ∀ letter, letter ∈ sourceBlock →
          2 ≤
            (pre ++ sourceBlock ++ separator :: sourceRest).count letter := by
        intro letter member
        have originalPositive :
            0 <
              (sourcePre ++ sourceBlock ++ separator :: sourceRest).count
                letter :=
          List.count_pos_iff.mpr (by simp [member])
        have originalNotOne :
            (sourcePre ++ sourceBlock ++ separator :: sourceRest).count
                letter ≠ 1 := by
          simpa [sourceShape, List.append_assoc] using
            sourceBlockNonlinear letter member
        have currentToOriginal :
            (pre ++ sourceBlock ++ separator :: sourceRest).count letter =
              (sourcePre ++ sourceBlock ++ separator :: sourceRest).count
                letter :=
          (currentCountsNorm letter).trans (totalCountsNorm letter).symm
        rw [currentToOriginal]
        omega
      have move := listDerivesRepeatedBlockPermutationAgainst
        targetBlock sourceBlock pre (separator :: sourceRest)
        (separator :: targetRest) blockPermutation sourceRepeated
        currentCountsNorm equivalentNorm
      have fullPermutation :
          (pre ++ sourceBlock ++ separator :: sourceRest).Perm
            (pre ++ targetBlock ++ separator :: sourceRest) := by
        simpa [List.append_assoc] using
          List.Perm.append
            (List.Perm.append (List.Perm.refl pre) blockPermutation)
            (List.Perm.refl (separator :: sourceRest))
      let nextSourcePre := sourcePre ++ sourceBlock ++ [separator]
      let nextPre := pre ++ targetBlock ++ [separator]
      have nextSourceCanonical :
          SimpleSplitCanonical (nextSourcePre ++ sourceRest) := by
        simpa [nextSourcePre, List.append_assoc] using sourceCanonicalNorm
      have nextTargetCanonical :
          SimpleSplitCanonical (nextPre ++ targetRest) := by
        simpa [nextPre, List.append_assoc] using targetCanonicalNorm
      have nextSourceBound : ∀ letter,
          (nextSourcePre ++ sourceRest).count letter ≤ 3 := by
        intro letter
        simpa [nextSourcePre, List.append_assoc] using
          sourceBoundNorm letter
      have nextTargetBound : ∀ letter,
          (nextPre ++ targetRest).count letter ≤ 3 := by
        intro letter
        simpa [nextPre, List.append_assoc] using targetBoundNorm letter
      have nextTotalCounts : ∀ letter,
          (nextSourcePre ++ sourceRest).count letter =
            (nextPre ++ targetRest).count letter := by
        intro letter
        simpa [nextSourcePre, nextPre, List.append_assoc] using
          totalCountsNorm letter
      have nextPrefixCounts : ∀ letter,
          nextSourcePre.count letter = nextPre.count letter := by
        intro letter
        simp only [nextSourcePre, nextPre, List.count_append]
        rw [prefixCounts letter, blockPermutation.count letter]
      have nextSimpleEqual :
          simpleProjection (nextSourcePre ++ sourceRest) sourceRest =
            simpleProjection (nextPre ++ targetRest) targetRest := by
        calc
          simpleProjection (nextSourcePre ++ sourceRest) sourceRest =
              remaining := by
            simpa [nextSourcePre, sourceShape, List.append_assoc] using
              sourceRestProjection
          _ = simpleProjection (nextPre ++ targetRest) targetRest := by
            simpa [nextPre, targetShape, List.append_assoc] using
              targetRestProjection.symm
      have nextPrecedence : ∀ x y,
          S5_841.CompletePrecedenceList
              (nextSourcePre ++ sourceRest) x y ↔
            S5_841.CompletePrecedenceList
              (nextPre ++ targetRest) x y := by
        intro x y
        simpa [nextSourcePre, nextPre, List.append_assoc] using
          precedenceNorm x y
      have nextCurrentCounts : ∀ letter,
          (nextPre ++ sourceRest).count letter =
            (nextPre ++ targetRest).count letter := by
        intro letter
        calc
          (nextPre ++ sourceRest).count letter =
              (pre ++ targetBlock ++ separator :: sourceRest).count
                letter := by simp [nextPre, List.append_assoc]
          _ = (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter := (fullPermutation.count letter).symm
          _ = (pre ++ targetBlock ++ separator :: targetRest).count
                letter := currentCountsNorm letter
          _ = (nextPre ++ targetRest).count letter := by
            simp [nextPre, List.append_assoc]
      have nextEquivalent :
          S5_841.M20ListEquivalent
            (nextPre ++ sourceRest) (nextPre ++ targetRest) := by
        have moved :=
          (m20EquivalentOfListDerives move).symm.trans equivalentNorm
        simpa [nextPre, List.append_assoc] using moved
      have recurse := listDerivesCanonicalSegmented
        sourceRest targetRest nextSourcePre nextPre
        nextSourceCanonical nextTargetCanonical nextSourceBound
        nextTargetBound nextTotalCounts nextPrefixCounts nextSimpleEqual
        nextPrecedence nextCurrentCounts nextEquivalent
      simpa [sourceShape, targetShape, List.append_assoc] using
        move.trans (by simpa [nextPre, List.append_assoc] using recurse)
termination_by sourceTail.length
decreasing_by
  exact sourceRestShorter

private theorem derivesOfFactorValid
    (identity : Identity Nat)
    (m20Valid : identity.SatisfiedBy S5_841.table.semigroup)
    (cyclicValid : identity.SatisfiedBy cyclicTwo.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  obtain ⟨leftReduced, leftBound, leftCounts, leftReduction⟩ :=
    existsPeriodReduction identity.lhs.toList
  obtain ⟨rightReduced, rightBound, rightCounts, rightReduction⟩ :=
    existsPeriodReduction identity.rhs.toList
  have exponentEq :=
    factorValid_periodExponentEq identity m20Valid cyclicValid
  have reducedCounts : ∀ tested,
      leftReduced.count tested = rightReduced.count tested := by
    intro tested
    calc
      leftReduced.count tested =
          periodTwoFromTwoExponent
            (identity.lhs.toList.count tested) := (leftCounts tested).symm
      _ = periodTwoFromTwoExponent
            (identity.rhs.toList.count tested) := exponentEq tested
      _ = rightReduced.count tested := rightCounts tested
  obtain ⟨leftNormalized, leftCanonical, leftNormalizedCounts,
      leftNormalization⟩ :=
    existsLeeLiCanonical leftReduced leftBound
  obtain ⟨rightNormalized, rightCanonical, rightNormalizedCounts,
      rightNormalization⟩ :=
    existsLeeLiCanonical rightReduced rightBound
  have normalizedCounts : ∀ tested,
      leftNormalized.count tested = rightNormalized.count tested := by
    intro tested
    calc
      leftNormalized.count tested = leftReduced.count tested :=
        leftNormalizedCounts tested
      _ = rightReduced.count tested := reducedCounts tested
      _ = rightNormalized.count tested :=
        (rightNormalizedCounts tested).symm
  have leftNormalizedBound : ∀ tested,
      leftNormalized.count tested ≤ 3 := by
    intro tested
    rw [leftNormalizedCounts tested]
    exact leftBound tested
  have rightNormalizedBound : ∀ tested,
      rightNormalized.count tested ≤ 3 := by
    intro tested
    rw [rightNormalizedCounts tested]
    exact rightBound tested
  have originalEquivalent := factorValid_m20Equivalent identity m20Valid
  have leftToNormalized :
      S5_841.M20ListEquivalent
        identity.lhs.toList leftNormalized :=
    m20EquivalentOfListDerives
      (leftReduction.trans leftNormalization)
  have rightToNormalized :
      S5_841.M20ListEquivalent
        identity.rhs.toList rightNormalized :=
    m20EquivalentOfListDerives
      (rightReduction.trans rightNormalization)
  have normalizedEquivalent :
      S5_841.M20ListEquivalent leftNormalized rightNormalized :=
    leftToNormalized.symm.trans
      (originalEquivalent.trans rightToNormalized)
  have normalizedPrecedence : ∀ x y,
      S5_841.CompletePrecedenceList leftNormalized x y ↔
        S5_841.CompletePrecedenceList rightNormalized x y := by
    intro x y
    exact S5_841.m20ListEquivalent_completePrecedenceList
      normalizedEquivalent x y
  have simpleEqual :
      simpleProjection leftNormalized leftNormalized =
        simpleProjection rightNormalized rightNormalized :=
    simpleProjection_eq_of_counts_precedence
      normalizedCounts normalizedPrecedence
  have middleRaw := listDerivesCanonicalSegmented
    leftNormalized rightNormalized [] []
    (by simpa using leftCanonical.simpleSplitCanonical)
    (by simpa using rightCanonical.simpleSplitCanonical)
    (by simpa using leftNormalizedBound)
    (by simpa using rightNormalizedBound)
    (by simpa using normalizedCounts)
    (by simp)
    (by simpa using simpleEqual)
    (by simpa using normalizedPrecedence)
    (by simpa using normalizedCounts)
    (by simpa using normalizedEquivalent)
  have middle : ListDerives leftNormalized rightNormalized := by
    simpa using middleRaw
  have full : ListDerives identity.lhs.toList identity.rhs.toList :=
    leftReduction.trans <| leftNormalization.trans <|
      middle.trans <| rightNormalization.symm.trans rightReduction.symm
  cases identity with
  | mk left right =>
      cases left with
      | mk leftHead leftTail =>
          cases right with
          | mk rightHead rightTail =>
              simpa [S5_107.listWordOfCons] using
                S5_107.ListDerives.toWord full

/-! ## Split factor projections -/

private def toM20 (value : Fin 6) : Fin 5 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 0 else
        if value = 3 then 2 else
          if value = 4 then 3 else 4

private def fromM20 (value : Fin 5) : Fin 6 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 3 else
        if value = 3 then 4 else 5

private def m20Projection :
    SplitSurjection table.semigroup
      SemigroupBasis.CoRoots.S5_841.table.semigroup where
  toFun := toM20
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fromM20
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

private def toCyclicTwo (value : Fin 6) : Fin 2 :=
  if value = 2 then 1 else 0

private def fromCyclicTwo (value : Fin 2) : Fin 6 :=
  if value = 0 then 0 else 2

private def cyclicProjection :
    SplitSurjection table.semigroup cyclicTwo.semigroup where
  toFun := toCyclicTwo
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  preimage := fromCyclicTwo
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

private def factorPair :
    SubdirectPair table.semigroup
      SemigroupBasis.CoRoots.S5_841.table.semigroup
      cyclicTwo.semigroup where
  left := m20Projection
  right := cyclicProjection
  jointlyInjective := by
    intro left right equality
    apply Fin.ext
    revert left right
    decide

theorem valid_m20
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.CoRoots.S5_841.table.semigroup :=
  m20Projection.pushforwardIdentity identity valid

theorem valid_cyclicTwo
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy cyclicTwo.semigroup :=
  cyclicProjection.pushforwardIdentity identity valid

private def intersectionBasis :
    IntersectionBasis S5_841.table.semigroup cyclicTwo.semigroup basis where
  leftModels := m20Models
  rightModels := cyclicModels
  complete := derivesOfFactorValid

/-- Unconditional Lee--Li Condition 6 basis theorem for the exact Smallsemi
representative `S6_8874`. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  IntersectionBasis.basisFor intersectionBasis factorPair

/-- The reversed Condition 6 system is a basis for the opposite
representative. -/
theorem opposite_representative_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.S6_8874
