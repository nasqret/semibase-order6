import SemigroupBasis.CoRoots.Order6D2D4SuffixTraceV2M1Concrete
import SemigroupBasis.CoRoots.S5_381Invariant

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6D2D4SuffixTrace.V2

open SemigroupBasis
open SemigroupBasis.CoRoots
open SemigroupBasis.CoRoots.Order6D2D4SuffixTrace

/-- `x y` begins with a globally simple letter and ends at the final
occurrence of a globally multiple letter. -/
def SimpleLastFactor (word : Word Nat) (x y : Nat) : Prop :=
  S5_107.SimpleIn word x ∧
    2 ≤ word.toList.count y ∧
      ∃ before after,
        word.toList = before ++ x :: y :: after ∧ y ∉ after

abbrev SameFSL (left right : Word Nat) : Prop :=
  ∀ x y, SimpleLastFactor left x y ↔ SimpleLastFactor right x y

/-- The exact zero-based Lee--Zhang valuation. -/
def fslValuation (x y : Nat) : Nat → Fin 6 :=
  fun letter => if letter = x then 2 else if letter = y then 4 else 5

@[simp] theorem fslValuation_x (x y : Nat) :
    fslValuation x y x = 2 := by
  simp [fslValuation]

theorem fslValuation_y {x y : Nat} (different : x ≠ y) :
    fslValuation x y y = 4 := by
  simp [fslValuation, Ne.symm different]

theorem fslValuation_other {x y letter : Nat}
    (notX : letter ≠ x) (notY : letter ≠ y) :
    fslValuation x y letter = 5 := by
  simp [fslValuation, notX, notY]

private def scanStep (G : Semigroup S) (valuation : Nat → S)
    (state : Option S) (letter : Nat) : Option S :=
  match state with
  | none => some (valuation letter)
  | some current => some (G.mul current (valuation letter))

private def scanFrom (G : Semigroup S) (valuation : Nat → S)
    (state : Option S) (letters : List Nat) : Option S :=
  letters.foldl (scanStep G valuation) state

private theorem scanFrom_eq_foldl (G : Semigroup S)
    (valuation : Nat → S) (state : Option S) (letters : List Nat) :
    scanFrom G valuation state letters =
      List.foldl (scanStep G valuation) state letters := rfl

private theorem scanFrom_append (G : Semigroup S) (valuation : Nat → S)
    (state : Option S) (left right : List Nat) :
    scanFrom G valuation state (left ++ right) =
      scanFrom G valuation (scanFrom G valuation state left) right := by
  simp [scanFrom, List.foldl_append]

private theorem scanFrom_some (G : Semigroup S) (valuation : Nat → S)
    (initial : S) (letters : List Nat) :
    scanFrom G valuation (some initial) letters =
      some (letters.foldl (fun state letter =>
        G.mul state (valuation letter)) initial) := by
  induction letters generalizing initial with
  | nil => rfl
  | cons first rest ih =>
      simp only [scanFrom, List.foldl_cons, scanStep]
      exact ih (G.mul initial (valuation first))

private theorem scanFrom_toList (G : Semigroup S)
    (valuation : Nat → S) (word : Word Nat) :
    scanFrom G valuation none word.toList =
      some (G.eval valuation word) := by
  cases word with
  | mk head tail =>
      simp only [Word.toList, scanFrom, List.foldl_cons, scanStep,
        Semigroup.eval]
      exact scanFrom_some G valuation (valuation head) tail

private def Background : Option (Fin 6) → Prop
  | none => True
  | some state => state = 3 ∨ state = 4 ∨ state = 5

private theorem d2_step_background
    {x y letter : Nat} (different : x ≠ y)
    (notX : letter ≠ x) (state : Option (Fin 6))
    (background : Background state) :
    Background
      (scanStep d2G (fslValuation x y) state letter) := by
  by_cases isY : letter = y
  · subst letter
    have yNotX : y ≠ x := Ne.symm different
    cases state with
    | none =>
        simp [Background, scanStep, fslValuation, yNotX]
    | some current =>
        rcases background with currentEq | currentEq | currentEq
        · subst current
          simp [Background, scanStep, fslValuation, yNotX, d2_mul_3_4]
        · subst current
          simp [Background, scanStep, fslValuation, yNotX, d2_mul_4_4]
        · subst current
          simp [Background, scanStep, fslValuation, yNotX, d2_mul_5_4]
  · cases state with
    | none =>
        simp [Background, scanStep, fslValuation, notX, isY]
    | some current =>
        rcases background with currentEq | currentEq | currentEq
        · subst current
          simp [Background, scanStep, fslValuation, notX, isY,
            d2_mul_3_5]
        · subst current
          simp [Background, scanStep, fslValuation, notX, isY,
            d2_mul_4_5]
        · subst current
          simp [Background, scanStep, fslValuation, notX, isY,
            d2_mul_5_5]

private theorem d2_scan_background
    {x y : Nat} (different : x ≠ y) (letters : List Nat)
    (xFree : x ∉ letters) (state : Option (Fin 6))
    (background : Background state) :
    Background
      (scanFrom d2G (fslValuation x y) state letters) := by
  induction letters generalizing state with
  | nil => simpa [scanFrom] using background
  | cons first rest ih =>
      have firstNotX : first ≠ x := by
        intro equal
        subst first
        exact xFree (by simp)
      have restFree : x ∉ rest := by
        intro member
        exact xFree (List.Mem.tail first member)
      simp only [scanFrom, List.foldl_cons]
      exact ih restFree
        (scanStep d2G (fslValuation x y) state first)
        (d2_step_background different firstNotX state background)

private theorem d2_scan_prefix_x
    {x y : Nat} (different : x ≠ y) (before : List Nat)
    (xFree : x ∉ before) :
    scanFrom d2G (fslValuation x y) none
        (before ++ [x]) = some 2 := by
  rw [scanFrom_append]
  have background :=
    d2_scan_background different before xFree none (by trivial)
  generalize priorEq :
      scanFrom d2G (fslValuation x y) none before = prior
      at background ⊢
  cases prior with
  | none => simp [scanFrom, scanStep, fslValuation]
  | some current =>
      rcases background with currentEq | currentEq | currentEq
      · subst current
        simp [scanFrom, scanStep, fslValuation, d2_mul_3_2]
      · subst current
        simp [scanFrom, scanStep, fslValuation, d2_mul_4_2]
      · subst current
        simp [scanFrom, scanStep, fslValuation, d2_mul_5_2]

private theorem d2_scan_zero
    {x y : Nat} (different : x ≠ y) (letters : List Nat)
    (xFree : x ∉ letters) :
    scanFrom d2G (fslValuation x y) (some 0) letters =
      some 0 := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      have firstNotX : first ≠ x := by
        intro equal
        subst first
        exact xFree (by simp)
      have restFree : x ∉ rest := by
        intro member
        exact xFree (List.Mem.tail first member)
      by_cases firstY : first = y
      · subst first
        have yNotX : y ≠ x := Ne.symm different
        simp only [scanFrom, List.foldl_cons, scanStep]
        rw [fslValuation_y different, d2_mul_0_4]
        exact ih restFree
      · simp only [scanFrom, List.foldl_cons, scanStep]
        rw [fslValuation_other firstNotX firstY, d2_mul_0_5]
        exact ih restFree

private theorem d2_scan_one_eq_one_iff
    {x y : Nat} (different : x ≠ y) (letters : List Nat)
    (xFree : x ∉ letters) :
    scanFrom d2G (fslValuation x y) (some 1) letters =
        some 1 ↔ y ∉ letters := by
  induction letters with
  | nil => simp [scanFrom]
  | cons first rest ih =>
      have firstNotX : first ≠ x := by
        intro equal
        subst first
        exact xFree (by simp)
      have restFree : x ∉ rest := by
        intro member
        exact xFree (List.Mem.tail first member)
      by_cases firstY : first = y
      · subst first
        simp only [scanFrom, List.foldl_cons, scanStep]
        rw [fslValuation_y different, d2_mul_1_4]
        simp only [← scanFrom_eq_foldl]
        rw [d2_scan_zero different rest restFree]
        simp
      · simp only [scanFrom, List.foldl_cons, scanStep]
        rw [fslValuation_other firstNotX firstY, d2_mul_1_5]
        simp only [← scanFrom_eq_foldl]
        rw [ih restFree]
        simp [Ne.symm firstY]

private theorem d2_scan_suffix_eq_one_iff
    {x y : Nat} (different : x ≠ y) (after : List Nat)
    (xFree : x ∉ after) :
    scanFrom d2G (fslValuation x y) (some 2) after =
        some 1 ↔
      ∃ rest, after = y :: rest ∧ y ∉ rest := by
  cases after with
  | nil => simp [scanFrom]
  | cons first rest =>
      have firstNotX : first ≠ x := by
        intro equal
        subst first
        exact xFree (by simp)
      have restFree : x ∉ rest := by
        intro member
        exact xFree (List.Mem.tail first member)
      by_cases firstY : first = y
      · subst first
        simp only [scanFrom, List.foldl_cons, scanStep]
        rw [fslValuation_y different, d2_mul_2_4]
        simp only [← scanFrom_eq_foldl]
        rw [d2_scan_one_eq_one_iff different rest restFree]
        simp
      · simp only [scanFrom, List.foldl_cons, scanStep]
        rw [fslValuation_other firstNotX firstY, d2_mul_2_5]
        simp only [← scanFrom_eq_foldl]
        rw [d2_scan_zero different rest restFree]
        simp [firstY]

private theorem unique_split_free
    {letters before after : List Nat} {x : Nat}
    (countOne : letters.count x = 1)
    (split : letters = before ++ x :: after) :
    x ∉ before ∧ x ∉ after := by
  have equation := countOne
  rw [split] at equation
  simp only [List.count_append, List.count_cons] at equation
  simp at equation
  have beforeZero : before.count x = 0 := by omega
  have afterZero : after.count x = 0 := by omega
  exact ⟨List.count_eq_zero.mp beforeZero,
    List.count_eq_zero.mp afterZero⟩

/-- D2 evaluates to state `1` exactly on the FSL relation under the inherited
simple/multiple signature assumptions. -/
theorem d2_eval_eq_one_iff_fsl
    (word : Word Nat) (x y : Nat)
    (xSimple : S5_107.SimpleIn word x)
    (yMultiple : 2 ≤ word.toList.count y) :
    d2G.eval (fslValuation x y) word = 1 ↔
      SimpleLastFactor word x y := by
  have different : x ≠ y := by
    intro equal
    subst y
    unfold S5_107.SimpleIn at xSimple
    omega
  constructor
  · intro evaluated
    have xMember : x ∈ word.toList :=
      List.count_pos_iff.mp (by
        unfold S5_107.SimpleIn at xSimple
        omega)
    obtain ⟨before, after, split⟩ :=
      List.mem_iff_append.mp xMember
    have free := unique_split_free xSimple split
    have scannedPrefix := d2_scan_prefix_x different before free.1
    have scanWhole :
        scanFrom d2G (fslValuation x y) none word.toList =
          scanFrom d2G (fslValuation x y) (some 2) after := by
      rw [split]
      rw [show before ++ x :: after = (before ++ [x]) ++ after by simp]
      rw [scanFrom_append, scannedPrefix]
    have scannedSuffix :
        scanFrom d2G (fslValuation x y) (some 2) after =
          some 1 := by
      rw [← scanWhole, scanFrom_toList, evaluated]
    obtain ⟨rest, afterEq, yFree⟩ :=
      (d2_scan_suffix_eq_one_iff different after free.2).mp scannedSuffix
    refine ⟨xSimple, yMultiple, before, rest, ?_, yFree⟩
    rw [split, afterEq]
  · rintro ⟨_, _, before, after, split, yFree⟩
    have splitAtX :
        word.toList = before ++ x :: (y :: after) := by
      simpa using split
    have free := unique_split_free xSimple splitAtX
    have scannedPrefix := d2_scan_prefix_x different before free.1
    have scannedSuffix :
        scanFrom d2G (fslValuation x y) (some 2)
            (y :: after) = some 1 :=
      (d2_scan_suffix_eq_one_iff different (y :: after) free.2).mpr
        ⟨after, rfl, yFree⟩
    have scanWhole :
        scanFrom d2G (fslValuation x y) none word.toList =
          some 1 := by
      rw [splitAtX]
      rw [show before ++ x :: y :: after =
          (before ++ [x]) ++ (y :: after) by simp]
      rw [scanFrom_append, scannedPrefix]
      exact scannedSuffix
    rw [scanFrom_toList] at scanWhole
    injection scanWhole

private theorem d4_step_background
    {x y letter : Nat} (different : x ≠ y)
    (notX : letter ≠ x) (state : Option (Fin 6))
    (background : Background state) :
    Background (scanStep d4G (fslValuation x y) state letter) := by
  by_cases isY : letter = y
  · subst letter
    have yNotX : y ≠ x := Ne.symm different
    cases state with
    | none => simp [Background, scanStep, fslValuation, yNotX]
    | some current =>
        rcases background with currentEq | currentEq | currentEq
        · subst current
          simp [Background, scanStep, fslValuation, yNotX, d4_mul_3_4]
        · subst current
          simp [Background, scanStep, fslValuation, yNotX, d4_mul_4_4]
        · subst current
          simp [Background, scanStep, fslValuation, yNotX, d4_mul_5_4]
  · cases state with
    | none => simp [Background, scanStep, fslValuation, notX, isY]
    | some current =>
        rcases background with currentEq | currentEq | currentEq
        · subst current
          simp [Background, scanStep, fslValuation, notX, isY,
            d4_mul_3_5]
        · subst current
          simp [Background, scanStep, fslValuation, notX, isY,
            d4_mul_4_5]
        · subst current
          simp [Background, scanStep, fslValuation, notX, isY,
            d4_mul_5_5]

private theorem d4_scan_background
    {x y : Nat} (different : x ≠ y) (letters : List Nat)
    (xFree : x ∉ letters) (state : Option (Fin 6))
    (background : Background state) :
    Background (scanFrom d4G (fslValuation x y) state letters) := by
  induction letters generalizing state with
  | nil => simpa [scanFrom] using background
  | cons first rest ih =>
      have firstNotX : first ≠ x := by
        intro equal
        subst first
        exact xFree (by simp)
      have restFree : x ∉ rest := by
        intro member
        exact xFree (List.Mem.tail first member)
      simp only [scanFrom, List.foldl_cons]
      exact ih restFree
        (scanStep d4G (fslValuation x y) state first)
        (d4_step_background different firstNotX state background)

private theorem d4_scan_prefix_x
    {x y : Nat} (different : x ≠ y) (before : List Nat)
    (xFree : x ∉ before) :
    scanFrom d4G (fslValuation x y) none (before ++ [x]) = some 2 := by
  rw [scanFrom_append]
  have background :=
    d4_scan_background different before xFree none (by trivial)
  generalize priorEq :
      scanFrom d4G (fslValuation x y) none before = prior
      at background ⊢
  cases prior with
  | none => simp [scanFrom, scanStep, fslValuation]
  | some current =>
      rcases background with currentEq | currentEq | currentEq
      · subst current
        simp [scanFrom, scanStep, fslValuation, d4_mul_3_2]
      · subst current
        simp [scanFrom, scanStep, fslValuation, d4_mul_4_2]
      · subst current
        simp [scanFrom, scanStep, fslValuation, d4_mul_5_2]

private theorem d4_scan_zero
    {x y : Nat} (different : x ≠ y) (letters : List Nat)
    (xFree : x ∉ letters) :
    scanFrom d4G (fslValuation x y) (some 0) letters = some 0 := by
  induction letters with
  | nil => rfl
  | cons first rest ih =>
      have firstNotX : first ≠ x := by
        intro equal
        subst first
        exact xFree (by simp)
      have restFree : x ∉ rest := by
        intro member
        exact xFree (List.Mem.tail first member)
      by_cases firstY : first = y
      · subst first
        simp only [scanFrom, List.foldl_cons, scanStep]
        rw [fslValuation_y different, d4_mul_0_4]
        exact ih restFree
      · simp only [scanFrom, List.foldl_cons, scanStep]
        rw [fslValuation_other firstNotX firstY, d4_mul_0_5]
        exact ih restFree

private theorem d4_scan_one_eq_one_iff
    {x y : Nat} (different : x ≠ y) (letters : List Nat)
    (xFree : x ∉ letters) :
    scanFrom d4G (fslValuation x y) (some 1) letters = some 1 ↔
      y ∉ letters := by
  induction letters with
  | nil => simp [scanFrom]
  | cons first rest ih =>
      have firstNotX : first ≠ x := by
        intro equal
        subst first
        exact xFree (by simp)
      have restFree : x ∉ rest := by
        intro member
        exact xFree (List.Mem.tail first member)
      by_cases firstY : first = y
      · subst first
        simp only [scanFrom, List.foldl_cons, scanStep]
        rw [fslValuation_y different, d4_mul_1_4]
        simp only [← scanFrom_eq_foldl]
        rw [d4_scan_zero different rest restFree]
        simp
      · simp only [scanFrom, List.foldl_cons, scanStep]
        rw [fslValuation_other firstNotX firstY, d4_mul_1_5]
        simp only [← scanFrom_eq_foldl]
        rw [ih restFree]
        simp [Ne.symm firstY]

private theorem d4_scan_suffix_eq_one_iff
    {x y : Nat} (different : x ≠ y) (after : List Nat)
    (xFree : x ∉ after) (yPresent : y ∈ after) :
    scanFrom d4G (fslValuation x y) (some 2) after = some 1 ↔
      ∃ rest, after = y :: rest ∧ y ∉ rest := by
  cases after with
  | nil => simp at yPresent
  | cons first rest =>
      have firstNotX : first ≠ x := by
        intro equal
        subst first
        exact xFree (by simp)
      have restFree : x ∉ rest := by
        intro member
        exact xFree (List.Mem.tail first member)
      by_cases firstY : first = y
      · subst first
        simp only [scanFrom, List.foldl_cons, scanStep]
        rw [fslValuation_y different, d4_mul_2_4]
        simp only [← scanFrom_eq_foldl]
        rw [d4_scan_one_eq_one_iff different rest restFree]
        simp
      · have yRest : y ∈ rest := by
          simpa [firstY, Ne.symm firstY] using yPresent
        simp only [scanFrom, List.foldl_cons, scanStep]
        rw [fslValuation_other firstNotX firstY, d4_mul_2_5]
        simp only [← scanFrom_eq_foldl]
        rw [d4_scan_one_eq_one_iff different rest restFree]
        simp [firstY, yRest]

/-- A selected multiple letter occurs after the unique selected simple
letter.  The inherited last-gap signature supplies this hypothesis exactly
in the D4 use site. -/
def SomeYAfterX (word : Word Nat) (x y : Nat) : Prop :=
  ∃ before after,
    word.toList = before ++ x :: after ∧ y ∈ after

/-- D4 has the same FSL detector once the inherited last-gap signature
excludes its documented all-`y`-before-`x` false-positive branch. -/
theorem d4_eval_eq_one_iff_fsl
    (word : Word Nat) (x y : Nat)
    (xSimple : S5_107.SimpleIn word x)
    (yMultiple : 2 ≤ word.toList.count y)
    (someYAfter : SomeYAfterX word x y) :
    d4G.eval (fslValuation x y) word = 1 ↔
      SimpleLastFactor word x y := by
  have different : x ≠ y := by
    intro equal
    subst y
    unfold S5_107.SimpleIn at xSimple
    omega
  constructor
  · intro evaluated
    obtain ⟨before, after, split, yPresent⟩ := someYAfter
    have free := unique_split_free xSimple split
    have scannedPrefix := d4_scan_prefix_x different before free.1
    have scanWhole :
        scanFrom d4G (fslValuation x y) none word.toList =
          scanFrom d4G (fslValuation x y) (some 2) after := by
      rw [split]
      rw [show before ++ x :: after = (before ++ [x]) ++ after by simp]
      rw [scanFrom_append, scannedPrefix]
    have scannedSuffix :
        scanFrom d4G (fslValuation x y) (some 2) after = some 1 := by
      rw [← scanWhole, scanFrom_toList, evaluated]
    obtain ⟨rest, afterEq, yFree⟩ :=
      (d4_scan_suffix_eq_one_iff different after free.2 yPresent).mp
        scannedSuffix
    refine ⟨xSimple, yMultiple, before, rest, ?_, yFree⟩
    rw [split, afterEq]
  · rintro ⟨_, _, before, after, split, yFree⟩
    have splitAtX : word.toList = before ++ x :: (y :: after) := by
      simpa using split
    have free := unique_split_free xSimple splitAtX
    have scannedPrefix := d4_scan_prefix_x different before free.1
    have scannedSuffix :
        scanFrom d4G (fslValuation x y) (some 2) (y :: after) = some 1 :=
      (d4_scan_suffix_eq_one_iff different (y :: after) free.2
        (by simp)).mpr ⟨after, rfl, yFree⟩
    have scanWhole :
        scanFrom d4G (fslValuation x y) none word.toList = some 1 := by
      rw [splitAtX]
      rw [show before ++ x :: y :: after =
          (before ++ [x]) ++ (y :: after) by simp]
      rw [scanFrom_append, scannedPrefix]
      exact scannedSuffix
    rw [scanFrom_toList] at scanWhole
    injection scanWhole

end SemigroupBasis.CoRoots.Order6D2D4SuffixTrace.V2
