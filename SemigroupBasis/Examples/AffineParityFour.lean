import SemigroupBasis.Examples.AffineParityFourSyntax
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The stored catalogue representative `S4_96`. Its elements are the four
affine maps `t ↦ a*t+b` on `F₂`, with multiplication given by composition in
the stored semigroup orientation. -/
def affineParityFour : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_96.table

private theorem affineParityMul_power (a : Fin 4) :
    SemigroupBasis.Generated.Catalogue.S4_96.mul
        (SemigroupBasis.Generated.Catalogue.S4_96.mul a a) a =
      a := by
  decide +revert

private theorem affineParityMul_squareReturn (a b : Fin 4) :
    SemigroupBasis.Generated.Catalogue.S4_96.mul
        (SemigroupBasis.Generated.Catalogue.S4_96.mul
          (SemigroupBasis.Generated.Catalogue.S4_96.mul a a) b) a =
      SemigroupBasis.Generated.Catalogue.S4_96.mul b a := by
  decide +revert

private theorem affineParityMul_middleSquare (a b : Fin 4) :
    SemigroupBasis.Generated.Catalogue.S4_96.mul
        (SemigroupBasis.Generated.Catalogue.S4_96.mul
          (SemigroupBasis.Generated.Catalogue.S4_96.mul a b) b) a =
      SemigroupBasis.Generated.Catalogue.S4_96.mul
        (SemigroupBasis.Generated.Catalogue.S4_96.mul
          (SemigroupBasis.Generated.Catalogue.S4_96.mul b a) b) a := by
  decide +revert

theorem affineParityFourBasis_models :
    Models affineParityFour.semigroup
      affineParityFourBasis := by
  intro identity hmem
  simp only [affineParityFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · intro valuation
    change valuation 0 =
      SemigroupBasis.Generated.Catalogue.S4_96.mul
        (SemigroupBasis.Generated.Catalogue.S4_96.mul
          (valuation 0) (valuation 0)) (valuation 0)
    exact (affineParityMul_power (valuation 0)).symm
  · intro valuation
    change
      SemigroupBasis.Generated.Catalogue.S4_96.mul
          (SemigroupBasis.Generated.Catalogue.S4_96.mul
            (SemigroupBasis.Generated.Catalogue.S4_96.mul
              (valuation 0) (valuation 0))
            (valuation 1))
          (valuation 0) =
        SemigroupBasis.Generated.Catalogue.S4_96.mul
          (valuation 1) (valuation 0)
    exact affineParityMul_squareReturn
      (valuation 0) (valuation 1)
  · intro valuation
    change
      SemigroupBasis.Generated.Catalogue.S4_96.mul
          (SemigroupBasis.Generated.Catalogue.S4_96.mul
            (SemigroupBasis.Generated.Catalogue.S4_96.mul
              (valuation 0) (valuation 1))
            (valuation 1))
          (valuation 0) =
        SemigroupBasis.Generated.Catalogue.S4_96.mul
          (SemigroupBasis.Generated.Catalogue.S4_96.mul
            (SemigroupBasis.Generated.Catalogue.S4_96.mul
              (valuation 1) (valuation 0))
            (valuation 1))
          (valuation 0)
    exact affineParityMul_middleSquare
      (valuation 0) (valuation 1)

private theorem affineParityMul_zero_left (a : Fin 4) :
    SemigroupBasis.Generated.Catalogue.S4_96.mul 0 a = a := by
  decide +revert

private theorem affineParityMul_zero_right (a : Fin 4) :
    SemigroupBasis.Generated.Catalogue.S4_96.mul a 0 = a := by
  decide +revert

/-- Evaluation of a possibly empty list, using the identity element `0`. -/
def affineParityListEval
    (valuation : Nat → Fin 4) (letters : List Nat) : Fin 4 :=
  letters.foldl
    (fun current letter =>
      SemigroupBasis.Generated.Catalogue.S4_96.mul
        current (valuation letter))
    0

theorem affineParityEval_eq_listEval
    (valuation : Nat → Fin 4) (word : Word Nat) :
    affineParityFour.semigroup.eval valuation word =
      affineParityListEval valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              SemigroupBasis.Generated.Catalogue.S4_96.mul
                current (valuation letter))
            (valuation head) =
          tail.foldl
            (fun current letter =>
              SemigroupBasis.Generated.Catalogue.S4_96.mul
                current (valuation letter))
            (SemigroupBasis.Generated.Catalogue.S4_96.mul
              0 (valuation head))
      rw [affineParityMul_zero_left]

/-- The linear coefficient of the affine-map encoding. -/
def affineParityLinearBit (value : Fin 4) : Nat :=
  if value.val < 2 then 1 else 0

/-- The translation coefficient of the affine-map encoding. -/
def affineParityTranslationBit (value : Fin 4) : Nat :=
  value.val % 2

private theorem affineParityTranslationBit_mul
    (a b : Fin 4) :
    affineParityTranslationBit
        (SemigroupBasis.Generated.Catalogue.S4_96.mul a b) =
      (affineParityTranslationBit a *
          affineParityLinearBit b +
        affineParityTranslationBit b) % 2 := by
  decide +revert

def affineParityTotalValuation
    (tested : Nat) : Nat → Fin 4 :=
  fun letter => if letter = tested then 1 else 0

def affineParitySuffixValuation
    (tested marker : Nat) : Nat → Fin 4 :=
  fun letter =>
    if letter = marker then 2
    else if letter = tested then 1 else 0

private def affineParityTotalStep
    (tested : Nat) (bit : Nat) (letter : Nat) : Nat :=
  if letter = tested then (bit + 1) % 2 else bit

private def affineParitySuffixStep
    (tested marker : Nat) (bit : Nat) (letter : Nat) : Nat :=
  if letter = marker then 0
  else if letter = tested then (bit + 1) % 2 else bit

/-- Parity of `tested` after the final occurrence of `marker`. If the marker
is absent, this is ordinary total parity. -/
def affineParitySuffixParity
    (tested marker : Nat) (letters : List Nat) : Nat :=
  letters.foldl
    (affineParitySuffixStep tested marker) 0

private theorem affineParityTranslationBit_total_step
    (tested letter : Nat) (current : Fin 4) :
    affineParityTranslationBit
        (SemigroupBasis.Generated.Catalogue.S4_96.mul
          current (affineParityTotalValuation tested letter)) =
      affineParityTotalStep tested
        (affineParityTranslationBit current) letter := by
  rw [affineParityTranslationBit_mul]
  by_cases h : letter = tested
  · subst letter
    simp [affineParityTotalValuation,
      affineParityTotalStep, affineParityLinearBit,
      affineParityTranslationBit, Nat.add_mod]
  · simp [affineParityTotalValuation,
      affineParityTotalStep, affineParityLinearBit,
      affineParityTranslationBit, h]

private theorem affineParityTranslationBit_suffix_step
    (tested marker letter : Nat) (current : Fin 4) :
    affineParityTranslationBit
        (SemigroupBasis.Generated.Catalogue.S4_96.mul
          current
          (affineParitySuffixValuation
            tested marker letter)) =
      affineParitySuffixStep tested marker
        (affineParityTranslationBit current) letter := by
  rw [affineParityTranslationBit_mul]
  by_cases hm : letter = marker
  · subst letter
    simp [affineParitySuffixValuation,
      affineParitySuffixStep, affineParityLinearBit,
      affineParityTranslationBit]
  · by_cases ht : letter = tested
    · subst letter
      simp [affineParitySuffixValuation,
        affineParitySuffixStep, affineParityLinearBit,
        affineParityTranslationBit, hm, Nat.add_mod]
    · simp [affineParitySuffixValuation,
        affineParitySuffixStep, affineParityLinearBit,
        affineParityTranslationBit, hm, ht]

private theorem affineParityTotalFold_bit
    (tested : Nat) :
    ∀ (letters : List Nat) (current : Fin 4),
      affineParityTranslationBit
          (letters.foldl
            (fun state letter =>
              SemigroupBasis.Generated.Catalogue.S4_96.mul
                state
                (affineParityTotalValuation tested letter))
            current) =
        letters.foldl
          (affineParityTotalStep tested)
          (affineParityTranslationBit current)
  | [], _ => rfl
  | letter :: rest, current => by
      simp only [List.foldl_cons]
      rw [affineParityTotalFold_bit,
        affineParityTranslationBit_total_step]

private theorem affineParitySuffixFold_bit
    (tested marker : Nat) :
    ∀ (letters : List Nat) (current : Fin 4),
      affineParityTranslationBit
          (letters.foldl
            (fun state letter =>
              SemigroupBasis.Generated.Catalogue.S4_96.mul
                state
                (affineParitySuffixValuation
                  tested marker letter))
            current) =
        letters.foldl
          (affineParitySuffixStep tested marker)
          (affineParityTranslationBit current)
  | [], _ => rfl
  | letter :: rest, current => by
      simp only [List.foldl_cons]
      rw [affineParitySuffixFold_bit tested marker,
        affineParityTranslationBit_suffix_step
          tested marker letter current]

private theorem affineParityTotalFold_eq_count
    (tested : Nat) :
    ∀ (letters : List Nat) (start : Nat),
      start < 2 →
      letters.foldl (affineParityTotalStep tested) start =
        (start + letters.count tested) % 2
  | [], start, startLt => by
      simp [Nat.mod_eq_of_lt startLt]
  | letter :: rest, start, startLt => by
      simp only [List.foldl_cons]
      by_cases h : letter = tested
      · subst letter
        have nextLt : (start + 1) % 2 < 2 :=
          Nat.mod_lt _ (by decide)
        rw [show
          affineParityTotalStep tested start tested =
            (start + 1) % 2 by
              simp [affineParityTotalStep]]
        rw [List.count_cons_self]
        rw [affineParityTotalFold_eq_count
          tested rest ((start + 1) % 2) nextLt]
        omega
      · simpa [affineParityTotalStep, h,
          List.count_cons_of_ne h] using
            affineParityTotalFold_eq_count
              tested rest start startLt

theorem affineParityListEval_total_bit
    (tested : Nat) (letters : List Nat) :
    affineParityTranslationBit
        (affineParityListEval
          (affineParityTotalValuation tested) letters) =
      letters.count tested % 2 := by
  rw [affineParityListEval,
    affineParityTotalFold_bit,
    affineParityTotalFold_eq_count tested _ _
      (by decide)]
  simp [affineParityTranslationBit]

theorem affineParityListEval_suffix_bit
    (tested marker : Nat) (letters : List Nat) :
    affineParityTranslationBit
        (affineParityListEval
          (affineParitySuffixValuation
            tested marker) letters) =
      affineParitySuffixParity tested marker letters := by
  rw [affineParityListEval,
    affineParitySuffixFold_bit tested marker]
  rfl

theorem affineParityValid_totalParity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy affineParityFour.semigroup) :
    ∀ tested,
      identity.lhs.toList.count tested % 2 =
        identity.rhs.toList.count tested % 2 := by
  intro tested
  have evaluated :=
    valid (affineParityTotalValuation tested)
  rw [affineParityEval_eq_listEval,
    affineParityEval_eq_listEval] at evaluated
  have bitEquality :=
    congrArg affineParityTranslationBit evaluated
  simpa [affineParityListEval_total_bit] using bitEquality

theorem affineParityValid_suffixParity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy affineParityFour.semigroup) :
    ∀ tested marker, tested ≠ marker →
      affineParitySuffixParity tested marker
          identity.lhs.toList =
        affineParitySuffixParity tested marker
          identity.rhs.toList := by
  intro tested marker different
  have evaluated :=
    valid (affineParitySuffixValuation tested marker)
  rw [affineParityEval_eq_listEval,
    affineParityEval_eq_listEval] at evaluated
  have bitEquality :=
    congrArg affineParityTranslationBit evaluated
  simpa [affineParityListEval_suffix_bit] using bitEquality

theorem AffineParitySegmentsNormal.markers_nodup :
    ∀ {segments : List AffineParitySegment},
      AffineParitySegmentsNormal segments →
      (affineParityMarkers segments).Nodup
  | [], AffineParitySegmentsNormal.nil =>
      List.nodup_nil
  | _ :: _, AffineParitySegmentsNormal.cons
      _ markerFresh _ restNormal =>
      List.nodup_cons.2
        ⟨markerFresh, restNormal.markers_nodup⟩

theorem AffineParitySegmentsNormal.mem_render_iff_marker :
    ∀ {segments : List AffineParitySegment},
      AffineParitySegmentsNormal segments →
      ∀ z,
        z ∈ affineParityRender segments ↔
          z ∈ affineParityMarkers segments
  | [], AffineParitySegmentsNormal.nil, z => by
      simp [affineParityRender, affineParityMarkers]
  | ⟨parity, marker⟩ :: rest,
      AffineParitySegmentsNormal.cons
        _ _ parityGuard restNormal, z => by
      simp only [affineParityRender, affineParityMarkers,
        List.mem_append, List.mem_cons]
      constructor
      · intro hz
        rcases hz with hz | rfl | hz
        · exact parityGuard z hz
        · exact Or.inl rfl
        · exact Or.inr <|
            (restNormal.mem_render_iff_marker z).mp hz
      · intro hz
        rcases hz with rfl | hz
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr <|
            (restNormal.mem_render_iff_marker z).mpr hz)

theorem AffineParitySegmentsNormal.marker_not_mem_render_rest
    {parity : List Nat} {marker : Nat}
    {rest : List AffineParitySegment}
    (normal :
      AffineParitySegmentsNormal
        (⟨parity, marker⟩ :: rest)) :
    marker ∉ affineParityRender rest := by
  cases normal with
  | cons _ markerFresh _ restNormal =>
      intro hmem
      exact markerFresh <|
        (restNormal.mem_render_iff_marker marker).mp hmem

private theorem affineParitySuffixFold_eq_count
    (tested marker : Nat) (different : tested ≠ marker) :
    ∀ (letters : List Nat) (start : Nat),
      start < 2 →
      marker ∉ letters →
      letters.foldl
          (affineParitySuffixStep tested marker) start =
        (start + letters.count tested) % 2
  | [], start, startLt, _ => by
      simp [Nat.mod_eq_of_lt startLt]
  | letter :: rest, start, startLt, markerAbsent => by
      have letterNeMarker : letter ≠ marker := by
        intro h
        subst letter
        exact markerAbsent (List.Mem.head rest)
      have restMarkerAbsent : marker ∉ rest := by
        intro h
        exact markerAbsent (List.Mem.tail letter h)
      simp only [List.foldl_cons]
      by_cases h : letter = tested
      · subst letter
        have nextLt : (start + 1) % 2 < 2 :=
          Nat.mod_lt _ (by decide)
        rw [show
          affineParitySuffixStep tested marker start tested =
            (start + 1) % 2 by
              simp [affineParitySuffixStep,
                different]]
        rw [List.count_cons_self]
        rw [affineParitySuffixFold_eq_count
          tested marker different rest
          ((start + 1) % 2) nextLt restMarkerAbsent]
        omega
      · simpa [affineParitySuffixStep,
          letterNeMarker, h,
          List.count_cons_of_ne h] using
            affineParitySuffixFold_eq_count
              tested marker different rest start
              startLt restMarkerAbsent

theorem affineParitySuffixParity_append_marker
    (tested marker : Nat) (different : tested ≠ marker)
    (before rest : List Nat) (markerAbsent : marker ∉ rest) :
    affineParitySuffixParity tested marker
        (before ++ marker :: rest) =
      rest.count tested % 2 := by
  unfold affineParitySuffixParity
  rw [List.foldl_append]
  simp only [List.foldl_cons]
  rw [show
    affineParitySuffixStep tested marker
        (before.foldl
          (affineParitySuffixStep tested marker) 0)
        marker = 0 by
      simp [affineParitySuffixStep]]
  simpa using
    affineParitySuffixFold_eq_count
      tested marker different rest 0
      (by decide) markerAbsent

private theorem affineParityMul_assoc (a b c : Fin 4) :
    SemigroupBasis.Generated.Catalogue.S4_96.mul
        (SemigroupBasis.Generated.Catalogue.S4_96.mul a b) c =
      SemigroupBasis.Generated.Catalogue.S4_96.mul a
        (SemigroupBasis.Generated.Catalogue.S4_96.mul b c) := by
  decide +revert

private theorem affineParityFold_assoc
    (valuation : Nat → Fin 4) (a b : Fin 4) :
    ∀ letters : List Nat,
      letters.foldl
          (fun current letter =>
            SemigroupBasis.Generated.Catalogue.S4_96.mul
              current (valuation letter))
          (SemigroupBasis.Generated.Catalogue.S4_96.mul a b) =
        SemigroupBasis.Generated.Catalogue.S4_96.mul a
          (letters.foldl
            (fun current letter =>
              SemigroupBasis.Generated.Catalogue.S4_96.mul
                current (valuation letter))
            b)
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [affineParityMul_assoc]
      exact affineParityFold_assoc valuation a
        (SemigroupBasis.Generated.Catalogue.S4_96.mul
          b (valuation letter)) rest

theorem affineParityListEval_append
    (valuation : Nat → Fin 4) (left right : List Nat) :
    affineParityListEval valuation (left ++ right) =
      SemigroupBasis.Generated.Catalogue.S4_96.mul
        (affineParityListEval valuation left)
        (affineParityListEval valuation right) := by
  unfold affineParityListEval
  rw [List.foldl_append]
  let leftValue :=
    left.foldl
      (fun current letter =>
        SemigroupBasis.Generated.Catalogue.S4_96.mul
          current (valuation letter))
      0
  have insertZero :
      right.foldl
          (fun current letter =>
            SemigroupBasis.Generated.Catalogue.S4_96.mul
              current (valuation letter))
          leftValue =
        right.foldl
          (fun current letter =>
            SemigroupBasis.Generated.Catalogue.S4_96.mul
              current (valuation letter))
          (SemigroupBasis.Generated.Catalogue.S4_96.mul
            leftValue 0) := by
    rw [affineParityMul_zero_right]
  exact insertZero.trans <|
    affineParityFold_assoc valuation leftValue 0 right

theorem affineParityListEval_cons
    (valuation : Nat → Fin 4) (letter : Nat)
    (rest : List Nat) :
    affineParityListEval valuation (letter :: rest) =
      SemigroupBasis.Generated.Catalogue.S4_96.mul
        (valuation letter)
        (affineParityListEval valuation rest) := by
  change
    rest.foldl
        (fun current z =>
          SemigroupBasis.Generated.Catalogue.S4_96.mul
            current (valuation z))
        (SemigroupBasis.Generated.Catalogue.S4_96.mul
          0 (valuation letter)) =
      SemigroupBasis.Generated.Catalogue.S4_96.mul
        (valuation letter)
        (rest.foldl
          (fun current z =>
            SemigroupBasis.Generated.Catalogue.S4_96.mul
              current (valuation z))
          0)
  rw [affineParityMul_zero_left]
  have insertZero :
      rest.foldl
          (fun current z =>
            SemigroupBasis.Generated.Catalogue.S4_96.mul
              current (valuation z))
          (valuation letter) =
        rest.foldl
          (fun current z =>
            SemigroupBasis.Generated.Catalogue.S4_96.mul
              current (valuation z))
          (SemigroupBasis.Generated.Catalogue.S4_96.mul
            (valuation letter) 0) := by
    rw [affineParityMul_zero_right]
  exact insertZero.trans <|
    affineParityFold_assoc valuation
      (valuation letter) 0 rest

private theorem affineParityMul_rightZero
    (a b : Fin 4) (aAvoids : a ≠ 1)
    (bAvoids : b ≠ 1) :
    SemigroupBasis.Generated.Catalogue.S4_96.mul a b =
      if b = 0 then a else b := by
  decide +revert

private theorem affineParityMul_avoidsOne
    (a b : Fin 4) (aAvoids : a ≠ 1)
    (bAvoids : b ≠ 1) :
    SemigroupBasis.Generated.Catalogue.S4_96.mul a b ≠ 1 := by
  decide +revert

theorem affineParityListEval_avoidsOne
    (valuation : Nat → Fin 4)
    (avoidsOne : ∀ z, valuation z ≠ 1) :
    ∀ letters,
      affineParityListEval valuation letters ≠ 1
  | [] => by
      simp [affineParityListEval]
  | letter :: rest => by
      rw [affineParityListEval_cons]
      exact affineParityMul_avoidsOne
        (valuation letter)
        (affineParityListEval valuation rest)
        (avoidsOne letter)
        (affineParityListEval_avoidsOne
          valuation avoidsOne rest)

private def affineParityFirstActive
    (valuation : Nat → Fin 4) : List Nat → Fin 4
  | [] => 0
  | letter :: rest =>
      if valuation letter = 0 then
        affineParityFirstActive valuation rest
      else valuation letter

private theorem affineParityFirstActive_append
    (valuation : Nat → Fin 4) :
    ∀ left right,
      affineParityFirstActive valuation (left ++ right) =
        if affineParityFirstActive valuation left = 0 then
          affineParityFirstActive valuation right
        else affineParityFirstActive valuation left
  | [], right => by
      simp [affineParityFirstActive]
  | letter :: rest, right => by
      by_cases h : valuation letter = 0
      · simp [affineParityFirstActive, h,
          affineParityFirstActive_append valuation rest right]
      · simp [affineParityFirstActive, h]

private theorem affineParityFirstActive_zero_iff
    (valuation : Nat → Fin 4) :
    ∀ letters,
      affineParityFirstActive valuation letters = 0 ↔
        ∀ z, z ∈ letters → valuation z = 0
  | [] => by simp [affineParityFirstActive]
  | letter :: rest => by
      by_cases h : valuation letter = 0
      · simp [affineParityFirstActive, h,
          affineParityFirstActive_zero_iff valuation rest]
      · constructor
        · intro impossible
          simp [affineParityFirstActive, h] at impossible
        · intro allZero
          exact False.elim <| h <|
            allZero letter (List.Mem.head rest)

private theorem affineParityListEval_eq_firstActive_reverse
    (valuation : Nat → Fin 4)
    (avoidsOne : ∀ z, valuation z ≠ 1) :
    ∀ letters,
      affineParityListEval valuation letters =
        affineParityFirstActive valuation letters.reverse
  | [] => rfl
  | letter :: rest => by
      rw [affineParityListEval_cons,
        List.reverse_cons,
        affineParityFirstActive_append]
      rw [affineParityListEval_eq_firstActive_reverse
        valuation avoidsOne rest]
      rw [affineParityMul_rightZero
        (valuation letter)
        (affineParityFirstActive valuation rest.reverse)
        (avoidsOne letter)]
      · by_cases h :
            affineParityFirstActive
              valuation rest.reverse = 0
        · by_cases hv : valuation letter = 0 <;>
            simp [h, hv, affineParityFirstActive]
        · simp [h]
      · rw [← affineParityListEval_eq_firstActive_reverse
          valuation avoidsOne rest]
        exact affineParityListEval_avoidsOne
          valuation avoidsOne rest

private theorem affineParityFirstActive_congr
    (left right : Nat → Fin 4) :
    ∀ letters,
      (∀ z, z ∈ letters → left z = right z) →
      affineParityFirstActive left letters =
        affineParityFirstActive right letters
  | [], _ => rfl
  | letter :: rest, agree => by
      rw [affineParityFirstActive,
        affineParityFirstActive,
        agree letter (List.Mem.head rest)]
      split
      · exact affineParityFirstActive_congr
          left right rest
          (fun z hz => agree z (List.Mem.tail letter hz))
      · rfl

private theorem affineParityNodup_eq_of_firstActive_eq :
    ∀ (left right : List Nat),
      left.Nodup →
      right.Nodup →
      (∀ valuation : Nat → Fin 4,
        (∀ z, valuation z ≠ 1) →
        affineParityFirstActive valuation left =
          affineParityFirstActive valuation right) →
      left = right
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, equalEval => by
      let valuation : Nat → Fin 4 :=
        fun z => if z = y then 2 else 0
      have avoids : ∀ z, valuation z ≠ 1 := by
        intro z
        by_cases h : z = y <;> simp [valuation, h]
      have h := equalEval valuation avoids
      simp [affineParityFirstActive, valuation] at h
  | x :: xs, [], _, _, equalEval => by
      let valuation : Nat → Fin 4 :=
        fun z => if z = x then 2 else 0
      have avoids : ∀ z, valuation z ≠ 1 := by
        intro z
        by_cases h : z = x <;> simp [valuation, h]
      have h := equalEval valuation avoids
      simp [affineParityFirstActive, valuation] at h
  | x :: xs, y :: ys, leftNodup, rightNodup, equalEval => by
      have heads : x = y := by
        apply Decidable.byContradiction
        intro hxy
        let valuation : Nat → Fin 4 :=
          fun z =>
            if z = x then 2
            else if z = y then 3 else 0
        have avoids : ∀ z, valuation z ≠ 1 := by
          intro z
          by_cases hzx : z = x
          · simp [valuation, hzx]
          · by_cases hzy : z = y
            · simp [valuation, hzy, Ne.symm hxy]
            · simp [valuation, hzx, hzy]
        have h := equalEval valuation avoids
        simp [affineParityFirstActive, valuation,
          Ne.symm hxy] at h
      subst y
      have xNotInLeft :
          x ∉ xs := (List.nodup_cons.mp leftNodup).1
      have xNotInRight :
          x ∉ ys := (List.nodup_cons.mp rightNodup).1
      have tailsEqual :
          ∀ valuation : Nat → Fin 4,
            (∀ z, valuation z ≠ 1) →
            affineParityFirstActive valuation xs =
              affineParityFirstActive valuation ys := by
        intro valuation avoids
        let masked : Nat → Fin 4 :=
          fun z => if z = x then 0 else valuation z
        have maskedAvoids : ∀ z, masked z ≠ 1 := by
          intro z
          by_cases hzx : z = x
          · simp [masked, hzx]
          · simp [masked, hzx, avoids z]
        have fullEqual := equalEval masked maskedAvoids
        have maskedX : masked x = 0 := by simp [masked]
        simp [affineParityFirstActive, maskedX] at fullEqual
        calc
          affineParityFirstActive valuation xs =
              affineParityFirstActive masked xs := by
                apply affineParityFirstActive_congr
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  subst z
                  exact xNotInLeft hz
                simp [masked, hzx]
          _ = affineParityFirstActive masked ys :=
            fullEqual
          _ = affineParityFirstActive valuation ys := by
                apply affineParityFirstActive_congr
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  subst z
                  exact xNotInRight hz
                simp [masked, hzx]
      congr 1
      exact affineParityNodup_eq_of_firstActive_eq
        xs ys
        (List.nodup_cons.mp leftNodup).2
        (List.nodup_cons.mp rightNodup).2
        tailsEqual

private theorem affineParityNodup_eq_of_listEval_eq
    (left right : List Nat)
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        (∀ z, valuation z ≠ 1) →
        affineParityListEval valuation left =
          affineParityListEval valuation right) :
    left = right := by
  have reversedEqual :
      left.reverse = right.reverse := by
    have leftReverseNodup : left.reverse.Nodup := by
      change left.reverse.Pairwise (fun a b => a ≠ b)
      rw [List.pairwise_reverse]
      exact leftNodup.imp (fun h => Ne.symm h)
    have rightReverseNodup : right.reverse.Nodup := by
      change right.reverse.Pairwise (fun a b => a ≠ b)
      rw [List.pairwise_reverse]
      exact rightNodup.imp (fun h => Ne.symm h)
    apply affineParityNodup_eq_of_firstActive_eq
      left.reverse right.reverse
      leftReverseNodup rightReverseNodup
    intro valuation avoids
    rw [← affineParityListEval_eq_firstActive_reverse
        valuation avoids left,
      ← affineParityListEval_eq_firstActive_reverse
        valuation avoids right]
    exact equalEval valuation avoids
  have := congrArg List.reverse reversedEqual
  simpa using this

private theorem affineParityListEval_prefix_guard
    (valuation : Nat → Fin 4)
    (avoidsOne : ∀ z, valuation z ≠ 1)
    (before suffix : List Nat)
    (guard : ∀ z, z ∈ before → z ∈ suffix) :
    affineParityListEval valuation (before ++ suffix) =
      affineParityListEval valuation suffix := by
  rw [affineParityListEval_eq_firstActive_reverse
      valuation avoidsOne,
    affineParityListEval_eq_firstActive_reverse
      valuation avoidsOne,
    List.reverse_append,
    affineParityFirstActive_append]
  by_cases suffixZero :
      affineParityFirstActive valuation suffix.reverse = 0
  · have prefixZero :
        affineParityFirstActive valuation before.reverse = 0 := by
      apply
        (affineParityFirstActive_zero_iff
          valuation before.reverse).2
      intro z hz
      have hzBefore : z ∈ before := by simpa using hz
      have hzSuffix : z ∈ suffix := guard z hzBefore
      exact
        (affineParityFirstActive_zero_iff
          valuation suffix.reverse).1
          suffixZero z (by simpa using hzSuffix)
    simp [suffixZero, prefixZero]
  · simp [suffixZero]

theorem AffineParitySegmentsNormal.listEval_render_eq_markers
    {segments : List AffineParitySegment}
    (normal : AffineParitySegmentsNormal segments)
    (valuation : Nat → Fin 4)
    (avoidsOne : ∀ z, valuation z ≠ 1) :
    affineParityListEval valuation
        (affineParityRender segments) =
      affineParityListEval valuation
        (affineParityMarkers segments) := by
  induction normal with
  | nil =>
      rfl
  | @cons parity marker rest parityNodup markerFresh
      parityGuard restNormal ih =>
      have blockGuard :
          ∀ z, z ∈ parity →
            z ∈ marker :: affineParityRender rest := by
        intro z hz
        rcases parityGuard z hz with rfl | hz
        · exact List.Mem.head _
        · exact List.Mem.tail _ <|
            affineParityMarker_mem_render hz
      calc
        affineParityListEval valuation
            (affineParityRender
              (⟨parity, marker⟩ :: rest)) =
            affineParityListEval valuation
              (marker :: affineParityRender rest) := by
                rw [affineParityRender]
                exact affineParityListEval_prefix_guard
                  valuation avoidsOne parity
                  (marker :: affineParityRender rest)
                  blockGuard
        _ = SemigroupBasis.Generated.Catalogue.S4_96.mul
              (valuation marker)
              (affineParityListEval valuation
                (affineParityRender rest)) := by
              rw [affineParityListEval_cons]
        _ = SemigroupBasis.Generated.Catalogue.S4_96.mul
              (valuation marker)
              (affineParityListEval valuation
                (affineParityMarkers rest)) := by
              rw [ih]
        _ = affineParityListEval valuation
              (affineParityMarkers
                (⟨parity, marker⟩ :: rest)) := by
              rw [affineParityMarkers,
                affineParityListEval_cons]

theorem affineParityMarkers_eq_of_eval_eq
    {left right : List AffineParitySegment}
    (leftNormal : AffineParitySegmentsNormal left)
    (rightNormal : AffineParitySegmentsNormal right)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        affineParityListEval valuation
            (affineParityRender left) =
          affineParityListEval valuation
            (affineParityRender right)) :
    affineParityMarkers left =
      affineParityMarkers right := by
  apply affineParityNodup_eq_of_listEval_eq
    (affineParityMarkers left)
    (affineParityMarkers right)
    leftNormal.markers_nodup rightNormal.markers_nodup
  intro valuation avoidsOne
  rw [← leftNormal.listEval_render_eq_markers
      valuation avoidsOne,
    ← rightNormal.listEval_render_eq_markers
      valuation avoidsOne]
  exact equalEval valuation

def affineParityBoundaryParity
    (source : List Nat) (previous : Option Nat)
    (tested : Nat) : Nat :=
  match previous with
  | none => source.count tested % 2
  | some marker =>
      if tested = marker then 0
      else affineParitySuffixParity tested marker source

private theorem affineParityBoundary_eq_of_signatures
    {leftSource rightSource : List Nat}
    (totalParity :
      ∀ tested,
        leftSource.count tested % 2 =
          rightSource.count tested % 2)
    (suffixParity :
      ∀ tested marker, tested ≠ marker →
        affineParitySuffixParity tested marker leftSource =
          affineParitySuffixParity tested marker rightSource)
    (previous : Option Nat) (tested : Nat) :
    affineParityBoundaryParity leftSource previous tested =
      affineParityBoundaryParity rightSource previous tested := by
  cases previous with
  | none =>
      exact totalParity tested
  | some marker =>
      by_cases h : tested = marker
      · simp [affineParityBoundaryParity, h]
      · simpa [affineParityBoundaryParity, h] using
          suffixParity tested marker h

private theorem affineParityBoundary_after_marker
    (source before block rest : List Nat)
    (marker tested : Nat)
    (sourceEq :
      source = before ++ block ++ marker :: rest)
    (markerAbsent : marker ∉ rest) :
    affineParityBoundaryParity source (some marker) tested =
      rest.count tested % 2 := by
  by_cases h : tested = marker
  · subst tested
    have countZero : rest.count marker = 0 :=
      List.count_eq_zero.mpr markerAbsent
    simp [affineParityBoundaryParity, countZero]
  · rw [sourceEq]
    simpa [affineParityBoundaryParity, h,
      List.append_assoc] using
        affineParitySuffixParity_append_marker
          tested marker h (before ++ block) rest markerAbsent

private theorem affineParityBlock_mem_iff
    (source : List Nat) (previous : Option Nat)
    (block rest : List Nat) (marker tested : Nat)
    (blockNodup : block.Nodup)
    (previousProfile :
      ∀ z,
        affineParityBoundaryParity source previous z =
          (block ++ marker :: rest).count z % 2)
    (currentProfile :
      ∀ z,
        affineParityBoundaryParity source (some marker) z =
          rest.count z % 2) :
    tested ∈ block ↔
      (affineParityBoundaryParity source previous tested +
          (if tested = marker then 1 else 0) +
        affineParityBoundaryParity source
          (some marker) tested) % 2 = 1 := by
  have previousEq := previousProfile tested
  have currentEq := currentProfile tested
  have markerCount :
      (marker :: rest).count tested =
        (if tested = marker then 1 else 0) +
          rest.count tested := by
    by_cases same : tested = marker
    · subst tested
      simp [Nat.add_comm]
    · rw [List.count_cons_of_ne (Ne.symm same)]
      simp [same]
  rw [List.count_append] at previousEq
  rw [blockNodup.count] at previousEq
  rw [markerCount] at previousEq
  rw [previousEq, currentEq]
  rw [show
    (((((if tested ∈ block then 1 else 0) +
          ((if tested = marker then 1 else 0) +
            rest.count tested)) % 2 +
        (if tested = marker then 1 else 0)) +
        rest.count tested % 2) % 2) =
      (if tested ∈ block then 1 else 0) % 2 by
        omega]
  by_cases h : tested ∈ block <;> simp [h]

private theorem affineParityPerm_of_nodup_mem_iff :
    ∀ {left right : List Nat},
      left.Nodup →
      right.Nodup →
      (∀ z, z ∈ left ↔ z ∈ right) →
      left.Perm right
  | [], [], _, _, _ => List.Perm.refl []
  | [], y :: ys, _, _, same => by
      exact False.elim <| by
        have := (same y).2 (List.Mem.head ys)
        exact List.not_mem_nil this
  | x :: xs, [], _, _, same => by
      exact False.elim <| by
        have := (same x).1 (List.Mem.head xs)
        exact List.not_mem_nil this
  | x :: xs, y :: ys, leftNodup, rightNodup, same => by
      have xInRight : x ∈ y :: ys :=
        (same x).1 (List.Mem.head xs)
      have expose :
          (y :: ys).Perm (x :: (y :: ys).erase x) :=
        List.perm_cons_erase xInRight
      have leftTailNodup : xs.Nodup :=
        (List.nodup_cons.mp leftNodup).2
      have erasedNodup : ((y :: ys).erase x).Nodup :=
        rightNodup.erase x
      have arrangedNodup :
          (x :: (y :: ys).erase x).Nodup :=
        expose.nodup_iff.mp rightNodup
      have xNotInErase : x ∉ (y :: ys).erase x :=
        (List.nodup_cons.mp arrangedNodup).1
      have tailSame :
          ∀ z, z ∈ xs ↔ z ∈ (y :: ys).erase x := by
        intro z
        have xNotInLeft : x ∉ xs :=
          (List.nodup_cons.mp leftNodup).1
        by_cases hzx : z = x
        · subst z
          exact iff_of_false xNotInLeft xNotInErase
        · constructor
          · intro hz
            have arrangedMem :=
              (expose.mem_iff).mp <|
                (same z).1 (List.Mem.tail x hz)
            simp only [List.mem_cons] at arrangedMem
            rcases arrangedMem with h | h
            · exact False.elim (hzx h)
            · exact h
          · intro hz
            have arrangedMem :
                z ∈ x :: (y :: ys).erase x :=
              List.Mem.tail x hz
            have sourceMem :=
              (same z).2 ((expose.mem_iff).mpr arrangedMem)
            simp only [List.mem_cons] at sourceMem
            rcases sourceMem with h | h
            · exact False.elim (hzx h)
            · exact h
      exact
        (List.Perm.cons x <|
          affineParityPerm_of_nodup_mem_iff
            leftTailNodup erasedNodup tailSame).trans
          expose.symm

inductive AffineParitySegmentsPerm :
    List AffineParitySegment →
    List AffineParitySegment → Prop
  | nil : AffineParitySegmentsPerm [] []
  | cons {leftBlock rightBlock : List Nat}
      {marker : Nat}
      {leftRest rightRest : List AffineParitySegment} :
      leftBlock.Perm rightBlock →
      AffineParitySegmentsPerm leftRest rightRest →
      AffineParitySegmentsPerm
        (⟨leftBlock, marker⟩ :: leftRest)
        (⟨rightBlock, marker⟩ :: rightRest)

private theorem affineParitySegmentsPerm_of_signatures :
    ∀ (leftSource rightSource : List Nat)
      (previous : Option Nat)
      (leftBefore rightBefore : List Nat)
      (left right : List AffineParitySegment),
      AffineParitySegmentsNormal left →
      AffineParitySegmentsNormal right →
      affineParityMarkers left =
        affineParityMarkers right →
      leftSource = leftBefore ++ affineParityRender left →
      rightSource = rightBefore ++ affineParityRender right →
      (∀ z,
        affineParityBoundaryParity leftSource previous z =
          (affineParityRender left).count z % 2) →
      (∀ z,
        affineParityBoundaryParity rightSource previous z =
          (affineParityRender right).count z % 2) →
      (∀ z,
        leftSource.count z % 2 =
          rightSource.count z % 2) →
      (∀ tested marker, tested ≠ marker →
        affineParitySuffixParity tested marker leftSource =
          affineParitySuffixParity tested marker rightSource) →
      AffineParitySegmentsPerm left right
  | _, _, _, _, _, [], [], _, _, _, _, _, _, _, _, _ =>
      AffineParitySegmentsPerm.nil
  | leftSource, rightSource, previous,
      leftBefore, rightBefore,
      [], _ :: _, _, _, markerEq, _, _, _, _, _, _ => by
      simp [affineParityMarkers] at markerEq
  | leftSource, rightSource, previous,
      leftBefore, rightBefore,
      _ :: _, [], _, _, markerEq, _, _, _, _, _, _ => by
      simp [affineParityMarkers] at markerEq
  | leftSource, rightSource, previous,
      leftBefore, rightBefore,
      ⟨leftBlock, leftMarker⟩ :: leftRest,
      ⟨rightBlock, rightMarker⟩ :: rightRest,
      leftNormal, rightNormal, markerEq,
      leftSourceEq, rightSourceEq,
      leftPreviousProfile, rightPreviousProfile,
      totalParity, suffixParity => by
      have markers :
          leftMarker = rightMarker ∧
            affineParityMarkers leftRest =
              affineParityMarkers rightRest := by
        simpa [affineParityMarkers] using markerEq
      rcases markers with ⟨rfl, restMarkers⟩
      cases leftNormal with
      | cons leftNodup leftMarkerFresh
          leftGuard leftRestNormal =>
          cases rightNormal with
          | cons rightNodup rightMarkerFresh
              rightGuard rightRestNormal =>
              have leftMarkerAbsent :
                  leftMarker ∉
                    affineParityRender leftRest :=
                AffineParitySegmentsNormal.marker_not_mem_render_rest
                  (AffineParitySegmentsNormal.cons
                    leftNodup leftMarkerFresh
                    leftGuard leftRestNormal)
              have rightMarkerAbsent :
                  leftMarker ∉
                    affineParityRender rightRest :=
                AffineParitySegmentsNormal.marker_not_mem_render_rest
                  (AffineParitySegmentsNormal.cons
                    rightNodup rightMarkerFresh
                    rightGuard rightRestNormal)
              have leftCurrentProfile :
                  ∀ z,
                    affineParityBoundaryParity leftSource
                        (some leftMarker) z =
                      (affineParityRender leftRest).count z % 2 := by
                intro z
                apply affineParityBoundary_after_marker
                  leftSource leftBefore leftBlock
                  (affineParityRender leftRest)
                  leftMarker z
                · simpa [affineParityRender,
                    List.append_assoc] using leftSourceEq
                · exact leftMarkerAbsent
              have rightCurrentProfile :
                  ∀ z,
                    affineParityBoundaryParity rightSource
                        (some leftMarker) z =
                      (affineParityRender rightRest).count z % 2 := by
                intro z
                apply affineParityBoundary_after_marker
                  rightSource rightBefore rightBlock
                  (affineParityRender rightRest)
                  leftMarker z
                · simpa [affineParityRender,
                    List.append_assoc] using rightSourceEq
                · exact rightMarkerAbsent
              have blockSame :
                  ∀ z, z ∈ leftBlock ↔ z ∈ rightBlock := by
                intro z
                rw [affineParityBlock_mem_iff
                    leftSource previous leftBlock
                    (affineParityRender leftRest)
                    leftMarker z leftNodup
                    (by
                      intro a
                      simpa [affineParityRender] using
                        leftPreviousProfile a)
                    leftCurrentProfile,
                  affineParityBlock_mem_iff
                    rightSource previous rightBlock
                    (affineParityRender rightRest)
                    leftMarker z rightNodup
                    (by
                      intro a
                      simpa [affineParityRender] using
                        rightPreviousProfile a)
                    rightCurrentProfile]
                rw [affineParityBoundary_eq_of_signatures
                    totalParity suffixParity previous z,
                  affineParityBoundary_eq_of_signatures
                    totalParity suffixParity
                    (some leftMarker) z]
              have blockPerm : leftBlock.Perm rightBlock :=
                affineParityPerm_of_nodup_mem_iff
                  leftNodup rightNodup blockSame
              apply AffineParitySegmentsPerm.cons
                blockPerm
              apply affineParitySegmentsPerm_of_signatures
                leftSource rightSource (some leftMarker)
                (leftBefore ++ leftBlock ++ [leftMarker])
                (rightBefore ++ rightBlock ++ [leftMarker])
                leftRest rightRest
                leftRestNormal rightRestNormal
                restMarkers
              · simpa [affineParityRender,
                  List.append_assoc] using leftSourceEq
              · simpa [affineParityRender,
                  List.append_assoc] using rightSourceEq
              · exact leftCurrentProfile
              · exact rightCurrentProfile
              · exact totalParity
              · exact suffixParity

/-- Duplicate-free affine normal segments are determined blockwise, up to
permutation, by their marker order together with total and suffix parities.
This is the invariant-level interface to the reconstruction used by the
affine normal-form completeness proof. -/
theorem affineParitySegmentsPerm_of_invariants
    {left right : List AffineParitySegment}
    (leftNormal : AffineParitySegmentsNormal left)
    (rightNormal : AffineParitySegmentsNormal right)
    (markers : affineParityMarkers left = affineParityMarkers right)
    (totalParity : ∀ tested,
      (affineParityRender left).count tested % 2 =
        (affineParityRender right).count tested % 2)
    (suffixParity : ∀ tested marker, tested ≠ marker →
      affineParitySuffixParity tested marker
          (affineParityRender left) =
        affineParitySuffixParity tested marker
          (affineParityRender right)) :
    AffineParitySegmentsPerm left right := by
  apply affineParitySegmentsPerm_of_signatures
    (affineParityRender left) (affineParityRender right)
    none [] [] left right leftNormal rightNormal markers
  · rfl
  · rfl
  · intro tested
    rfl
  · intro tested
    rfl
  · exact totalParity
  · exact suffixParity

private def AffineParitySegmentsDerivable
    (left right : List AffineParitySegment) : Prop :=
  match left, right with
  | [], [] => True
  | leftHead :: leftRest,
      rightHead :: rightRest =>
      Derives affineParityFourBasis
        (affineParityRenderWord leftHead leftRest)
        (affineParityRenderWord rightHead rightRest)
  | _, _ => False

private theorem affineParityDerivesSegmentsPerm :
    ∀ {left right : List AffineParitySegment},
      AffineParitySegmentsPerm left right →
      AffineParitySegmentsNormal left →
      AffineParitySegmentsNormal right →
      AffineParitySegmentsDerivable left right
  | [], [], AffineParitySegmentsPerm.nil,
      AffineParitySegmentsNormal.nil,
      AffineParitySegmentsNormal.nil =>
      True.intro
  | ⟨leftBlock, marker⟩ :: leftRest,
      ⟨rightBlock, .(marker)⟩ :: rightRest,
      AffineParitySegmentsPerm.cons blockPerm restPerm,
      AffineParitySegmentsNormal.cons
        leftNodup leftFresh leftGuard leftRestNormal,
      AffineParitySegmentsNormal.cons
        rightNodup rightFresh rightGuard rightRestNormal => by
      let leftSuffix :=
        affineParityWordOfCons marker
          (affineParityRender leftRest)
      have blockGuard :
          ∀ z, z ∈ leftBlock →
            z ∈ leftSuffix.toList := by
        intro z hz
        change z ∈ marker :: affineParityRender leftRest
        rcases leftGuard z hz with rfl | hz
        · exact List.Mem.head _
        · exact List.Mem.tail _ <|
            affineParityMarker_mem_render hz
      have first :=
        affineParityDerivesGuardedPermutation
          leftSuffix blockPerm blockGuard
      cases restPerm with
      | nil =>
          simpa [affineParityRenderWord, leftSuffix,
            affineParityRender] using first
      | @cons nextLeft nextRight nextMarker
          leftTail rightTail nextPerm tailPerm =>
          have tailDerivation :=
            affineParityDerivesSegmentsPerm
              (AffineParitySegmentsPerm.cons
                nextPerm tailPerm)
              leftRestNormal rightRestNormal
          have underMarker :=
            Derives.prepend (Word.singleton marker)
              tailDerivation
          have underBlock :=
            affineParityPrependLetters_derivation
              rightBlock underMarker
          have leftWordEq :
              affineParityPrependLetters rightBlock
                  (Word.singleton marker ++
                    affineParityRenderWord
                      ⟨nextLeft, nextMarker⟩ leftTail) =
                affineParityRenderWord
                  ⟨rightBlock, marker⟩
                  (⟨nextLeft, nextMarker⟩ :: leftTail) := by
            apply Word.toList_injective
            rw [affineParityPrependLetters_toList,
              Word.toList_append, Word.toList_singleton,
              affineParityRenderWord_toList,
              affineParityRenderWord_toList]
            rfl
          have rightWordEq :
              affineParityPrependLetters rightBlock
                  (Word.singleton marker ++
                    affineParityRenderWord
                      ⟨nextRight, nextMarker⟩ rightTail) =
                affineParityRenderWord
                  ⟨rightBlock, marker⟩
                  (⟨nextRight, nextMarker⟩ :: rightTail) := by
            apply Word.toList_injective
            rw [affineParityPrependLetters_toList,
              Word.toList_append, Word.toList_singleton,
              affineParityRenderWord_toList,
              affineParityRenderWord_toList]
            rfl
          rw [leftWordEq, rightWordEq] at underBlock
          exact Derives.trans
            (by
              simpa [affineParityRenderWord,
                leftSuffix] using first)
            underBlock

private theorem affineParityNormalizedDerives
    {left right : List AffineParitySegment}
    (leftNormal : AffineParitySegmentsNormal left)
    (rightNormal : AffineParitySegmentsNormal right)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        affineParityListEval valuation
            (affineParityRender left) =
          affineParityListEval valuation
            (affineParityRender right)) :
    AffineParitySegmentsDerivable left right := by
  have markerEq :=
    affineParityMarkers_eq_of_eval_eq
      leftNormal rightNormal equalEval
  have totalParity :
      ∀ z,
        (affineParityRender left).count z % 2 =
          (affineParityRender right).count z % 2 := by
    intro z
    have evaluated :=
      equalEval (affineParityTotalValuation z)
    have bitEquality :=
      congrArg affineParityTranslationBit evaluated
    simpa [affineParityListEval_total_bit] using bitEquality
  have suffixParity :
      ∀ tested marker, tested ≠ marker →
        affineParitySuffixParity tested marker
            (affineParityRender left) =
          affineParitySuffixParity tested marker
            (affineParityRender right) := by
    intro tested marker different
    have evaluated :=
      equalEval
        (affineParitySuffixValuation tested marker)
    have bitEquality :=
      congrArg affineParityTranslationBit evaluated
    simpa [affineParityListEval_suffix_bit] using bitEquality
  have segmentsPerm :=
    affineParitySegmentsPerm_of_signatures
      (affineParityRender left)
      (affineParityRender right)
      none [] [] left right
      leftNormal rightNormal markerEq
      (by simp) (by simp)
      (by
        intro z
        rfl)
      (by
        intro z
        rfl)
      totalParity suffixParity
  exact affineParityDerivesSegmentsPerm
    segmentsPerm leftNormal rightNormal

/-- Unrestricted completeness over `Nat` variables. Every word reduces to
last-occurrence markers with guarded parity blocks. The affine table recovers
the marker order, total parity, and parity after each final marker, so two
valid sides have blockwise permutation-equivalent normal forms. -/
theorem affineParityFourBasis_complete :
    BasisFor affineParityFour.semigroup
      affineParityFourBasis := by
  refine ⟨affineParityFourBasis_models, ?_⟩
  intro identity valid
  have leftDerivation :=
    affineParityDerivesNormal identity.lhs
  have rightDerivation :=
    affineParityDerivesNormal identity.rhs
  have leftSegmentsNormal :=
    affineParityNormalSegments_normal
      identity.lhs.toList
  have rightSegmentsNormal :=
    affineParityNormalSegments_normal
      identity.rhs.toList
  cases leftEq :
      affineParityNormalSegments identity.lhs.toList with
  | nil =>
      exact False.elim <|
        affineParityNormalSegments_cons_ne_nil
          identity.lhs.head identity.lhs.tail (by
            simpa [Word.toList] using leftEq)
  | cons leftHead leftRest =>
      rw [leftEq] at leftDerivation leftSegmentsNormal
      cases rightEq :
          affineParityNormalSegments identity.rhs.toList with
      | nil =>
          exact False.elim <|
            affineParityNormalSegments_cons_ne_nil
              identity.rhs.head identity.rhs.tail (by
                simpa [Word.toList] using rightEq)
      | cons rightHead rightRest =>
          rw [rightEq] at rightDerivation rightSegmentsNormal
          have normalEval :
              ∀ valuation : Nat → Fin 4,
                affineParityListEval valuation
                    (affineParityRender
                      (leftHead :: leftRest)) =
                  affineParityListEval valuation
                    (affineParityRender
                      (rightHead :: rightRest)) := by
            intro valuation
            have leftSound :=
              leftDerivation.sound
                affineParityFourBasis_models valuation
            have rightSound :=
              rightDerivation.sound
                affineParityFourBasis_models valuation
            have evaluated :=
              leftSound.symm.trans <|
                (valid valuation).trans rightSound
            rw [affineParityEval_eq_listEval,
              affineParityEval_eq_listEval,
              affineParityRenderWord_toList,
              affineParityRenderWord_toList] at evaluated
            exact evaluated
          have middle :=
            affineParityNormalizedDerives
              leftSegmentsNormal rightSegmentsNormal
              normalEval
          change
            Derives affineParityFourBasis
              (affineParityRenderWord
                leftHead leftRest)
              (affineParityRenderWord
                rightHead rightRest) at middle
          exact Derives.trans leftDerivation <|
            Derives.trans middle
              (Derives.symm rightDerivation)

def affineParityFourOppositeBasis :
    List (Identity Nat) :=
  reversedBasis affineParityFourBasis

theorem affineParityFourOppositeBasis_complete :
    BasisFor affineParityFour.semigroup.opposite
      affineParityFourOppositeBasis := by
  simpa [affineParityFourOppositeBasis] using
    affineParityFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples
