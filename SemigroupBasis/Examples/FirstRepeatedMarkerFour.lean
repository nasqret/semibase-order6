import SemigroupBasis.Examples.FirstCappedMultiplicityFour

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for the catalogue table
`[[1,1,1,1],[1,1,1,2],[3,3,3,3],[1,1,1,4]]`. -/
def firstRepeatedMarkerFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 1 then (if b = 3 then 1 else 0) else
      if a = 2 then 2 else
        if b = 3 then 3 else 0

/-- The Smallsemi representative `S4_72`. -/
def firstRepeatedMarkerFour : FiniteTable where
  order := 4
  mul := firstRepeatedMarkerFourMul
  assoc := by decide

def firstRepeatedXY : Word Nat := ⟨0, [1]⟩
def firstRepeatedXYY : Word Nat := ⟨0, [1, 1]⟩

def firstRepeatedRightDuplicationLaw : Identity Nat :=
  ⟨firstRepeatedXY, firstRepeatedXYY⟩

/-- The exact basis `xx = xxx`, `xy = xyy`, `xxy = xyx`,
`xyz = xzy`. -/
def firstRepeatedMarkerFourBasis : List (Identity Nat) :=
  [firstCappedPowerLaw, firstRepeatedRightDuplicationLaw,
    firstCappedRepeatedFirstLaw, firstCappedSuffixCommutationLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- Duplicate an arbitrary nonempty suffix block. -/
theorem firstRepeatedDerivesRightDuplication (u v : Word Nat) :
    Derives firstRepeatedMarkerFourBasis
      (u ++ v) ((u ++ v) ++ v) := by
  have hbase :
      Derives firstRepeatedMarkerFourBasis
        firstRepeatedXY firstRepeatedXYY :=
    Derives.fromBasis (e := firstRepeatedRightDuplicationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [firstRepeatedMarkerFourBasis,
    firstRepeatedRightDuplicationLaw, firstRepeatedXY, firstRepeatedXYY,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private theorem firstCappedAxiomsDerive :
    ∀ e : Identity Nat, e ∈ firstCappedMultiplicityFourBasis →
      Derives firstRepeatedMarkerFourBasis e.lhs e.rhs := by
  intro e he
  simp only [firstCappedMultiplicityFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact Derives.fromBasis (e := firstCappedPowerLaw) <|
      List.Mem.head _
  · exact Derives.fromBasis (e := firstCappedRepeatedFirstLaw) <|
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · exact Derives.fromBasis
      (e := firstCappedSuffixCommutationLaw) <|
        List.Mem.tail _ <| List.Mem.tail _ <|
          List.Mem.tail _ <| List.Mem.head _

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- First use the unrestricted `S4_74` normal form. If its tail is nonempty,
duplicate the whole tail; this is the extra normalization forced by
`xy = xyy`. -/
def firstRepeatedNormal (w : Word Nat) : Word Nat :=
  let base := firstCappedNormal w
  match base.tail with
  | [] => base
  | y :: ys =>
      let suffix := wordOfCons y ys
      (Word.singleton base.head ++ suffix) ++ suffix

theorem firstRepeatedDerivesNormal (w : Word Nat) :
    Derives firstRepeatedMarkerFourBasis w (firstRepeatedNormal w) := by
  have transported :=
    (firstCappedDerivesNormal w).transport firstCappedAxiomsDerive
  cases hbase : firstCappedNormal w with
  | mk head tail =>
      rw [hbase] at transported
      cases htail : tail with
      | nil =>
          simpa [firstRepeatedNormal, hbase, htail] using transported
      | cons y ys =>
          let suffix := wordOfCons y ys
          have duplicated :=
            firstRepeatedDerivesRightDuplication
              (Word.singleton head) suffix
          exact Derives.trans transported <| by
            simpa [firstRepeatedNormal, hbase, htail, suffix,
              wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using duplicated

/-- During a common evaluation, the `S4_74` value and the `S4_72` value are
either equal or are respectively `1` and `0`. -/
private def ValuesRelated (a b : Fin 4) : Prop :=
  a = b ∨ (a = 1 ∧ b = 0)

private theorem valuesRelated_step (a b c : Fin 4)
    (related : ValuesRelated a b) :
    ValuesRelated
      (firstCappedMultiplicityFourMul a c)
      (firstRepeatedMarkerFourMul b c) := by
  rcases related with rfl | ⟨rfl, rfl⟩ <;>
    simp only [ValuesRelated] <;> decide +revert

private theorem fold_valuesRelated
    (valuation : Nat → Fin 4) :
    ∀ (xs : List Nat) (a b : Fin 4),
      ValuesRelated a b →
      ValuesRelated
        (xs.foldl
          (fun current x =>
            firstCappedMultiplicityFourMul current (valuation x)) a)
        (xs.foldl
          (fun current x =>
            firstRepeatedMarkerFourMul current (valuation x)) b)
  | [], _, _, related => related
  | x :: xs, a, b, related => by
      simp only [List.foldl_cons]
      exact fold_valuesRelated valuation xs _ _
        (valuesRelated_step a b (valuation x) related)

private theorem eval_valuesRelated
    (valuation : Nat → Fin 4) (w : Word Nat) :
    ValuesRelated
      (firstCappedMultiplicityFour.semigroup.eval valuation w)
      (firstRepeatedMarkerFour.semigroup.eval valuation w) := by
  cases w with
  | mk head tail =>
      exact fold_valuesRelated valuation tail _ _ (Or.inl rfl)

private theorem doubledSuffix_values_equal
    (initial a b : Fin 4) (related : ValuesRelated a b) :
    firstCappedMultiplicityFourMul
        (firstCappedMultiplicityFourMul initial a) a =
      firstRepeatedMarkerFourMul
        (firstRepeatedMarkerFourMul initial b) b := by
  rcases related with rfl | ⟨rfl, rfl⟩ <;> decide +revert

private theorem eval_doubledSuffix_eq
    (valuation : Nat → Fin 4) (x : Nat) (suffix : Word Nat) :
    firstCappedMultiplicityFour.semigroup.eval valuation
        ((Word.singleton x ++ suffix) ++ suffix) =
      firstRepeatedMarkerFour.semigroup.eval valuation
        ((Word.singleton x ++ suffix) ++ suffix) := by
  rw [Semigroup.eval_append, Semigroup.eval_append,
    Semigroup.eval_append, Semigroup.eval_append]
  exact doubledSuffix_values_equal
    (valuation x)
    (firstCappedMultiplicityFour.semigroup.eval valuation suffix)
    (firstRepeatedMarkerFour.semigroup.eval valuation suffix)
    (eval_valuesRelated valuation suffix)

private theorem normal_eval_eq
    (valuation : Nat → Fin 4) (w : Word Nat) :
    firstCappedMultiplicityFour.semigroup.eval valuation
        (firstRepeatedNormal w) =
      firstRepeatedMarkerFour.semigroup.eval valuation
        (firstRepeatedNormal w) := by
  cases hbase : firstCappedNormal w with
  | mk head tail =>
      cases htail : tail with
      | nil =>
          simp [firstRepeatedNormal, hbase, htail, Semigroup.eval]
      | cons y ys =>
          simpa [firstRepeatedNormal, hbase, htail] using
            eval_doubledSuffix_eq valuation head (wordOfCons y ys)

private theorem firstRepeatedMul_power (a : Fin 4) :
    firstRepeatedMarkerFourMul a a =
      firstRepeatedMarkerFourMul
        (firstRepeatedMarkerFourMul a a) a := by
  decide +revert

private theorem firstRepeatedMul_right_duplication (a b : Fin 4) :
    firstRepeatedMarkerFourMul a b =
      firstRepeatedMarkerFourMul
        (firstRepeatedMarkerFourMul a b) b := by
  decide +revert

private theorem firstRepeatedMul_repeated_first (a b : Fin 4) :
    firstRepeatedMarkerFourMul
        (firstRepeatedMarkerFourMul a a) b =
      firstRepeatedMarkerFourMul
        (firstRepeatedMarkerFourMul a b) a := by
  decide +revert

private theorem firstRepeatedMul_suffix_commutative (a b c : Fin 4) :
    firstRepeatedMarkerFourMul
        (firstRepeatedMarkerFourMul a b) c =
      firstRepeatedMarkerFourMul
        (firstRepeatedMarkerFourMul a c) b := by
  decide +revert

theorem firstRepeatedMarkerFourBasis_models :
    Models firstRepeatedMarkerFour.semigroup
      firstRepeatedMarkerFourBasis := by
  intro e he
  simp only [firstRepeatedMarkerFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · intro valuation
    exact firstRepeatedMul_power (valuation 0)
  · intro valuation
    exact firstRepeatedMul_right_duplication
      (valuation 0) (valuation 1)
  · intro valuation
    exact firstRepeatedMul_repeated_first
      (valuation 0) (valuation 1)
  · intro valuation
    exact firstRepeatedMul_suffix_commutative
      (valuation 0) (valuation 1) (valuation 2)

/-- Unrestricted completeness over `Nat` variables. Words first reduce to the
`S4_74` capped-multiplicity normal form and then acquire a doubled nonempty
tail. These normalized words evaluate identically in `S4_72` and `S4_74`. -/
theorem firstRepeatedMarkerFourBasis_complete :
    BasisFor firstRepeatedMarkerFour.semigroup
      firstRepeatedMarkerFourBasis := by
  refine ⟨firstRepeatedMarkerFourBasis_models, ?_⟩
  intro e valid
  have lhsNormal := firstRepeatedDerivesNormal e.lhs
  have rhsNormal := firstRepeatedDerivesNormal e.rhs
  let normalIdentity : Identity Nat :=
    ⟨firstRepeatedNormal e.lhs, firstRepeatedNormal e.rhs⟩
  have normalValid :
      normalIdentity.SatisfiedBy
        firstCappedMultiplicityFour.semigroup := by
    intro valuation
    have lhsSound :=
      lhsNormal.sound firstRepeatedMarkerFourBasis_models valuation
    have rhsSound :=
      rhsNormal.sound firstRepeatedMarkerFourBasis_models valuation
    change
      firstCappedMultiplicityFour.semigroup.eval valuation
          (firstRepeatedNormal e.lhs) =
        firstCappedMultiplicityFour.semigroup.eval valuation
          (firstRepeatedNormal e.rhs)
    rw [normal_eval_eq valuation e.lhs, normal_eval_eq valuation e.rhs]
    exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
  have middleCapped :=
    firstCappedMultiplicityFourBasis_complete.2
      normalIdentity normalValid
  have middle := middleCapped.transport firstCappedAxiomsDerive
  exact Derives.trans lhsNormal <|
    Derives.trans middle (Derives.symm rhsNormal)

def firstRepeatedMarkerFourOppositeBasis : List (Identity Nat) :=
  reversedBasis firstRepeatedMarkerFourBasis

theorem firstRepeatedMarkerFourOppositeBasis_complete :
    BasisFor firstRepeatedMarkerFour.semigroup.opposite
      firstRepeatedMarkerFourOppositeBasis := by
  simpa [firstRepeatedMarkerFourOppositeBasis] using
    firstRepeatedMarkerFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples
