import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Examples.LeftRegularBandThree
import SemigroupBasis.CoRoots.S5_443Family
import SemigroupBasis.Subdirect

/-! Msg0447 section A: the exact sixteen laws and the literal S6_10960.
The actual table is a subdirect product of LRB3 and S5_614.  This gives an
unrestricted factor-theory characterization, not B16 completeness.
The two-anchor tail budget implements msg0448 without truncated subtraction. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15

open SemigroupBasis
open SemigroupBasis.Examples

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [0, 0, 1, 0]⟩
def law02 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [0, 1, 0, 0]⟩
def law03 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 0, 0, 0]⟩
def law04 : Identity Nat := ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 0, 1]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [0, 1, 1], Word.mk 0 [1, 1, 0]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [0, 1, 0, 2], Word.mk 0 [1, 0, 0, 2]⟩
def law07 : Identity Nat := ⟨Word.mk 0 [0, 1, 1, 1], Word.mk 0 [1, 1, 1, 0]⟩
def law08 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 0], Word.mk 0 [1, 0, 2, 0]⟩
def law09 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 0], Word.mk 0 [1, 2, 0, 0]⟩
def law10 : Identity Nat := ⟨Word.mk 0 [0, 1, 2, 1], Word.mk 0 [1, 0, 2, 1]⟩
def law11 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 2], Word.mk 0 [1, 2, 0, 2]⟩
def law12 : Identity Nat := ⟨Word.mk 0 [1, 0, 2, 2], Word.mk 0 [1, 2, 2, 0]⟩
def law13 : Identity Nat := ⟨Word.mk 0 [1, 1, 2, 1], Word.mk 0 [1, 2, 1, 1]⟩
def law14 : Identity Nat := ⟨Word.mk 0 [1, 2, 0, 1], Word.mk 0 [1, 2, 1, 0]⟩
def law15 : Identity Nat := ⟨Word.mk 0 [0, 1, 0], Word.mk 0 [1, 0, 0]⟩

def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11, law12, law13, law14, law15]
abbrev displayedBasisSHA256 : String := "f8ca06d7135bb2d516b4e3c4368949ee74b6ce34cfd28d49de43b7f51014c9cb"
abbrev initialTable : FiniteTable := leftRegularBandThree
abbrev lowerTable : FiniteTable := Generated.Catalogue.S5_614.table
abbrev lowerBasis : List (Identity Nat) := SemigroupBasis.CoRoots.S5_443Family.basis

theorem basis_length : basis.length = 16 := by decide

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem rawLaw00 (u : Word Nat) :
    Derives basis (u ++ u) (((u ++ u) ++ u) ++ u) := by
  have primitive : Derives basis law00.lhs law00.rhs :=
    Derives.fromBasis (e := law00) (by decide)
  have mapped := primitive.subst (fun _ => u)
  simpa [law00, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw01 (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((((u ++ u) ++ u) ++ v) ++ u) := by
  have primitive : Derives basis law01.lhs law01.rhs :=
    Derives.fromBasis (e := law01) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law01, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw02 (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((((u ++ u) ++ v) ++ u) ++ u) := by
  have primitive : Derives basis law02.lhs law02.rhs :=
    Derives.fromBasis (e := law02) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law02, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw03 (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((((u ++ v) ++ u) ++ u) ++ u) := by
  have primitive : Derives basis law03.lhs law03.rhs :=
    Derives.fromBasis (e := law03) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law03, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw04 (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v) (((u ++ v) ++ u) ++ v) := by
  have primitive : Derives basis law04.lhs law04.rhs :=
    Derives.fromBasis (e := law04) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law04, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw05 (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v) (((u ++ v) ++ v) ++ u) := by
  have primitive : Derives basis law05.lhs law05.rhs :=
    Derives.fromBasis (e := law05) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law05, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw06 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ u) ++ w) ((((u ++ v) ++ u) ++ u) ++ w) := by
  have primitive : Derives basis law06.lhs law06.rhs :=
    Derives.fromBasis (e := law06) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law06, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw07 (u v : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ v) ++ v) ((((u ++ v) ++ v) ++ v) ++ u) := by
  have primitive : Derives basis law07.lhs law07.rhs :=
    Derives.fromBasis (e := law07) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law07, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw08 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ w) ++ u) ((((u ++ v) ++ u) ++ w) ++ u) := by
  have primitive : Derives basis law08.lhs law08.rhs :=
    Derives.fromBasis (e := law08) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law08, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw09 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ w) ++ u) ((((u ++ v) ++ w) ++ u) ++ u) := by
  have primitive : Derives basis law09.lhs law09.rhs :=
    Derives.fromBasis (e := law09) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law09, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw10 (u v w : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ w) ++ v) ((((u ++ v) ++ u) ++ w) ++ v) := by
  have primitive : Derives basis law10.lhs law10.rhs :=
    Derives.fromBasis (e := law10) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law10, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw11 (u v w : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ w) ++ w) ((((u ++ v) ++ w) ++ u) ++ w) := by
  have primitive : Derives basis law11.lhs law11.rhs :=
    Derives.fromBasis (e := law11) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law11, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw12 (u v w : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ w) ++ w) ((((u ++ v) ++ w) ++ w) ++ u) := by
  have primitive : Derives basis law12.lhs law12.rhs :=
    Derives.fromBasis (e := law12) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law12, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw13 (u v w : Word Nat) :
    Derives basis ((((u ++ v) ++ v) ++ w) ++ v) ((((u ++ v) ++ w) ++ v) ++ v) := by
  have primitive : Derives basis law13.lhs law13.rhs :=
    Derives.fromBasis (e := law13) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law13, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw14 (u v w : Word Nat) :
    Derives basis ((((u ++ v) ++ w) ++ u) ++ v) ((((u ++ v) ++ w) ++ v) ++ u) := by
  have primitive : Derives basis law14.lhs law14.rhs :=
    Derives.fromBasis (e := law14) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | 2 => w | _ => Word.singleton 0)
  simpa [law14, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem rawLaw15 (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have primitive : Derives basis law15.lhs law15.rhs :=
    Derives.fromBasis (e := law15) (by decide)
  have mapped := primitive.subst (fun | 0 => u | 1 => v | _ => Word.singleton 0)
  simpa [law15, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

namespace Representative

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then (if b = 5 then 1 else 0)
  else if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 0 else 2)
  else if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 3 else if b = 3 then 2 else if b = 4 then 0 else 3)
  else if a = 4 then 4
  else b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1,1,1,1,1,1], [1,1,1,1,1,2], [1,2,3,4,1,3],
   [1,2,4,3,1,4], [5,5,5,5,5,5], [1,2,3,4,5,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) =
      catalogueRows := by decide

theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

def initialMap (a : Fin 6) : Fin 3 :=
  if a = 4 then 2 else if a = 5 then 1 else 0

def initialSection (a : Fin 3) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 5 else 4

def ontoInitial : SplitSurjection table.semigroup initialTable.semigroup where
  toFun := initialMap
  map_mul := by decide
  preimage := initialSection
  right_inverse := by intro value; exact by decide +revert

def lowerMap (a : Fin 6) : Fin 5 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2
  else if a = 3 then 3 else if a = 4 then 0 else 4

def lowerSection (a : Fin 5) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 3 else 5

def ontoLower : SplitSurjection table.semigroup lowerTable.semigroup where
  toFun := lowerMap
  map_mul := by decide
  preimage := lowerSection
  right_inverse := by intro value; exact by decide +revert

def factorPair : SubdirectPair table.semigroup initialTable.semigroup lowerTable.semigroup where
  left := ontoInitial
  right := ontoLower
  jointlyInjective := by intro a b; exact by decide +revert

/-- Exact unrestricted semantic reduction for the literal representative. -/
theorem valid_iff_factors (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      identity.SatisfiedBy initialTable.semigroup ∧ identity.SatisfiedBy lowerTable.semigroup :=
  factorPair.satisfiedBy_iff identity

/-- Both factor presentations are already complete; their intersection remains
the new proof obligation. No common derivation is inferred from this pair. -/
theorem valid_iff_factor_derivations (identity : Identity Nat) :
    identity.SatisfiedBy table.semigroup ↔
      Derives leftRegularBandThreeBasis identity.lhs identity.rhs ∧
      Derives lowerBasis identity.lhs identity.rhs := by
  rw [valid_iff_factors]
  constructor
  · rintro ⟨initialValid, lowerValid⟩
    exact ⟨leftRegularBandThreeBasis_complete.2 identity initialValid,
      SemigroupBasis.CoRoots.S5_443Family.S5_614.basis_complete.2 identity lowerValid⟩
  · rintro ⟨initialDerivation, lowerDerivation⟩
    exact ⟨initialDerivation.sound leftRegularBandThreeBasis_models,
      lowerDerivation.sound SemigroupBasis.CoRoots.S5_443Family.S5_614.models⟩

theorem modelsInitial : Models initialTable.semigroup basis := by
  intro identity member
  exact (valid_iff_factors identity).1 (models identity member) |>.1

theorem modelsLower : Models lowerTable.semigroup basis := by
  intro identity member
  exact (valid_iff_factors identity).1 (models identity member) |>.2

end Representative

def cap22 (count : Nat) : Nat :=
  if count < 2 then count else 2 + count % 2

def tailBudget22 (count : Nat) : Nat := count % 2

theorem cap22_two_add (extra : Nat) : cap22 (2 + extra) = 2 + extra % 2 := by
  unfold cap22
  rw [if_neg (by omega)]
  omega

/-- Two anchors plus this least nonnegative budget reproduce the count class. -/
theorem tailBudget22_correct (count : Nat) (repeated : 2 ≤ count) :
    cap22 (2 + tailBudget22 count) = cap22 count := by
  rw [cap22_two_add]
  unfold tailBudget22 cap22
  rw [if_neg (by omega)]
  omega

theorem tailBudget22_least (count : Nat) (repeated : 2 ≤ count)
    (extra : Nat) (same : cap22 (2 + extra) = cap22 count) :
    tailBudget22 count ≤ extra := by
  rw [cap22_two_add] at same
  unfold cap22 at same
  rw [if_neg (by omega)] at same
  unfold tailBudget22
  have bounded := Nat.mod_le extra 2
  omega

theorem tailBudget22_available (count : Nat) (repeated : 2 ≤ count) :
    2 + tailBudget22 count ≤ count := by
  unfold tailBudget22
  omega

/-- These two words are B16-equivalent but have different last-occurrence lists. -/
theorem crossing_to_nested :
    Derives basis (Word.mk 0 [1,0,1]) (Word.mk 0 [1,1,0]) := by
  have first : Derives basis law04.lhs law04.rhs := Derives.fromBasis (by decide)
  have second : Derives basis law05.lhs law05.rhs := Derives.fromBasis (by decide)
  exact first.symm.trans second

def fullLord (word : Word Nat) : List Nat :=
  (firstOccurrenceSequence word.toList.reverse).reverse

theorem fullLord_differs :
    fullLord (Word.mk 0 [1,0,1]) ≠ fullLord (Word.mk 0 [1,1,0]) := by decide

theorem fullLord_not_necessary :
    ¬ (∀ identity : Identity Nat, identity.SatisfiedBy Representative.table.semigroup →
      fullLord identity.lhs = fullLord identity.rhs) := by
  intro asserted
  exact fullLord_differs (asserted ⟨Word.mk 0 [1,0,1], Word.mk 0 [1,1,0]⟩
    (crossing_to_nested.sound Representative.models))

end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15

