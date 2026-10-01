import SemigroupBasis.FiniteNilpotent

namespace SemigroupBasis
namespace FiniteNilpotentLongCollapse

/-- The reversed, disjoint four-letter universal zero-product law used by all
cutoff-four representative bases in the generated order-six lane. -/
def cutoffFourUniversal : Identity Nat :=
  ⟨⟨3, [2, 1, 0]⟩, ⟨7, [6, 5, 4]⟩⟩

/-- The fixed common word on the right of `cutoffFourUniversal`. -/
def cutoffFourCommon : Word Nat :=
  cutoffFourUniversal.rhs

/-- A compact membership checker for the universal cutoff-four law. -/
def checkCutoffFour (basis : List (Identity Nat)) : Bool :=
  decide (cutoffFourUniversal ∈ basis)

private def cutoffFourSubstitution
    (first second third fourth : Nat) (rest : List Nat) : Nat → Word Nat
  | 0 => ⟨fourth, rest⟩
  | 1 => Word.singleton third
  | 2 => Word.singleton second
  | 3 => Word.singleton first
  | n => Word.singleton n

private theorem cutoffFourSubstitution_lhs
    (first second third fourth : Nat) (rest : List Nat) :
    cutoffFourUniversal.lhs.bind
        (cutoffFourSubstitution first second third fourth rest) =
      ⟨first, second :: third :: fourth :: rest⟩ := by
  rfl

private theorem cutoffFourSubstitution_rhs
    (first second third fourth : Nat) (rest : List Nat) :
    cutoffFourUniversal.rhs.bind
        (cutoffFourSubstitution first second third fourth rest) =
      cutoffFourCommon := by
  rfl

/-- One checked disjoint universal law sends every word of length at least four
to the fixed common word.  The fourth source variable receives the entire
nonempty suffix, so no induction over the residual length is needed. -/
theorem toCommon_of_mem {basis : List (Identity Nat)}
    (member : cutoffFourUniversal ∈ basis) :
    ∀ word : Word Nat,
      4 ≤ word.toList.length →
        Derives basis word cutoffFourCommon := by
  intro word long
  cases word with
  | mk first tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at long
      | cons second tail =>
          cases tail with
          | nil =>
              simp [Word.toList] at long
          | cons third tail =>
              cases tail with
              | nil =>
                  simp [Word.toList] at long
              | cons fourth rest =>
                  have base :
                      Derives basis cutoffFourUniversal.lhs
                        cutoffFourUniversal.rhs :=
                    Derives.fromBasis member
                  have instantiated :=
                    Derives.subst base
                      (cutoffFourSubstitution first second third fourth rest)
                  rw [cutoffFourSubstitution_lhs,
                    cutoffFourSubstitution_rhs] at instantiated
                  exact instantiated

/-- Boolean-checking entrypoint for generated cutoff-four signatures. -/
theorem toCommon_of_check {basis : List (Identity Nat)}
    (checked : checkCutoffFour basis = true) :
    ∀ word : Word Nat,
      4 ≤ word.toList.length →
        Derives basis word cutoffFourCommon := by
  apply toCommon_of_mem
  exact of_decide_eq_true (by
    simpa only [checkCutoffFour] using checked)

/-- The reversed disjoint five-letter universal zero-product law. -/
def cutoffFiveUniversal : Identity Nat :=
  ⟨⟨4, [3, 2, 1, 0]⟩, ⟨9, [8, 7, 6, 5]⟩⟩

def cutoffFiveCommon : Word Nat :=
  cutoffFiveUniversal.rhs

def checkCutoffFive (basis : List (Identity Nat)) : Bool :=
  decide (cutoffFiveUniversal ∈ basis)

private def cutoffFiveSubstitution
    (first second third fourth fifth : Nat) (rest : List Nat) :
    Nat → Word Nat
  | 0 => ⟨fifth, rest⟩
  | 1 => Word.singleton fourth
  | 2 => Word.singleton third
  | 3 => Word.singleton second
  | 4 => Word.singleton first
  | n => Word.singleton n

private theorem cutoffFiveSubstitution_lhs
    (first second third fourth fifth : Nat) (rest : List Nat) :
    cutoffFiveUniversal.lhs.bind
        (cutoffFiveSubstitution first second third fourth fifth rest) =
      ⟨first, second :: third :: fourth :: fifth :: rest⟩ := by
  rfl

private theorem cutoffFiveSubstitution_rhs
    (first second third fourth fifth : Nat) (rest : List Nat) :
    cutoffFiveUniversal.rhs.bind
        (cutoffFiveSubstitution first second third fourth fifth rest) =
      cutoffFiveCommon := by
  rfl

theorem toCommonFive_of_mem {basis : List (Identity Nat)}
    (member : cutoffFiveUniversal ∈ basis) :
    ∀ word : Word Nat,
      5 ≤ word.toList.length →
        Derives basis word cutoffFiveCommon := by
  intro word long
  cases word with
  | mk first tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second tail =>
          cases tail with
          | nil => simp [Word.toList] at long
          | cons third tail =>
              cases tail with
              | nil => simp [Word.toList] at long
              | cons fourth tail =>
                  cases tail with
                  | nil => simp [Word.toList] at long
                  | cons fifth rest =>
                      have base :
                          Derives basis cutoffFiveUniversal.lhs
                            cutoffFiveUniversal.rhs :=
                        Derives.fromBasis member
                      have instantiated :=
                        Derives.subst base
                          (cutoffFiveSubstitution first second third fourth
                            fifth rest)
                      rw [cutoffFiveSubstitution_lhs,
                        cutoffFiveSubstitution_rhs] at instantiated
                      exact instantiated

theorem toCommonFive_of_check {basis : List (Identity Nat)}
    (checked : checkCutoffFive basis = true) :
    ∀ word : Word Nat,
      5 ≤ word.toList.length →
        Derives basis word cutoffFiveCommon := by
  apply toCommonFive_of_mem
  exact of_decide_eq_true (by
    simpa only [checkCutoffFive] using checked)

/-- The reversed disjoint six-letter universal zero-product law. -/
def cutoffSixUniversal : Identity Nat :=
  ⟨⟨5, [4, 3, 2, 1, 0]⟩, ⟨11, [10, 9, 8, 7, 6]⟩⟩

def cutoffSixCommon : Word Nat :=
  cutoffSixUniversal.rhs

def checkCutoffSix (basis : List (Identity Nat)) : Bool :=
  decide (cutoffSixUniversal ∈ basis)

private def cutoffSixSubstitution
    (first second third fourth fifth sixth : Nat) (rest : List Nat) :
    Nat → Word Nat
  | 0 => ⟨sixth, rest⟩
  | 1 => Word.singleton fifth
  | 2 => Word.singleton fourth
  | 3 => Word.singleton third
  | 4 => Word.singleton second
  | 5 => Word.singleton first
  | n => Word.singleton n

private theorem cutoffSixSubstitution_lhs
    (first second third fourth fifth sixth : Nat) (rest : List Nat) :
    cutoffSixUniversal.lhs.bind
        (cutoffSixSubstitution first second third fourth fifth sixth rest) =
      ⟨first, second :: third :: fourth :: fifth :: sixth :: rest⟩ := by
  rfl

private theorem cutoffSixSubstitution_rhs
    (first second third fourth fifth sixth : Nat) (rest : List Nat) :
    cutoffSixUniversal.rhs.bind
        (cutoffSixSubstitution first second third fourth fifth sixth rest) =
      cutoffSixCommon := by
  rfl

theorem toCommonSix_of_mem {basis : List (Identity Nat)}
    (member : cutoffSixUniversal ∈ basis) :
    ∀ word : Word Nat,
      6 ≤ word.toList.length →
        Derives basis word cutoffSixCommon := by
  intro word long
  cases word with
  | mk first tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second tail =>
          cases tail with
          | nil => simp [Word.toList] at long
          | cons third tail =>
              cases tail with
              | nil => simp [Word.toList] at long
              | cons fourth tail =>
                  cases tail with
                  | nil => simp [Word.toList] at long
                  | cons fifth tail =>
                      cases tail with
                      | nil => simp [Word.toList] at long
                      | cons sixth rest =>
                          have base :
                              Derives basis cutoffSixUniversal.lhs
                                cutoffSixUniversal.rhs :=
                            Derives.fromBasis member
                          have instantiated :=
                            Derives.subst base
                              (cutoffSixSubstitution first second third fourth
                                fifth sixth rest)
                          rw [cutoffSixSubstitution_lhs,
                            cutoffSixSubstitution_rhs] at instantiated
                          exact instantiated

theorem toCommonSix_of_check {basis : List (Identity Nat)}
    (checked : checkCutoffSix basis = true) :
    ∀ word : Word Nat,
      6 ≤ word.toList.length →
        Derives basis word cutoffSixCommon := by
  apply toCommonSix_of_mem
  exact of_decide_eq_true (by
    simpa only [checkCutoffSix] using checked)

end FiniteNilpotentLongCollapse
end SemigroupBasis
