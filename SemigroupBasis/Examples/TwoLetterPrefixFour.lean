import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for the catalogue table
`[[1,1,1,1],[1,1,1,3],[3,3,3,3],[4,4,4,4]]`. -/
def twoLetterPrefixFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0
  else if a = 1 then
    if b = 3 then 2 else 0
  else if a = 2 then 2
  else 3

/-- The four-element semigroup representing `S4_77`. -/
def twoLetterPrefixFour : FiniteTable where
  order := 4
  mul := twoLetterPrefixFourMul
  assoc := by decide

def twoLetterPrefixXY : Word Nat := ⟨0, [1]⟩
def twoLetterPrefixXYZ : Word Nat := ⟨0, [1, 2]⟩

def twoLetterPrefixLaw : Identity Nat :=
  ⟨twoLetterPrefixXYZ, twoLetterPrefixXY⟩

/-- The exact one-law basis `xyz = xy` for `S4_77`. -/
def twoLetterPrefixBasis : List (Identity Nat) :=
  [twoLetterPrefixLaw]

private def instantiateThreeWords (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Every nonempty suffix after the first two blocks can be deleted in one
substitution instance of `xyz = xy`. -/
theorem twoLetterPrefixDerivesDropSuffix (u v w : Word Nat) :
    Derives twoLetterPrefixBasis ((u ++ v) ++ w) (u ++ v) := by
  have hbase :
      Derives twoLetterPrefixBasis
        twoLetterPrefixXYZ twoLetterPrefixXY :=
    Derives.fromBasis (e := twoLetterPrefixLaw) (by
      simp [twoLetterPrefixBasis])
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [twoLetterPrefixLaw, twoLetterPrefixXYZ, twoLetterPrefixXY,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- Canonically contract a word of length at least two to its first two
variables. -/
theorem twoLetterPrefixDerivesToPair (x y : Nat) :
    (rest : List Nat) →
      Derives twoLetterPrefixBasis
        (wordOfCons x (y :: rest)) (wordOfCons x [y])
  | [] => Derives.refl _
  | z :: zs => by
      have h := twoLetterPrefixDerivesDropSuffix
        (Word.singleton x) (Word.singleton y) (wordOfCons z zs)
      simpa [wordOfCons, Word.singleton, Word.append] using h

private theorem twoLetterPrefixFourMul_stable
    (a b c : Fin 4) :
    twoLetterPrefixFourMul (twoLetterPrefixFourMul a b) c =
      twoLetterPrefixFourMul a b := by
  decide +revert

theorem twoLetterPrefixFourBasis_models :
    Models twoLetterPrefixFour.semigroup twoLetterPrefixBasis := by
  intro e he
  simp only [twoLetterPrefixBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl
  intro valuation
  change
    twoLetterPrefixFourMul
        (twoLetterPrefixFourMul (valuation 0) (valuation 1))
        (valuation 2) =
      twoLetterPrefixFourMul (valuation 0) (valuation 1)
  exact twoLetterPrefixFourMul_stable _ _ _

private theorem twoLetterPrefixFold_stable
    (xs : List Nat) (valuation : Nat → Fin 4) (a b : Fin 4) :
    xs.foldl
        (fun current x =>
          twoLetterPrefixFourMul current (valuation x))
        (twoLetterPrefixFourMul a b) =
      twoLetterPrefixFourMul a b := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [twoLetterPrefixFourMul_stable]
      exact ih

/-- Evaluation of every word of length at least two depends only on its first
two variables. -/
theorem twoLetterPrefixEval_pair
    (valuation : Nat → Fin 4) (x y : Nat) (rest : List Nat) :
    twoLetterPrefixFour.semigroup.eval valuation
        (wordOfCons x (y :: rest)) =
      twoLetterPrefixFourMul (valuation x) (valuation y) := by
  change
    rest.foldl
        (fun current z =>
          twoLetterPrefixFourMul current (valuation z))
        (twoLetterPrefixFourMul (valuation x) (valuation y)) =
      twoLetterPrefixFourMul (valuation x) (valuation y)
  exact twoLetterPrefixFold_stable rest valuation _ _

private def singletonSeparator (x : Nat) : Nat → Fin 4 :=
  fun y => if y = x then 3 else 0

private theorem twoLetterPrefixValidSingleton_eq {x y : Nat}
    (valid :
      (Identity.mk (Word.singleton x) (Word.singleton y)).SatisfiedBy
        twoLetterPrefixFour.semigroup) :
    x = y := by
  have evaluated := valid (singletonSeparator x)
  change singletonSeparator x x = singletonSeparator x y at evaluated
  apply Decidable.byContradiction
  intro hne
  simp [singletonSeparator, Ne.symm hne] at evaluated

private def firstCoordinateSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 3 else 2

private theorem firstCoordinateSeparator_eval (z a b : Nat) :
    twoLetterPrefixFour.semigroup.eval (firstCoordinateSeparator z)
        (wordOfCons a [b]) =
      if a = z then (3 : Fin 4) else (2 : Fin 4) := by
  change
    twoLetterPrefixFourMul
        (firstCoordinateSeparator z a)
        (firstCoordinateSeparator z b) =
      if a = z then (3 : Fin 4) else (2 : Fin 4)
  by_cases ha : a = z <;>
    simp [firstCoordinateSeparator, ha, twoLetterPrefixFourMul]

private theorem twoLetterPrefixValidPair_first_eq {a b c d : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        twoLetterPrefixFour.semigroup) :
    a = c := by
  have evaluated := valid (firstCoordinateSeparator a)
  rw [firstCoordinateSeparator_eval,
    firstCoordinateSeparator_eval] at evaluated
  apply Decidable.byContradiction
  intro hne
  simp [Ne.symm hne] at evaluated

/-- The exact table separates ordered two-letter words coordinate by
coordinate. -/
private theorem twoLetterPrefixValidPair_eq {a b c d : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        twoLetterPrefixFour.semigroup) :
    a = c ∧ b = d := by
  have first : a = c := twoLetterPrefixValidPair_first_eq valid
  subst c
  by_cases hba : b = a
  · subst b
    let valuation : Nat → Fin 4 :=
      fun x => if x = a then 1 else 3
    have evaluated := valid valuation
    change
      twoLetterPrefixFourMul (valuation a) (valuation a) =
        twoLetterPrefixFourMul (valuation a) (valuation d) at evaluated
    have second : a = d := by
      apply Decidable.byContradiction
      intro hda
      simp [valuation, twoLetterPrefixFourMul] at evaluated
      exact hda evaluated.symm
    exact ⟨rfl, second⟩
  · let valuation : Nat → Fin 4 :=
      fun x => if x = a then 1 else if x = b then 3 else 0
    have evaluated := valid valuation
    change
      twoLetterPrefixFourMul (valuation a) (valuation b) =
        twoLetterPrefixFourMul (valuation a) (valuation d) at evaluated
    have second : b = d := by
      apply Decidable.byContradiction
      intro hbd
      by_cases hda : d = a
      · simp [valuation, hba, hda, twoLetterPrefixFourMul] at evaluated
      · simp [valuation, hba, hda, Ne.symm hbd,
          twoLetterPrefixFourMul] at evaluated
    exact ⟨rfl, second⟩

private theorem constantOne_nontrivial
    (x y : Nat) (rest : List Nat) :
    twoLetterPrefixFour.semigroup.eval (fun _ => (1 : Fin 4))
      (wordOfCons x (y :: rest)) = (0 : Fin 4) := by
  rw [twoLetterPrefixEval_pair]
  rfl

/-- Unrestricted completeness over `Nat` variables. The one law contracts
every nontrivial word to its first two variables, and the exact table
separates projections from ordered pairs and separates both pair
coordinates. -/
theorem twoLetterPrefixFourBasis_complete :
    BasisFor twoLetterPrefixFour.semigroup
      twoLetterPrefixBasis := by
  refine ⟨twoLetterPrefixFourBasis_models, ?_⟩
  intro e valid
  cases e with
  | mk lhs rhs =>
      cases lhs with
      | mk lx ltail =>
          cases rhs with
          | mk rx rtail =>
              cases ltail with
              | nil =>
                  cases rtail with
                  | nil =>
                      have same : lx = rx :=
                        twoLetterPrefixValidSingleton_eq valid
                      subst rx
                      exact Derives.refl _
                  | cons ry rrest =>
                      have evaluated := valid (fun _ => (1 : Fin 4))
                      change
                        (1 : Fin 4) =
                          twoLetterPrefixFour.semigroup.eval
                            (fun _ => (1 : Fin 4))
                            (wordOfCons rx (ry :: rrest)) at evaluated
                      rw [constantOne_nontrivial] at evaluated
                      simp at evaluated
              | cons ly lrest =>
                  cases rtail with
                  | nil =>
                      have evaluated := valid (fun _ => (1 : Fin 4))
                      change
                        twoLetterPrefixFour.semigroup.eval
                            (fun _ => (1 : Fin 4))
                            (wordOfCons lx (ly :: lrest)) =
                          (1 : Fin 4) at evaluated
                      rw [constantOne_nontrivial] at evaluated
                      simp at evaluated
                  | cons ry rrest =>
                      have pairValid :
                          (Identity.mk
                            (wordOfCons lx [ly])
                            (wordOfCons rx [ry])).SatisfiedBy
                            twoLetterPrefixFour.semigroup := by
                        intro valuation
                        have evaluated := valid valuation
                        change
                          twoLetterPrefixFour.semigroup.eval valuation
                              (wordOfCons lx (ly :: lrest)) =
                            twoLetterPrefixFour.semigroup.eval valuation
                              (wordOfCons rx (ry :: rrest)) at evaluated
                        rw [twoLetterPrefixEval_pair,
                          twoLetterPrefixEval_pair] at evaluated
                        exact evaluated
                      have same :=
                        twoLetterPrefixValidPair_eq pairValid
                      rcases same with ⟨rfl, rfl⟩
                      exact Derives.trans
                        (twoLetterPrefixDerivesToPair lx ly lrest)
                        (Derives.symm
                          (twoLetterPrefixDerivesToPair lx ly rrest))

theorem twoLetterPrefixFourOppositeBasis_complete :
    BasisFor twoLetterPrefixFour.semigroup.opposite
      (reversedBasis twoLetterPrefixBasis) :=
  twoLetterPrefixFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples
