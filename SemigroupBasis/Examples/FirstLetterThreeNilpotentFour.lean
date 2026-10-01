import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The exact zero-based form of the catalogue table
`[[1,1,1,1],[1,1,1,1],[1,1,2,1],[4,4,4,4]]`. -/
def firstLetterThreeNilpotentFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else 0
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else 0
  else if a = 2 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 1 else 0
  else
    if b = 0 then 3 else if b = 1 then 3 else if b = 2 then 3 else 3

/-- The four-element semigroup representing `S4_39`. Products of length at
least three remember only whether the first letter evaluates to `3`. -/
def firstLetterThreeNilpotentFour : FiniteTable where
  order := 4
  mul := firstLetterThreeNilpotentFourMul
  assoc := by decide

def firstLetterThreeNilpotentXXX : Word Nat := ⟨0, [0, 0]⟩
def firstLetterThreeNilpotentXXY : Word Nat := ⟨0, [0, 1]⟩
def firstLetterThreeNilpotentXYX : Word Nat := ⟨0, [1, 0]⟩
def firstLetterThreeNilpotentXYY : Word Nat := ⟨0, [1, 1]⟩
def firstLetterThreeNilpotentXYZ : Word Nat := ⟨0, [1, 2]⟩

def firstLetterThreeNilpotentXXXLawXXY : Identity Nat :=
  ⟨firstLetterThreeNilpotentXXX, firstLetterThreeNilpotentXXY⟩

def firstLetterThreeNilpotentXXXLawXYX : Identity Nat :=
  ⟨firstLetterThreeNilpotentXXX, firstLetterThreeNilpotentXYX⟩

def firstLetterThreeNilpotentXXXLawXYY : Identity Nat :=
  ⟨firstLetterThreeNilpotentXXX, firstLetterThreeNilpotentXYY⟩

def firstLetterThreeNilpotentXXXLawXYZ : Identity Nat :=
  ⟨firstLetterThreeNilpotentXXX, firstLetterThreeNilpotentXYZ⟩

/-- The exact stored basis
`xxx = xxy`, `xxx = xyx`, `xxx = xyy`, `xxx = xyz`. -/
def firstLetterThreeNilpotentFourBasis : List (Identity Nat) :=
  [firstLetterThreeNilpotentXXXLawXXY,
    firstLetterThreeNilpotentXXXLawXYX,
    firstLetterThreeNilpotentXXXLawXYY,
    firstLetterThreeNilpotentXXXLawXYZ]

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem firstLetterThreeNilpotentDerivesXYZ
    (u v w : Word Nat) :
    Derives firstLetterThreeNilpotentFourBasis
      ((u ++ u) ++ u) ((u ++ v) ++ w) := by
  have hbase :
      Derives firstLetterThreeNilpotentFourBasis
        firstLetterThreeNilpotentXXX
        firstLetterThreeNilpotentXYZ :=
    Derives.fromBasis
      (e := firstLetterThreeNilpotentXXXLawXYZ) (by
        simp [firstLetterThreeNilpotentFourBasis])
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [firstLetterThreeNilpotentXXXLawXYZ,
    firstLetterThreeNilpotentXXX, firstLetterThreeNilpotentXYZ,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- Every word of length at least three is derivably equal to the cube of its
first variable. -/
theorem firstLetterThreeNilpotentDerivesLongToCube
    (x y z : Nat) (zs : List Nat) :
    Derives firstLetterThreeNilpotentFourBasis
      (wordOfCons x (y :: z :: zs)) (wordOfCons x [x, x]) := by
  have h :=
    firstLetterThreeNilpotentDerivesXYZ
      (Word.singleton x) (Word.singleton y) (wordOfCons z zs)
  exact Derives.symm <| by
    simpa [wordOfCons, Word.singleton, Word.append] using h

private theorem firstLetterThreeNilpotentFourMul_spec
    (a b : Fin 4) :
    firstLetterThreeNilpotentFourMul a b =
      if a = 3 then 3 else if a = 2 ∧ b = 2 then 1 else 0 := by
  decide +revert

private theorem firstLetterThreeNilpotentFourMul_triple_spec
    (a b c : Fin 4) :
    firstLetterThreeNilpotentFourMul
        (firstLetterThreeNilpotentFourMul a b) c =
      if a = 3 then 3 else 0 := by
  decide +revert

private theorem firstLetterThreeNilpotentFourMul_zero_left
    (a : Fin 4) :
    firstLetterThreeNilpotentFourMul 0 a = 0 := by
  decide +revert

private theorem firstLetterThreeNilpotentFourMul_three_left
    (a : Fin 4) :
    firstLetterThreeNilpotentFourMul 3 a = 3 := by
  decide +revert

private theorem firstLetterThreeNilpotentFold_zero
    (xs : List Nat) (valuation : Nat → Fin 4) :
    xs.foldl
        (fun current x =>
          firstLetterThreeNilpotentFourMul current (valuation x))
        0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons,
        firstLetterThreeNilpotentFourMul_zero_left]
      exact ih

private theorem firstLetterThreeNilpotentFold_three
    (xs : List Nat) (valuation : Nat → Fin 4) :
    xs.foldl
        (fun current x =>
          firstLetterThreeNilpotentFourMul current (valuation x))
        3 = 3 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons,
        firstLetterThreeNilpotentFourMul_three_left]
      exact ih

theorem firstLetterThreeNilpotentEval_long
    (valuation : Nat → Fin 4) (x y z : Nat) (zs : List Nat) :
    firstLetterThreeNilpotentFour.semigroup.eval valuation
        (wordOfCons x (y :: z :: zs)) =
      if valuation x = (3 : Fin 4) then (3 : Fin 4) else (0 : Fin 4) := by
  change
    zs.foldl
        (fun current t =>
          firstLetterThreeNilpotentFourMul current (valuation t))
        (firstLetterThreeNilpotentFourMul
          (firstLetterThreeNilpotentFourMul
            (valuation x) (valuation y))
          (valuation z)) =
      if valuation x = 3 then 3 else 0
  rw [firstLetterThreeNilpotentFourMul_triple_spec]
  by_cases hx : valuation x = 3
  · simp only [hx, if_pos]
    exact firstLetterThreeNilpotentFold_three zs valuation
  · simp only [hx, if_false]
    exact firstLetterThreeNilpotentFold_zero zs valuation

theorem firstLetterThreeNilpotentFourBasis_models :
    Models firstLetterThreeNilpotentFour.semigroup
      firstLetterThreeNilpotentFourBasis := by
  intro e he
  simp only [firstLetterThreeNilpotentFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · intro valuation
    change
      firstLetterThreeNilpotentFourMul
          (firstLetterThreeNilpotentFourMul
            (valuation 0) (valuation 0))
          (valuation 0) =
        firstLetterThreeNilpotentFourMul
          (firstLetterThreeNilpotentFourMul
            (valuation 0) (valuation 0))
          (valuation 1)
    rw [firstLetterThreeNilpotentFourMul_triple_spec,
      firstLetterThreeNilpotentFourMul_triple_spec]
  · intro valuation
    change
      firstLetterThreeNilpotentFourMul
          (firstLetterThreeNilpotentFourMul
            (valuation 0) (valuation 0))
          (valuation 0) =
        firstLetterThreeNilpotentFourMul
          (firstLetterThreeNilpotentFourMul
            (valuation 0) (valuation 1))
          (valuation 0)
    rw [firstLetterThreeNilpotentFourMul_triple_spec,
      firstLetterThreeNilpotentFourMul_triple_spec]
  · intro valuation
    change
      firstLetterThreeNilpotentFourMul
          (firstLetterThreeNilpotentFourMul
            (valuation 0) (valuation 0))
          (valuation 0) =
        firstLetterThreeNilpotentFourMul
          (firstLetterThreeNilpotentFourMul
            (valuation 0) (valuation 1))
          (valuation 1)
    rw [firstLetterThreeNilpotentFourMul_triple_spec,
      firstLetterThreeNilpotentFourMul_triple_spec]
  · intro valuation
    change
      firstLetterThreeNilpotentFourMul
          (firstLetterThreeNilpotentFourMul
            (valuation 0) (valuation 0))
          (valuation 0) =
        firstLetterThreeNilpotentFourMul
          (firstLetterThreeNilpotentFourMul
            (valuation 0) (valuation 1))
          (valuation 2)
    rw [firstLetterThreeNilpotentFourMul_triple_spec,
      firstLetterThreeNilpotentFourMul_triple_spec]

private def singletonSeparator (x : Nat) : Nat → Fin 4 :=
  fun y => if y = x then 3 else 0

private theorem validSingleton_eq {x y : Nat}
    (valid :
      (Identity.mk (Word.singleton x) (Word.singleton y)).SatisfiedBy
        firstLetterThreeNilpotentFour.semigroup) :
    x = y := by
  have evaluated := valid (singletonSeparator x)
  change singletonSeparator x x = singletonSeparator x y at evaluated
  apply Decidable.byContradiction
  intro hne
  simp [singletonSeparator, Ne.symm hne] at evaluated

private def firstCoordinateSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 3 else 0

private theorem firstCoordinateSeparator_pair_eval
    (z a b : Nat) :
    firstLetterThreeNilpotentFour.semigroup.eval
        (firstCoordinateSeparator z) (wordOfCons a [b]) =
      if a = z then (3 : Fin 4) else 0 := by
  change
    firstLetterThreeNilpotentFourMul
        (firstCoordinateSeparator z a)
        (firstCoordinateSeparator z b) =
      if a = z then (3 : Fin 4) else 0
  rw [firstLetterThreeNilpotentFourMul_spec]
  by_cases ha : a = z <;>
    simp [firstCoordinateSeparator, ha]

private theorem validPair_first_eq {a b c d : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        firstLetterThreeNilpotentFour.semigroup) :
    a = c := by
  have evaluated := valid (firstCoordinateSeparator a)
  rw [firstCoordinateSeparator_pair_eval,
    firstCoordinateSeparator_pair_eval] at evaluated
  apply Decidable.byContradiction
  intro hne
  simp [Ne.symm hne] at evaluated

private def diagonalSeparator (a : Nat) : Nat → Fin 4 :=
  fun x => if x = a then 2 else 0

private theorem diagonalSeparator_pair_eval (a b : Nat) :
    firstLetterThreeNilpotentFour.semigroup.eval
        (diagonalSeparator a) (wordOfCons a [b]) =
      if b = a then (1 : Fin 4) else 0 := by
  change
    firstLetterThreeNilpotentFourMul
        (diagonalSeparator a a) (diagonalSeparator a b) =
      if b = a then (1 : Fin 4) else 0
  rw [firstLetterThreeNilpotentFourMul_spec]
  by_cases hb : b = a <;> simp [diagonalSeparator, hb]

/-- The exact table separates ordered quadratic words coordinate by
coordinate. -/
theorem firstLetterThreeNilpotentValidPair_eq {a b c d : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        firstLetterThreeNilpotentFour.semigroup) :
    a = c ∧ b = d := by
  have first : a = c := validPair_first_eq valid
  subst c
  have diagonalEq := valid (diagonalSeparator a)
  rw [diagonalSeparator_pair_eval,
    diagonalSeparator_pair_eval] at diagonalEq
  have second : b = d := by
    by_cases hba : b = a
    · have hda : d = a := by
        apply Decidable.byContradiction
        intro hda
        simp [hba, hda] at diagonalEq
      exact hba.trans hda.symm
    · have hda : d ≠ a := by
        intro h
        simp [hba, h] at diagonalEq
      let valuation : Nat → Fin 4 := fun x =>
        if x = a then 2 else if x = b then 2 else 0
      have evaluated := valid valuation
      change
        firstLetterThreeNilpotentFourMul
            (valuation a) (valuation b) =
          firstLetterThreeNilpotentFourMul
            (valuation a) (valuation d) at evaluated
      rw [firstLetterThreeNilpotentFourMul_spec,
        firstLetterThreeNilpotentFourMul_spec] at evaluated
      apply Decidable.byContradiction
      intro hbd
      simp [valuation, hba, hda, Ne.symm hbd] at evaluated
  exact ⟨rfl, second⟩

private theorem firstCoordinateSeparator_long_eval
    (z x y t : Nat) (ts : List Nat) :
    firstLetterThreeNilpotentFour.semigroup.eval
        (firstCoordinateSeparator z) (wordOfCons x (y :: t :: ts)) =
      if x = z then (3 : Fin 4) else 0 := by
  rw [firstLetterThreeNilpotentEval_long]
  by_cases hx : x = z <;>
    simp [firstCoordinateSeparator, hx]

private theorem validLong_first_eq
    {a b c : Nat} {as : List Nat}
    {d e f : Nat} {ds : List Nat}
    (valid :
      (Identity.mk
        (wordOfCons a (b :: c :: as))
        (wordOfCons d (e :: f :: ds))).SatisfiedBy
          firstLetterThreeNilpotentFour.semigroup) :
    a = d := by
  have evaluated := valid (firstCoordinateSeparator a)
  rw [firstCoordinateSeparator_long_eval,
    firstCoordinateSeparator_long_eval] at evaluated
  apply Decidable.byContradiction
  intro hne
  simp [Ne.symm hne] at evaluated

private theorem allTwo_singleton (a : Nat) :
    firstLetterThreeNilpotentFour.semigroup.eval
        (fun _ => (2 : Fin 4)) (Word.singleton a) = (2 : Fin 4) := rfl

private theorem allTwo_pair (a b : Nat) :
    firstLetterThreeNilpotentFour.semigroup.eval
        (fun _ => (2 : Fin 4)) (wordOfCons a [b]) = (1 : Fin 4) := by
  change firstLetterThreeNilpotentFourMul 2 2 = 1
  decide

private theorem allTwo_long
    (x y z : Nat) (zs : List Nat) :
    firstLetterThreeNilpotentFour.semigroup.eval
        (fun _ => (2 : Fin 4)) (wordOfCons x (y :: z :: zs)) =
      (0 : Fin 4) := by
  rw [firstLetterThreeNilpotentEval_long]
  decide

/-- Unrestricted completeness over `Nat` variables. Normal forms are
singleton projections, ordered quadratic words, and one long-word class for
each first variable. -/
theorem firstLetterThreeNilpotentValid_class
    (e : Identity Nat)
    (valid : e.SatisfiedBy firstLetterThreeNilpotentFour.semigroup) :
    (e.lhs.toList.length = 1 ∧ e.rhs.toList.length = 1 ∧
        e.lhs = e.rhs) ∨
      (e.lhs.toList.length = 2 ∧ e.rhs.toList.length = 2 ∧
        e.lhs = e.rhs) ∨
      (3 ≤ e.lhs.toList.length ∧ 3 ≤ e.rhs.toList.length ∧
        e.lhs.head = e.rhs.head) := by
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
                      have same : lx = rx := by
                        apply validSingleton_eq
                        exact valid
                      subst rx
                      exact Or.inl ⟨by rfl, by rfl, rfl⟩
                  | cons ry rrest =>
                      cases rrest with
                      | nil =>
                          have evaluated := valid (fun _ => (2 : Fin 4))
                          change
                            firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (Word.singleton lx) =
                              firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (wordOfCons rx [ry]) at evaluated
                          rw [allTwo_singleton, allTwo_pair] at evaluated
                          simp at evaluated
                      | cons rz rzs =>
                          have evaluated := valid (fun _ => (2 : Fin 4))
                          change
                            firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (Word.singleton lx) =
                              firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (wordOfCons rx (ry :: rz :: rzs))
                                at evaluated
                          rw [allTwo_singleton, allTwo_long] at evaluated
                          simp at evaluated
              | cons ly lrest =>
                  cases lrest with
                  | nil =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (2 : Fin 4))
                          change
                            firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (wordOfCons lx [ly]) =
                              firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (Word.singleton rx) at evaluated
                          rw [allTwo_pair, allTwo_singleton] at evaluated
                          simp at evaluated
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              have same : lx = rx ∧ ly = ry := by
                                apply firstLetterThreeNilpotentValidPair_eq
                                exact valid
                              rcases same with ⟨rfl, rfl⟩
                              exact Or.inr <| Or.inl ⟨by rfl, by rfl, rfl⟩
                          | cons rz rzs =>
                              have evaluated :=
                                valid (fun _ => (2 : Fin 4))
                              change
                                firstLetterThreeNilpotentFour.semigroup.eval
                                    (fun _ => (2 : Fin 4))
                                    (wordOfCons lx [ly]) =
                                  firstLetterThreeNilpotentFour.semigroup.eval
                                    (fun _ => (2 : Fin 4))
                                    (wordOfCons rx (ry :: rz :: rzs))
                                    at evaluated
                              rw [allTwo_pair, allTwo_long] at evaluated
                              simp at evaluated
                  | cons lz lzs =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (2 : Fin 4))
                          change
                            firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (wordOfCons lx (ly :: lz :: lzs)) =
                              firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (Word.singleton rx) at evaluated
                          rw [allTwo_long, allTwo_singleton] at evaluated
                          simp at evaluated
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              have evaluated :=
                                valid (fun _ => (2 : Fin 4))
                              change
                                firstLetterThreeNilpotentFour.semigroup.eval
                                    (fun _ => (2 : Fin 4))
                                    (wordOfCons lx (ly :: lz :: lzs)) =
                                  firstLetterThreeNilpotentFour.semigroup.eval
                                    (fun _ => (2 : Fin 4))
                                    (wordOfCons rx [ry]) at evaluated
                              rw [allTwo_long, allTwo_pair] at evaluated
                              simp at evaluated
                          | cons rz rzs =>
                              have heads : lx = rx := by
                                apply validLong_first_eq
                                exact valid
                              exact Or.inr <| Or.inr ⟨by simp [Word.toList], by simp [Word.toList], heads⟩

theorem firstLetterThreeNilpotentFourBasis_complete :
    BasisFor firstLetterThreeNilpotentFour.semigroup
      firstLetterThreeNilpotentFourBasis := by
  refine ⟨firstLetterThreeNilpotentFourBasis_models, ?_⟩
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
                      have same : lx = rx := by
                        apply validSingleton_eq
                        exact valid
                      subst rx
                      exact Derives.refl _
                  | cons ry rrest =>
                      cases rrest with
                      | nil =>
                          have evaluated := valid (fun _ => (2 : Fin 4))
                          change
                            firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (Word.singleton lx) =
                              firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (wordOfCons rx [ry]) at evaluated
                          rw [allTwo_singleton, allTwo_pair] at evaluated
                          simp at evaluated
                      | cons rz rzs =>
                          have evaluated := valid (fun _ => (2 : Fin 4))
                          change
                            firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (Word.singleton lx) =
                              firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (wordOfCons rx (ry :: rz :: rzs))
                                at evaluated
                          rw [allTwo_singleton, allTwo_long] at evaluated
                          simp at evaluated
              | cons ly lrest =>
                  cases lrest with
                  | nil =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (2 : Fin 4))
                          change
                            firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (wordOfCons lx [ly]) =
                              firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (Word.singleton rx) at evaluated
                          rw [allTwo_pair, allTwo_singleton] at evaluated
                          simp at evaluated
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              have same : lx = rx ∧ ly = ry := by
                                apply firstLetterThreeNilpotentValidPair_eq
                                exact valid
                              rcases same with ⟨rfl, rfl⟩
                              exact Derives.refl _
                          | cons rz rzs =>
                              have evaluated :=
                                valid (fun _ => (2 : Fin 4))
                              change
                                firstLetterThreeNilpotentFour.semigroup.eval
                                    (fun _ => (2 : Fin 4))
                                    (wordOfCons lx [ly]) =
                                  firstLetterThreeNilpotentFour.semigroup.eval
                                    (fun _ => (2 : Fin 4))
                                    (wordOfCons rx (ry :: rz :: rzs))
                                    at evaluated
                              rw [allTwo_pair, allTwo_long] at evaluated
                              simp at evaluated
                  | cons lz lzs =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (2 : Fin 4))
                          change
                            firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (wordOfCons lx (ly :: lz :: lzs)) =
                              firstLetterThreeNilpotentFour.semigroup.eval
                                (fun _ => (2 : Fin 4))
                                (Word.singleton rx) at evaluated
                          rw [allTwo_long, allTwo_singleton] at evaluated
                          simp at evaluated
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              have evaluated :=
                                valid (fun _ => (2 : Fin 4))
                              change
                                firstLetterThreeNilpotentFour.semigroup.eval
                                    (fun _ => (2 : Fin 4))
                                    (wordOfCons lx (ly :: lz :: lzs)) =
                                  firstLetterThreeNilpotentFour.semigroup.eval
                                    (fun _ => (2 : Fin 4))
                                    (wordOfCons rx [ry]) at evaluated
                              rw [allTwo_long, allTwo_pair] at evaluated
                              simp at evaluated
                          | cons rz rzs =>
                              have heads : lx = rx := by
                                apply validLong_first_eq
                                exact valid
                              subst rx
                              exact Derives.trans
                                (firstLetterThreeNilpotentDerivesLongToCube
                                  lx ly lz lzs)
                                (Derives.symm
                                  (firstLetterThreeNilpotentDerivesLongToCube
                                    lx ry rz rzs))

theorem firstLetterThreeNilpotentFourOppositeBasis_complete :
    BasisFor firstLetterThreeNilpotentFour.semigroup.opposite
      (reversedBasis firstLetterThreeNilpotentFourBasis) :=
  firstLetterThreeNilpotentFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples
