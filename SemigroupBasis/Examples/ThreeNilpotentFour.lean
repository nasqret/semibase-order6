import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The exact zero-based form of the catalogue table
`[[1,1,1,1],[1,1,1,1],[1,1,1,1],[1,1,2,2]]`. -/
def threeNilpotentFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else 0
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else 0
  else if a = 2 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else 0
  else
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 1 else 1

/-- The four-element three-nilpotent semigroup representing `S4_9`. -/
def threeNilpotentFour : FiniteTable where
  order := 4
  mul := threeNilpotentFourMul
  assoc := by decide

def threeNilpotentXXX : Word Nat := ⟨0, [0, 0]⟩
def threeNilpotentXXY : Word Nat := ⟨0, [0, 1]⟩
def threeNilpotentXYX : Word Nat := ⟨0, [1, 0]⟩
def threeNilpotentXYY : Word Nat := ⟨0, [1, 1]⟩
def threeNilpotentXYZ : Word Nat := ⟨0, [1, 2]⟩
def threeNilpotentYXX : Word Nat := ⟨1, [0, 0]⟩

def threeNilpotentXXXLawXXY : Identity Nat :=
  ⟨threeNilpotentXXX, threeNilpotentXXY⟩

def threeNilpotentXXXLawXYX : Identity Nat :=
  ⟨threeNilpotentXXX, threeNilpotentXYX⟩

def threeNilpotentXXXLawXYY : Identity Nat :=
  ⟨threeNilpotentXXX, threeNilpotentXYY⟩

def threeNilpotentXXXLawXYZ : Identity Nat :=
  ⟨threeNilpotentXXX, threeNilpotentXYZ⟩

def threeNilpotentXXXLawYXX : Identity Nat :=
  ⟨threeNilpotentXXX, threeNilpotentYXX⟩

/-- The exact basis
`xxx = xxy`, `xxx = xyx`, `xxx = xyy`, `xxx = xyz`, `xxx = yxx`. -/
def threeNilpotentFourBasis : List (Identity Nat) :=
  [threeNilpotentXXXLawXXY, threeNilpotentXXXLawXYX,
    threeNilpotentXXXLawXYY, threeNilpotentXXXLawXYZ,
    threeNilpotentXXXLawYXX]

private def instantiateThreeWords (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem threeNilpotentDerivesXYY (u v : Word Nat) :
    Derives threeNilpotentFourBasis
      ((u ++ u) ++ u) ((u ++ v) ++ v) := by
  have hbase :
      Derives threeNilpotentFourBasis
        threeNilpotentXXX threeNilpotentXYY :=
    Derives.fromBasis (e := threeNilpotentXXXLawXYY) (by
      simp [threeNilpotentFourBasis])
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [threeNilpotentXXXLawXYY, threeNilpotentXXX,
    threeNilpotentXYY, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem threeNilpotentDerivesXYZ (u v w : Word Nat) :
    Derives threeNilpotentFourBasis
      ((u ++ u) ++ u) ((u ++ v) ++ w) := by
  have hbase :
      Derives threeNilpotentFourBasis
        threeNilpotentXXX threeNilpotentXYZ :=
    Derives.fromBasis (e := threeNilpotentXXXLawXYZ) (by
      simp [threeNilpotentFourBasis])
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [threeNilpotentXXXLawXYZ, threeNilpotentXXX,
    threeNilpotentXYZ, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem threeNilpotentDerivesYXX (u v : Word Nat) :
    Derives threeNilpotentFourBasis
      ((u ++ u) ++ u) ((v ++ u) ++ u) := by
  have hbase :
      Derives threeNilpotentFourBasis
        threeNilpotentXXX threeNilpotentYXX :=
    Derives.fromBasis (e := threeNilpotentXXXLawYXX) (by
      simp [threeNilpotentFourBasis])
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [threeNilpotentXXXLawYXX, threeNilpotentXXX,
    threeNilpotentYXX, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

/-- All products of three nonempty blocks belong to one derivability class. -/
theorem threeNilpotentDerivesCommonLongProduct
    (u v w p : Word Nat) :
    Derives threeNilpotentFourBasis
      ((u ++ v) ++ w) ((p ++ p) ++ p) := by
  exact Derives.trans
    (Derives.symm (threeNilpotentDerivesXYZ u v w)) <|
      Derives.trans (threeNilpotentDerivesYXX u p) <|
        Derives.symm (threeNilpotentDerivesXYY p u)

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- Globally over `Nat` variables, any two words of length at least three
are derivably equal from the five displayed identities. -/
theorem threeNilpotentDerivesLongWords (u v : Word Nat)
    (hu : 3 ≤ u.toList.length) (hv : 3 ≤ v.toList.length) :
    Derives threeNilpotentFourBasis u v := by
  cases u with
  | mk ux utail =>
      cases utail with
      | nil => simp [Word.toList] at hu
      | cons uy urest =>
          cases urest with
          | nil => simp [Word.toList] at hu
          | cons uz uzs =>
              cases v with
              | mk vx vtail =>
                  cases vtail with
                  | nil => simp [Word.toList] at hv
                  | cons vy vrest =>
                      cases vrest with
                      | nil => simp [Word.toList] at hv
                      | cons vz vzs =>
                          let p := Word.singleton 0
                          have lhs :=
                            threeNilpotentDerivesCommonLongProduct
                              (Word.singleton ux) (Word.singleton uy)
                              (wordOfCons uz uzs) p
                          have rhs :=
                            threeNilpotentDerivesCommonLongProduct
                              (Word.singleton vx) (Word.singleton vy)
                              (wordOfCons vz vzs) p
                          exact Derives.trans
                            (by simpa [wordOfCons, Word.singleton,
                                Word.append] using lhs)
                            (Derives.symm <| by
                              simpa [wordOfCons, Word.singleton,
                                Word.append] using rhs)

private theorem threeNilpotentFourMul_spec (a b : Fin 4) :
    threeNilpotentFourMul a b =
      if a = 3 ∧ (b = 2 ∨ b = 3) then 1 else 0 := by
  decide +revert

private theorem threeNilpotentFourMul_triple_zero
    (a b c : Fin 4) :
    threeNilpotentFourMul (threeNilpotentFourMul a b) c = 0 := by
  decide +revert

theorem threeNilpotentFourBasis_models :
    Models threeNilpotentFour.semigroup threeNilpotentFourBasis := by
  intro e he
  simp only [threeNilpotentFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · intro valuation
    change
      threeNilpotentFourMul
          (threeNilpotentFourMul (valuation 0) (valuation 0))
          (valuation 0) =
        threeNilpotentFourMul
          (threeNilpotentFourMul (valuation 0) (valuation 0))
          (valuation 1)
    rw [threeNilpotentFourMul_triple_zero,
      threeNilpotentFourMul_triple_zero]
  · intro valuation
    change
      threeNilpotentFourMul
          (threeNilpotentFourMul (valuation 0) (valuation 0))
          (valuation 0) =
        threeNilpotentFourMul
          (threeNilpotentFourMul (valuation 0) (valuation 1))
          (valuation 0)
    rw [threeNilpotentFourMul_triple_zero,
      threeNilpotentFourMul_triple_zero]
  · intro valuation
    change
      threeNilpotentFourMul
          (threeNilpotentFourMul (valuation 0) (valuation 0))
          (valuation 0) =
        threeNilpotentFourMul
          (threeNilpotentFourMul (valuation 0) (valuation 1))
          (valuation 1)
    rw [threeNilpotentFourMul_triple_zero,
      threeNilpotentFourMul_triple_zero]
  · intro valuation
    change
      threeNilpotentFourMul
          (threeNilpotentFourMul (valuation 0) (valuation 0))
          (valuation 0) =
        threeNilpotentFourMul
          (threeNilpotentFourMul (valuation 0) (valuation 1))
          (valuation 2)
    rw [threeNilpotentFourMul_triple_zero,
      threeNilpotentFourMul_triple_zero]
  · intro valuation
    change
      threeNilpotentFourMul
          (threeNilpotentFourMul (valuation 0) (valuation 0))
          (valuation 0) =
        threeNilpotentFourMul
          (threeNilpotentFourMul (valuation 1) (valuation 0))
          (valuation 0)
    rw [threeNilpotentFourMul_triple_zero,
      threeNilpotentFourMul_triple_zero]

private theorem threeNilpotentFourMul_zero_left (a : Fin 4) :
    threeNilpotentFourMul 0 a = 0 := by
  decide +revert

private theorem threeNilpotentFold_zero (xs : List Nat)
    (valuation : Nat → Fin 4) :
    xs.foldl
        (fun current x =>
          threeNilpotentFourMul current (valuation x)) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, threeNilpotentFourMul_zero_left]
      exact ih

theorem threeNilpotentEval_long
    (valuation : Nat → Fin 4) (x y z : Nat) (zs : List Nat) :
    threeNilpotentFour.semigroup.eval valuation
      (wordOfCons x (y :: z :: zs)) = (0 : Fin 4) := by
  change
    zs.foldl
      (fun current t =>
        threeNilpotentFourMul current (valuation t))
      (threeNilpotentFourMul
        (threeNilpotentFourMul (valuation x) (valuation y))
        (valuation z)) = 0
  rw [threeNilpotentFourMul_triple_zero]
  exact threeNilpotentFold_zero zs valuation

private def singletonSeparator (x : Nat) : Nat → Fin 4 :=
  fun y => if y = x then 3 else 0

/-- The exact table separates singleton projections. -/
theorem threeNilpotentValidSingleton_eq {x y : Nat}
    (valid :
      (Identity.mk (Word.singleton x) (Word.singleton y)).SatisfiedBy
        threeNilpotentFour.semigroup) :
    x = y := by
  have evaluated := valid (singletonSeparator x)
  change singletonSeparator x x = singletonSeparator x y at evaluated
  apply Decidable.byContradiction
  intro hne
  simp [singletonSeparator, Ne.symm hne] at evaluated

private def firstCoordinateSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 3 else 2

private theorem firstCoordinateSeparator_eval (z a b : Nat) :
    threeNilpotentFour.semigroup.eval (firstCoordinateSeparator z)
        (wordOfCons a [b]) =
      if a = z then (1 : Fin 4) else (0 : Fin 4) := by
  change
    threeNilpotentFourMul
      (firstCoordinateSeparator z a)
      (firstCoordinateSeparator z b) =
        if a = z then (1 : Fin 4) else (0 : Fin 4)
  rw [threeNilpotentFourMul_spec]
  by_cases ha : a = z <;> by_cases hb : b = z <;>
    simp [firstCoordinateSeparator, ha, hb]

private theorem validPair_first_eq {a b c d : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        threeNilpotentFour.semigroup) :
    a = c := by
  have evaluated := valid (firstCoordinateSeparator a)
  rw [firstCoordinateSeparator_eval,
    firstCoordinateSeparator_eval] at evaluated
  apply Decidable.byContradiction
  intro hne
  simp [Ne.symm hne] at evaluated

private def diagonalSeparator (a : Nat) : Nat → Fin 4 :=
  fun x => if x = a then 3 else 0

private theorem diagonalSeparator_eval (a b : Nat) :
    threeNilpotentFour.semigroup.eval (diagonalSeparator a)
        (wordOfCons a [b]) =
      if b = a then (1 : Fin 4) else (0 : Fin 4) := by
  change
    threeNilpotentFourMul
      (diagonalSeparator a a) (diagonalSeparator a b) =
        if b = a then (1 : Fin 4) else (0 : Fin 4)
  rw [threeNilpotentFourMul_spec]
  by_cases hb : b = a <;> simp [diagonalSeparator, hb]

/-- The exact table separates ordered quadratic words coordinate by
coordinate; validity forces literal equality of both variables. -/
theorem threeNilpotentValidPair_eq {a b c d : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        threeNilpotentFour.semigroup) :
    a = c ∧ b = d := by
  have first : a = c := validPair_first_eq valid
  subst c
  have diagonalEq := valid (diagonalSeparator a)
  rw [diagonalSeparator_eval, diagonalSeparator_eval] at diagonalEq
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
        if x = a then 3 else if x = b then 2 else 0
      have evaluated := valid valuation
      change
        threeNilpotentFourMul (valuation a) (valuation b) =
          threeNilpotentFourMul (valuation a) (valuation d) at evaluated
      rw [threeNilpotentFourMul_spec,
        threeNilpotentFourMul_spec] at evaluated
      apply Decidable.byContradiction
      intro hbd
      simp [valuation, hba, hda, Ne.symm hbd] at evaluated
  exact ⟨rfl, second⟩

private theorem allThree_pair (a b : Nat) :
    threeNilpotentFour.semigroup.eval (fun _ => (3 : Fin 4))
      (wordOfCons a [b]) = (1 : Fin 4) := by
  change threeNilpotentFourMul 3 3 = 1
  rw [threeNilpotentFourMul_spec]
  decide

private theorem allThree_long (x y z : Nat) (zs : List Nat) :
    threeNilpotentFour.semigroup.eval (fun _ => (3 : Fin 4))
      (wordOfCons x (y :: z :: zs)) = (0 : Fin 4) :=
  threeNilpotentEval_long _ _ _ _ _

/-- Unrestricted completeness over `Nat` variables. The exact table
distinguishes singleton projections and ordered quadratic words, while the
basis collapses all words of length at least three. -/
theorem threeNilpotentFourBasis_complete :
    BasisFor threeNilpotentFour.semigroup
      threeNilpotentFourBasis := by
  refine ⟨threeNilpotentFourBasis_models, ?_⟩
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
                        apply threeNilpotentValidSingleton_eq
                        exact valid
                      subst rx
                      exact Derives.refl _
                  | cons ry rrest =>
                      cases rrest with
                      | nil =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            (3 : Fin 4) =
                              threeNilpotentFour.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons rx [ry]) at evaluated
                          rw [allThree_pair] at evaluated
                          simp at evaluated
                      | cons rz rzs =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            (3 : Fin 4) =
                              threeNilpotentFour.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons rx (ry :: rz :: rzs)) at evaluated
                          rw [allThree_long] at evaluated
                          simp at evaluated
              | cons ly lrest =>
                  cases lrest with
                  | nil =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            threeNilpotentFour.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons lx [ly]) =
                              (3 : Fin 4) at evaluated
                          rw [allThree_pair] at evaluated
                          simp at evaluated
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              have same : lx = rx ∧ ly = ry := by
                                apply threeNilpotentValidPair_eq
                                exact valid
                              rcases same with ⟨rfl, rfl⟩
                              exact Derives.refl _
                          | cons rz rzs =>
                              have evaluated := valid (fun _ => (3 : Fin 4))
                              change
                                threeNilpotentFour.semigroup.eval
                                    (fun _ => (3 : Fin 4))
                                    (wordOfCons lx [ly]) =
                                  threeNilpotentFour.semigroup.eval
                                    (fun _ => (3 : Fin 4))
                                    (wordOfCons rx (ry :: rz :: rzs))
                                    at evaluated
                              rw [allThree_pair, allThree_long] at evaluated
                              simp at evaluated
                  | cons lz lzs =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (3 : Fin 4))
                          change
                            threeNilpotentFour.semigroup.eval
                                (fun _ => (3 : Fin 4))
                                (wordOfCons lx (ly :: lz :: lzs)) =
                              (3 : Fin 4) at evaluated
                          rw [allThree_long] at evaluated
                          simp at evaluated
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              have evaluated := valid (fun _ => (3 : Fin 4))
                              change
                                threeNilpotentFour.semigroup.eval
                                    (fun _ => (3 : Fin 4))
                                    (wordOfCons lx (ly :: lz :: lzs)) =
                                  threeNilpotentFour.semigroup.eval
                                    (fun _ => (3 : Fin 4))
                                    (wordOfCons rx [ry]) at evaluated
                              rw [allThree_long, allThree_pair] at evaluated
                              simp at evaluated
                          | cons rz rzs =>
                              have lhsCommon :=
                                threeNilpotentDerivesCommonLongProduct
                                  (Word.singleton lx) (Word.singleton ly)
                                  (wordOfCons lz lzs) (Word.singleton 0)
                              have rhsCommon :=
                                threeNilpotentDerivesCommonLongProduct
                                  (Word.singleton rx) (Word.singleton ry)
                                  (wordOfCons rz rzs) (Word.singleton 0)
                              exact Derives.trans
                                (by simpa [wordOfCons, Word.singleton,
                                    Word.append] using lhsCommon)
                                (Derives.symm <| by
                                  simpa [wordOfCons, Word.singleton,
                                    Word.append] using rhsCommon)

theorem threeNilpotentFourOppositeBasis_complete :
    BasisFor threeNilpotentFour.semigroup.opposite
      (reversedBasis threeNilpotentFourBasis) :=
  threeNilpotentFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples
