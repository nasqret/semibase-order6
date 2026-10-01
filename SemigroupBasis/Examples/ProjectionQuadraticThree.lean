import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The exact zero-based form of the table
`[[1,1,1],[1,1,1],[1,1,2]]`. -/
def projectionQuadraticThreeMul (a b : Fin 3) : Fin 3 :=
  if a = 2 ∧ b = 2 then 1 else 0

/-- The three-element semigroup that retains a singleton value, records
whether both entries of a quadratic word are `2`, and sends every longer
product to `0`. -/
def projectionQuadraticThree : FiniteTable where
  order := 3
  mul := projectionQuadraticThreeMul
  assoc := by decide

def projectionQuadraticX : Word Nat := Word.singleton 0
def projectionQuadraticY : Word Nat := Word.singleton 1
def projectionQuadraticZ : Word Nat := Word.singleton 2
def projectionQuadraticXY : Word Nat := ⟨0, [1]⟩
def projectionQuadraticYX : Word Nat := ⟨1, [0]⟩
def projectionQuadraticXXX : Word Nat := ⟨0, [0, 0]⟩
def projectionQuadraticXXY : Word Nat := ⟨0, [0, 1]⟩
def projectionQuadraticXYZ : Word Nat := ⟨0, [1, 2]⟩

def projectionQuadraticCommutativityLaw : Identity Nat :=
  ⟨projectionQuadraticXY, projectionQuadraticYX⟩

def projectionQuadraticRepeatedLaw : Identity Nat :=
  ⟨projectionQuadraticXXX, projectionQuadraticXXY⟩

def projectionQuadraticLongLaw : Identity Nat :=
  ⟨projectionQuadraticXXX, projectionQuadraticXYZ⟩

/-- The exact basis `xy = yx`, `xxx = xxy`, `xxx = xyz`. -/
def projectionQuadraticThreeBasis : List (Identity Nat) :=
  [projectionQuadraticCommutativityLaw,
    projectionQuadraticRepeatedLaw,
    projectionQuadraticLongLaw]

private def instantiateThreeWords (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem projectionQuadraticDerivesCommutativity (u v : Word Nat) :
    Derives projectionQuadraticThreeBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives projectionQuadraticThreeBasis
        projectionQuadraticXY projectionQuadraticYX :=
    Derives.fromBasis (e := projectionQuadraticCommutativityLaw) <| by
      exact List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [projectionQuadraticThreeBasis,
    projectionQuadraticCommutativityLaw, projectionQuadraticXY,
    projectionQuadraticYX, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton] using h

theorem projectionQuadraticDerivesLongExpansion
    (u v w : Word Nat) :
    Derives projectionQuadraticThreeBasis
      ((u ++ u) ++ u) ((u ++ v) ++ w) := by
  have hbase :
      Derives projectionQuadraticThreeBasis
        projectionQuadraticXXX projectionQuadraticXYZ :=
    Derives.fromBasis (e := projectionQuadraticLongLaw) <| by
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [projectionQuadraticThreeBasis, projectionQuadraticLongLaw,
    projectionQuadraticXXX, projectionQuadraticXYZ,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- All products of three nonempty blocks belong to one derivability class. -/
theorem projectionQuadraticDerivesCommonLongProduct
    (u v w p : Word Nat) :
    Derives projectionQuadraticThreeBasis
      ((u ++ v) ++ w) ((p ++ p) ++ p) := by
  have collapse :=
    Derives.symm (projectionQuadraticDerivesLongExpansion u v w)
  have changeTail :=
    projectionQuadraticDerivesLongExpansion u p p
  have commute :
      Derives projectionQuadraticThreeBasis
        ((u ++ p) ++ p) ((p ++ p) ++ u) := by
    simpa [Word.append_assoc] using
      projectionQuadraticDerivesCommutativity u (p ++ p)
  have finish :=
    Derives.symm (projectionQuadraticDerivesLongExpansion p p u)
  exact Derives.trans collapse <|
    Derives.trans changeTail <| Derives.trans commute finish

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives projectionQuadraticThreeBasis
        (wordOfCons x xs) (wordOfCons y ys) →
      ListDerives (x :: xs) (y :: ys)

private theorem listDerives_of_perm {xs ys : List Nat}
    (h : xs.Perm ys) : ListDerives xs ys := by
  induction h with
  | nil =>
      exact ListDerives.empty
  | cons x _ ih =>
      cases ih with
      | empty =>
          exact ListDerives.words (Derives.refl _)
      | words derivation =>
          exact ListDerives.words <| by
            simpa [wordOfCons, Word.singleton, Word.append] using
              Derives.prepend (Word.singleton x) derivation
  | swap x y xs =>
      exact ListDerives.words <| by
        cases xs with
        | nil =>
            simpa [wordOfCons, Word.append, Word.singleton] using
              projectionQuadraticDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (projectionQuadraticDerivesCommutativity
                  (Word.singleton y) (Word.singleton x))
                (wordOfCons z zs)
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using swapped
  | trans _ _ ih₁ ih₂ =>
      cases ih₁ with
      | empty =>
          cases ih₂
          exact ListDerives.empty
      | words first =>
          cases ih₂ with
          | words second =>
              exact ListDerives.words (Derives.trans first second)

theorem projectionQuadraticDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives projectionQuadraticThreeBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- The fixed representative of the unique long-product class. -/
def projectionQuadraticLongNormal : Word Nat :=
  (Word.singleton 0 ++ Word.singleton 0) ++ Word.singleton 0

/-- The unrestricted normal form has three cases: the original projection,
the quadratic multiset, or the unique common long product. -/
def projectionQuadraticNormal (w : Word Nat) : Word Nat :=
  match w.tail with
  | [] => w
  | [_] => w
  | _ :: _ :: _ => projectionQuadraticLongNormal

theorem projectionQuadraticDerivesNormal (w : Word Nat) :
    Derives projectionQuadraticThreeBasis w
      (projectionQuadraticNormal w) := by
  cases w with
  | mk x tail =>
      cases tail with
      | nil =>
          exact Derives.refl _
      | cons y tail =>
          cases tail with
          | nil =>
              exact Derives.refl _
          | cons z zs =>
              simpa [projectionQuadraticNormal,
                projectionQuadraticLongNormal, wordOfCons, Word.append,
                Word.singleton, Word.append_assoc] using
                projectionQuadraticDerivesCommonLongProduct
                  (Word.singleton x) (Word.singleton y)
                  (wordOfCons z zs) (Word.singleton 0)

private theorem projectionQuadraticMul_commutative (a b : Fin 3) :
    projectionQuadraticThreeMul a b =
      projectionQuadraticThreeMul b a := by
  by_cases ha : a = 2 <;> by_cases hb : b = 2 <;>
    simp [projectionQuadraticThreeMul, ha, hb]

private theorem projectionQuadraticMul_repeated (a b : Fin 3) :
    projectionQuadraticThreeMul
        (projectionQuadraticThreeMul a a) a =
      projectionQuadraticThreeMul
        (projectionQuadraticThreeMul a a) b := by
  decide +revert

private theorem projectionQuadraticMul_long (a b c : Fin 3) :
    projectionQuadraticThreeMul
        (projectionQuadraticThreeMul a a) a =
      projectionQuadraticThreeMul
        (projectionQuadraticThreeMul a b) c := by
  decide +revert

theorem projectionQuadraticThreeBasis_models :
    Models projectionQuadraticThree.semigroup
      projectionQuadraticThreeBasis := by
  intro e he
  simp only [projectionQuadraticThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    change
      projectionQuadraticThreeMul (valuation 0) (valuation 1) =
        projectionQuadraticThreeMul (valuation 1) (valuation 0)
    exact projectionQuadraticMul_commutative _ _
  · intro valuation
    change
      projectionQuadraticThreeMul
          (projectionQuadraticThreeMul (valuation 0) (valuation 0))
          (valuation 0) =
        projectionQuadraticThreeMul
          (projectionQuadraticThreeMul (valuation 0) (valuation 0))
          (valuation 1)
    exact projectionQuadraticMul_repeated _ _
  · intro valuation
    change
      projectionQuadraticThreeMul
          (projectionQuadraticThreeMul (valuation 0) (valuation 0))
          (valuation 0) =
        projectionQuadraticThreeMul
          (projectionQuadraticThreeMul (valuation 0) (valuation 1))
          (valuation 2)
    exact projectionQuadraticMul_long _ _ _

private theorem projectionQuadraticMul_zero_left (a : Fin 3) :
    projectionQuadraticThreeMul 0 a = 0 := by
  decide +revert

private theorem projectionQuadraticFold_zero (xs : List Nat)
    (valuation : Nat → Fin 3) :
    xs.foldl
        (fun current x =>
          projectionQuadraticThreeMul current (valuation x)) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, projectionQuadraticMul_zero_left]
      exact ih

private theorem projectionQuadraticTriple_zero (a b c : Fin 3) :
    projectionQuadraticThreeMul
      (projectionQuadraticThreeMul a b) c = 0 := by
  decide +revert

theorem projectionQuadraticEval_long
    (valuation : Nat → Fin 3) (x y z : Nat) (zs : List Nat) :
    projectionQuadraticThree.semigroup.eval valuation
      (wordOfCons x (y :: z :: zs)) = (0 : Fin 3) := by
  change
    zs.foldl
      (fun current t =>
        projectionQuadraticThreeMul current (valuation t))
      (projectionQuadraticThreeMul
        (projectionQuadraticThreeMul (valuation x) (valuation y))
        (valuation z)) = 0
  rw [projectionQuadraticTriple_zero]
  exact projectionQuadraticFold_zero zs valuation

private def projectionSeparator (x : Nat) : Nat → Fin 3 :=
  fun y => if y = x then 2 else 0

private def quadraticSeparator (x : Nat) : Nat → Fin 3 :=
  fun y => if y = x then 0 else 2

private theorem quadraticSeparator_eval (x a b : Nat) :
    projectionQuadraticThree.semigroup.eval (quadraticSeparator x)
        (wordOfCons a [b]) =
      if a = x ∨ b = x then (0 : Fin 3) else (1 : Fin 3) := by
  change
    projectionQuadraticThreeMul
      (quadraticSeparator x a) (quadraticSeparator x b) =
      if a = x ∨ b = x then 0 else 1
  by_cases ha : a = x <;> by_cases hb : b = x <;>
    simp [projectionQuadraticThreeMul, quadraticSeparator, ha, hb]

private theorem valid_projection_eq {x y : Nat}
    (valid :
      (Identity.mk (Word.singleton x) (Word.singleton y)).SatisfiedBy
        projectionQuadraticThree.semigroup) :
    x = y := by
  have evaluated := valid (projectionSeparator x)
  change projectionSeparator x x = projectionSeparator x y at evaluated
  by_cases hxy : x = y
  · exact hxy
  · exfalso
    simp [projectionSeparator] at evaluated
    exact hxy evaluated.symm

private theorem valid_quadratic_support_iff {a b c d z : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        projectionQuadraticThree.semigroup) :
    (a = z ∨ b = z) ↔ (c = z ∨ d = z) := by
  have evaluated := valid (quadraticSeparator z)
  rw [quadraticSeparator_eval, quadraticSeparator_eval] at evaluated
  constructor
  · intro hab
    by_cases hcd : c = z ∨ d = z
    · exact hcd
    · exfalso
      simp [hab, hcd] at evaluated
  · intro hcd
    by_cases hab : a = z ∨ b = z
    · exact hab
    · exfalso
      simp [hab, hcd] at evaluated

private theorem valid_quadratic_perm {a b c d : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        projectionQuadraticThree.semigroup) :
    [a, b].Perm [c, d] := by
  have support (z : Nat) :
      (a = z ∨ b = z) ↔ (c = z ∨ d = z) :=
    valid_quadratic_support_iff valid
  have hc : c = a ∨ c = b := by
    have := (support c).mpr (Or.inl rfl)
    exact this.imp Eq.symm Eq.symm
  have hd : d = a ∨ d = b := by
    have := (support d).mpr (Or.inr rfl)
    exact this.imp Eq.symm Eq.symm
  rcases hc with hca | hcb
  · rcases hd with hda | hdb
    · subst c
      subst d
      by_cases hab : a = b
      · subst b
        exact List.Perm.refl _
      · have missing := (support b).mp (Or.inr rfl)
        have ab : a = b := missing.elim id id
        exact False.elim (hab ab)
    · subst c
      subst d
      exact List.Perm.refl _
  · rcases hd with hda | hdb
    · subst c
      subst d
      exact List.Perm.swap _ _ []
    · subst c
      subst d
      by_cases hab : a = b
      · subst b
        exact List.Perm.refl _
      · have missing := (support a).mp (Or.inl rfl)
        have ba : b = a := missing.elim id id
        exact False.elim (hab ba.symm)

private theorem allTwo_long (x y z : Nat) (zs : List Nat) :
    projectionQuadraticThree.semigroup.eval (fun _ => (2 : Fin 3))
      (wordOfCons x (y :: z :: zs)) = (0 : Fin 3) :=
  projectionQuadraticEval_long _ _ _ _ _

/-- Unrestricted completeness over `Nat` variables. The table separates the
projection, quadratic-multiset, and common-long-product normal forms. -/
theorem projectionQuadraticThreeBasis_complete :
    BasisFor projectionQuadraticThree.semigroup
      projectionQuadraticThreeBasis := by
  refine ⟨projectionQuadraticThreeBasis_models, ?_⟩
  intro e valid
  have lhsNormal := projectionQuadraticDerivesNormal e.lhs
  have rhsNormal := projectionQuadraticDerivesNormal e.rhs
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
                        apply valid_projection_eq
                        exact valid
                      subst rx
                      exact Derives.refl _
                  | cons ry rtail =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (2 : Fin 3))
                          change (2 : Fin 3) =
                            projectionQuadraticThreeMul 2 2 at evaluated
                          simp [projectionQuadraticThreeMul] at evaluated
                      | cons rz rzs =>
                          have evaluated := valid (fun _ => (2 : Fin 3))
                          change (2 : Fin 3) =
                            projectionQuadraticThree.semigroup.eval
                              (fun _ => (2 : Fin 3))
                              (wordOfCons rx (ry :: rz :: rzs)) at evaluated
                          rw [allTwo_long] at evaluated
                          contradiction
              | cons ly ltail =>
                  cases ltail with
                  | nil =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (2 : Fin 3))
                          change projectionQuadraticThreeMul 2 2 =
                            (2 : Fin 3) at evaluated
                          simp [projectionQuadraticThreeMul] at evaluated
                      | cons ry rtail =>
                          cases rtail with
                          | nil =>
                              have pairPerm : [lx, ly].Perm [rx, ry] := by
                                apply valid_quadratic_perm
                                exact valid
                              exact projectionQuadraticDerivesPermutation
                                (wordOfCons lx [ly])
                                (wordOfCons rx [ry]) pairPerm
                          | cons rz rzs =>
                              have evaluated := valid (fun _ => (2 : Fin 3))
                              change projectionQuadraticThreeMul 2 2 =
                                projectionQuadraticThree.semigroup.eval
                                  (fun _ => (2 : Fin 3))
                                  (wordOfCons rx (ry :: rz :: rzs)) at evaluated
                              rw [allTwo_long] at evaluated
                              simp [projectionQuadraticThreeMul] at evaluated
                  | cons lz lzs =>
                      cases rtail with
                      | nil =>
                          have evaluated := valid (fun _ => (2 : Fin 3))
                          change
                            projectionQuadraticThree.semigroup.eval
                                (fun _ => (2 : Fin 3))
                                (wordOfCons lx (ly :: lz :: lzs)) =
                              (2 : Fin 3) at evaluated
                          rw [allTwo_long] at evaluated
                          contradiction
                      | cons ry rtail =>
                          cases rtail with
                          | nil =>
                              have evaluated := valid (fun _ => (2 : Fin 3))
                              change
                                projectionQuadraticThree.semigroup.eval
                                    (fun _ => (2 : Fin 3))
                                    (wordOfCons lx (ly :: lz :: lzs)) =
                                  projectionQuadraticThreeMul 2 2 at evaluated
                              rw [allTwo_long] at evaluated
                              simp [projectionQuadraticThreeMul] at evaluated
                          | cons rz rzs =>
                              change
                                Derives projectionQuadraticThreeBasis
                                  (wordOfCons lx (ly :: lz :: lzs))
                                  (wordOfCons rx (ry :: rz :: rzs))
                              change
                                Derives projectionQuadraticThreeBasis
                                  (wordOfCons lx (ly :: lz :: lzs))
                                  projectionQuadraticLongNormal at lhsNormal
                              change
                                Derives projectionQuadraticThreeBasis
                                  (wordOfCons rx (ry :: rz :: rzs))
                                  projectionQuadraticLongNormal at rhsNormal
                              exact Derives.trans lhsNormal
                                (Derives.symm rhsNormal)

theorem projectionQuadraticThree_selfDual :
    projectionQuadraticThree.semigroup.opposite =
      projectionQuadraticThree.semigroup := by
  unfold projectionQuadraticThree FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  exact projectionQuadraticMul_commutative b a

theorem projectionQuadraticThreeOppositeBasis_complete :
    BasisFor projectionQuadraticThree.semigroup.opposite
      projectionQuadraticThreeBasis := by
  rw [projectionQuadraticThree_selfDual]
  exact projectionQuadraticThreeBasis_complete

end SemigroupBasis.Examples
