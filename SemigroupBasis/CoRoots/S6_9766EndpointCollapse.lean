import SemigroupBasis.FiniteCertificate

/-!
# The endpoint-collapse basis for S6_9766

Every word of length at least three collapses to `xxy`, where `x` and `y`
are its first and final variables.  The exact six-element table separates
the singleton, pair, and long-word strata and recovers both ordered endpoint
coordinates.
-/

namespace SemigroupBasis.CoRoots.S6_9766EndpointCollapse

open SemigroupBasis

/-- The zero-based multiplication table of Smallsemi class `S6_9766`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 2 ∧ right = 2 then 1
  else if left = 3 ∨ left = 5 then
    if right = 4 ∨ right = 5 then 5 else 3
  else if right = 4 ∨ right = 5 then 4 else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 =>
      (table.semigroup.mul left right).val + 1

theorem tableOneBased_certificate :
    tableOneBased =
      [[1, 1, 1, 1, 5, 5],
       [1, 1, 1, 1, 5, 5],
       [1, 1, 2, 1, 5, 5],
       [4, 4, 4, 4, 6, 6],
       [1, 1, 1, 1, 5, 5],
       [4, 4, 4, 4, 6, 6]] := by
  decide

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def yyx : Word Nat := w 1 [1, 0]
def yzx : Word Nat := w 1 [2, 0]

def sandwichLaw : Identity Nat := ⟨xxx, xyx⟩
def endpointLaw : Identity Nat := ⟨yxx, yyx⟩
def middleLaw : Identity Nat := ⟨yxx, yzx⟩

/-- The exact displayed basis `xxx = xyx`, `yxx = yyx`, `yxx = yzx`. -/
def basis : List (Identity Nat) :=
  [sandwichLaw, endpointLaw, middleLaw]

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

set_option maxRecDepth 100000 in
theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

private def instantiateThreeWords
    (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisEndpoint : Derives basis yxx yyx :=
  Derives.fromBasis (e := endpointLaw) <| by
    simp [basis, endpointLaw]

private theorem basisMiddle : Derives basis yxx yzx :=
  Derives.fromBasis (e := middleLaw) <| by
    simp [basis, middleLaw]

/-- Substitute arbitrary nonempty blocks in `yxx = yzx`. -/
theorem derivesMiddleExpansion (u v middle : Word Nat) :
    Derives basis ((u ++ v) ++ v) ((u ++ middle) ++ v) := by
  have substituted :=
    Derives.subst basisMiddle (instantiateThreeWords v u middle)
  simpa [middleLaw, yxx, yzx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Substitute arbitrary nonempty blocks in `yxx = yyx`. -/
theorem derivesEndpointTransfer (u v : Word Nat) :
    Derives basis ((u ++ v) ++ v) ((u ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisEndpoint (instantiateThreeWords v u v)
  simpa [endpointLaw, yxx, yyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Replace an arbitrary nonempty middle block by a second copy of the
initial block while preserving the final block. -/
theorem derivesCollapseMiddle (initial middle final : Word Nat) :
    Derives basis
      ((initial ++ middle) ++ final)
      ((initial ++ initial) ++ final) :=
  Derives.trans
    (Derives.symm (derivesMiddleExpansion initial final middle))
    (derivesEndpointTransfer initial final)

private theorem dropLast_append_final (x : Nat) (xs : List Nat) :
    (x :: xs).dropLast ++ [xs.getLastD x] = x :: xs := by
  have reconstruction :=
    List.dropLast_concat_getLast
      (l := x :: xs) (by simp)
  rw [List.getLast_eq_getLastD] at reconstruction
  simpa only [List.getLastD_cons] using reconstruction

/-- Words of length one and two stay unchanged.  A longer word is represented
by its first variable twice followed by its final variable. -/
def normal : Word Nat → Word Nat
  | ⟨head, []⟩ => ⟨head, []⟩
  | ⟨head, [next]⟩ => ⟨head, [next]⟩
  | ⟨head, middle :: next :: rest⟩ =>
      ⟨head, [head, rest.getLastD next]⟩

/-- Unrestricted endpoint-collapse normalization. -/
theorem derivesNormal (word : Word Nat) :
    Derives basis word (normal word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          exact Derives.refl _
      | cons middle remaining =>
          cases remaining with
          | nil =>
              exact Derives.refl _
          | cons next rest =>
              let interior : Word Nat :=
                ⟨middle, (next :: rest).dropLast⟩
              let final := rest.getLastD next
              have collapse :=
                derivesCollapseMiddle
                  (Word.singleton head) interior (Word.singleton final)
              have reconstruction := dropLast_append_final next rest
              have sourceShape :
                  ((Word.singleton head ++ interior) ++ Word.singleton final) =
                    ⟨head,
                      middle ::
                        ((next :: rest).dropLast ++ [rest.getLastD next])⟩ := by
                rfl
              have targetShape :
                  ((Word.singleton head ++ Word.singleton head) ++
                      Word.singleton final) =
                    ⟨head, [head, rest.getLastD next]⟩ := by
                rfl
              rw [sourceShape, targetShape] at collapse
              rw [reconstruction] at collapse
              simpa only [normal] using collapse

private theorem singleton_pair_probe :
    (2 : Fin 6) ≠ mul 2 2 := by
  decide

private theorem singleton_long_probe :
    (2 : Fin 6) ≠ mul (mul 2 2) 2 := by
  decide

private theorem pair_long_probe :
    mul 2 2 ≠ mul (mul 2 2) 2 := by
  decide

private theorem singleton_coordinate_eq_of_valid
    {left right : Nat}
    (valid :
      (⟨Word.singleton left, Word.singleton right⟩ : Identity Nat).SatisfiedBy
        table.semigroup) :
    left = right := by
  apply Classical.byContradiction
  intro different
  let valuation : Nat → Fin 6 :=
    fun letter => if letter = left then 2 else 0
  have evaluated := valid valuation
  change valuation left = valuation right at evaluated
  simp [valuation, different, Ne.symm different] at evaluated

private theorem pair_coordinates_eq_of_valid
    {leftFirst leftFinal rightFirst rightFinal : Nat}
    (valid :
      (⟨w leftFirst [leftFinal], w rightFirst [rightFinal]⟩ :
        Identity Nat).SatisfiedBy table.semigroup) :
    leftFirst = rightFirst ∧ leftFinal = rightFinal := by
  have first : leftFirst = rightFirst := by
    apply Classical.byContradiction
    intro different
    let valuation : Nat → Fin 6 :=
      fun letter => if letter = leftFirst then 3 else 0
    have evaluated := valid valuation
    change
      mul (valuation leftFirst) (valuation leftFinal) =
        mul (valuation rightFirst) (valuation rightFinal) at evaluated
    by_cases leftLast : leftFinal = leftFirst <;>
      by_cases rightLast : rightFinal = leftFirst <;>
        simp [valuation, different, Ne.symm different, leftLast,
          rightLast, mul] at evaluated
  subst rightFirst
  have final : leftFinal = rightFinal := by
    apply Classical.byContradiction
    intro different
    let valuation : Nat → Fin 6 :=
      fun letter => if letter = leftFinal then 4 else 0
    have evaluated := valid valuation
    change
      mul (valuation leftFirst) (valuation leftFinal) =
        mul (valuation leftFirst) (valuation rightFinal) at evaluated
    by_cases firstIsFinal : leftFirst = leftFinal <;>
      simp [valuation, different, Ne.symm different, firstIsFinal, mul]
        at evaluated
  exact ⟨rfl, final⟩

private theorem long_coordinates_eq_of_valid
    {leftFirst leftFinal rightFirst rightFinal : Nat}
    (valid :
      (⟨w leftFirst [leftFirst, leftFinal],
          w rightFirst [rightFirst, rightFinal]⟩ :
        Identity Nat).SatisfiedBy table.semigroup) :
    leftFirst = rightFirst ∧ leftFinal = rightFinal := by
  have first : leftFirst = rightFirst := by
    apply Classical.byContradiction
    intro different
    let valuation : Nat → Fin 6 :=
      fun letter => if letter = leftFirst then 3 else 0
    have evaluated := valid valuation
    change
      mul (mul (valuation leftFirst) (valuation leftFirst))
          (valuation leftFinal) =
        mul (mul (valuation rightFirst) (valuation rightFirst))
          (valuation rightFinal) at evaluated
    by_cases leftLast : leftFinal = leftFirst <;>
      by_cases rightLast : rightFinal = leftFirst <;>
        simp [valuation, different, Ne.symm different, leftLast,
          rightLast, mul] at evaluated
  subst rightFirst
  have final : leftFinal = rightFinal := by
    apply Classical.byContradiction
    intro different
    let valuation : Nat → Fin 6 :=
      fun letter => if letter = leftFinal then 4 else 0
    have evaluated := valid valuation
    change
      mul (mul (valuation leftFirst) (valuation leftFirst))
          (valuation leftFinal) =
        mul (mul (valuation leftFirst) (valuation leftFirst))
          (valuation rightFinal) at evaluated
    by_cases firstIsFinal : leftFirst = leftFinal <;>
      simp [valuation, different, Ne.symm different, firstIsFinal, mul]
        at evaluated
  exact ⟨rfl, final⟩

private theorem normal_eq_of_valid
    (left right : Word Nat)
    (valid :
      (⟨normal left, normal right⟩ : Identity Nat).SatisfiedBy
        table.semigroup) :
    normal left = normal right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          cases leftTail with
          | nil =>
              cases rightTail with
              | nil =>
                  have same := singleton_coordinate_eq_of_valid <| by
                    simpa [normal, w] using valid
                  subst rightHead
                  rfl
              | cons rightNext rightRest =>
                  cases rightRest with
                  | nil =>
                      have evaluated := valid (fun _ => (2 : Fin 6))
                      change (2 : Fin 6) = mul 2 2 at evaluated
                      exact False.elim (singleton_pair_probe evaluated)
                  | cons rightThird rightMore =>
                      have evaluated := valid (fun _ => (2 : Fin 6))
                      change
                        (2 : Fin 6) = mul (mul 2 2) 2 at evaluated
                      exact False.elim (singleton_long_probe evaluated)
          | cons leftNext leftRest =>
              cases leftRest with
              | nil =>
                  cases rightTail with
                  | nil =>
                      have evaluated := valid (fun _ => (2 : Fin 6))
                      change mul 2 2 = (2 : Fin 6) at evaluated
                      exact False.elim
                        (singleton_pair_probe evaluated.symm)
                  | cons rightNext rightRest =>
                      cases rightRest with
                      | nil =>
                          have coordinates :=
                            pair_coordinates_eq_of_valid <| by
                              simpa [normal, w] using valid
                          rcases coordinates with ⟨rfl, rfl⟩
                          rfl
                      | cons rightThird rightMore =>
                          have evaluated := valid (fun _ => (2 : Fin 6))
                          change
                            mul 2 2 = mul (mul 2 2) 2 at evaluated
                          exact False.elim (pair_long_probe evaluated)
              | cons leftThird leftMore =>
                  cases rightTail with
                  | nil =>
                      have evaluated := valid (fun _ => (2 : Fin 6))
                      change mul (mul 2 2) 2 = (2 : Fin 6) at evaluated
                      exact False.elim
                        (singleton_long_probe evaluated.symm)
                  | cons rightNext rightRest =>
                      cases rightRest with
                      | nil =>
                          have evaluated := valid (fun _ => (2 : Fin 6))
                          change
                            mul (mul 2 2) 2 = mul 2 2 at evaluated
                          exact False.elim (pair_long_probe evaluated.symm)
                      | cons rightThird rightMore =>
                          have coordinates :=
                            long_coordinates_eq_of_valid <| by
                              simpa [normal, w] using valid
                          rcases coordinates with ⟨rfl, final⟩
                          simpa only [normal, w, List.getLastD_eq_getLast?] using
                            congrArg
                              (fun endpoint => w leftHead [leftHead, endpoint])
                              final

/-- Every identity valid in the exact `S6_9766` table follows from the three
displayed laws. -/
theorem basis_complete : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  have leftNormal := derivesNormal identity.lhs
  have rightNormal := derivesNormal identity.rhs
  have normalizedValid :
      (⟨normal identity.lhs, normal identity.rhs⟩ : Identity Nat).SatisfiedBy
        table.semigroup := by
    intro valuation
    exact (leftNormal.sound models valuation).symm.trans <|
      (valid valuation).trans (rightNormal.sound models valuation)
  have sameNormal :=
    normal_eq_of_valid identity.lhs identity.rhs normalizedValid
  exact Derives.trans leftNormal <| by
    rw [sameNormal]
    exact Derives.symm rightNormal

end SemigroupBasis.CoRoots.S6_9766EndpointCollapse
