import SemigroupBasis.EdmundsInflation
import SemigroupBasis.Examples.RectangularBandFourSyntax

namespace SemigroupBasis.S5_917Inflation

open SemigroupBasis
open SemigroupBasis.Examples

def xy : Word Nat := ⟨0, [1]⟩
def xxy : Word Nat := ⟨0, [0, 1]⟩
def xyxy : Word Nat := ⟨0, [1, 0, 1]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩
def xyzxy : Word Nat := ⟨0, [1, 2, 0, 1]⟩
def xyzy : Word Nat := ⟨0, [1, 2, 1]⟩
def xzxy : Word Nat := ⟨0, [2, 0, 1]⟩

def rightContextLaw : Identity Nat := ⟨xy, xxy⟩
def productPowerLaw : Identity Nat := ⟨xy, xyxy⟩
def leftContextLaw : Identity Nat := ⟨xy, xyy⟩
def wholeSandwichLaw : Identity Nat := ⟨xy, xyzxy⟩
def rightSandwichLaw : Identity Nat := ⟨xy, xyzy⟩
def leftSandwichLaw : Identity Nat := ⟨xy, xzxy⟩

/--
The exact product-sided replacement of the rectangular-band basis
`x = xx`, `x = xyx`.
-/
def basis : List (Identity Nat) :=
  [rightContextLaw, productPowerLaw, leftContextLaw,
    wholeSandwichLaw, rightSandwichLaw, leftSandwichLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

def square (w : Word Nat) : Word Nat :=
  w ++ w

/-- Replace singleton words by their squares and leave products fixed. -/
def productize (w : Word Nat) : Word Nat :=
  match w.tail with
  | [] => square w
  | _ :: _ => w

private theorem append_isProduct (u v : Word Nat) :
    (u ++ v).tail ≠ [] := by
  simp

private theorem foldl_append_isProduct
    (σ : Nat → Word Nat) (xs : List Nat) (current : Word Nat)
    (currentProduct : current.tail ≠ []) :
    (xs.foldl (fun value symbol => value ++ σ symbol) current).tail ≠
      [] := by
  induction xs generalizing current with
  | nil => exact currentProduct
  | cons symbol xs ih =>
      simp only [List.foldl_cons]
      exact ih (current ++ σ symbol)
        (append_isProduct current (σ symbol))

private theorem bind_isProduct
    (w : Word Nat) (wordProduct : w.tail ≠ [])
    (σ : Nat → Word Nat) :
    (w.bind σ).tail ≠ [] := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil => contradiction
      | cons next rest =>
          unfold Word.bind
          simp only [List.foldl_cons]
          exact foldl_append_isProduct σ rest (σ head ++ σ next)
            (append_isProduct (σ head) (σ next))

@[simp]
theorem productize_of_isProduct
    (w : Word Nat) (wordProduct : w.tail ≠ []) :
    productize w = w := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil => contradiction
      | cons next rest => rfl

private theorem derivesRightContextSquare (u v : Word Nat) :
    Derives basis (u ++ v) (square u ++ v) := by
  have base :
      Derives basis rightContextLaw.lhs rightContextLaw.rhs :=
    Derives.fromBasis (e := rightContextLaw) (List.Mem.head _)
  have instantiated :=
    Derives.subst base (instantiateTwoWords u v)
  simpa [basis, rightContextLaw, xy, xxy, square,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

private theorem derivesProductSquare (u v : Word Nat) :
    Derives basis (u ++ v) (square (u ++ v)) := by
  have base :
      Derives basis productPowerLaw.lhs productPowerLaw.rhs :=
    Derives.fromBasis (e := productPowerLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have instantiated :=
    Derives.subst base (instantiateTwoWords u v)
  simpa [basis, productPowerLaw, xy, xyxy, square,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

private theorem derivesLeftContextSquare (u v : Word Nat) :
    Derives basis (u ++ v) (u ++ square v) := by
  have base :
      Derives basis leftContextLaw.lhs leftContextLaw.rhs :=
    Derives.fromBasis (e := leftContextLaw) <|
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have instantiated :=
    Derives.subst base (instantiateTwoWords u v)
  simpa [basis, leftContextLaw, xy, xyy, square,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

private theorem derivesWholeSquare
    (w : Word Nat) (wordProduct : w.tail ≠ []) :
    Derives basis w (square w) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil => contradiction
      | cons next rest =>
          simpa [Word.singleton, Word.append] using
            derivesProductSquare (Word.singleton head) ⟨next, rest⟩

private theorem derivesAppendProductize (u v : Word Nat) :
    Derives basis (u ++ v) (productize u ++ v) := by
  cases u with
  | mk head tail =>
      cases tail with
      | nil =>
          simpa [productize] using
            derivesRightContextSquare (Word.singleton head) v
      | cons next rest =>
          exact Derives.refl _

private theorem derivesPrependProductize (u v : Word Nat) :
    Derives basis (u ++ v) (u ++ productize v) := by
  cases v with
  | mk head tail =>
      cases tail with
      | nil =>
          simpa [productize] using
            derivesLeftContextSquare u (Word.singleton head)
      | cons next rest =>
          exact Derives.refl _

private theorem derivesBindProductize
    (w : Word Nat) (σ : Nat → Word Nat) :
    Derives basis ((productize w).bind σ) (productize (w.bind σ)) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          by_cases substitutedProduct : (σ head).tail = []
          · simpa [productize, square, Word.bind, Word.append,
              substitutedProduct] using
                (Derives.refl (square (σ head)) :
                  Derives basis (square (σ head)) (square (σ head)))
          · have contraction :=
              Derives.symm (derivesWholeSquare (σ head) substitutedProduct)
            change
              Derives basis (square (σ head)) (productize (σ head))
            rw [productize_of_isProduct (σ head) substitutedProduct]
            exact contraction
      | cons next rest =>
          have boundProduct :
              ((Word.mk head (next :: rest)).bind σ).tail ≠ [] :=
            bind_isProduct ⟨head, next :: rest⟩ (by simp) σ
          change
            Derives basis
              ((Word.mk head (next :: rest)).bind σ)
              (productize ((Word.mk head (next :: rest)).bind σ))
          rw [productize_of_isProduct _ boundProduct]
          exact Derives.refl _

private theorem derivesProductizedSandwichLaw :
    Derives basis
      (productize rectangularBandSandwichLaw.lhs)
      (productize rectangularBandSandwichLaw.rhs) := by
  have sandwichBase :
      Derives basis leftSandwichLaw.lhs leftSandwichLaw.rhs :=
    Derives.fromBasis (e := leftSandwichLaw) <|
      List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ (List.Mem.head _)
  have expanded :=
    Derives.subst sandwichBase <|
      instantiateThreeWords
        (Word.singleton 0) (Word.singleton 0) (Word.singleton 1)
  have contextBase :
      Derives basis leftContextLaw.lhs leftContextLaw.rhs :=
    Derives.fromBasis (e := leftContextLaw) <|
      List.Mem.tail _ <|
        List.Mem.tail _ (List.Mem.head _)
  have duplicated :=
    Derives.subst contextBase <|
      instantiateTwoWords xy (Word.singleton 0)
  have result :
      Derives basis
        (Word.mk 0 [0])
        (Word.mk 0 [1, 0]) :=
    Derives.trans
      (by
        simpa [leftSandwichLaw, xy, xzxy, instantiateThreeWords,
          Word.bind, Word.append, Word.singleton, Word.append_assoc]
          using expanded)
      (by
        simpa [leftContextLaw, xy, xyy, instantiateTwoWords,
          Word.bind, Word.append, Word.singleton, Word.append_assoc]
          using (Derives.symm duplicated))
  simpa [productize, square, rectangularBandSandwichLaw,
    rectangularBandX, rectangularBandXYX, Word.singleton,
    Word.append] using result

private theorem sourceModelsTarget
    {A : Type u} {source : Semigroup A}
    (sourceBasis : BasisFor source rectangularBandBasis) :
    Models source basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · have derivation :=
      Derives.appendRight
        (rectangularBandDerivesIdempotenceExpansion (Word.singleton 0))
        (Word.singleton 1)
    intro valuation
    simpa [rightContextLaw, xy, xxy, Word.append, Word.singleton,
      Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · have derivation :=
      rectangularBandDerivesIdempotenceExpansion xy
    intro valuation
    simpa [productPowerLaw, xy, xyxy, Word.append, Word.singleton,
      Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · have derivation :=
      Derives.prepend (Word.singleton 0) <|
        rectangularBandDerivesIdempotenceExpansion (Word.singleton 1)
    intro valuation
    simpa [leftContextLaw, xy, xyy, Word.append, Word.singleton,
      Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · have derivation :=
      rectangularBandDerivesSandwichExpansion xy (Word.singleton 2)
    intro valuation
    simpa [wholeSandwichLaw, xy, xyzxy, Word.append,
      Word.singleton, Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · have derivation :=
      Derives.prepend (Word.singleton 0) <|
        rectangularBandDerivesSandwichExpansion
          (Word.singleton 1) (Word.singleton 2)
    intro valuation
    simpa [rightSandwichLaw, xy, xyzy, Word.append,
      Word.singleton, Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · have derivation :=
      Derives.appendRight
        (rectangularBandDerivesSandwichExpansion
          (Word.singleton 0) (Word.singleton 2))
        (Word.singleton 1)
    intro valuation
    simpa [leftSandwichLaw, xy, xzxy, Word.append,
      Word.singleton, Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation

/--
Every derivation from the rectangular-band basis remains derivable after
singleton words are replaced by their squares.
-/
theorem derivesProductized
    {u v : Word Nat}
    (derivation : Derives rectangularBandBasis u v) :
    Derives basis (productize u) (productize v) := by
  induction derivation with
  | fromBasis member =>
      simp only [rectangularBandBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact Derives.refl _
      · exact derivesProductizedSandwichLaw
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm ih
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans ih₁ ih₂
  | prepend stem derivation ih =>
      exact Derives.trans
        (by
          simpa [productize_of_isProduct _
            (append_isProduct stem _)] using
              derivesPrependProductize stem _)
        (Derives.trans
          (Derives.prepend stem ih)
          (by
            simpa [productize_of_isProduct _
              (append_isProduct stem _)] using
                Derives.symm (derivesPrependProductize stem _)))
  | appendRight derivation suffix ih =>
      exact Derives.trans
        (by
          simpa [productize_of_isProduct _
            (append_isProduct _ suffix)] using
              derivesAppendProductize _ suffix)
        (Derives.trans
          (Derives.appendRight ih suffix)
          (by
            simpa [productize_of_isProduct _
              (append_isProduct _ suffix)] using
                Derives.symm (derivesAppendProductize _ suffix)))
  | subst derivation σ ih =>
      exact Derives.trans
        (Derives.symm (derivesBindProductize _ σ)) <|
        Derives.trans (Derives.subst ih σ)
          (derivesBindProductize _ σ)

theorem derivesProductIdentity
    {u v : Word Nat}
    (lhsProduct : u.tail ≠ []) (rhsProduct : v.tail ≠ [])
    (derivation : Derives rectangularBandBasis u v) :
    Derives basis u v := by
  simpa [productize_of_isProduct u lhsProduct,
    productize_of_isProduct v rhsProduct] using
      derivesProductized derivation

end SemigroupBasis.S5_917Inflation

namespace SemigroupBasis.Inflation

/--
The exact six-law `S5_917` presentation is a complete basis for every proper
inflation of a semigroup with the rectangular-band basis.
-/
theorem inheritS5_917Basis
    {A : Type u} {B : Type v}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source target)
    (proper : inflation.Proper)
    (sourceBasis :
      BasisFor source SemigroupBasis.Examples.rectangularBandBasis) :
    BasisFor target SemigroupBasis.S5_917Inflation.basis := by
  have sourceModels :
      Models source SemigroupBasis.S5_917Inflation.basis :=
    SemigroupBasis.S5_917Inflation.sourceModelsTarget sourceBasis
  have targetModels :
      Models target SemigroupBasis.S5_917Inflation.basis := by
    intro identity member
    simp only [SemigroupBasis.S5_917Inflation.basis,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact inflation.pushforwardProductIdentity _ (by decide) (by decide)
        (sourceModels _ (List.Mem.head _))
    · exact inflation.pushforwardProductIdentity _ (by decide) (by decide)
        (sourceModels _ (List.Mem.tail _ (List.Mem.head _)))
    · exact inflation.pushforwardProductIdentity _ (by decide) (by decide)
        (sourceModels _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ (List.Mem.head _))
    · exact inflation.pushforwardProductIdentity _ (by decide) (by decide)
        (sourceModels _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ (List.Mem.head _))
    · exact inflation.pushforwardProductIdentity _ (by decide) (by decide)
        (sourceModels _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ (List.Mem.head _))
    · exact inflation.pushforwardProductIdentity _ (by decide) (by decide)
        (sourceModels _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ (List.Mem.head _))
  refine ⟨targetModels, ?_⟩
  intro identity valid
  obtain ⟨outside, outsideImage⟩ := proper
  cases identity with
  | mk lhs rhs =>
      cases lhs with
      | mk lhsHead lhsTail =>
          cases lhsTail with
          | nil =>
              cases rhs with
              | mk rhsHead rhsTail =>
                  cases rhsTail with
                  | nil =>
                      have heads : lhsHead = rhsHead := by
                        apply Decidable.byContradiction
                        intro headsNe
                        let inside :=
                          inflation.embedding.toFun
                            (inflation.retract outside)
                        let valuation : Nat → B :=
                          fun symbol =>
                            if symbol = lhsHead then outside else inside
                        have evaluated := valid valuation
                        change valuation lhsHead = valuation rhsHead at evaluated
                        have rhsNe : rhsHead ≠ lhsHead := Ne.symm headsNe
                        simp [valuation, rhsNe, inside] at evaluated
                        exact outsideImage _ evaluated
                      subst rhsHead
                      exact Derives.refl _
                  | cons rhsNext rhsRest =>
                      let valuation : Nat → B := fun _ => outside
                      have evaluated := valid valuation
                      rw [inflation.eval_represented valuation
                        rhsHead rhsNext rhsRest] at evaluated
                      exact False.elim <|
                        outsideImage _ evaluated
          | cons lhsNext lhsRest =>
              cases rhs with
              | mk rhsHead rhsTail =>
                  cases rhsTail with
                  | nil =>
                      let valuation : Nat → B := fun _ => outside
                      have evaluated := valid valuation
                      rw [inflation.eval_represented valuation
                        lhsHead lhsNext lhsRest] at evaluated
                      exact False.elim <|
                        outsideImage _ evaluated.symm
                  | cons rhsNext rhsRest =>
                      have sourceValid :
                          (Identity.mk
                            (Word.mk lhsHead (lhsNext :: lhsRest))
                            (Word.mk rhsHead (rhsNext :: rhsRest))).SatisfiedBy
                              source :=
                        inflation.embedding.pullback_identity _ valid
                      exact
                        SemigroupBasis.S5_917Inflation.derivesProductIdentity
                          (by simp) (by simp)
                          (sourceBasis.2 _ sourceValid)

end SemigroupBasis.Inflation
