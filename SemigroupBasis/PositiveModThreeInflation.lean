import SemigroupBasis.EdmundsInflation
import SemigroupBasis.Examples.CommutativePositiveModThreeFour

namespace SemigroupBasis.PositiveModThreeInflation

open SemigroupBasis
open SemigroupBasis.Examples

def xy : Word Nat := ⟨0, [1]⟩
def xxxxy : Word Nat := ⟨0, [0, 0, 0, 1]⟩
def xyxyxyxy : Word Nat := ⟨0, [1, 0, 1, 0, 1, 0, 1]⟩
def xyyyy : Word Nat := ⟨0, [1, 1, 1, 1]⟩
def yx : Word Nat := ⟨1, [0]⟩

def rightContextLaw : Identity Nat := ⟨xy, xxxxy⟩
def productPowerLaw : Identity Nat := ⟨xy, xyxyxyxy⟩
def leftContextLaw : Identity Nat := ⟨xy, xyyyy⟩
def commutativityLaw : Identity Nat := ⟨xy, yx⟩

/--
The product-sided replacement for the commutative positive-mod-three basis
`x = xxxx`, `xy = yx`.
-/
def basis : List (Identity Nat) :=
  [rightContextLaw, productPowerLaw, leftContextLaw, commutativityLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private def instantiatePowerWord (u : Word Nat) : Nat → Word Nat
  | 0 => u
  | n + 1 => Word.singleton (n + 1)

def fourth (w : Word Nat) : Word Nat :=
  (((w ++ w) ++ w) ++ w)

/-- Replace singleton words by their fourth power and leave products fixed. -/
def productize (w : Word Nat) : Word Nat :=
  match w.tail with
  | [] => fourth w
  | _ :: _ => w

private theorem append_isProduct (u v : Word Nat) :
    (u ++ v).tail ≠ [] := by
  simp

private theorem foldl_append_isProduct
    (σ : Nat → Word Nat) (xs : List Nat) (current : Word Nat)
    (currentProduct : current.tail ≠ []) :
    (xs.foldl (fun value x => value ++ σ x) current).tail ≠ [] := by
  induction xs generalizing current with
  | nil => exact currentProduct
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (current ++ σ x) (append_isProduct current (σ x))

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

private theorem derivesRightContextFourth (u v : Word Nat) :
    Derives basis (u ++ v) (fourth u ++ v) := by
  have base :
      Derives basis rightContextLaw.lhs rightContextLaw.rhs :=
    Derives.fromBasis (e := rightContextLaw) (List.Mem.head _)
  have instantiated :=
    Derives.subst base (instantiateTwoWords u v)
  simpa [basis, rightContextLaw, xy, xxxxy, fourth,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

private theorem derivesProductFourth (u v : Word Nat) :
    Derives basis (u ++ v) (fourth (u ++ v)) := by
  have base :
      Derives basis productPowerLaw.lhs productPowerLaw.rhs :=
    Derives.fromBasis (e := productPowerLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have instantiated :=
    Derives.subst base (instantiateTwoWords u v)
  simpa [basis, productPowerLaw, xy, xyxyxyxy, fourth,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

private theorem derivesLeftContextFourth (u v : Word Nat) :
    Derives basis (u ++ v) (u ++ fourth v) := by
  have base :
      Derives basis leftContextLaw.lhs leftContextLaw.rhs :=
    Derives.fromBasis (e := leftContextLaw) <|
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have instantiated :=
    Derives.subst base (instantiateTwoWords u v)
  simpa [basis, leftContextLaw, xy, xyyyy, fourth,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

private theorem derivesWholeFourth
    (w : Word Nat) (wordProduct : w.tail ≠ []) :
    Derives basis w (fourth w) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil => contradiction
      | cons next rest =>
          simpa [Word.singleton, Word.append] using
            derivesProductFourth (Word.singleton head) ⟨next, rest⟩

private theorem derivesAppendProductize (u v : Word Nat) :
    Derives basis (u ++ v) (productize u ++ v) := by
  cases u with
  | mk head tail =>
      cases tail with
      | nil =>
          simpa [productize] using
            derivesRightContextFourth (Word.singleton head) v
      | cons next rest =>
          exact Derives.refl _

private theorem derivesPrependProductize (u v : Word Nat) :
    Derives basis (u ++ v) (u ++ productize v) := by
  cases v with
  | mk head tail =>
      cases tail with
      | nil =>
          simpa [productize] using
            derivesLeftContextFourth u (Word.singleton head)
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
          · simpa [productize, fourth, Word.bind, Word.append,
              substitutedProduct] using
                (Derives.refl (fourth (σ head)) :
                  Derives basis (fourth (σ head)) (fourth (σ head)))
          · have contraction :=
              Derives.symm (derivesWholeFourth (σ head) substitutedProduct)
            change
              Derives basis (fourth (σ head)) (productize (σ head))
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

private theorem sourcePowerDerivation :
    Derives commutativePositiveModThreeBasis
      positiveModThreePowerLaw.lhs positiveModThreePowerLaw.rhs :=
  Derives.fromBasis (e := positiveModThreePowerLaw) <|
    List.Mem.head _

private theorem sourceModelsTarget
    {A : Type u} {source : Semigroup A}
    (sourceBasis :
      BasisFor source commutativePositiveModThreeBasis) :
    Models source basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · have derivation :=
      Derives.appendRight sourcePowerDerivation (Word.singleton 1)
    intro valuation
    simpa [rightContextLaw, xy, xxxxy, positiveModThreePowerLaw,
      positiveModThreeX, positiveModThreeXXXX, Word.append,
      Word.singleton, Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · have derivation :=
      Derives.subst sourcePowerDerivation
        (instantiatePowerWord xy)
    intro valuation
    simpa [productPowerLaw, xy, xyxyxyxy, positiveModThreePowerLaw,
      positiveModThreeX, positiveModThreeXXXX, instantiatePowerWord,
      Word.bind, Word.append, Word.singleton, Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · have renamed :=
      Derives.subst sourcePowerDerivation
        (instantiatePowerWord (Word.singleton 1))
    have derivation :=
      Derives.prepend (Word.singleton 0) renamed
    intro valuation
    simpa [leftContextLaw, xy, xyyyy, positiveModThreePowerLaw,
      positiveModThreeX, positiveModThreeXXXX, instantiatePowerWord,
      Word.bind, Word.append, Word.singleton, Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · intro valuation
    simpa [commutativityLaw, xy, yx, positiveModThreeCommutativityLaw,
      positiveModThreeXY, positiveModThreeYX] using
        sourceBasis.1 positiveModThreeCommutativityLaw
          (List.Mem.tail _ (List.Mem.head _)) valuation

/--
Every source derivation remains derivable after singleton words are replaced
by their fourth powers.
-/
theorem derivesProductized
    {u v : Word Nat}
    (derivation :
      Derives commutativePositiveModThreeBasis u v) :
    Derives basis (productize u) (productize v) := by
  induction derivation with
  | fromBasis member =>
      simp only [commutativePositiveModThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact Derives.refl _
      · exact Derives.fromBasis <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ (List.Mem.head _)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm ih
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans ih₁ ih₂
  | prepend p derivation ih =>
      exact Derives.trans
        (by
          simpa [productize_of_isProduct _ (append_isProduct p _)] using
            derivesPrependProductize p _)
        (Derives.trans
          (Derives.prepend p ih)
          (by
            simpa [productize_of_isProduct _ (append_isProduct p _)] using
              Derives.symm (derivesPrependProductize p _)))
  | appendRight derivation q ih =>
      exact Derives.trans
        (by
          simpa [productize_of_isProduct _ (append_isProduct _ q)] using
            derivesAppendProductize _ q)
        (Derives.trans
          (Derives.appendRight ih q)
          (by
            simpa [productize_of_isProduct _ (append_isProduct _ q)] using
              Derives.symm (derivesAppendProductize _ q)))
  | subst derivation σ ih =>
      exact Derives.trans
        (Derives.symm (derivesBindProductize _ σ)) <|
        Derives.trans (Derives.subst ih σ)
          (derivesBindProductize _ σ)

theorem derivesProductIdentity
    {u v : Word Nat}
    (lhsProduct : u.tail ≠ []) (rhsProduct : v.tail ≠ [])
    (derivation :
      Derives commutativePositiveModThreeBasis u v) :
    Derives basis u v := by
  simpa [productize_of_isProduct u lhsProduct,
    productize_of_isProduct v rhsProduct] using
      derivesProductized derivation

end SemigroupBasis.PositiveModThreeInflation

namespace SemigroupBasis.Inflation

/--
The product-sided positive-mod-three replacement is a complete basis for every
proper inflation of a semigroup with basis `x = xxxx`, `xy = yx`.
-/
theorem inheritCommutativePositiveModThreeBasis
    {A : Type u} {B : Type v}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source target)
    (proper : inflation.Proper)
    (sourceBasis :
      BasisFor source
        SemigroupBasis.Examples.commutativePositiveModThreeBasis) :
    BasisFor target SemigroupBasis.PositiveModThreeInflation.basis := by
  have sourceModels :
      Models source SemigroupBasis.PositiveModThreeInflation.basis :=
    SemigroupBasis.PositiveModThreeInflation.sourceModelsTarget sourceBasis
  have targetModels :
      Models target SemigroupBasis.PositiveModThreeInflation.basis := by
    intro identity member
    simp only [SemigroupBasis.PositiveModThreeInflation.basis,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact inflation.pushforwardProductIdentity _ (by decide) (by decide)
        (sourceModels _ (List.Mem.head _))
    · exact inflation.pushforwardProductIdentity _ (by decide) (by decide)
        (sourceModels _ (List.Mem.tail _ (List.Mem.head _)))
    · exact inflation.pushforwardProductIdentity _ (by decide) (by decide)
        (sourceModels _ (List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)))
    · exact inflation.pushforwardProductIdentity _ (by decide) (by decide)
        (sourceModels _ (List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ (List.Mem.head _)))
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
                          fun x => if x = lhsHead then outside else inside
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
                        SemigroupBasis.PositiveModThreeInflation.derivesProductIdentity
                          (by simp) (by simp)
                          (sourceBasis.2 _ sourceValid)

end SemigroupBasis.Inflation
