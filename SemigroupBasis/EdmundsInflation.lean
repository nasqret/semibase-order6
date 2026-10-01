import SemigroupBasis.CoRoots.S4_90
import SemigroupBasis.Inflation

namespace SemigroupBasis.EdmundsInflation

open SemigroupBasis
open SemigroupBasis.CoRoots.S4_90

def xy : Word Nat := ⟨0, [1]⟩
def xxxy : Word Nat := ⟨0, [0, 0, 1]⟩
def xyxyxy : Word Nat := ⟨0, [1, 0, 1, 0, 1]⟩
def xyyy : Word Nat := ⟨0, [1, 1, 1]⟩

def rightContextLaw : Identity Nat := ⟨xy, xxxy⟩
def productPowerLaw : Identity Nat := ⟨xy, xyxyxy⟩
def leftContextLaw : Identity Nat := ⟨xy, xyyy⟩

/--
Edmunds' product-sided replacement for the suffix-parity basis
`xyz = xzy`, `x = xxx`.
-/
def basis : List (Identity Nat) :=
  [rightContextLaw, productPowerLaw, leftContextLaw,
    suffixParityCommutationLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private def instantiatePowerWord (u : Word Nat) : Nat → Word Nat
  | 0 => u
  | n + 1 => Word.singleton (n + 1)

def triple (w : Word Nat) : Word Nat :=
  (w ++ w) ++ w

/-- Replace singleton words by their third power and leave products fixed. -/
def productize (w : Word Nat) : Word Nat :=
  match w.tail with
  | [] => triple w
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

private theorem derivesRightContextTriple (u v : Word Nat) :
    Derives basis (u ++ v) (triple u ++ v) := by
  have base :
      Derives basis rightContextLaw.lhs rightContextLaw.rhs :=
    Derives.fromBasis (e := rightContextLaw) (List.Mem.head _)
  have instantiated :=
    Derives.subst base (instantiateTwoWords u v)
  simpa [basis, rightContextLaw, xy, xxxy, triple,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

private theorem derivesProductTriple (u v : Word Nat) :
    Derives basis (u ++ v) (triple (u ++ v)) := by
  have base :
      Derives basis productPowerLaw.lhs productPowerLaw.rhs :=
    Derives.fromBasis (e := productPowerLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have instantiated :=
    Derives.subst base (instantiateTwoWords u v)
  simpa [basis, productPowerLaw, xy, xyxyxy, triple,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

private theorem derivesLeftContextTriple (u v : Word Nat) :
    Derives basis (u ++ v) (u ++ triple v) := by
  have base :
      Derives basis leftContextLaw.lhs leftContextLaw.rhs :=
    Derives.fromBasis (e := leftContextLaw) <|
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have instantiated :=
    Derives.subst base (instantiateTwoWords u v)
  simpa [basis, leftContextLaw, xy, xyyy, triple,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

private theorem derivesWholeTriple
    (w : Word Nat) (wordProduct : w.tail ≠ []) :
    Derives basis w (triple w) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil => contradiction
      | cons next rest =>
          simpa [Word.singleton, Word.append] using
            derivesProductTriple (Word.singleton head) ⟨next, rest⟩

private theorem derivesAppendProductize (u v : Word Nat) :
    Derives basis (u ++ v) (productize u ++ v) := by
  cases u with
  | mk head tail =>
      cases tail with
      | nil =>
          simpa [productize] using
            derivesRightContextTriple (Word.singleton head) v
      | cons next rest =>
          exact Derives.refl _

private theorem derivesPrependProductize (u v : Word Nat) :
    Derives basis (u ++ v) (u ++ productize v) := by
  cases v with
  | mk head tail =>
      cases tail with
      | nil =>
          simpa [productize] using
            derivesLeftContextTriple u (Word.singleton head)
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
          · simpa [productize, triple, Word.bind, Word.append,
              substitutedProduct] using
                (Derives.refl (triple (σ head)) :
                  Derives basis (triple (σ head)) (triple (σ head)))
          · have contraction :=
              Derives.symm (derivesWholeTriple (σ head) substitutedProduct)
            change
              Derives basis (triple (σ head)) (productize (σ head))
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
    Derives SemigroupBasis.CoRoots.S4_90.basis
      suffixParityPowerLaw.lhs suffixParityPowerLaw.rhs :=
  Derives.fromBasis (e := suffixParityPowerLaw) <|
    List.Mem.tail _ (List.Mem.head _)

private theorem sourceModelsTarget
    {A : Type u} {source : Semigroup A}
    (sourceBasis :
      BasisFor source SemigroupBasis.CoRoots.S4_90.basis) :
    Models source basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · have derivation :=
      Derives.appendRight sourcePowerDerivation (Word.singleton 1)
    intro valuation
    simpa [rightContextLaw, xy, xxxy, suffixParityPowerLaw,
      suffixParityX, suffixParityXXX, Word.append, Word.singleton,
      Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · have derivation :=
      Derives.subst sourcePowerDerivation
        (instantiatePowerWord xy)
    intro valuation
    simpa [productPowerLaw, xy, xyxyxy, suffixParityPowerLaw,
      suffixParityX, suffixParityXXX, instantiatePowerWord,
      Word.bind, Word.append, Word.singleton, Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · have renamed :=
      Derives.subst sourcePowerDerivation
        (instantiatePowerWord (Word.singleton 1))
    have derivation :=
      Derives.prepend (Word.singleton 0) renamed
    intro valuation
    simpa [leftContextLaw, xy, xyyy, suffixParityPowerLaw,
      suffixParityX, suffixParityXXX, instantiatePowerWord,
      Word.bind, Word.append, Word.singleton, Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · exact sourceBasis.1 suffixParityCommutationLaw (List.Mem.head _)

/--
Every source derivation remains derivable after singleton words are replaced
by their third powers.
-/
theorem derivesProductized
    {u v : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S4_90.basis u v) :
    Derives basis (productize u) (productize v) := by
  induction derivation with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S4_90.basis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact Derives.fromBasis <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ (List.Mem.head _)
      · exact Derives.refl _
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
      Derives SemigroupBasis.CoRoots.S4_90.basis u v) :
    Derives basis u v := by
  simpa [productize_of_isProduct u lhsProduct,
    productize_of_isProduct v rhsProduct] using
      derivesProductized derivation

end SemigroupBasis.EdmundsInflation

namespace SemigroupBasis.Inflation

/-- A proper inflation contains an element outside the embedded source. -/
def Proper
    {A : Type u} {B : Type v}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source target) : Prop :=
  ∃ outside, ∀ a, outside ≠ inflation.embedding.toFun a

/--
The Edmunds product-sided replacement is a complete basis for every proper
inflation of a semigroup with the suffix-parity basis.
-/
theorem inheritEdmundsSuffixParityBasis
    {A : Type u} {B : Type v}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source target)
    (proper : inflation.Proper)
    (sourceBasis :
      BasisFor source SemigroupBasis.CoRoots.S4_90.basis) :
    BasisFor target SemigroupBasis.EdmundsInflation.basis := by
  have sourceModels :
      Models source SemigroupBasis.EdmundsInflation.basis :=
    SemigroupBasis.EdmundsInflation.sourceModelsTarget sourceBasis
  have targetModels :
      Models target SemigroupBasis.EdmundsInflation.basis := by
    intro identity member
    simp only [SemigroupBasis.EdmundsInflation.basis, List.mem_cons,
      List.not_mem_nil, or_false] at member
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
                        SemigroupBasis.EdmundsInflation.derivesProductIdentity
                          (by simp) (by simp)
                          (sourceBasis.2 _ sourceValid)

end SemigroupBasis.Inflation
