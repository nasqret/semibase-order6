import SemigroupBasis.EdmundsInflation

namespace SemigroupBasis.S5_267Inflation

open SemigroupBasis

def x : Word Nat := Word.singleton 0
def xxx : Word Nat := ⟨0, [0, 0]⟩
def xy : Word Nat := ⟨0, [1]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xzy : Word Nat := ⟨0, [2, 1]⟩
def xyzz : Word Nat := ⟨0, [1, 2, 2]⟩
def xzzy : Word Nat := ⟨0, [2, 2, 1]⟩

def sourceCommutationLaw : Identity Nat := ⟨xyz, xzy⟩
def sourceContractionLaw : Identity Nat := ⟨xyy, x⟩

/-- The exact source basis `xyz = xzy`, `xyy = x` of `S4_52`. -/
def sourceBasis : List (Identity Nat) :=
  [sourceCommutationLaw, sourceContractionLaw]

def appendPairLaw : Identity Nat := ⟨xy, xyzz⟩
def insertPairLaw : Identity Nat := ⟨xy, xzzy⟩
def suffixCommutationLaw : Identity Nat := ⟨xyz, xzy⟩

/--
The product-sided Edmunds replacement for the `S4_52` basis:
`xy = xyzz`, `xy = xzzy`, `xyz = xzy`.
-/
def basis : List (Identity Nat) :=
  [appendPairLaw, insertPairLaw, suffixCommutationLaw]

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

def triple (w : Word Nat) : Word Nat :=
  (w ++ w) ++ w

/-- Replace singleton words by their cubes and leave products fixed. -/
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

private theorem derivesRightContextTriple (u v : Word Nat) :
    Derives basis (u ++ v) (triple u ++ v) := by
  have base :
      Derives basis insertPairLaw.lhs insertPairLaw.rhs :=
    Derives.fromBasis (e := insertPairLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have instantiated :=
    Derives.subst base (instantiateThreeWords u v u)
  simpa [basis, insertPairLaw, xy, xzzy, triple,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

private theorem derivesProductTriple (u v : Word Nat) :
    Derives basis (u ++ v) (triple (u ++ v)) := by
  have base :
      Derives basis appendPairLaw.lhs appendPairLaw.rhs :=
    Derives.fromBasis (e := appendPairLaw) (List.Mem.head _)
  have instantiated :=
    Derives.subst base (instantiateThreeWords u v (u ++ v))
  simpa [basis, appendPairLaw, xy, xyzz, triple,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

private theorem derivesLeftContextTriple (u v : Word Nat) :
    Derives basis (u ++ v) (u ++ triple v) := by
  have base :
      Derives basis appendPairLaw.lhs appendPairLaw.rhs :=
    Derives.fromBasis (e := appendPairLaw) (List.Mem.head _)
  have instantiated :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [basis, appendPairLaw, xy, xyzz, triple,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

/--
The translated singleton law is derivable:
`uvv = uuuvv = uuu`.
-/
private theorem derivesTranslatedContraction (u v : Word Nat) :
    Derives basis ((u ++ v) ++ v) (triple u) := by
  have insertBase :
      Derives basis insertPairLaw.lhs insertPairLaw.rhs :=
    Derives.fromBasis (e := insertPairLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have leftExpansion :=
    Derives.subst insertBase
      (instantiateThreeWords u (v ++ v) u)
  have appendBase :
      Derives basis appendPairLaw.lhs appendPairLaw.rhs :=
    Derives.fromBasis (e := appendPairLaw) (List.Mem.head _)
  have rightExpansion :=
    Derives.subst appendBase
      (instantiateThreeWords u (u ++ u) v)
  exact Derives.trans
    (by
      simpa [basis, insertPairLaw, xy, xzzy, triple,
        instantiateThreeWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using leftExpansion)
    (Derives.symm <| by
      simpa [basis, appendPairLaw, xy, xyzz, triple,
        instantiateThreeWords, Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using rightExpansion)

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

private theorem sourceDerivesExpansion (u v : Word Nat) :
    Derives sourceBasis u ((u ++ v) ++ v) := by
  have base :
      Derives sourceBasis sourceContractionLaw.rhs
        sourceContractionLaw.lhs :=
    Derives.symm <|
      Derives.fromBasis (e := sourceContractionLaw) <|
        List.Mem.tail _ (List.Mem.head _)
  have instantiated :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [sourceBasis, sourceContractionLaw, xyy, x,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using instantiated

private theorem sourceModelsTarget
    {A : Type u} {source : Semigroup A}
    (sourceBasisComplete : BasisFor source sourceBasis) :
    Models source basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · have derivation :=
      sourceDerivesExpansion xy (Word.singleton 2)
    intro valuation
    simpa [appendPairLaw, xy, xyzz, Word.append, Word.singleton,
      Word.append_assoc] using
        Derives.sound sourceBasisComplete.1 derivation valuation
  · have expansion :=
      sourceDerivesExpansion (Word.singleton 0) (Word.singleton 2)
    have derivation :=
      Derives.appendRight expansion (Word.singleton 1)
    intro valuation
    simpa [insertPairLaw, xy, xzzy, Word.append, Word.singleton,
      Word.append_assoc] using
        Derives.sound sourceBasisComplete.1 derivation valuation
  · exact sourceBasisComplete.1 sourceCommutationLaw (List.Mem.head _)

/--
Every source derivation remains derivable after singleton words are replaced
by their cubes.
-/
theorem derivesProductized
    {u v : Word Nat}
    (derivation : Derives sourceBasis u v) :
    Derives basis (productize u) (productize v) := by
  induction derivation with
  | fromBasis member =>
      simp only [sourceBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact Derives.fromBasis <|
          List.Mem.tail _ <|
            List.Mem.tail _ (List.Mem.head _)
      · simpa [productize, sourceContractionLaw, xyy, x, triple,
          Word.append, Word.singleton, Word.append_assoc] using
            derivesTranslatedContraction
              (Word.singleton 0) (Word.singleton 1)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm ih
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans ih₁ ih₂
  | prepend pre derivation ih =>
      exact Derives.trans
        (by
          simpa [productize_of_isProduct _
            (append_isProduct pre _)] using
              derivesPrependProductize pre _)
        (Derives.trans
          (Derives.prepend pre ih)
          (by
            simpa [productize_of_isProduct _
              (append_isProduct pre _)] using
                Derives.symm (derivesPrependProductize pre _)))
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
    (derivation : Derives sourceBasis u v) :
    Derives basis u v := by
  simpa [productize_of_isProduct u lhsProduct,
    productize_of_isProduct v rhsProduct] using
      derivesProductized derivation

end SemigroupBasis.S5_267Inflation

namespace SemigroupBasis.Inflation

/--
The three-law product-sided replacement is a complete basis for every proper
inflation of a semigroup with basis `xyz = xzy`, `xyy = x`.
-/
theorem inheritS5_267Basis
    {A : Type u} {B : Type v}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source target)
    (proper : inflation.Proper)
    (sourceBasisComplete :
      BasisFor source SemigroupBasis.S5_267Inflation.sourceBasis) :
    BasisFor target SemigroupBasis.S5_267Inflation.basis := by
  have sourceModels :
      Models source SemigroupBasis.S5_267Inflation.basis :=
    SemigroupBasis.S5_267Inflation.sourceModelsTarget sourceBasisComplete
  have targetModels :
      Models target SemigroupBasis.S5_267Inflation.basis := by
    intro identity member
    simp only [SemigroupBasis.S5_267Inflation.basis,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact inflation.pushforwardProductIdentity _ (by decide) (by decide)
        (sourceModels _ (List.Mem.head _))
    · exact inflation.pushforwardProductIdentity _ (by decide) (by decide)
        (sourceModels _ (List.Mem.tail _ (List.Mem.head _)))
    · exact inflation.pushforwardProductIdentity _ (by decide) (by decide)
        (sourceModels _ <|
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
                        SemigroupBasis.S5_267Inflation.derivesProductIdentity
                          (by simp) (by simp)
                          (sourceBasisComplete.2 _ sourceValid)

end SemigroupBasis.Inflation
