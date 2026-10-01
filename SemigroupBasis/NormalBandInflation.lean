import SemigroupBasis.EdmundsInflation
import SemigroupBasis.Examples.NormalBandFour

namespace SemigroupBasis.NormalBandInflation

open SemigroupBasis
open SemigroupBasis.Examples

def xy : Word Nat := ⟨0, [1]⟩
def xxy : Word Nat := ⟨0, [0, 1]⟩
def xyxy : Word Nat := ⟨0, [1, 0, 1]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩

def rightContextLaw : Identity Nat := ⟨xy, xxy⟩
def productPowerLaw : Identity Nat := ⟨xy, xyxy⟩
def leftContextLaw : Identity Nat := ⟨xy, xyy⟩

/--
The product-sided replacement for the normal-band basis
`x = xx`, `xyzx = xzyx`.
-/
def basis : List (Identity Nat) :=
  [rightContextLaw, productPowerLaw, leftContextLaw,
    normalBandInteriorSwapLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

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

private theorem sourceModelsTarget
    {A : Type u} {source : Semigroup A}
    (sourceBasis :
      BasisFor source normalBandBasis) :
    Models source basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · have derivation :=
      Derives.appendRight
        (normalBandDerivesIdempotenceExpansion (Word.singleton 0))
        (Word.singleton 1)
    intro valuation
    simpa [rightContextLaw, xy, xxy, Word.append, Word.singleton,
      Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · have derivation :=
      normalBandDerivesIdempotenceExpansion xy
    intro valuation
    simpa [productPowerLaw, xy, xyxy, Word.append, Word.singleton,
      Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · have derivation :=
      Derives.prepend (Word.singleton 0) <|
        normalBandDerivesIdempotenceExpansion (Word.singleton 1)
    intro valuation
    simpa [leftContextLaw, xy, xyy, Word.append, Word.singleton,
      Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · exact sourceBasis.1 normalBandInteriorSwapLaw <|
      List.Mem.tail _ (List.Mem.head _)

/--
Every source derivation remains derivable after singleton words are replaced
by their squares.
-/
theorem derivesProductized
    {u v : Word Nat}
    (derivation :
      Derives normalBandBasis u v) :
    Derives basis (productize u) (productize v) := by
  induction derivation with
  | fromBasis member =>
      simp only [normalBandBasis, List.mem_cons,
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
      Derives normalBandBasis u v) :
    Derives basis u v := by
  simpa [productize_of_isProduct u lhsProduct,
    productize_of_isProduct v rhsProduct] using
      derivesProductized derivation

private def normalBandInteriorSwapLawSymm : Identity Nat :=
  ⟨normalBandXZYX, normalBandXYZX⟩

private theorem reversed_normalBandIdempotenceLaw :
    normalBandIdempotenceLaw.reversed =
      normalBandIdempotenceLaw := by
  decide

private theorem reversed_normalBandInteriorSwapLaw :
    normalBandInteriorSwapLaw.reversed =
      normalBandInteriorSwapLawSymm := by
  decide

/--
The normal-band basis can be restored from its reversed basis because
idempotence is reversal-invariant and the interior-swap law is symmetric.
-/
theorem normalBandBasis_complete_of_reversed
    {S : Type u} {G : Semigroup S}
    (complete :
      BasisFor G (reversedBasis normalBandBasis)) :
    BasisFor G normalBandBasis := by
  apply complete.replace
  · intro identity member
    simp only [normalBandBasis, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact complete.1 normalBandIdempotenceLaw <| by
        simp [reversedBasis, normalBandBasis,
          reversed_normalBandIdempotenceLaw,
          reversed_normalBandInteriorSwapLaw]
    · have reversedModels :
          normalBandInteriorSwapLawSymm.SatisfiedBy G :=
        complete.1 normalBandInteriorSwapLawSymm <| by
          simp [reversedBasis, normalBandBasis,
            reversed_normalBandIdempotenceLaw,
            reversed_normalBandInteriorSwapLaw]
      intro valuation
      simpa [normalBandInteriorSwapLaw,
        normalBandInteriorSwapLawSymm] using
          (reversedModels valuation).symm
  · intro identity member
    simp only [reversedBasis, normalBandBasis, List.map_cons,
      List.map_nil, reversed_normalBandIdempotenceLaw,
      reversed_normalBandInteriorSwapLaw, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Derives.fromBasis (List.Mem.head _)
    · exact Derives.symm <|
        Derives.fromBasis (List.Mem.tail _ (List.Mem.head _))

end SemigroupBasis.NormalBandInflation

namespace SemigroupBasis.Inflation

/--
The product-sided normal-band replacement is a complete basis for every
proper inflation of a semigroup with basis `x = xx`, `xyzx = xzyx`.
-/
theorem inheritNormalBandBasis
    {A : Type u} {B : Type v}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source target)
    (proper : inflation.Proper)
    (sourceBasis :
      BasisFor source SemigroupBasis.Examples.normalBandBasis) :
    BasisFor target SemigroupBasis.NormalBandInflation.basis := by
  have sourceModels :
      Models source SemigroupBasis.NormalBandInflation.basis :=
    SemigroupBasis.NormalBandInflation.sourceModelsTarget sourceBasis
  have targetModels :
      Models target SemigroupBasis.NormalBandInflation.basis := by
    intro identity member
    simp only [SemigroupBasis.NormalBandInflation.basis,
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
                        SemigroupBasis.NormalBandInflation.derivesProductIdentity
                          (by simp) (by simp)
                          (sourceBasis.2 _ sourceValid)

end SemigroupBasis.Inflation
