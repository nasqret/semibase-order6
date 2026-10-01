import SemigroupBasis.EdmundsInflation
import SemigroupBasis.Examples.FirstFinalBandFour
import SemigroupBasis.Generated.CatalogueOrder5Part08
import SemigroupBasis.Generated.S4_120
import SemigroupBasis.Inflation
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_933

open SemigroupBasis
open SemigroupBasis.Examples

def x : Word Nat := Word.singleton 0
def xx : Word Nat := ⟨0, [0]⟩
def xy : Word Nat := ⟨0, [1]⟩
def xxy : Word Nat := ⟨0, [0, 1]⟩
def xyxy : Word Nat := ⟨0, [1, 0, 1]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xzyz : Word Nat := ⟨0, [2, 1, 2]⟩
def zyx : Word Nat := ⟨2, [1, 0]⟩
def zxyx : Word Nat := ⟨2, [0, 1, 0]⟩

def idempotenceLaw : Identity Nat := ⟨x, xx⟩
def rightContextLaw : Identity Nat := ⟨xy, xxy⟩
def productPowerLaw : Identity Nat := ⟨xy, xyxy⟩
def leftContextLaw : Identity Nat := ⟨xy, xyy⟩
def returnLaw : Identity Nat := ⟨xyz, xzyz⟩
def literalOppositeReturnLaw : Identity Nat := ⟨zyx, zxyx⟩

/-- The exact authoritative basis for the stored `S5_933` table. -/
def basis : List (Identity Nat) :=
  [rightContextLaw, productPowerLaw, leftContextLaw, returnLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

/--
An alpha-renamed form of the released opposite `S4_120` basis.
-/
def orientedSourceBasis : List (Identity Nat) :=
  [idempotenceLaw, returnLaw]

/-- The literal reverse-word form recorded by the `S4_120` release. -/
def literalSourceBasis : List (Identity Nat) :=
  [idempotenceLaw, literalOppositeReturnLaw]

theorem literalSourceBasis_eq_reversedFirstFinalBandBasis :
    literalSourceBasis = reversedBasis firstFinalBandBasis := by
  decide

private def swapFirstThird : Nat → Word Nat
  | 0 => Word.singleton 2
  | 1 => Word.singleton 1
  | 2 => Word.singleton 0
  | n + 3 => Word.singleton (n + 3)

private theorem orientedAxiomsDeriveLiteral
    (identity : Identity Nat) (member : identity ∈ orientedSourceBasis) :
    Derives literalSourceBasis identity.lhs identity.rhs := by
  simp only [orientedSourceBasis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl
  · exact Derives.fromBasis (e := idempotenceLaw) (List.Mem.head _)
  · have base :
        Derives literalSourceBasis
          literalOppositeReturnLaw.lhs literalOppositeReturnLaw.rhs :=
      Derives.fromBasis (e := literalOppositeReturnLaw) <|
        List.Mem.tail _ (List.Mem.head _)
    have renamed := Derives.subst base swapFirstThird
    simpa [returnLaw, literalOppositeReturnLaw, xyz, xzyz, zyx, zxyx,
      swapFirstThird, Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using renamed

private theorem literalAxiomsDeriveOriented
    (identity : Identity Nat) (member : identity ∈ literalSourceBasis) :
    Derives orientedSourceBasis identity.lhs identity.rhs := by
  simp only [literalSourceBasis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl
  · exact Derives.fromBasis (e := idempotenceLaw) (List.Mem.head _)
  · have base :
        Derives orientedSourceBasis returnLaw.lhs returnLaw.rhs :=
      Derives.fromBasis (e := returnLaw) <|
        List.Mem.tail _ (List.Mem.head _)
    have renamed := Derives.subst base swapFirstThird
    simpa [returnLaw, literalOppositeReturnLaw, xyz, xzyz, zyx, zxyx,
      swapFirstThird, Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using renamed

private theorem orientedModelsOfLiteral
    {S : Type u} {G : Semigroup S}
    (complete : BasisFor G literalSourceBasis) :
    Models G orientedSourceBasis := by
  intro identity member valuation
  exact
    Derives.sound complete.1
      (orientedAxiomsDeriveLiteral identity member) valuation

theorem orientedBasisCompleteOfLiteral
    {S : Type u} {G : Semigroup S}
    (complete : BasisFor G literalSourceBasis) :
    BasisFor G orientedSourceBasis :=
  complete.replace (orientedModelsOfLiteral complete)
    literalAxiomsDeriveOriented

theorem release_literal_source_basis :
    BasisFor SemigroupBasis.Generated.S4_120.table.semigroup.opposite
      literalSourceBasis := by
  rw [literalSourceBasis_eq_reversedFirstFinalBandBasis]
  exact SemigroupBasis.Generated.S4_120.opposite_basis

theorem oriented_source_basis :
    BasisFor SemigroupBasis.Generated.S4_120.table.semigroup.opposite
      orientedSourceBasis :=
  orientedBasisCompleteOfLiteral release_literal_source_basis

private def instantiateOneWord (u : Word Nat) : Nat → Word Nat
  | 0 => u
  | n + 1 => Word.singleton (n + 1)

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
    (sigma : Nat → Word Nat) (xs : List Nat) (current : Word Nat)
    (currentProduct : current.tail ≠ []) :
    (xs.foldl (fun value symbol => value ++ sigma symbol) current).tail ≠
      [] := by
  induction xs generalizing current with
  | nil => exact currentProduct
  | cons symbol xs ih =>
      simp only [List.foldl_cons]
      exact ih (current ++ sigma symbol)
        (append_isProduct current (sigma symbol))

private theorem bind_isProduct
    (w : Word Nat) (wordProduct : w.tail ≠ [])
    (sigma : Nat → Word Nat) :
    (w.bind sigma).tail ≠ [] := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil => contradiction
      | cons next rest =>
          unfold Word.bind
          simp only [List.foldl_cons]
          exact foldl_append_isProduct sigma rest
            (sigma head ++ sigma next)
            (append_isProduct (sigma head) (sigma next))

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
    (w : Word Nat) (sigma : Nat → Word Nat) :
    Derives basis ((productize w).bind sigma)
      (productize (w.bind sigma)) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          by_cases substitutedProduct : (sigma head).tail = []
          · simpa [productize, square, Word.bind, Word.append,
              substitutedProduct] using
                (Derives.refl (square (sigma head)) :
                  Derives basis (square (sigma head))
                    (square (sigma head)))
          · have contraction :=
              Derives.symm
                (derivesWholeSquare (sigma head) substitutedProduct)
            change
              Derives basis (square (sigma head))
                (productize (sigma head))
            rw [productize_of_isProduct (sigma head)
              substitutedProduct]
            exact contraction
      | cons next rest =>
          have boundProduct :
              ((Word.mk head (next :: rest)).bind sigma).tail ≠ [] :=
            bind_isProduct ⟨head, next :: rest⟩ (by simp) sigma
          change
            Derives basis
              ((Word.mk head (next :: rest)).bind sigma)
              (productize ((Word.mk head (next :: rest)).bind sigma))
          rw [productize_of_isProduct _ boundProduct]
          exact Derives.refl _

private theorem orientedDerivesIdempotenceExpansion (u : Word Nat) :
    Derives orientedSourceBasis u (u ++ u) := by
  have base :
      Derives orientedSourceBasis idempotenceLaw.lhs
        idempotenceLaw.rhs :=
    Derives.fromBasis (e := idempotenceLaw) (List.Mem.head _)
  have instantiated :=
    Derives.subst base (instantiateOneWord u)
  simpa [idempotenceLaw, x, xx, instantiateOneWord, Word.bind,
    Word.append, Word.singleton] using instantiated

private theorem sourceModelsTarget
    {A : Type u} {source : Semigroup A}
    (sourceBasis : BasisFor source orientedSourceBasis) :
    Models source basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · have derivation :=
      Derives.appendRight
        (orientedDerivesIdempotenceExpansion (Word.singleton 0))
        (Word.singleton 1)
    intro valuation
    simpa [rightContextLaw, xy, xxy, Word.append, Word.singleton,
      Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · have derivation :=
      orientedDerivesIdempotenceExpansion xy
    intro valuation
    simpa [productPowerLaw, xy, xyxy, Word.append, Word.singleton,
      Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · have derivation :=
      Derives.prepend (Word.singleton 0) <|
        orientedDerivesIdempotenceExpansion (Word.singleton 1)
    intro valuation
    simpa [leftContextLaw, xy, xyy, Word.append, Word.singleton,
      Word.append_assoc] using
        Derives.sound sourceBasis.1 derivation valuation
  · exact sourceBasis.1 returnLaw <|
      List.Mem.tail _ (List.Mem.head _)

/--
Every derivation from the alpha-renamed opposite `S4_120` basis remains
derivable after singleton words are replaced by their squares.
-/
theorem derivesProductized
    {u v : Word Nat}
    (derivation : Derives orientedSourceBasis u v) :
    Derives basis (productize u) (productize v) := by
  induction derivation with
  | fromBasis member =>
      simp only [orientedSourceBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact Derives.refl _
      · simpa [productize, returnLaw, xyz, xzyz] using
          (Derives.fromBasis <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ (List.Mem.head _))
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
  | subst derivation sigma ih =>
      exact Derives.trans
        (Derives.symm (derivesBindProductize _ sigma)) <|
        Derives.trans (Derives.subst ih sigma)
          (derivesBindProductize _ sigma)

theorem derivesProductIdentity
    {u v : Word Nat}
    (lhsProduct : u.tail ≠ []) (rhsProduct : v.tail ≠ [])
    (derivation : Derives orientedSourceBasis u v) :
    Derives basis u v := by
  simpa [productize_of_isProduct u lhsProduct,
    productize_of_isProduct v rhsProduct] using
      derivesProductized derivation

/--
The exact four-law `S5_933` presentation is a complete basis for every proper
inflation of a semigroup with the oriented opposite `S4_120` basis.
-/
theorem basisForProperInflation
    {A : Type u} {B : Type v}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source target)
    (proper : inflation.Proper)
    (sourceBasis : BasisFor source orientedSourceBasis) :
    BasisFor target basis := by
  have sourceModels : Models source basis :=
    sourceModelsTarget sourceBasis
  have targetModels : Models target basis := by
    intro identity member
    simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
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
                            (Word.mk rhsHead
                              (rhsNext :: rhsRest))).SatisfiedBy source :=
                        inflation.embedding.pullback_identity _ valid
                      exact
                        derivesProductIdentity
                          (by simp) (by simp)
                          (sourceBasis.2 _ sourceValid)

/-- The recorded one-based image `[4,1,3,5]` embeds `S4_120` opposite. -/
def embedding :
    Embedding SemigroupBasis.Generated.S4_120.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_933.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (3 : Fin 5)
    else if a = 1 then (0 : Fin 5)
    else if a = 2 then (2 : Fin 5)
    else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

/--
The recorded representatives are `[1,1,3,4,5]`; the corresponding source
retraction is `[2,2,3,1,4]`.
-/
def inflation :
    Inflation SemigroupBasis.Generated.S4_120.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_933.table.semigroup where
  embedding := embedding
  retract := fun b : Fin 5 =>
    if b = 0 then (1 : Fin 4)
    else if b = 1 then (1 : Fin 4)
    else if b = 2 then (2 : Fin 4)
    else if b = 3 then (0 : Fin 4)
    else (3 : Fin 4)
  retract_embedding := by
    intro a
    exact by decide +revert
  product_represented := by
    intro a b
    exact by decide +revert

def embeddingImageOneBased : List Nat :=
  List.ofFn fun a : Fin 4 => (embedding.toFun a).val + 1

theorem embeddingImageOneBased_certificate :
    embeddingImageOneBased = [4, 1, 3, 5] := by
  decide

def retractionRepresentativeImageOneBased : List Nat :=
  List.ofFn fun b : Fin 5 =>
    (embedding.toFun (inflation.retract b)).val + 1

theorem retractionRepresentativeImageOneBased_certificate :
    retractionRepresentativeImageOneBased = [1, 1, 3, 4, 5] := by
  decide

def retractToSourceOneBased : List Nat :=
  List.ofFn fun b : Fin 5 => (inflation.retract b).val + 1

theorem retractToSourceOneBased_certificate :
    retractToSourceOneBased = [2, 2, 3, 1, 4] := by
  decide

def outside : Fin 5 := 1

theorem outsideOneBased_certificate :
    outside.val + 1 = 2 := by
  decide

theorem proper : inflation.Proper := by
  refine ⟨outside, ?_⟩
  intro a
  exact by decide +revert

theorem representative_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_933.table.semigroup
      basis :=
  basisForProperInflation inflation proper oriented_source_basis

theorem opposite_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_933.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.S5_933
