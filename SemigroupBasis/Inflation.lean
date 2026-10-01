import SemigroupBasis.Transfer

namespace SemigroupBasis

/--
An inflation whose products are represented inside an embedded source
semigroup. The retraction need not be a homomorphism on single elements; every
binary product is nevertheless the embedded product of the representatives.
-/
structure Inflation {A : Type u} {B : Type v}
    (source : Semigroup A) (target : Semigroup B) where
  embedding : Embedding source target
  retract : B → A
  retract_embedding : ∀ a, retract (embedding.toFun a) = a
  product_represented :
    ∀ a b,
      target.mul a b =
        embedding.toFun (source.mul (retract a) (retract b))

namespace Inflation

private theorem fold_eval_represented
    {A : Type u} {B : Type v} {α : Type w}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source target)
    (valuation : α → B) (rest : List α) (current : A) :
    rest.foldl
        (fun value x => target.mul value (valuation x))
        (inflation.embedding.toFun current) =
      inflation.embedding.toFun
        (rest.foldl
          (fun value x => source.mul value (inflation.retract (valuation x)))
          current) := by
  induction rest generalizing current with
  | nil => rfl
  | cons next rest ih =>
      simp only [List.foldl_cons]
      have firstProduct :
          target.mul (inflation.embedding.toFun current) (valuation next) =
            inflation.embedding.toFun
              (source.mul current (inflation.retract (valuation next))) := by
        rw [inflation.product_represented,
          inflation.retract_embedding]
      rw [firstProduct]
      exact ih _

/--
Every word of length at least two evaluates in the inflation as the embedded
evaluation of the word on the chosen source representatives.
-/
theorem eval_represented
    {A : Type u} {B : Type v} {α : Type w}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source target)
    (valuation : α → B) (head next : α) (rest : List α) :
    target.eval valuation ⟨head, next :: rest⟩ =
      inflation.embedding.toFun
        (source.eval (fun x => inflation.retract (valuation x))
          ⟨head, next :: rest⟩) := by
  simp only [Semigroup.eval, List.foldl_cons]
  have firstProduct :
      target.mul (valuation head) (valuation next) =
        inflation.embedding.toFun
          (source.mul
            (inflation.retract (valuation head))
            (inflation.retract (valuation next))) :=
    inflation.product_represented _ _
  rw [firstProduct]
  exact inflation.fold_eval_represented valuation rest
    (source.mul
      (inflation.retract (valuation head))
      (inflation.retract (valuation next)))

/-- Source identities remain valid in an inflation when both sides are products. -/
theorem pushforwardProductIdentity
    {A : Type u} {B : Type v} {α : Type w}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source target)
    (identity : Identity α)
    (lhs_product : identity.lhs.tail ≠ [])
    (rhs_product : identity.rhs.tail ≠ [])
    (source_valid : identity.SatisfiedBy source) :
    identity.SatisfiedBy target := by
  intro valuation
  cases identity with
  | mk lhs rhs =>
      cases lhs with
      | mk lhsHead lhsTail =>
          cases lhsTail with
          | nil => contradiction
          | cons lhsNext lhsRest =>
              cases rhs with
              | mk rhsHead rhsTail =>
                  cases rhsTail with
                  | nil => contradiction
                  | cons rhsNext rhsRest =>
                      rw [inflation.eval_represented,
                        inflation.eval_represented]
                      exact congrArg inflation.embedding.toFun
                        (source_valid
                          (fun x => inflation.retract (valuation x)))

/--
For identities whose two sides have length at least two, an inflation and its
embedded source have exactly the same identity theory.
-/
theorem productIdentity_iff
    {A : Type u} {B : Type v} {α : Type w}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source target)
    (identity : Identity α)
    (lhs_product : identity.lhs.tail ≠ [])
    (rhs_product : identity.rhs.tail ≠ []) :
    identity.SatisfiedBy target ↔ identity.SatisfiedBy source := by
  constructor
  · exact inflation.embedding.pullback_identity identity
  · exact inflation.pushforwardProductIdentity identity
      lhs_product rhs_product

end Inflation

end SemigroupBasis
