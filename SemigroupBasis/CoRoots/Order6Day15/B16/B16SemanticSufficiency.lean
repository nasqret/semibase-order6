import SemigroupBasis.CoRoots.Order6Day15.B16.B16ManySections
import SemigroupBasis.CoRoots.Order6Day15.B16.B16ValuationAdapters

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Literal

theorem observation_values_sufficient (S : Semigroup (Fin 6)) (D : SplitAction S)
    (hpos : ∀ a : Fin 6, 3 ≤ a.val → D.Pos a)
    (hlow : ∀ a : Fin 6, a.val < 3 → D.Low a)
    (hom : ∀ a b, S.mul (positiveEmbed a) (positiveEmbed b) = positiveEmbed (positive.mul a b))
    {u v : Word Nat} (h : SameObservation u v) (rho : Nat → Fin 6) :
    evalValues S (u.toList.map rho) = evalValues S (v.toList.map rho) := by
  let P : Nat → Prop := fun x => 3 ≤ (rho x).val
  rcases predicate_cases P u.toList with hp | ⟨pre, post, x, eq, hp, hx, hs⟩ |
    ⟨pre, mid, post, x, y, eq, hx, hy⟩
  · have target : ∀ x ∈ v.toList, 3 ≤ (rho x).val := observation_positive h P hp
    exact positive_word_equal S hom h.1 rho hp target
  · rcases observation_one h P x pre post eq hx hp hs with
      ⟨pre', post', eq', hp', hs', keys⟩
    have low : D.Low (rho x) := hlow (rho x) (Nat.lt_of_not_ge hx)
    have leftPositive : ∀ y ∈ pre, D.Pos (rho y) := fun y hy => hpos (rho y) (hp y hy)
    have rightPositive : ∀ y ∈ pre', D.Pos (rho y) := fun y hy => hpos (rho y) (hp' y hy)
    have left : evalValues S (u.toList.map rho) = some (runTail S (rho x) (post.map rho)) :=
      (congrArg (fun xs => evalValues S (xs.map rho)) eq).trans
        (mapped_one_value S D rho pre post x low leftPositive)
    have right : evalValues S (v.toList.map rho) = some (runTail S (rho x) (post'.map rho)) :=
      (congrArg (fun xs => evalValues S (xs.map rho)) eq').trans
        (mapped_one_value S D rho pre' post' x low rightPositive)
    have actions : runTail S (rho x) (post.map rho) = runTail S (rho x) (post'.map rho) :=
      mapped_continuation_equal S hom rho post post' keys hs hs' (rho x)
    exact left.trans ((congrArg some actions).trans right.symm)
  · rcases observation_many h P pre mid post x y eq hx hy with
      ⟨pre', mid', post', x', y', eq', hx', hy'⟩
    have lowx : D.Low (rho x) := hlow (rho x) (Nat.lt_of_not_ge hx)
    have lowy : D.Low (rho y) := hlow (rho y) (Nat.lt_of_not_ge hy)
    have lowx' : D.Low (rho x') := hlow (rho x') (Nat.lt_of_not_ge hx')
    have lowy' : D.Low (rho y') := hlow (rho y') (Nat.lt_of_not_ge hy')
    have left : evalValues S (u.toList.map rho) = some D.zero :=
      (congrArg (fun xs => evalValues S (xs.map rho)) eq).trans
        (mapped_many_value S D rho pre mid post x y lowx lowy)
    have right : evalValues S (v.toList.map rho) = some D.zero :=
      (congrArg (fun xs => evalValues S (xs.map rho)) eq').trans
        (mapped_many_value S D rho pre' mid' post' x' y' lowx' lowy')
    exact left.trans right.symm

theorem observation_eval_sufficient (S : Semigroup (Fin 6)) (D : SplitAction S)
    (hpos : ∀ a : Fin 6, 3 ≤ a.val → D.Pos a)
    (hlow : ∀ a : Fin 6, a.val < 3 → D.Low a)
    (hom : ∀ a b, S.mul (positiveEmbed a) (positiveEmbed b) = positiveEmbed (positive.mul a b))
    {u v : Word Nat} (h : SameObservation u v) (rho : Nat → Fin 6) :
    S.eval rho u = S.eval rho v := by
  have values : evalValues S (u.toList.map rho) = evalValues S (v.toList.map rho) :=
    observation_values_sufficient S D hpos hlow hom h rho
  have tagged : some (S.eval rho u) = some (S.eval rho v) :=
    (evalValues_valuation S rho u).symm.trans (values.trans (evalValues_valuation S rho v))
  exact Option.some.inj tagged

theorem semantic_sufficiency6432 {u v : Word Nat} (h : SameObservation u v) :
    ∀ rho : Nat → Fin 6, s6432.eval rho u = s6432.eval rho v := by
  intro rho
  exact observation_eval_sufficient s6432 split6432 (fun _ ha => ha) (fun _ ha => ha)
    positiveEmbed_hom6432 h rho

theorem semantic_sufficiency6439 {u v : Word Nat} (h : SameObservation u v) :
    ∀ rho : Nat → Fin 6, s6439.eval rho u = s6439.eval rho v := by
  intro rho
  exact observation_eval_sufficient s6439 split6439 (fun _ ha => ha) (fun _ ha => ha)
    positiveEmbed_hom6439 h rho

theorem identity_of_observation6432 (e : Identity Nat) (h : SameObservation e.lhs e.rhs) :
    e.SatisfiedBy s6432 := semantic_sufficiency6432 h

theorem identity_of_observation6439 (e : Identity Nat) (h : SameObservation e.lhs e.rhs) :
    e.SatisfiedBy s6439 := semantic_sufficiency6439 h

end SemigroupBasis.CoRoots.Order6Day15.B16.Literal
