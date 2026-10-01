import SemigroupBasis.Equational

namespace SemigroupBasis.RightGuardedTransport

universe u

private theorem bindAppend {α : Type u}
    (left right : Word α) (substitution : α → Word α) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp only [Word.toList_bind, Word.toList_append, List.flatMap_append]

private theorem bindBind {α : Type u}
    (word : Word α) (first second : α → Word α) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp only [Word.toList_bind]
  have flatten : ∀ letters : List α,
      (letters.flatMap (fun letter => (first letter).toList)).flatMap
        (fun letter => (second letter).toList) =
      letters.flatMap (fun letter =>
        (first letter).toList.flatMap (fun next => (second next).toList)) := by
    intro letters
    induction letters with
    | nil => rfl
    | cons letter rest ih =>
        simp only [List.flatMap_cons, List.flatMap_append, ih]
  exact flatten word.toList

private theorem bindSingleton {α : Type u} (word : Word α) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp only [Word.toList_bind, Word.toList_singleton]
  have flatten : ∀ letters : List α,
      letters.flatMap (fun letter => [letter]) = letters := by
    intro letters
    induction letters with
    | nil => rfl
    | cons letter rest ih =>
        change letter :: rest.flatMap (fun next => [next]) = letter :: rest
        exact congrArg (List.cons letter) ih
  exact flatten word.toList

/-- A right-guarded axiom interpretation transports arbitrary derivations.
Substitutions are quantified in the induction invariant: the guard need not
lie in the image of an earlier substitution. -/
theorem transportSubstitution {α : Type u}
    {source target : List (Identity α)}
    (onAxioms : ∀ identity : Identity α, identity ∈ source →
      ∀ substitution : α → Word α, ∀ suffix : Word α,
        Derives target (identity.lhs.bind substitution ++ suffix)
          (identity.rhs.bind substitution ++ suffix))
    {left right : Word α} (derivation : Derives source left right) :
    ∀ substitution : α → Word α, ∀ suffix : Word α,
      Derives target (left.bind substitution ++ suffix)
        (right.bind substitution ++ suffix) := by
  induction derivation with
  | fromBasis member => exact onAxioms _ member
  | refl word =>
      intro substitution suffix
      exact Derives.refl _
  | symm _ ih =>
      intro substitution suffix
      exact Derives.symm (ih substitution suffix)
  | trans _ _ ihLeft ihRight =>
      intro substitution suffix
      exact Derives.trans (ihLeft substitution suffix) (ihRight substitution suffix)
  | prepend leftContext _ ih =>
      intro substitution suffix
      have lifted := Derives.prepend (leftContext.bind substitution)
        (ih substitution suffix)
      simpa only [bindAppend, Word.append_assoc] using lifted
  | appendRight _ trailing ih =>
      intro substitution suffix
      have lifted := ih substitution (trailing.bind substitution ++ suffix)
      simpa only [bindAppend, Word.append_assoc] using lifted
  | subst _ first ih =>
      intro second suffix
      have lifted := ih (fun letter => (first letter).bind second) suffix
      simpa only [bindBind] using lifted

/-- The un-substituted right-context transport used by fixed-last joins. -/
theorem transport {α : Type u}
    {source target : List (Identity α)}
    (onAxioms : ∀ identity : Identity α, identity ∈ source →
      ∀ substitution : α → Word α, ∀ suffix : Word α,
        Derives target (identity.lhs.bind substitution ++ suffix)
          (identity.rhs.bind substitution ++ suffix))
    {left right : Word α} (derivation : Derives source left right)
    (suffix : Word α) :
    Derives target (left ++ suffix) (right ++ suffix) := by
  have lifted := transportSubstitution onAxioms derivation Word.singleton suffix
  simpa only [bindSingleton] using lifted

#print axioms transportSubstitution
#print axioms transport

end SemigroupBasis.RightGuardedTransport
