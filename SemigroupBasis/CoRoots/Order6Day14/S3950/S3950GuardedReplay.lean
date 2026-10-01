import SemigroupBasis.CoRoots.Order6Day14.S3950.S3950Presentation
import SemigroupBasis.CoRoots.S5_110Family

/-! Reuse the published complete S5_110 calculus behind a nonempty prefix.
The substitution-generalized induction follows the proved Rank048 template.
The new head duplication uses only the two displayed gather/power laws. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day14.S3950

open SemigroupBasis
open SemigroupBasis.CoRoots

abbrev lowerBasis : List (Identity Nat) := S5_110.basis

theorem lowerLaw00 : S5_110.powerLaw =
    (⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩ : Identity Nat) := by decide
theorem lowerLaw01 : S5_110.leftFoldLaw =
    (⟨Word.mk 0 [1, 0], Word.mk 0 [0, 1]⟩ : Identity Nat) := by decide
theorem lowerLaw02 : S5_110.rightFoldLaw =
    (⟨Word.mk 0 [1, 0], Word.mk 1 [0, 0]⟩ : Identity Nat) := by decide

theorem lowerBasis_exact :
    lowerBasis.map (fun identity => (identity.lhs.toList, identity.rhs.toList)) =
      [([0, 0], [0, 0, 0]), ([0, 1, 0], [0, 0, 1]),
       ([0, 1, 0], [1, 0, 0])] := by decide

/-- The two typed edges p·uvu -> p·uuv -> p·vuu. -/
theorem guardedRightFold (guard u v : Word Nat) :
    Derives basis (guard ++ ((u ++ v) ++ u)) (guard ++ ((v ++ u) ++ u)) := by
  have first : Derives basis (guard ++ ((u ++ v) ++ u))
      (guard ++ ((u ++ u) ++ v)) :=
    Derives.prepend guard (rawLaw01 u v).symm
  have second : Derives basis (guard ++ ((u ++ u) ++ v))
      (guard ++ ((v ++ u) ++ u)) := by
    simpa only [Word.append_assoc] using rawLaw02 guard u v
  exact first.trans second

theorem guardedLowerAxiom (identity : Identity Nat) (member : identity ∈ lowerBasis)
    (substitution : Nat → Word Nat) (guard : Word Nat) :
    Derives basis (guard ++ identity.lhs.bind substitution)
      (guard ++ identity.rhs.bind substitution) := by
  simp only [lowerBasis, S5_110.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rw [lowerLaw00]
    change Derives basis (guard ++ (substitution 0 ++ substitution 0))
      (guard ++ ((substitution 0 ++ substitution 0) ++ substitution 0))
    exact Derives.prepend guard (rawLaw00 (substitution 0))
  · rw [lowerLaw01]
    change Derives basis (guard ++ ((substitution 0 ++ substitution 1) ++ substitution 0))
      (guard ++ ((substitution 0 ++ substitution 0) ++ substitution 1))
    exact Derives.prepend guard (rawLaw01 (substitution 0) (substitution 1)).symm
  · rw [lowerLaw02]
    change Derives basis (guard ++ ((substitution 0 ++ substitution 1) ++ substitution 0))
      (guard ++ ((substitution 1 ++ substitution 0) ++ substitution 0))
    exact guardedRightFold guard (substitution 0) (substitution 1)

private theorem bind_append (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution = left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second = word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) : word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

theorem liftLowerWithPrefix {left right : Word Nat}
    (derivation : Derives lowerBasis left right)
    (guard : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (guard ++ left.bind substitution) (guard ++ right.bind substitution) := by
  induction derivation generalizing guard substitution with
  | fromBasis member => exact guardedLowerAxiom _ member substitution guard
  | refl => exact Derives.refl _
  | symm _ induction => exact (induction guard substitution).symm
  | trans _ _ first second => exact (first guard substitution).trans (second guard substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (guard ++ stem.bind substitution) substitution
  | appendRight _ final induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (induction guard substitution) (final.bind substitution)
  | subst _ next induction =>
      simpa [bind_bind] using
        induction guard (fun letter => (next letter).bind substitution)

theorem derivesSamePrefixOfLowerValid (left right guard : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy Generated.Catalogue.S5_110.table.semigroup) :
    Derives basis (guard ++ left) (guard ++ right) := by
  have lower := S5_110Family.S5_110.basisFor.2 (Identity.mk left right) valid
  simpa only [bind_singleton] using liftLowerWithPrefix lower guard Word.singleton

/-- Append a possibly empty list as context, never as a substitution word. -/
theorem appendTail {left right : Word Nat} (derivation : Derives basis left right)
    (tail : List Nat) :
    Derives basis (Word.mk left.head (left.tail ++ tail))
      (Word.mk right.head (right.tail ++ tail)) := by
  cases tail with
  | nil => simpa only [List.append_nil] using derivation
  | cons head rest => exact derivation.appendRight (Word.mk head rest)

theorem gatherHead (head : Nat) (front suffix : List Nat) :
    Derives basis (Word.mk head (front ++ head :: suffix))
      (Word.mk head (head :: (front ++ suffix))) := by
  cases front with
  | nil => exact Derives.refl _
  | cons first rest =>
      have core : Derives basis (Word.mk head ((first :: rest) ++ [head]))
          (Word.mk head (head :: first :: rest)) := by
        simpa only [Word.singleton, Word.append, List.nil_append, List.cons_append] using
          (rawLaw01 (Word.singleton head) (Word.mk first rest)).symm
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        appendTail core suffix

private theorem splitAtMember (letter : Nat) :
    ∀ letters : List Nat, letter ∈ letters →
      ∃ front back : List Nat, letters = front ++ letter :: back
  | [], member => by cases member
  | first :: rest, member => by
      rcases List.mem_cons.mp member with headEq | restMember
      · subst first
        exact ⟨[], rest, rfl⟩
      · obtain ⟨front, back, shape⟩ := splitAtMember letter rest restMember
        exact ⟨first :: front, back, congrArg (List.cons first) shape⟩

theorem duplicateRepeatedHead (head : Nat) (tail : List Nat) (repeated : head ∈ tail) :
    Derives basis (Word.mk head tail) (Word.singleton head ++ Word.mk head tail) := by
  obtain ⟨front, suffix, split⟩ := splitAtMember head tail repeated
  rw [split]
  have gather := gatherHead head front suffix
  have expand : Derives basis (Word.mk head (head :: (front ++ suffix)))
      (Word.singleton head ++ Word.mk head (head :: (front ++ suffix))) := by
    exact appendTail (rawLaw00 (Word.singleton head)) (front ++ suffix)
  have undo : Derives basis
      (Word.singleton head ++ Word.mk head (head :: (front ++ suffix)))
      (Word.singleton head ++ Word.mk head (front ++ head :: suffix)) :=
    Derives.prepend (Word.singleton head) gather.symm
  exact gather.trans (expand.trans undo)

end SemigroupBasis.CoRoots.Order6Day14.S3950
