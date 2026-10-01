import SemigroupBasis.CoRoots.Order6L3Root3.Blocks

/-!
# Shared word-context infrastructure for the L3 rank-3 light root

This module is intentionally theorem-generic in the displayed basis.  The
two factor-specific macro modules use it to transport block-law instances
through optional nonempty contexts and substitutions.
-/

namespace SemigroupBasis.CoRoots.Order6L3Root3

open SemigroupBasis

def surround
    (pre : Option (Word Nat)) (core : Word Nat)
    (suf : Option (Word Nat)) : Word Nat :=
  match pre, suf with
  | none, none => core
  | some left, none => left ++ core
  | none, some right => core ++ right
  | some left, some right => (left ++ core) ++ right

def addPrefix
    (pre : Option (Word Nat)) (next : Word Nat) : Option (Word Nat) :=
  match pre with
  | none => some next
  | some current => some (current ++ next)

def addSuffix
    (next : Word Nat) (suf : Option (Word Nat)) : Option (Word Nat) :=
  match suf with
  | none => some next
  | some current => some (next ++ current)

theorem surround_prepend
    (pre suf : Option (Word Nat)) (left core : Word Nat) :
    surround pre (left ++ core) suf =
      surround (addPrefix pre left) core suf := by
  cases pre <;> cases suf <;>
    simp [surround, addPrefix, Word.append_assoc]

theorem surround_append
    (pre suf : Option (Word Nat)) (core right : Word Nat) :
    surround pre (core ++ right) suf =
      surround pre core (addSuffix right suf) := by
  cases pre <;> cases suf <;>
    simp [surround, addSuffix, Word.append_assoc]

theorem surroundDerives
    {laws : List (Identity Nat)}
    {left right : Word Nat}
    (pre suf : Option (Word Nat))
    (derivation : Derives laws left right) :
    Derives laws
      (surround pre left suf)
      (surround pre right suf) := by
  cases pre with
  | none =>
      cases suf with
      | none => exact derivation
      | some suffix => exact Derives.appendRight derivation suffix
  | some preWord =>
      cases suf with
      | none => exact Derives.prepend preWord derivation
      | some suffix =>
          exact Derives.appendRight
            (Derives.prepend preWord derivation) suffix

theorem wordLengthPositive (value : Word Nat) :
    0 < value.toList.length := by
  cases value
  simp [Word.toList]

theorem twoBlocksLong (left right : Word Nat) :
    2 ≤ (left ++ right).toList.length := by
  rw [Word.toList_append, List.length_append]
  have leftPositive := wordLengthPositive left
  have rightPositive := wordLengthPositive right
  omega

theorem threeBlocksLong (first second third : Word Nat) :
    3 ≤ ((first ++ second) ++ third).toList.length := by
  rw [Word.toList_append, Word.toList_append,
    List.length_append, List.length_append]
  have firstPositive := wordLengthPositive first
  have secondPositive := wordLengthPositive second
  have thirdPositive := wordLengthPositive third
  omega

theorem fourBlocksLong
    (first second third fourth : Word Nat) :
    3 ≤ (((first ++ second) ++ third) ++ fourth).toList.length := by
  rw [Word.toList_append, Word.toList_append, Word.toList_append,
    List.length_append, List.length_append, List.length_append]
  have firstPositive := wordLengthPositive first
  have secondPositive := wordLengthPositive second
  have thirdPositive := wordLengthPositive third
  have fourthPositive := wordLengthPositive fourth
  omega

theorem surroundLong
    (pre suf : Option (Word Nat)) (core : Word Nat)
    (long : 3 ≤ core.toList.length) :
    3 ≤ (surround pre core suf).toList.length := by
  cases pre with
  | none =>
      cases suf with
      | none => exact long
      | some right =>
          rw [surround, Word.toList_append, List.length_append]
          omega
  | some left =>
      cases suf with
      | none =>
          rw [surround, Word.toList_append, List.length_append]
          omega
      | some right =>
          rw [surround, Word.toList_append, Word.toList_append,
            List.length_append, List.length_append]
          omega

theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

theorem bind_bind
    (value : Word Nat)
    (first second : Nat → Word Nat) :
    (value.bind first).bind second =
      value.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

theorem bind_singleton (value : Word Nat) :
    value.bind Word.singleton = value := by
  apply Word.toList_injective
  simp [Word.toList_bind]

end SemigroupBasis.CoRoots.Order6L3Root3
