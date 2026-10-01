import SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank001
import SemigroupBasis.CoRoots.S5_441Normalization
import SemigroupBasis.Opposite

/-!
# Complete fixed-first replay of the parity/exact-separator normalizer

The rank-001 target is used in its literal reversed orientation.  Every one
of the 25 complete `S5_441` displayed laws is replayed behind a protected
nonempty prefix.  Every edge below names an immutable rank-001 law, proves
membership by `decide`, and fixes its intermediate word and substitution.

In particular, source laws 20 and 24 require genuine composite substitutions
and respectively four and seven separately typed frozen edges.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_796Opposite

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) :=
  reversedBasis Rank001.basis

private def word (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

private def surround
    (front : Option (Word Nat)) (middle : Word Nat)
    (suffix : Option (Word Nat)) : Word Nat :=
  match front, suffix with
  | none, none => middle
  | some first, none => first ++ middle
  | none, some last => middle ++ last
  | some first, some last => (first ++ middle) ++ last

private theorem displayedForward
    (identity : Identity Nat) (member : identity ∈ Rank001.basis)
    (substitution : Nat → Word Nat)
    (front suffix : Option (Word Nat)) :
    Derives targetBasis
      (surround front (identity.reversed.lhs.bind substitution) suffix)
      (surround front (identity.reversed.rhs.bind substitution) suffix) := by
  have primitive := (Derives.fromBasis member).reverse
  have instantiated := Derives.subst primitive substitution
  cases front with
  | none =>
      cases suffix with
      | none => exact instantiated
      | some last => exact Derives.appendRight instantiated last
  | some first =>
      cases suffix with
      | none => exact Derives.prepend first instantiated
      | some last =>
          exact Derives.appendRight (Derives.prepend first instantiated) last

private theorem displayedBackward
    (identity : Identity Nat) (member : identity ∈ Rank001.basis)
    (substitution : Nat → Word Nat)
    (front suffix : Option (Word Nat)) :
    Derives targetBasis
      (surround front (identity.reversed.rhs.bind substitution) suffix)
      (surround front (identity.reversed.lhs.bind substitution) suffix) :=
  (displayedForward identity member substitution front suffix).symm

private theorem guardedMacro00 :
    Derives targetBasis (word 3 [0, 0]) (word 3 [0, 0, 0, 0]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 0]) (word 3 [0, 0, 0, 0]) := by
    exact displayedForward Rank001.law00
      (show Rank001.law00 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  exact edge00

private theorem guardedMacro01 :
    Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 0, 0, 1, 0]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 0, 0, 1, 0]) := by
    exact displayedForward Rank001.law11
      (show Rank001.law11 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  exact edge00

private theorem guardedMacro02 :
    Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 0, 1, 0, 0]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 0, 1, 0, 0]) := by
    exact displayedBackward Rank001.law03
      (show Rank001.law03 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  exact edge00

private theorem guardedMacro03 :
    Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 0, 1, 1, 1]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 0, 1, 1, 1]) := by
    exact displayedForward Rank001.law15
      (show Rank001.law15 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  exact edge00

private theorem guardedMacro04 :
    Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 1, 0, 0, 0]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 1, 0, 0, 0]) := by
    exact displayedBackward Rank001.law01
      (show Rank001.law01 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  exact edge00

private theorem guardedMacro05 :
    Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 1, 0, 1, 1]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 1, 0, 1, 1]) := by
    exact displayedForward Rank001.law14
      (show Rank001.law14 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  exact edge00

private theorem guardedMacro06 :
    Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 1, 1, 0, 1]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 1, 1, 0, 1]) := by
    exact displayedForward Rank001.law13
      (show Rank001.law13 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  exact edge00

private theorem guardedMacro07 :
    Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 1, 1, 1, 0]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 1, 1, 1, 0]) := by
    exact displayedForward Rank001.law12
      (show Rank001.law12 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  exact edge00

private theorem guardedMacro08 :
    Derives targetBasis (word 3 [0, 1, 0]) (word 3 [1, 0, 0, 1, 1]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 0, 1, 1, 1]) := by
    exact displayedForward Rank001.law15
      (show Rank001.law15 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  have edge01 :
      Derives targetBasis (word 3 [0, 0, 1, 1, 1]) (word 3 [1, 0, 0, 1, 1]) := by
    exact displayedForward Rank001.law07
      (show Rank001.law07 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 0 []) (word 3 []))
      none (some (word 1 []))
  exact edge00.trans edge01

private theorem guardedMacro09 :
    Derives targetBasis (word 3 [0, 1, 0]) (word 3 [1, 0, 1, 0, 1]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 1, 1, 0, 1]) := by
    exact displayedForward Rank001.law13
      (show Rank001.law13 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  have edge01 :
      Derives targetBasis (word 3 [0, 1, 1, 0, 1]) (word 3 [1, 1, 0, 0, 1]) := by
    exact displayedBackward Rank001.law07
      (show Rank001.law07 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 3 []))
      none (some (word 1 []))
  have edge02 :
      Derives targetBasis (word 3 [1, 1, 0, 0, 1]) (word 3 [1, 0, 1, 0, 1]) := by
    exact displayedForward Rank001.law05
      (show Rank001.law05 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) (some (word 1 []))
  exact edge00.trans (edge01.trans edge02)

private theorem guardedMacro10 :
    Derives targetBasis (word 3 [0, 1, 0]) (word 3 [1, 0, 1, 1, 0]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 0, 1, 0, 0]) := by
    exact displayedBackward Rank001.law03
      (show Rank001.law03 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  have edge01 :
      Derives targetBasis (word 3 [0, 0, 1, 0, 0]) (word 3 [1, 0, 1, 1, 0]) := by
    exact displayedBackward Rank001.law04
      (show Rank001.law04 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 0 []) (word 3 []))
      none (some (word 0 []))
  exact edge00.trans edge01

private theorem guardedMacro11 :
    Derives targetBasis (word 3 [0, 1, 0]) (word 3 [1, 1, 0, 0, 1]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 1, 1, 0, 1]) := by
    exact displayedForward Rank001.law13
      (show Rank001.law13 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  have edge01 :
      Derives targetBasis (word 3 [0, 1, 1, 0, 1]) (word 3 [1, 1, 0, 0, 1]) := by
    exact displayedBackward Rank001.law07
      (show Rank001.law07 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 3 []))
      none (some (word 1 []))
  exact edge00.trans edge01

private theorem guardedMacro12 :
    Derives targetBasis (word 3 [0, 1, 0]) (word 3 [1, 1, 0, 1, 0]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 1, 0, 0, 0]) := by
    exact displayedBackward Rank001.law01
      (show Rank001.law01 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  have edge01 :
      Derives targetBasis (word 3 [0, 1, 0, 0, 0]) (word 3 [1, 1, 0, 1, 0]) := by
    exact displayedForward Rank001.law04
      (show Rank001.law04 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 3 []))
      none (some (word 0 []))
  exact edge00.trans edge01

private theorem guardedMacro13 :
    Derives targetBasis (word 3 [0, 1, 0]) (word 3 [1, 1, 1, 0, 0]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 0]) (word 3 [0, 1, 0, 0, 0]) := by
    exact displayedBackward Rank001.law01
      (show Rank001.law01 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  have edge01 :
      Derives targetBasis (word 3 [0, 1, 0, 0, 0]) (word 3 [1, 1, 0, 1, 0]) := by
    exact displayedForward Rank001.law04
      (show Rank001.law04 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 3 []))
      none (some (word 0 []))
  have edge02 :
      Derives targetBasis (word 3 [1, 1, 0, 1, 0]) (word 3 [1, 1, 1, 0, 0]) := by
    exact displayedBackward Rank001.law05
      (show Rank001.law05 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [1])) none
  exact edge00.trans (edge01.trans edge02)

private theorem guardedMacro14 :
    Derives targetBasis (word 3 [0, 0, 1, 0]) (word 3 [0, 1, 0, 0]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 0, 1, 0]) (word 3 [0, 1, 0, 0]) := by
    exact displayedBackward Rank001.law02
      (show Rank001.law02 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  exact edge00

private theorem guardedMacro15 :
    Derives targetBasis (word 3 [0, 0, 1, 0]) (word 3 [1, 0, 1, 1]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 0, 1, 0]) (word 3 [1, 0, 1, 1]) := by
    exact displayedBackward Rank001.law04
      (show Rank001.law04 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 0 []) (word 3 []))
      none none
  exact edge00

private theorem guardedMacro16 :
    Derives targetBasis (word 3 [0, 0, 1, 1]) (word 3 [0, 1, 0, 1]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 0, 1, 1]) (word 3 [0, 1, 0, 1]) := by
    exact displayedForward Rank001.law05
      (show Rank001.law05 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 0 []) (word 2 []))
      (some (word 3 [])) none
  exact edge00

private theorem guardedMacro17 :
    Derives targetBasis (word 3 [0, 0, 1, 1]) (word 3 [0, 1, 1, 0]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 0, 1, 1]) (word 3 [0, 1, 1, 0]) := by
    exact displayedForward Rank001.law06
      (show Rank001.law06 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 0 []) (word 2 []))
      (some (word 3 [])) none
  exact edge00

private theorem guardedMacro18 :
    Derives targetBasis (word 3 [0, 0, 1, 1]) (word 3 [1, 0, 0, 1]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 0, 1, 1]) (word 3 [1, 0, 0, 1]) := by
    exact displayedForward Rank001.law07
      (show Rank001.law07 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 0 []) (word 3 []))
      none none
  exact edge00

private theorem guardedMacro19 :
    Derives targetBasis (word 3 [0, 1, 2, 0]) (word 3 [0, 2, 1, 0]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 1, 2, 0]) (word 3 [0, 2, 1, 0]) := by
    exact displayedForward Rank001.law16
      (show Rank001.law16 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 2 []) (word 1 []))
      (some (word 3 [])) none
  exact edge00

private theorem guardedMacro20 :
    Derives targetBasis (word 3 [0, 0, 1, 2, 0]) (word 3 [1, 0, 1, 2, 1]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 0, 1, 2, 0]) (word 3 [1, 2, 0, 1, 2, 1, 2]) := by
    exact displayedBackward Rank001.law04
      (show Rank001.law04 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 [2]) (word 0 []) (word 3 []))
      none none
  have edge01 :
      Derives targetBasis (word 3 [1, 2, 0, 1, 2, 1, 2]) (word 3 [1, 0, 2, 1, 2, 1, 2]) := by
    exact displayedForward Rank001.law16
      (show Rank001.law16 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 0 []) (word 2 []))
      (some (word 3 [])) (some (word 2 [1, 2]))
  have edge02 :
      Derives targetBasis (word 3 [1, 0, 2, 1, 2, 1, 2]) (word 3 [1, 0, 1, 2, 2, 1, 2]) := by
    exact displayedBackward Rank001.law08
      (show Rank001.law08 ∈ Rank001.basis by decide)
      (instantiateThree (word 2 []) (word 1 []) (word 0 []))
      (some (word 3 [])) (some (word 1 [2]))
  have edge03 :
      Derives targetBasis (word 3 [1, 0, 1, 2, 2, 1, 2]) (word 3 [1, 0, 1, 2, 1]) := by
    exact displayedBackward Rank001.law13
      (show Rank001.law13 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 2 []) (word 2 []))
      (some (word 3 [1, 0])) none
  exact edge00.trans (edge01.trans (edge02.trans edge03))

private theorem guardedMacro21 :
    Derives targetBasis (word 3 [0, 0, 1, 2, 1]) (word 3 [0, 1, 0, 2, 1]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 0, 1, 2, 1]) (word 3 [0, 2, 0, 1, 1]) := by
    exact displayedBackward Rank001.law09
      (show Rank001.law09 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 0 []) (word 2 []))
      (some (word 3 [])) none
  have edge01 :
      Derives targetBasis (word 3 [0, 2, 0, 1, 1]) (word 3 [0, 2, 1, 0, 1]) := by
    exact displayedForward Rank001.law08
      (show Rank001.law08 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 0 []) (word 2 []))
      (some (word 3 [])) none
  have edge02 :
      Derives targetBasis (word 3 [0, 2, 1, 0, 1]) (word 3 [0, 1, 2, 0, 1]) := by
    exact displayedBackward Rank001.law16
      (show Rank001.law16 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 2 []) (word 1 []))
      (some (word 3 [])) (some (word 1 []))
  have edge03 :
      Derives targetBasis (word 3 [0, 1, 2, 0, 1]) (word 3 [0, 1, 0, 2, 1]) := by
    exact displayedBackward Rank001.law16
      (show Rank001.law16 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 2 []) (word 0 []))
      (some (word 3 [0])) none
  exact edge00.trans (edge01.trans (edge02.trans edge03))

private theorem guardedMacro22 :
    Derives targetBasis (word 3 [0, 0, 1, 2, 1]) (word 3 [0, 1, 1, 2, 0]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 0, 1, 2, 1]) (word 3 [0, 2, 0, 1, 1]) := by
    exact displayedBackward Rank001.law09
      (show Rank001.law09 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 0 []) (word 2 []))
      (some (word 3 [])) none
  have edge01 :
      Derives targetBasis (word 3 [0, 2, 0, 1, 1]) (word 3 [0, 2, 1, 1, 0]) := by
    exact displayedForward Rank001.law10
      (show Rank001.law10 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 0 []) (word 2 []))
      (some (word 3 [])) none
  have edge02 :
      Derives targetBasis (word 3 [0, 2, 1, 1, 0]) (word 3 [0, 1, 1, 2, 0]) := by
    exact displayedBackward Rank001.law16
      (show Rank001.law16 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 2 []) (word 1 [1]))
      (some (word 3 [])) none
  exact edge00.trans (edge01.trans edge02)

private theorem guardedMacro23 :
    Derives targetBasis (word 3 [0, 0, 1, 2, 1]) (word 3 [0, 2, 0, 1, 1]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 0, 1, 2, 1]) (word 3 [0, 2, 0, 1, 1]) := by
    exact displayedBackward Rank001.law09
      (show Rank001.law09 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 0 []) (word 2 []))
      (some (word 3 [])) none
  exact edge00

private theorem guardedMacro24 :
    Derives targetBasis (word 3 [0, 0, 1, 2, 1]) (word 3 [1, 0, 0, 2, 1]) := by
  have edge00 :
      Derives targetBasis (word 3 [0, 0, 1, 2, 1]) (word 3 [0, 0, 1, 1, 2, 1, 1]) := by
    exact displayedBackward Rank001.law03
      (show Rank001.law03 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 2 []) (word 2 []))
      (some (word 3 [0, 0])) none
  have edge01 :
      Derives targetBasis (word 3 [0, 0, 1, 1, 2, 1, 1]) (word 3 [1, 0, 0, 1, 2, 1, 1]) := by
    exact displayedForward Rank001.law07
      (show Rank001.law07 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 0 []) (word 3 []))
      none (some (word 2 [1, 1]))
  have edge02 :
      Derives targetBasis (word 3 [1, 0, 0, 1, 2, 1, 1]) (word 3 [1, 1, 2, 0, 0, 1, 1]) := by
    exact displayedForward Rank001.law16
      (show Rank001.law16 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 1 [2]) (word 0 [0]))
      (some (word 3 [])) (some (word 1 []))
  have edge03 :
      Derives targetBasis (word 3 [1, 1, 2, 0, 0, 1, 1]) (word 3 [1, 1, 2, 1, 1, 0, 0]) := by
    exact displayedBackward Rank001.law10
      (show Rank001.law10 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 [1]) (word 2 []))
      (some (word 3 [])) none
  have edge04 :
      Derives targetBasis (word 3 [1, 1, 2, 1, 1, 0, 0]) (word 3 [1, 2, 1, 0, 0]) := by
    exact displayedForward Rank001.law03
      (show Rank001.law03 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 2 []) (word 2 []))
      (some (word 3 [])) (some (word 0 [0]))
  have edge05 :
      Derives targetBasis (word 3 [1, 2, 1, 0, 0]) (word 3 [1, 2, 0, 0, 1]) := by
    exact displayedForward Rank001.law10
      (show Rank001.law10 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 []))
      (some (word 3 [])) none
  have edge06 :
      Derives targetBasis (word 3 [1, 2, 0, 0, 1]) (word 3 [1, 0, 0, 2, 1]) := by
    exact displayedBackward Rank001.law16
      (show Rank001.law16 ∈ Rank001.basis by decide)
      (instantiateThree (word 1 []) (word 2 []) (word 0 [0]))
      (some (word 3 [])) none
  exact edge00.trans
    (edge01.trans (edge02.trans (edge03.trans (edge04.trans (edge05.trans edge06)))))

private def guardedSubstitution
    (guard : Word Nat) (substitution : Nat → Word Nat) : Nat → Word Nat
  | 0 => substitution 0
  | 1 => substitution 1
  | 2 => substitution 2
  | 3 => guard
  | letter + 4 => substitution (letter + 4)

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (source : Word Nat) (first second : Nat → Word Nat) :
    (source.bind first).bind second =
      source.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem liftGuardedIdentity
    (identity : Identity Nat)
    (macroDerivation :
      Derives targetBasis
        (Word.singleton 3 ++ identity.lhs)
        (Word.singleton 3 ++ identity.rhs))
    (guard : Word Nat) (substitution : Nat → Word Nat)
    (leftAgreement :
      identity.lhs.bind (guardedSubstitution guard substitution) =
        identity.lhs.bind substitution)
    (rightAgreement :
      identity.rhs.bind (guardedSubstitution guard substitution) =
        identity.rhs.bind substitution) :
    Derives targetBasis
      (guard ++ identity.lhs.bind substitution)
      (guard ++ identity.rhs.bind substitution) := by
  have lifted :=
    Derives.subst macroDerivation (guardedSubstitution guard substitution)
  rw [bind_append, bind_append] at lifted
  change
    Derives targetBasis
      (guard ++ identity.lhs.bind (guardedSubstitution guard substitution))
      (guard ++ identity.rhs.bind (guardedSubstitution guard substitution))
    at lifted
  rw [leftAgreement, rightAgreement] at lifted
  exact lifted

/-- Replay the complete twenty-five-law separator/parity derivation behind
an arbitrary protected nonempty prefix and arbitrary nonempty substitution. -/
theorem liftS5_441UnderPrefix
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_441.basis left right)
    (guard : Word Nat) (substitution : Nat → Word Nat) :
    Derives targetBasis
      (guard ++ left.bind substitution)
      (guard ++ right.bind substitution) := by
  induction derivation generalizing guard substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_441.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact liftGuardedIdentity S5_441.powerLaw
          guardedMacro00 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyxXXXYXLaw
          guardedMacro01 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyxXXYXXLaw
          guardedMacro02 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyxXXYYYLaw
          guardedMacro03 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyxXYXXXLaw
          guardedMacro04 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyxXYXYYLaw
          guardedMacro05 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyxXYYXYLaw
          guardedMacro06 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyxXYYYXLaw
          guardedMacro07 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyxYXXYYLaw
          guardedMacro08 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyxYXYXYLaw
          guardedMacro09 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyxYXYYXLaw
          guardedMacro10 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyxYYXXYLaw
          guardedMacro11 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyxYYXYXLaw
          guardedMacro12 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyxYYYXXLaw
          guardedMacro13 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xxyxXYXXLaw
          guardedMacro14 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xxyxYXYYLaw
          guardedMacro15 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xxyyXYXYLaw
          guardedMacro16 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xxyyXYYXLaw
          guardedMacro17 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xxyyYXXYLaw
          guardedMacro18 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xyzxXZYXLaw
          guardedMacro19 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xxyzxYXYZYLaw
          guardedMacro20 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xxyzyXYXZYLaw
          guardedMacro21 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xxyzyXYYZXLaw
          guardedMacro22 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xxyzyXZXYYLaw
          guardedMacro23 guard substitution (by rfl) (by rfl)
      · exact liftGuardedIdentity S5_441.xxyzyYXXZYLaw
          guardedMacro24 guard substitution (by rfl) (by rfl)
  | refl => exact Derives.refl _
  | symm _ hypothesis => exact (hypothesis guard substitution).symm
  | trans _ _ first second =>
      exact (first guard substitution).trans (second guard substitution)
  | prepend front _ hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        hypothesis (guard ++ front.bind substitution) substitution
  | appendRight _ suffix hypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (hypothesis guard substitution) (suffix.bind substitution)
  | subst _ first hypothesis =>
      simpa [bind_bind] using
        hypothesis guard (fun letter => (first letter).bind substitution)

/-- The frozen reversed power law adds precisely two copies of a block. -/
theorem derivesPowerExpansion (block : Word Nat) :
    Derives targetBasis
      (block ++ block)
      (((block ++ block) ++ block) ++ block) := by
  have primitive :
      Derives targetBasis (word 0 [0]) (word 0 [0, 0, 0]) :=
    displayedForward Rank001.law00
      (show Rank001.law00 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 [])) none none
  have substituted := Derives.subst primitive
    (instantiateThree block block block)
  simpa [word, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The frozen reversed endpoint law adds two copies before a returning head. -/
theorem derivesTripleInitialExpansion
    (first middle : Word Nat) :
    Derives targetBasis
      ((first ++ middle) ++ first)
      ((((first ++ first) ++ first) ++ middle) ++ first) := by
  have primitive :
      Derives targetBasis (word 0 [1, 0]) (word 0 [0, 0, 1, 0]) :=
    displayedForward Rank001.law11
      (show Rank001.law11 ∈ Rank001.basis by decide)
      (instantiateThree (word 0 []) (word 1 []) (word 2 [])) none none
  have substituted := Derives.subst primitive
    (instantiateThree first middle middle)
  simpa [word, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_796Opposite
