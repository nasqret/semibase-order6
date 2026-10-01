import SemigroupBasis.CoRoots.Order6L3RootS3_15S4_12.Blocks
import SemigroupBasis.Examples.CommutativeParityThree

/-!
# L3 light root `S3_15 / S4_12`: frozen derivation macros

The inclusive pre-freeze battery records that every long oracle class is
classified by head, support, and coordinate parity.  This layer realizes that
classifier syntactically.  Two copies of the fixed head are inserted around a
long word; behind those markers the ordinary commutative-parity calculus can
be replayed using only displayed laws five, nine, and ten.
-/

namespace SemigroupBasis.CoRoots.Order6L3RootS3_15S4_12

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def instantiateThreeWords
    (u v q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => q
  | n + 3 => Word.singleton (n + 3)

/-- Swap two arbitrary nonempty blocks behind a fixed nonempty prefix. -/
theorem derivesSuffixSwap (pre u v : Word Nat) :
    Derives basis ((pre ++ u) ++ v) ((pre ++ v) ++ u) := by
  have base :
      Derives basis (w 0 [1, 2]) (w 0 [2, 1]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [1, 2]) (w 0 [2, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords pre u v)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Insert two copies of the first block in a product of three nonempty
blocks.  This is displayed law five, used in the expanding direction. -/
theorem derivesLongInsertion (u v q : Word Nat) :
    Derives basis ((u ++ v) ++ q)
      ((((u ++ u) ++ u) ++ v) ++ q) := by
  have base :
      Derives basis (w 0 [1, 2]) (w 0 [0, 0, 1, 2]) :=
    Derives.symm <|
      Derives.fromBasis
        (e := Identity.mk (w 0 [0, 0, 1, 2]) (w 0 [1, 2]))
        (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v q)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Insert two copies of a middle block while retaining nonempty blocks on
both sides.  This is displayed law nine in the expanding direction. -/
theorem derivesMiddleTripleExpansion (pre u post : Word Nat) :
    Derives basis ((pre ++ u) ++ post)
      ((((pre ++ u) ++ u) ++ u) ++ post) := by
  have base :
      Derives basis (w 0 [1, 2]) (w 0 [1, 1, 1, 2]) :=
    Derives.symm <|
      Derives.fromBasis
        (e := Identity.mk (w 0 [1, 1, 1, 2]) (w 0 [1, 2]))
        (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords pre u post)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The parity power step `u = u³` is available after two protected
nonempty marker blocks. -/
theorem derivesContextPower (a b u : Word Nat) :
    Derives basis ((a ++ b) ++ u)
      ((a ++ b) ++ ((u ++ u) ++ u)) := by
  have enter := derivesSuffixSwap a b u
  have expand := derivesMiddleTripleExpansion a u b
  have moveOne :=
    derivesSuffixSwap ((a ++ u) ++ u) u b
  have moveTwo :=
    Derives.appendRight (derivesSuffixSwap (a ++ u) u b) u
  have moveThree :=
    Derives.appendRight (derivesSuffixSwap a u b) (u ++ u)
  exact Derives.trans
    (by simpa [Word.append_assoc] using enter) <|
    Derives.trans
      (by simpa [Word.append_assoc] using expand) <|
      Derives.trans
        (by simpa [Word.append_assoc] using moveOne) <|
        Derives.trans
          (by simpa [Word.append_assoc] using moveTwo)
          (by simpa [Word.append_assoc] using moveThree)

private theorem bind_append (u v : Word Nat) (σ : Nat → Word Nat) :
    (u ++ v).bind σ = u.bind σ ++ v.bind σ := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (τ σ : Nat → Word Nat) :
    (word.bind τ).bind σ =
      word.bind (fun x => (τ x).bind σ) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay `x = xxx`, `xy = yx` after two protected nonempty markers. -/
theorem liftParity
    {u v : Word Nat}
    (derivation : Derives commutativeParityBasis u v)
    (a b : Word Nat) (σ : Nat → Word Nat) :
    Derives basis
      ((a ++ b) ++ u.bind σ)
      ((a ++ b) ++ v.bind σ) := by
  induction derivation generalizing a b σ with
  | fromBasis member =>
      simp only [commutativeParityBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [parityPowerLaw, parityX, parityXXX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          derivesContextPower a b (σ 0)
      · simpa [parityCommutativityLaw, parityXY, parityYX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc]
          using derivesSuffixSwap (a ++ b) (σ 0) (σ 1)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih a b σ)
  | trans _ _ ihFirst ihSecond =>
      exact Derives.trans (ihFirst a b σ) (ihSecond a b σ)
  | prepend pre _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih a (b ++ pre.bind σ) σ
  | appendRight _ post ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (ih a b σ) (post.bind σ)
  | subst _ τ ih =>
      simpa [bind_bind] using
        ih a b (fun x => (τ x).bind σ)

private theorem parityDerivesOfSupportParity
    (u v : Word Nat)
    (supportEq : ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parityEq : ∀ z,
      u.toList.count z % 2 = v.toList.count z % 2) :
    Derives commutativeParityBasis u v := by
  have reducedPerm :=
    positiveParityReduce_perm supportEq parityEq
  have lhsNormal := positiveParityDerivesNormal u
  have rhsNormal := positiveParityDerivesNormal v
  cases hl : positiveParityReduce u.toList with
  | nil =>
      have present :
          u.head ∈ positiveParityReduce u.toList :=
        (mem_positiveParityReduce_iff _ _).mpr
          (by simp [Word.toList])
      exact False.elim (by simpa [hl] using present)
  | cons x xs =>
      cases hr : positiveParityReduce v.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (parityDerivesPermutation
                (w x xs) (w y ys) reducedPerm)
              (Derives.symm rhsNormal)

private theorem derivesHeadExpansion
    (letter a b : Nat) (rest : List Nat) :
    Derives basis (w letter (a :: b :: rest))
      ((Word.singleton letter ++ Word.singleton letter) ++
        w letter (a :: b :: rest)) := by
  simpa [w, Word.singleton, Word.append, Word.append_assoc] using
    derivesLongInsertion
      (Word.singleton letter) (Word.singleton a) (w b rest)

/-- Long words with the same head, support, and exponent-parity vector are
derivably equal. -/
theorem derivesLongHeadSupportParity
    (u v : Word Nat)
    (uLong : 3 ≤ u.toList.length)
    (vLong : 3 ≤ v.toList.length)
    (heads : u.head = v.head)
    (supportEq : ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parityEq : ∀ z,
      u.toList.count z % 2 = v.toList.count z % 2) :
    Derives basis u v := by
  have parityDerivation :=
    parityDerivesOfSupportParity u v supportEq parityEq
  have lifted :=
    liftParity parityDerivation
      (Word.singleton u.head) (Word.singleton u.head) Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          simp only at heads
          subst vHead
          cases uTail with
          | nil =>
              simp [Word.toList] at uLong
          | cons ua uRest =>
              cases uRest with
              | nil =>
                  simp [Word.toList] at uLong
              | cons ub ur =>
                  cases vTail with
                  | nil =>
                      simp [Word.toList] at vLong
                  | cons va vRest =>
                      cases vRest with
                      | nil =>
                          simp [Word.toList] at vLong
                      | cons vb vr =>
                          have expandU :
                              Derives basis (w uHead (ua :: ub :: ur))
                                ((Word.singleton uHead ++
                                    Word.singleton uHead) ++
                                  w uHead (ua :: ub :: ur)) :=
                            derivesHeadExpansion uHead ua ub ur
                          have expandV :
                              Derives basis (w uHead (va :: vb :: vr))
                                ((Word.singleton uHead ++
                                    Word.singleton uHead) ++
                                  w uHead (va :: vb :: vr)) :=
                            derivesHeadExpansion uHead va vb vr
                          exact expandU.trans <|
                            lifted.trans (Derives.symm expandV)

end SemigroupBasis.CoRoots.Order6L3RootS3_15S4_12
