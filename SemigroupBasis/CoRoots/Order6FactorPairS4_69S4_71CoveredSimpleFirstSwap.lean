import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71GlueMoves

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis

/-!
# Covered simple/first crossings

The event dispatcher invokes an adjacent simple/first crossing only after it
has found a multiple guard covering the site.  This module proves the
constructive direction needed by that branch.  It does not claim that an
arbitrary simple/first exchange is derivable or prove the converse guard
extraction theorem.
-/

/-- The laws 10--14 orbit contains the guarded block exchange

`g s a g a = g a s g a`.

The explicit two-step chain is reversed law 10 followed by law 12:

`g s a g a -> g s g a a -> g a s g a`.

All three arguments are arbitrary nonempty words, so this theorem is
width-free. -/
theorem derivesCoveredSimpleFirstOrbit
    (g s a : Word Nat) :
    Derives basis
      ((((g ++ s) ++ a) ++ g) ++ a)
      ((((g ++ a) ++ s) ++ g) ++ a) :=
  (derivesLaw10 g s a).symm.trans
    (derivesLaw12 g s a)

private theorem listDerivesCoveredSimpleFirstOrbit
    (g s a : Nat) :
    ListDerives
      [g, s, a, g, a]
      [g, a, s, g, a] := by
  exact S5_107.ListDerives.words <| by
    simpa [Word.singleton, Word.append, List.append_assoc] using
      derivesCoveredSimpleFirstOrbit
        (Word.singleton g)
        (Word.singleton s)
        (Word.singleton a)

/-- Dispatcher-facing covered crossing.

Suppose the adjacent site is `s, a`, the letter `g` occurs on both sides of
the site, and `a` has a later occurrence.  Then the exact 14-law basis derives
the exchange to `a, s`.

The proof temporarily duplicates `a`, inserts two copies of `g`, applies the
two-step laws 10/12 orbit above, and deletes the temporary copies.  The three
membership hypotheses are a sufficient local contract: there is no support,
word-length, or multiplicity bound in the statement. -/
theorem listDerivesCoveredSimpleFirstSwap
    (initial suffix : List Nat) (g s a : Nat)
    (guardPast : g ∈ initial)
    (guardFuture : g ∈ suffix)
    (aFuture : a ∈ suffix) :
    ListDerives
      (initial ++ s :: a :: suffix)
      (initial ++ a :: s :: suffix) := by
  have expandA :
      ListDerives
        (initial ++ s :: a :: suffix)
        (initial ++ s :: a :: a :: suffix) := by
    have core :=
      (listDerivesDeleteCurrent
        (initial ++ [s, a]) suffix a (by simp) aFuture).symm
    simpa [List.append_assoc] using core
  have insertFirstGuard :
      ListDerives
        (initial ++ s :: a :: a :: suffix)
        (initial ++ g :: s :: a :: a :: suffix) := by
    have future : g ∈ s :: a :: a :: suffix := by
      simp [guardFuture]
    have core :=
      (listDerivesDeleteCurrent
        initial (s :: a :: a :: suffix) g guardPast future).symm
    simpa [List.append_assoc] using core
  have insertSecondGuard :
      ListDerives
        (initial ++ g :: s :: a :: a :: suffix)
        (initial ++ g :: s :: a :: g :: a :: suffix) := by
    have past : g ∈ initial ++ [g, s, a] := by
      simp
    have future : g ∈ a :: suffix := by
      simp [guardFuture]
    have core :=
      (listDerivesDeleteCurrent
        (initial ++ [g, s, a]) (a :: suffix) g past future).symm
    simpa [List.append_assoc] using core
  have cross :
      ListDerives
        (initial ++ g :: s :: a :: g :: a :: suffix)
        (initial ++ g :: a :: s :: g :: a :: suffix) := by
    simpa [List.append_assoc] using
      (listDerivesCoveredSimpleFirstOrbit g s a).context initial suffix
  have deleteFirstGuard :
      ListDerives
        (initial ++ g :: a :: s :: g :: a :: suffix)
        (initial ++ a :: s :: g :: a :: suffix) := by
    have future : g ∈ a :: s :: g :: a :: suffix := by
      simp
    have core :=
      listDerivesDeleteCurrent
        initial (a :: s :: g :: a :: suffix) g guardPast future
    simpa [List.append_assoc] using core
  have deleteSecondGuard :
      ListDerives
        (initial ++ a :: s :: g :: a :: suffix)
        (initial ++ a :: s :: a :: suffix) := by
    have past : g ∈ initial ++ [a, s] :=
      List.mem_append_left [a, s] guardPast
    have future : g ∈ a :: suffix := by
      simp [guardFuture]
    have core :=
      listDerivesDeleteCurrent
        (initial ++ [a, s]) (a :: suffix) g past future
    simpa [List.append_assoc] using core
  have deleteA :
      ListDerives
        (initial ++ a :: s :: a :: suffix)
        (initial ++ a :: s :: suffix) := by
    have past : a ∈ initial ++ [a, s] := by
      simp
    have core :=
      listDerivesDeleteCurrent
        (initial ++ [a, s]) suffix a past aFuture
    simpa [List.append_assoc] using core
  exact
    expandA.trans <|
      insertFirstGuard.trans <|
        insertSecondGuard.trans <|
          cross.trans <|
            deleteFirstGuard.trans <|
              deleteSecondGuard.trans deleteA

/-- The same covered exchange in the reverse orientation. -/
theorem listDerivesCoveredFirstSimpleSwap
    (initial suffix : List Nat) (g s a : Nat)
    (guardPast : g ∈ initial)
    (guardFuture : g ∈ suffix)
    (aFuture : a ∈ suffix) :
    ListDerives
      (initial ++ a :: s :: suffix)
      (initial ++ s :: a :: suffix) :=
  (listDerivesCoveredSimpleFirstSwap
    initial suffix g s a guardPast guardFuture aFuture).symm

/-- Explicit `A g B s a C g D` form of the covered crossing.  The final
hypothesis records that the second occurrence of `a` lies in the guarded
suffix `C g D`. -/
theorem listDerivesCoveredSimpleFirstSwapInContext
    (A B C D : List Nat) (g s a : Nat)
    (aFuture : a ∈ C ++ g :: D) :
    ListDerives
      (A ++ g :: (B ++ s :: a :: (C ++ g :: D)))
      (A ++ g :: (B ++ a :: s :: (C ++ g :: D))) := by
  have core :=
    listDerivesCoveredSimpleFirstSwap
      (A ++ g :: B) (C ++ g :: D) g s a
      (by simp) (by simp) aFuture
  simpa [List.append_assoc] using core

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71
