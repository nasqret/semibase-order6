import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415BrandtParityBridge
import SemigroupBasis.CoRoots.S5_415HeadNormalization

/-!
# Rank 040: parity-safe excursion replay and the necessary head retarget

The doubled power and sandwich laws support arbitrary optional-excursion
permutations and insertion of TWO extra copies of an existing excursion.
These are genuine unrestricted derivations from the frozen fifteen laws.

They do not make a fixed-head traversal canonical.  Frozen law03 already
equates xxyx with yxyy: the exact Brandt signature and all occurrence parities
agree, but the literal heads differ.  The existing normalizeBrandtWord
preserves the literal head.  Therefore neither it nor ANY head-preserving
count refinement can be the equality renderer required by the join proof.

This refutes the specified fixed-head/count-only renderer construction, not
the rank-040 basis or the existence of a more general BrandtParityLift.
The explicit arbitrary-word law03 retarget below is a valid first repair;
the unrestricted choice and realization of a common anchor remains open.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.DoubledReplayBoundary

open SemigroupBasis

abbrev anchoredGapWalk := SemigroupBasis.CoRoots.S5_415.anchoredGapWalk
abbrev SameFactorSignature := BrandtParityBridge.SameFactorSignature

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- The displayed parity-neutral switch for arbitrary nonempty blocks. -/
theorem derivesGraphSwitch (anchor first second : Word Nat) :
    Derives basis
      ((((anchor ++ first) ++ anchor) ++ second) ++ anchor)
      ((((anchor ++ second) ++ anchor) ++ first) ++ anchor) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 0, 2, 0]) (Word.mk 0 [2, 0, 1, 0]) :=
    Derives.fromBasis (e := law07) (by simp [basis])
  have substituted := Derives.subst primitive
    (instantiateThree anchor first second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Frozen law03 realizes a genuine parity-preserving change of anchor. -/
theorem derivesParityRetarget (first second : Word Nat) :
    Derives basis
      (((first ++ first) ++ second) ++ first)
      (((second ++ first) ++ second) ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 0]) (Word.mk 1 [0, 1, 1]) :=
    Derives.fromBasis (e := law03) (by simp [basis])
  have substituted := Derives.subst primitive
    (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The same anchor change is available inside arbitrary nonempty contexts. -/
theorem derivesContextualParityRetarget
    (leftContext first second suffix : Word Nat) :
    Derives basis
      ((leftContext ++ (((first ++ first) ++ second) ++ first)) ++ suffix)
      ((leftContext ++ (((second ++ first) ++ second) ++ second)) ++ suffix) :=
  Derives.appendRight
    (Derives.prepend leftContext (derivesParityRetarget first second)) suffix

private def gapSuffix (anchor : Word Nat) :
    Option (Word Nat) → List (Option (Word Nat)) → Word Nat
  | none, rest => anchoredGapWalk anchor rest
  | some excursion, rest => excursion ++ anchoredGapWalk anchor rest

/-- Optional excursions commute, including empty excursions. -/
theorem derivesGapBaseSwap
    (anchor : Word Nat) (first second : Option (Word Nat)) :
    Derives basis
      (anchoredGapWalk anchor [first, second])
      (anchoredGapWalk anchor [second, first]) := by
  cases first with
  | none =>
      cases second with
      | none => exact Derives.refl _
      | some excursion =>
          simpa [anchoredGapWalk, S5_415.anchoredGapWalk, Word.append_assoc] using
            (BrandtParityBridge.derivesSandwichMiddleSwitch anchor excursion).symm
  | some excursion =>
      cases second with
      | none =>
          simpa [anchoredGapWalk, S5_415.anchoredGapWalk, Word.append_assoc] using
            BrandtParityBridge.derivesSandwichMiddleSwitch anchor excursion
      | some other =>
          simpa [anchoredGapWalk, S5_415.anchoredGapWalk, Word.append_assoc] using
            derivesGraphSwitch anchor excursion other

/-- A parity-neutral adjacent swap survives an arbitrary list suffix. -/
theorem derivesGapAdjacentSwap
    (anchor : Word Nat) (first second : Option (Word Nat))
    (suffix : List (Option (Word Nat))) :
    Derives basis
      (anchoredGapWalk anchor (first :: second :: suffix))
      (anchoredGapWalk anchor (second :: first :: suffix)) := by
  cases suffix with
  | nil => exact derivesGapBaseSwap anchor first second
  | cons next rest =>
      have swapped := Derives.appendRight
        (derivesGapBaseSwap anchor first second) (gapSuffix anchor next rest)
      cases first <;> cases second <;> cases next <;>
        simpa [anchoredGapWalk, S5_415.anchoredGapWalk, gapSuffix,
          Word.append_assoc] using swapped

/-- The doubled laws replace one optional excursion by THREE, not two. -/
theorem derivesGapTripleBase
    (anchor : Word Nat) (gap : Option (Word Nat)) :
    Derives basis
      (anchoredGapWalk anchor [gap])
      (anchoredGapWalk anchor [gap, gap, gap]) := by
  cases gap with
  | none =>
      simpa [anchoredGapWalk, S5_415.anchoredGapWalk, Word.append_assoc] using
        BrandtParityBridge.derivesPairExpansion anchor
  | some excursion =>
      simpa [anchoredGapWalk, S5_415.anchoredGapWalk, Word.append_assoc] using
        BrandtParityBridge.derivesJointSandwichExpansion anchor excursion

/-- Insert two copies of the first optional excursion before any suffix. -/
theorem derivesGapTripleHead
    (anchor : Word Nat) (gap : Option (Word Nat))
    (rest : List (Option (Word Nat))) :
    Derives basis
      (anchoredGapWalk anchor (gap :: rest))
      (anchoredGapWalk anchor (gap :: gap :: gap :: rest)) := by
  cases rest with
  | nil => exact derivesGapTripleBase anchor gap
  | cons next suffix =>
      have expanded := Derives.appendRight
        (derivesGapTripleBase anchor gap) (gapSuffix anchor next suffix)
      cases gap <;> cases next <;>
        simpa [anchoredGapWalk, S5_415.anchoredGapWalk, gapSuffix,
          Word.append_assoc] using expanded

/-- All optional-excursion permutations replay under the frozen join laws. -/
theorem derivesGapPermutation
    {source target : List (Option (Word Nat))}
    (permutation : source.Perm target) (anchor : Word Nat) :
    Derives basis
      (anchoredGapWalk anchor source) (anchoredGapWalk anchor target) := by
  induction permutation with
  | nil => exact Derives.refl _
  | cons gap _ ih =>
      cases gap with
      | none =>
          simpa [anchoredGapWalk, S5_415.anchoredGapWalk] using
            Derives.prepend anchor ih
      | some excursion =>
          simpa [anchoredGapWalk, S5_415.anchoredGapWalk] using
            Derives.prepend (anchor ++ excursion) ih
  | swap first second rest =>
      exact derivesGapAdjacentSwap anchor second first rest
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The exact counterexample is itself one frozen displayed identity. -/
theorem witnessDisplayed : Derives basis law03.lhs law03.rhs :=
  Derives.fromBasis (by simp [basis])

theorem witnessFactorSignature : SameFactorSignature law03.lhs law03.rhs :=
  BrandtParityBridge.sameFactorSignature_of_factorValid law03
    left_law03_valid right_law03_valid

theorem witnessHeadsDiffer : law03.lhs.head ≠ law03.rhs.head := by decide

/-- A concrete two-element observer detects the information wrongly retained
by a literal-head renderer.  It is NOT a model of the frozen basis. -/
def headObserver : Semigroup (Fin 2) where
  mul := fun first _ => first
  assoc := fun _ _ _ => rfl

def observerValuation : Nat → Fin 2 := fun letter =>
  if letter = 0 then 0 else 1

theorem witnessObserverValues :
    headObserver.eval observerValuation law03.lhs = 0 ∧
    headObserver.eval observerValuation law03.rhs = 1 := by decide

theorem witnessNotHeadObserverValid : ¬ law03.SatisfiedBy headObserver := by
  intro valid
  have contradiction := valid observerValuation
  have values := witnessObserverValues
  rw [values.1, values.2] at contradiction
  exact (by decide : (0 : Fin 2) ≠ 1) contradiction

def PreservesLiteralHead (render : Word Nat → Word Nat) : Prop :=
  ∀ word, (render word).head = word.head

def EqualOnFactorSignature (render : Word Nat → Word Nat) : Prop :=
  ∀ left right, SameFactorSignature left right → render left = render right

/-- No head-preserving renderer can identify all valid pairs of this join. -/
theorem noHeadPreservingSignatureRenderer
    (render : Word Nat → Word Nat) (heads : PreservesLiteralHead render) :
    ¬ EqualOnFactorSignature render := by
  intro equality
  have equalHeads := congrArg Word.head
    (equality law03.lhs law03.rhs witnessFactorSignature)
  rw [heads law03.lhs, heads law03.rhs] at equalHeads
  exact witnessHeadsDiffer equalHeads

/-- The actual existing recursive Brandt normalizer fails equality on this
specific pair, despite its complete semantic signature and parity agreement. -/
theorem actualLowerNormalizerWitnessUnequal :
    S5_415.normalizeBrandtWord law03.lhs ≠
      S5_415.normalizeBrandtWord law03.rhs := by
  intro equality
  have equalHeads := congrArg Word.head equality
  apply witnessHeadsDiffer
  simpa only [S5_415.normalizeBrandtWord_head] using equalHeads

/-- Its recursive traversal alone is not a canonical equality renderer. -/
theorem actualLowerNormalizerNotSignatureRenderer :
    ¬ EqualOnFactorSignature S5_415.normalizeBrandtWord :=
  noHeadPreservingSignatureRenderer _ S5_415.normalizeBrandtWord_head

/-- ANY subsequent count-only repair that leaves the head in place still
fails.  No particular parity-capping algorithm is assumed or guessed. -/
theorem headPreservingCountRefinementRefuted
    (refineCounts : Word Nat → Word Nat)
    (heads : PreservesLiteralHead refineCounts) :
    ¬ EqualOnFactorSignature (fun word =>
      refineCounts (S5_415.normalizeBrandtWord word)) := by
  apply noHeadPreservingSignatureRenderer
  intro word
  exact (heads _).trans (S5_415.normalizeBrandtWord_head word)

/-- Any genuine join normalizer must abandon literal-head preservation. -/
theorem anyJoinNormalizerMustRetarget
    (normalizer : IntersectionNormalizer leftTable.semigroup
      rightTable.semigroup basis) :
    ¬ PreservesLiteralHead normalizer.normal := by
  intro heads
  have equalHeads := congrArg Word.head
    (normalizer.normal_eq_of_factor_valid law03
      left_law03_valid right_law03_valid)
  rw [heads law03.lhs, heads law03.rhs] at equalHeads
  exact witnessHeadsDiffer equalHeads

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.DoubledReplayBoundary
