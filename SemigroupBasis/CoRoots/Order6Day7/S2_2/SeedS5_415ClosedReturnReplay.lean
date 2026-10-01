import SemigroupBasis.ChainReplay
import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415CanonicalHead

/-!
# Rank040: actual doubled-loop composition and excursion replay

Eight separately checked frozen-law edges establish the GUARDED product
identity x²y² = (xy)²x²y² and the cross-head insertion xxyx = y²xxyx.
Neither asserts the false unrestricted law (xy)² = x²y².

These identities prove closure of genuine square-prefix absorption under
products, word derivations, and suffixes. Every loop generated from the
actual head excursions is then absorbed; when an empty head excursion is
present, the bare nonempty excursions are generators too, allowing a real
change of literal head. All conclusions are Derives from the frozen basis.

This is not the complete ClosedReturnDerivation theorem. A closed walk's
tail need not itself be closed at the ORIGINAL initial component: xy is a
closed return for xyx, but y is not. The actual matrix units witness why a
class-walk induction needs an open-path, endpoint-indexed hypothesis.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.ClosedReturnReplay

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415

private def fixedStep (lawIndex : Nat) (direction : ChainReplay.Direction)
    (leftContext rightContext : List Nat) (substitution : List (List Nat)) :
    ChainReplay.Chain Nat :=
  [{lawIndex, direction, leftContext, rightContext, substitution}]

theorem productGuardEdge0 :
    Derives Rank040.basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [0, 0, 0, 1, 1]) :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 0 .forward [] [1, 1] [[0], [0], [0]]) (by decide)

theorem productGuardEdge1 :
    Derives Rank040.basis (Word.mk 0 [0, 0, 0, 1, 1])
      (Word.mk 0 [0, 0, 0, 1, 1, 1, 1]) :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 0 .forward [0, 0, 0, 0] [] [[1], [0], [0]]) (by decide)

theorem productGuardEdge2 :
    Derives Rank040.basis (Word.mk 0 [0, 0, 0, 1, 1, 1, 1])
      (Word.mk 0 [0, 0, 1, 1, 0, 1, 1]) :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 4 .forward [0, 0] [1, 1] [[0], [1], [0]]) (by decide)

theorem productGuardEdge3 :
    Derives Rank040.basis (Word.mk 0 [0, 0, 1, 1, 0, 1, 1])
      (Word.mk 0 [1, 0, 0, 1, 0, 1, 1]) :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 5 .forward [0] [0, 1, 1] [[0], [1], [0]]) (by decide)

theorem productGuardEdge4 :
    Derives Rank040.basis (Word.mk 0 [1, 0, 0, 1, 0, 1, 1])
      (Word.mk 0 [1, 0, 1, 0, 0, 1, 1]) :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 2 .forward [0, 1] [1, 1] [[0], [1], [0]]) (by decide)

theorem crossHeadEdge0 :
    Derives Rank040.basis (Word.mk 0 [0, 1, 0]) (Word.mk 0 [0, 0, 0, 1, 0]) :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 0 .forward [] [1, 0] [[0], [0], [0]]) (by decide)

theorem crossHeadEdge1 :
    Derives Rank040.basis (Word.mk 0 [0, 0, 0, 1, 0]) (Word.mk 0 [0, 1, 1, 1, 0]) :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 1 .forward [0] [] [[0], [1], [0]]) (by decide)

theorem crossHeadEdge2 :
    Derives Rank040.basis (Word.mk 0 [0, 1, 1, 1, 0]) (Word.mk 1 [1, 0, 0, 1, 0]) :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := fixedStep 6 .forward [] [0] [[0], [1], [1]]) (by decide)

theorem guardedProductPrimitive :
    Derives Rank040.basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 0, 1, 0, 0, 1, 1]) :=
  productGuardEdge0.trans (productGuardEdge1.trans
    (productGuardEdge2.trans (productGuardEdge3.trans productGuardEdge4)))

theorem crossHeadPrimitive :
    Derives Rank040.basis (Word.mk 0 [0, 1, 0]) (Word.mk 1 [1, 0, 0, 1, 0]) :=
  crossHeadEdge0.trans (crossHeadEdge1.trans crossHeadEdge2)

private def instantiateTwo (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | n + 2 => Word.singleton (n + 2)

/-- Product-square insertion is valid behind the two genuinely exposed squares. -/
theorem derivesGuardedProductSquare (first second : Word Nat) :
    Derives Rank040.basis ((first ++ first) ++ (second ++ second))
      (((first ++ second) ++ (first ++ second)) ++
        ((first ++ first) ++ (second ++ second))) := by
  have substituted := Derives.subst guardedProductPrimitive (instantiateTwo first second)
  simpa [instantiateTwo, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

/-- A real head-changing square insertion, for arbitrary nonempty blocks. -/
theorem derivesCrossHeadSquarePrefix (first second : Word Nat) :
    Derives Rank040.basis (((first ++ first) ++ second) ++ first)
      ((second ++ second) ++ (((first ++ first) ++ second) ++ first)) := by
  have substituted := Derives.subst crossHeadPrimitive (instantiateTwo first second)
  simpa [instantiateTwo, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

def SquareAbsorbs (word loop : Word Nat) : Prop :=
  Derives Rank040.basis word ((loop ++ loop) ++ word)

theorem SquareAbsorbs.ofDerives
    {source target loop : Word Nat} (equivalent : Derives Rank040.basis source target)
    (absorbs : SquareAbsorbs target loop) : SquareAbsorbs source loop :=
  equivalent.trans (Derives.trans absorbs (Derives.prepend (loop ++ loop) equivalent.symm))

theorem SquareAbsorbs.loopCongruence
    {word first second : Word Nat} (absorbs : SquareAbsorbs word first)
    (equivalent : Derives Rank040.basis first second) : SquareAbsorbs word second :=
  Derives.trans absorbs (Derives.appendRight
    (BrandtParityBridge.squareOfDisplayedDerivation equivalent) word)

theorem SquareAbsorbs.appendRight
    {word loop : Word Nat} (absorbs : SquareAbsorbs word loop) (suffix : Word Nat) :
    SquareAbsorbs (word ++ suffix) loop := by
  simpa only [SquareAbsorbs, Word.append_assoc] using Derives.appendRight absorbs suffix

theorem SquareAbsorbs.appendTrailing
    {word loop : Word Nat} (absorbs : SquareAbsorbs word loop) (suffix : List Nat) :
    SquareAbsorbs (appendTrailingLetters word suffix) loop := by
  cases suffix with
  | nil => exact absorbs
  | cons head tail => exact absorbs.appendRight (Word.mk head tail)

/-- The actual composition step, using guarded insertion rather than false
whole-square multiplicativity. Both input hypotheses are genuine derivations. -/
theorem SquareAbsorbs.product
    {word first second : Word Nat}
    (firstAbsorbs : SquareAbsorbs word first) (secondAbsorbs : SquareAbsorbs word second) :
    SquareAbsorbs word (first ++ second) := by
  have expose : Derives Rank040.basis word
      (((first ++ first) ++ (second ++ second)) ++ word) := by
    simpa only [Word.append_assoc] using
      Derives.trans firstAbsorbs (Derives.prepend (first ++ first) secondAbsorbs)
  have insert := Derives.appendRight (derivesGuardedProductSquare first second) word
  have restore : Derives Rank040.basis
      ((((first ++ second) ++ (first ++ second)) ++
        ((first ++ first) ++ (second ++ second))) ++ word)
      (((first ++ second) ++ (first ++ second)) ++ word) := by
    simpa only [Word.append_assoc] using
      Derives.prepend ((first ++ second) ++ (first ++ second)) expose.symm
  exact expose.trans (insert.trans restore)

theorem sandwichSquareAbsorbs (first second : Word Nat) :
    SquareAbsorbs ((first ++ second) ++ first) (first ++ second) := by
  simpa only [SquareAbsorbs, Word.append_assoc] using
    BrandtParityBridge.derivesJointSandwichExpansion first second

def gapBlock (anchor : Word Nat) : Option (Word Nat) → Word Nat
  | none => anchor
  | some excursion => anchor ++ excursion

theorem headGapSquareAbsorbs
    (anchor : Word Nat) (gap : Option (Word Nat)) (rest : List (Option (Word Nat))) :
    SquareAbsorbs (anchoredGapWalk anchor (gap :: rest)) (gapBlock anchor gap) := by
  have expanded := DoubledReplayBoundary.derivesGapTripleHead anchor gap rest
  cases gap <;>
    simpa [SquareAbsorbs, gapBlock, anchoredGapWalk, Word.append_assoc] using expanded

/-- A represented excursion can be exposed, doubled at the front, and restored. -/
theorem memberGapSquareAbsorbs
    (anchor : Word Nat) (gaps : List (Option (Word Nat)))
    (gap : Option (Word Nat)) (member : gap ∈ gaps) :
    SquareAbsorbs (anchoredGapWalk anchor gaps) (gapBlock anchor gap) := by
  have permutation : gaps.Perm (gap :: gaps.erase gap) := List.perm_cons_erase member
  exact SquareAbsorbs.ofDerives
    (DoubledReplayBoundary.derivesGapPermutation permutation anchor)
    (headGapSquareAbsorbs anchor gap (gaps.erase gap))

theorem bareHeadSquareAbsorbs
    (anchor excursion : Word Nat) (rest : List (Option (Word Nat))) :
    SquareAbsorbs (anchoredGapWalk anchor (none :: some excursion :: rest)) excursion := by
  cases rest with
  | nil =>
      simpa [SquareAbsorbs, anchoredGapWalk, Word.append_assoc] using
        derivesCrossHeadSquarePrefix anchor excursion
  | cons next tail =>
      cases next with
      | none =>
          simpa [SquareAbsorbs, anchoredGapWalk, Word.append_assoc] using
            Derives.appendRight (derivesCrossHeadSquarePrefix anchor excursion)
              (anchoredGapWalk anchor tail)
      | some other =>
          simpa [SquareAbsorbs, anchoredGapWalk, Word.append_assoc] using
            Derives.appendRight (derivesCrossHeadSquarePrefix anchor excursion)
              (other ++ anchoredGapWalk anchor tail)

/-- An empty excursion makes every represented bare excursion a genuine
return generator; this is the new non-literal-head case. -/
theorem bareMemberGapSquareAbsorbs
    (anchor : Word Nat) (gaps : List (Option (Word Nat))) (excursion : Word Nat)
    (emptyMember : none ∈ gaps) (excursionMember : some excursion ∈ gaps) :
    SquareAbsorbs (anchoredGapWalk anchor gaps) excursion := by
  have exposeEmpty : gaps.Perm (none :: gaps.erase none) := List.perm_cons_erase emptyMember
  have excursionRemains : some excursion ∈ gaps.erase none := by
    have member := exposeEmpty.mem_iff.mp excursionMember
    simpa only [List.mem_cons, reduceCtorEq, false_or] using member
  have exposeExcursion :
      (gaps.erase none).Perm (some excursion :: (gaps.erase none).erase (some excursion)) :=
    List.perm_cons_erase excursionRemains
  have expose := exposeEmpty.trans (List.Perm.cons none exposeExcursion)
  exact SquareAbsorbs.ofDerives
    (DoubledReplayBoundary.derivesGapPermutation expose anchor)
    (bareHeadSquareAbsorbs anchor excursion ((gaps.erase none).erase (some excursion)))

/-- Pure structural generation from the actual head excursion data, not an
unrestricted semantic field or an assumed derivation of the desired result. -/
inductive GeneratedHeadReturn (anchor : Word Nat) (gaps : List (Option (Word Nat))) :
    Word Nat → Prop
  | anchored (gap : Option (Word Nat)) (member : gap ∈ gaps) :
      GeneratedHeadReturn anchor gaps (gapBlock anchor gap)
  | bare (excursion : Word Nat) (emptyMember : none ∈ gaps)
      (excursionMember : some excursion ∈ gaps) : GeneratedHeadReturn anchor gaps excursion
  | product {first second : Word Nat} :
      GeneratedHeadReturn anchor gaps first → GeneratedHeadReturn anchor gaps second →
        GeneratedHeadReturn anchor gaps (first ++ second)

theorem GeneratedHeadReturn.squareAbsorbs
    {anchor : Word Nat} {gaps : List (Option (Word Nat))} {loop : Word Nat}
    (generated : GeneratedHeadReturn anchor gaps loop) :
    SquareAbsorbs (anchoredGapWalk anchor gaps) loop := by
  induction generated with
  | anchored gap member => exact memberGapSquareAbsorbs anchor gaps gap member
  | bare excursion emptyMember excursionMember =>
      exact bareMemberGapSquareAbsorbs anchor gaps excursion emptyMember excursionMember
  | product _ _ firstIH secondIH => exact firstIH.product secondIH

/-- Unrestricted replay on ANY original word, using its exact head decomposition. -/
theorem generatedHeadReturnSquareAbsorbs
    (word loop : Word Nat)
    (generated : GeneratedHeadReturn (Word.singleton word.head) (headExcursions word) loop) :
    SquareAbsorbs word loop := by
  have rebuilt : SquareAbsorbs (headAnchoredRebuild word) loop :=
    generated.squareAbsorbs.appendTrailing (headTrailingSegment word)
  simpa only [headAnchoredRebuild_eq] using rebuilt

theorem headExcursionSquareAbsorbs
    (word : Word Nat) (gap : Option (Word Nat)) (member : gap ∈ headExcursions word) :
    SquareAbsorbs word (gapBlock (Word.singleton word.head) gap) :=
  generatedHeadReturnSquareAbsorbs word _ (.anchored gap member)

theorem bareHeadExcursionSquareAbsorbs
    (word excursion : Word Nat) (emptyMember : none ∈ headExcursions word)
    (member : some excursion ∈ headExcursions word) : SquareAbsorbs word excursion :=
  generatedHeadReturnSquareAbsorbs word _ (.bare excursion emptyMember member)

theorem SquareAbsorbs.sameFactorSignature
    {word loop : Word Nat} (absorbs : SquareAbsorbs word loop) :
    BrandtParityBridge.SameFactorSignature word ((loop ++ loop) ++ word) :=
  BrandtParityBridge.sameFactorSignature_of_factorValid
    (Identity.mk word ((loop ++ loop) ++ word))
    (Derives.sound Rank040.leftModels absorbs) (Derives.sound Rank040.rightModels absorbs)

/-- Every derived square absorption has the exact intended closed-return
semantics. This is the sound direction, not an assumed completeness theorem. -/
theorem SquareAbsorbs.closedReturnWord
    {word loop : Word Nat} (absorbs : SquareAbsorbs word loop) :
    HeadRetargetBoundary.ClosedReturnWord word loop := by
  have same := absorbs.sameFactorSignature.brandt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro letter member
    apply (same.1 letter).mpr
    simp only [Word.toList_append, List.mem_append]
    exact Or.inl (Or.inl member)
  · exact (incomingHeads_connected_of_sameBrandtSignature same).symm
  · intro first second member
    apply (brandtEndpointConnected_iff_of_sameBrandtSignature same _ _).mpr
    apply BrandtEndpointConnected.adjacency
    simp only [Word.adjacentPairs_append, List.mem_append, List.mem_cons]
    exact Or.inl (Or.inl member)
  · apply (brandtEndpointConnected_iff_of_sameBrandtSignature same _ _).mpr
    apply BrandtEndpointConnected.adjacency
    simp only [Word.adjacentPairs_append, Word.final_append, List.mem_append, List.mem_cons]
    exact Or.inr (Or.inl True.intro)

theorem twoLetterClosedLoop :
    HeadRetargetBoundary.ClosedReturnWord (Word.mk 0 [1, 0]) (Word.mk 0 [1]) :=
  (sandwichSquareAbsorbs (Word.singleton 0) (Word.singleton 1)).closedReturnWord

def returnTailLaw : Identity Nat :=
  ⟨Word.mk 0 [1, 0], Word.mk 1 [1, 0, 1, 0]⟩

def returnTailValuation : Nat → Fin 5 := fun letter => if letter = 0 then 1 else 2

theorem returnTailCountervaluation :
    rightTable.semigroup.eval returnTailValuation returnTailLaw.lhs = (1 : Fin 5) ∧
    rightTable.semigroup.eval returnTailValuation returnTailLaw.rhs = (0 : Fin 5) := by
  decide

theorem returnTailNotRightValid : ¬ returnTailLaw.SatisfiedBy rightTable.semigroup := by
  intro valid
  have equality := valid returnTailValuation
  change (1 : Fin 5) = 0 at equality
  exact (by decide : (1 : Fin 5) ≠ 0) equality

theorem returnTailNotClosed :
    ¬ HeadRetargetBoundary.ClosedReturnWord (Word.mk 0 [1, 0]) (Word.singleton 1) := by
  intro closed
  exact returnTailNotRightValid closed.factorValid.2

/-- A fixed-initial-component hypothesis cannot simply be inherited by the
tail in class-walk induction. This does NOT refute ClosedReturnDerivation. -/
theorem naiveClosedTailInductionRefuted :
    ¬ (∀ word first rest : Word Nat,
      HeadRetargetBoundary.ClosedReturnWord word (first ++ rest) →
        HeadRetargetBoundary.ClosedReturnWord word rest) := by
  intro inherit
  exact returnTailNotClosed
    (inherit (Word.mk 0 [1, 0]) (Word.singleton 0) (Word.singleton 1) twoLetterClosedLoop)

/-- The right side of frozen law03 has an actual derived retarget to head zero. -/
theorem law03RightAbsorbsZero : SquareAbsorbs law03.rhs (Word.singleton 0) := by
  have expose := BrandtParityBridge.derivesSandwichMiddleSwitch
    (Word.singleton 1) (Word.singleton 0)
  have insert : SquareAbsorbs (Word.mk 1 [1, 0, 1]) (Word.singleton 0) := by
    simpa [SquareAbsorbs, Word.singleton, Word.append] using
      derivesCrossHeadSquarePrefix (Word.singleton 1) (Word.singleton 0)
  exact SquareAbsorbs.ofDerives expose insert

theorem SquareAbsorbs.square (loop : Word Nat) : SquareAbsorbs (loop ++ loop) loop := by
  simpa only [SquareAbsorbs, Word.append_assoc] using BrandtParityBridge.derivesPairExpansion loop

/-- Absorption in a suffix propagates across any exposed square prefix.
This handles return loops beyond the literal head-excursion segment. -/
theorem SquareAbsorbs.prependSquare
    {word loop : Word Nat} (absorbs : SquareAbsorbs word loop) (before : Word Nat) :
    SquareAbsorbs ((before ++ before) ++ word) loop := by
  have expose := Derives.prepend (before ++ before) absorbs
  have swapped := Derives.appendRight
    (BrandtParityBridge.derivesSquareCommutation before loop) word
  have aligned : Derives Rank040.basis
      ((before ++ before) ++ ((loop ++ loop) ++ word))
      ((loop ++ loop) ++ ((before ++ before) ++ word)) := by
    simpa only [Word.append_assoc] using swapped
  exact expose.trans aligned

/-- Once every letter is an actual absorbed loop, so is every nonempty word
over those letters. This is a derivational induction, not finite-table inference. -/
theorem squareAbsorbsOfLetters (word loop : Word Nat)
    (available : ∀ letter, letter ∈ loop.toList → SquareAbsorbs word (Word.singleton letter)) :
    SquareAbsorbs word loop := by
  cases loop with
  | mk head tail =>
      induction tail generalizing head with
      | nil => exact available head (by simp [Word.toList])
      | cons next rest ih =>
          have first := available head (by simp [Word.toList])
          have remaining : SquareAbsorbs word (Word.mk next rest) :=
            ih next (fun letter member => available letter (List.mem_cons_of_mem _ member))
          exact first.product remaining

def squareLetterBank (first : Nat) : List Nat → Word Nat
  | [] => Word.mk first [first]
  | next :: rest => Word.mk first [first] ++ squareLetterBank next rest

theorem squareLetterBankSupport (first : Nat) (rest : List Nat) (letter : Nat) :
    letter ∈ (squareLetterBank first rest).toList ↔ letter ∈ first :: rest := by
  induction rest generalizing first with
  | nil => simp [squareLetterBank, Word.toList]
  | cons next tail ih =>
      simp only [squareLetterBank, Word.toList_append, List.mem_append]
      rw [ih next]
      simp [Word.toList]

theorem squareLetterBankMemberAbsorbs
    (first : Nat) (rest : List Nat) (letter : Nat) (member : letter ∈ first :: rest) :
    SquareAbsorbs (squareLetterBank first rest) (Word.singleton letter) := by
  induction rest generalizing first with
  | nil =>
      have same : letter = first := by simpa using member
      subst letter
      exact SquareAbsorbs.square (Word.singleton first)
  | cons next tail ih =>
      rcases List.mem_cons.mp member with same | later
      · subst letter
        exact (SquareAbsorbs.square (Word.singleton first)).appendRight (squareLetterBank next tail)
      · exact (ih next later).prependSquare (Word.singleton first)

/-- The complete unrestricted square-bank case: every supported loop works. -/
theorem squareLetterBankWordAbsorbs
    (first : Nat) (rest : List Nat) (loop : Word Nat)
    (support : ∀ letter, letter ∈ loop.toList → letter ∈ first :: rest) :
    SquareAbsorbs (squareLetterBank first rest) loop :=
  squareAbsorbsOfLetters _ loop
    (fun letter member => squareLetterBankMemberAbsorbs first rest letter (support letter member))

/-- ClosedReturnDerivation is discharged for EVERY finite literal square bank
and EVERY nonempty closed return word, with no length or alphabet bound. -/
theorem squareLetterBankClosedReturnDerivation
    (first : Nat) (rest : List Nat) (loop : Word Nat)
    (closed : HeadRetargetBoundary.ClosedReturnWord (squareLetterBank first rest) loop) :
    Derives Rank040.basis (squareLetterBank first rest)
      ((loop ++ loop) ++ squareLetterBank first rest) :=
  squareLetterBankWordAbsorbs first rest loop
    (fun letter member => (squareLetterBankSupport first rest letter).mp (closed.support letter member))

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.ClosedReturnReplay
