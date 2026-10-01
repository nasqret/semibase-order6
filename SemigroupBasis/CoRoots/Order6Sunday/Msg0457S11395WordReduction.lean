import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395WordGaps

/-! Right-to-left B12 reduction of the actual gap chain of any word.
Pairs survive only in a letter's final gap. Sector placement remains a
separate obligation: this is not yet the signature-canonical renderer. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395WordReduction

open SemigroupBasis
open Msg0457S11395Semantics Msg0457S11395EvenInsertion Msg0457S11395SeenSwaps
open Msg0457S11395SeenGap Msg0457S11395FutureRuns Msg0457S11395FutureGap Msg0457S11395WordGaps

def reduceChain (prefixWords : List Nat) : Chain → Chain
  | .stop gap => .stop (futureGap prefixWords gap [])
  | .step gap fresh tail =>
      let normalTail := reduceChain (prefixWords ++ gap ++ [fresh]) tail
      .step (futureGap prefixWords gap (fresh :: flatten normalTail)) fresh normalTail

theorem reduceChain_introductions (prefixWords : List Nat) (chain : Chain) :
    introductions (reduceChain prefixWords chain) = introductions chain := by
  induction chain generalizing prefixWords with
  | stop gap => rfl
  | step gap fresh tail ih => simp only [reduceChain, introductions, ih]

theorem reduceChain_derives (prefixWords : List Nat) (chain : Chain) (good : WellFormed prefixWords chain) :
    LD (prefixWords ++ flatten chain) (prefixWords ++ flatten (reduceChain prefixWords chain)) := by
  induction chain generalizing prefixWords with
  | stop gap => simpa [reduceChain, flatten] using normalizeFutureGap prefixWords gap [] good
  | step gap fresh tail ih =>
      have tailStep := ih (prefixWords ++ gap ++ [fresh]) good.2.2
      have gapStep := normalizeFutureGap prefixWords gap
        (fresh :: flatten (reduceChain (prefixWords ++ gap ++ [fresh]) tail)) good.1
      have first : LD (prefixWords ++ flatten (.step gap fresh tail))
          (prefixWords ++ gap ++ fresh :: flatten (reduceChain (prefixWords ++ gap ++ [fresh]) tail)) := by
        simpa [flatten, List.append_assoc] using tailStep
      apply first.trans
      simpa [reduceChain, flatten, List.append_assoc] using gapStep

theorem reduceChain_support (prefixWords : List Nat) (chain : Chain) (good : WellFormed prefixWords chain)
    (tested : Nat) : tested ∈ flatten (reduceChain prefixWords chain) ↔ tested ∈ flatten chain := by
  induction chain generalizing prefixWords with
  | stop gap =>
      simpa [reduceChain, flatten] using futureGap_supportWithSuffix prefixWords gap [] good tested
  | step gap fresh tail ih =>
      have tailSupport := ih (prefixWords ++ gap ++ [fresh]) good.2.2
      have gapSupport := futureGap_supportWithSuffix prefixWords gap
        (fresh :: flatten (reduceChain (prefixWords ++ gap ++ [fresh]) tail)) good.1 tested
      apply gapSupport.trans
      simp only [flatten, List.mem_append, List.mem_cons, tailSupport]

theorem reduceChain_wellFormed (prefixWords : List Nat) (chain : Chain) (good : WellFormed prefixWords chain) :
    WellFormed prefixWords (reduceChain prefixWords chain) := by
  induction chain generalizing prefixWords with
  | stop gap => exact futureGap_seen prefixWords gap []
  | step gap fresh tail ih =>
      refine ⟨futureGap_seen _ _ _, good.2.1, ?_⟩
      exact wellFormed_congr _ _ _
        (seen_prefix_extension_support prefixWords gap _ fresh good.1 (futureGap_seen _ _ _))
        (ih (prefixWords ++ gap ++ [fresh]) good.2.2)

def GapBound (gap suffix : List Nat) : Prop :=
  ∀ tested, gap.count tested ≤ if tested ∈ suffix then 1 else 2

def Reduced : Chain → Prop
  | .stop gap => GapBound gap []
  | .step gap fresh tail => GapBound gap (fresh :: flatten tail) ∧ Reduced tail

theorem futureGap_bound (prefixWords gap suffix : List Nat) (seen : AllSeen prefixWords gap) :
    GapBound (futureGap prefixWords gap suffix) suffix := by
  intro tested
  rw [futureGap_count _ _ _ seen]
  by_cases future : tested ∈ suffix
  · simp only [futureCopies, if_pos future]
    have bound := Nat.mod_lt (gap.count tested) (show 0 < 2 by decide)
    omega
  · simp only [if_neg future]
    exact futureCopies_le_two suffix tested (gap.count tested)

theorem reduceChain_reduced (prefixWords : List Nat) (chain : Chain) (good : WellFormed prefixWords chain) :
    Reduced (reduceChain prefixWords chain) := by
  induction chain generalizing prefixWords with
  | stop gap => exact futureGap_bound prefixWords gap [] good
  | step gap fresh tail ih =>
      exact ⟨futureGap_bound prefixWords gap _ good.1, ih (prefixWords ++ gap ++ [fresh]) good.2.2⟩

/-- A doubled letter in a reduced gap cannot occur anywhere later. -/
theorem reduced_pair_is_final (gap : List Nat) (fresh tested : Nat) (tail : Chain)
    (reduced : Reduced (.step gap fresh tail)) (pair : 2 ≤ gap.count tested) :
    tested ∉ fresh :: flatten tail := by
  intro later
  have bound := reduced.1 tested
  rw [if_pos later] at bound
  omega

theorem futureGap_prefix_congr (left right gap suffix : List Nat)
    (same : ∀ tested, tested ∈ left ↔ tested ∈ right) :
    futureGap left gap suffix = futureGap right gap suffix := by
  unfold futureGap
  rw [canonicalLabels_eq_of_support left right same]

theorem reduceChain_prefix_congr (chain : Chain) (left right : List Nat)
    (same : ∀ tested, tested ∈ left ↔ tested ∈ right) : reduceChain left chain = reduceChain right chain := by
  induction chain generalizing left right with
  | stop gap => exact congrArg Chain.stop (futureGap_prefix_congr left right gap [] same)
  | step gap fresh tail ih =>
      have tailSame := ih (left ++ gap ++ [fresh]) (right ++ gap ++ [fresh]) (by
        intro tested
        simp only [List.mem_append, same tested])
      simp only [reduceChain, tailSame]
      rw [futureGap_prefix_congr left right gap _ same]

theorem reduceChain_idempotent (prefixWords : List Nat) (chain : Chain) (good : WellFormed prefixWords chain) :
    reduceChain prefixWords (reduceChain prefixWords chain) = reduceChain prefixWords chain := by
  induction chain generalizing prefixWords with
  | stop gap =>
      exact congrArg Chain.stop (futureGap_idempotent prefixWords gap [] good)
  | step gap fresh tail ih =>
      let originalPrefix := prefixWords ++ gap ++ [fresh]
      let normalTail := reduceChain originalPrefix tail
      let normalGap := futureGap prefixWords gap (fresh :: flatten normalTail)
      have same : ∀ tested, tested ∈ prefixWords ++ normalGap ++ [fresh] ↔ tested ∈ originalPrefix :=
        fun tested => (seen_prefix_extension_support prefixWords gap normalGap fresh good.1
          (futureGap_seen _ _ _) tested).symm
      have tailStable : reduceChain (prefixWords ++ normalGap ++ [fresh]) normalTail = normalTail :=
        (reduceChain_prefix_congr normalTail _ originalPrefix same).trans (ih originalPrefix good.2.2)
      change Chain.step (futureGap prefixWords normalGap
          (fresh :: flatten (reduceChain (prefixWords ++ normalGap ++ [fresh]) normalTail))) fresh
          (reduceChain (prefixWords ++ normalGap ++ [fresh]) normalTail) = Chain.step normalGap fresh normalTail
      rw [tailStable]
      exact congrArg (fun gap => Chain.step gap fresh normalTail)
        (futureGap_idempotent prefixWords gap (fresh :: flatten normalTail) good.1)

theorem splitSeen_allSeen (prefixWords gap : List Nat) (seen : AllSeen prefixWords gap) :
    splitSeen prefixWords gap = (gap, []) := by
  induction gap with
  | nil => rfl
  | cons letter rest ih =>
      have letterSeen := seen letter (by simp)
      have tailSeen : AllSeen prefixWords rest := fun tested member => seen tested (List.mem_cons_of_mem letter member)
      simp only [splitSeen, if_pos letterSeen, ih tailSeen]

theorem splitSeen_beforeFresh (prefixWords gap rest : List Nat) (fresh : Nat)
    (seen : AllSeen prefixWords gap) (absent : fresh ∉ prefixWords) :
    splitSeen prefixWords (gap ++ fresh :: rest) = (gap, fresh :: rest) := by
  induction gap with
  | nil => simp [splitSeen, absent]
  | cons letter tail ih =>
      have letterSeen := seen letter (by simp)
      have tailSeen : AllSeen prefixWords tail := fun tested member => seen tested (List.mem_cons_of_mem letter member)
      simp only [List.cons_append, splitSeen, if_pos letterSeen, ih tailSeen]

theorem factor_of_wellFormed (prefixWords : List Nat) (chain : Chain) (good : WellFormed prefixWords chain) :
    factor prefixWords (flatten chain) = chain := by
  induction chain generalizing prefixWords with
  | stop gap =>
      have parts := splitSeen_allSeen prefixWords gap good
      rw [factor]
      split
      next _ => exact congrArg Chain.stop (congrArg Prod.fst parts)
      next fresh rest shape =>
        have impossible : ([] : List Nat) = fresh :: rest := (congrArg Prod.snd parts).symm.trans shape
        cases impossible
  | step gap fresh tail ih =>
      have parts := splitSeen_beforeFresh prefixWords gap (flatten tail) fresh good.1 good.2.1
      rw [factor]
      split
      next shape =>
        have impossible : fresh :: flatten tail = ([] : List Nat) := (congrArg Prod.snd parts).symm.trans shape
        cases impossible
      next nextFresh nextRest shape =>
        have equal : fresh :: flatten tail = nextFresh :: nextRest := (congrArg Prod.snd parts).symm.trans shape
        have equalFresh := (List.cons.inj equal).1
        have equalRest := (List.cons.inj equal).2
        subst nextFresh
        subst nextRest
        rw [show (splitSeen prefixWords (flatten (.step gap fresh tail))).1 = gap from congrArg Prod.fst parts]
        rw [ih _ good.2.2]

def normalWord : Word Nat → Word Nat
  | ⟨head, tail⟩ => ⟨head, flatten (reduceChain [head] (factor [head] tail))⟩

theorem normalizeWord (word : Word Nat) : Derives basis word (normalWord word) := by
  cases word with
  | mk head tail =>
      have proof := reduceChain_derives [head] (factor [head] tail) (factor_wellFormed [head] tail)
      rw [factor_flatten] at proof
      exact (show LD (head :: tail) (head :: flatten (reduceChain [head] (factor [head] tail))) from
        by simpa using proof).toWord

theorem normalWord_signature (word : Word Nat) : Msg0457S11395Observations.SameSignature word (normalWord word) :=
  Msg0457S11395Signature.derives_preserve_signature (normalizeWord word)

theorem normalWord_idempotent (word : Word Nat) : normalWord (normalWord word) = normalWord word := by
  cases word with
  | mk head tail =>
      simp only [normalWord]
      rw [factor_of_wellFormed [head] _ (reduceChain_wellFormed [head] _ (factor_wellFormed [head] tail)),
        reduceChain_idempotent [head] _ (factor_wellFormed [head] tail)]

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395WordReduction
