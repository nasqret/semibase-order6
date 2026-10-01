import SemigroupBasis.CoRoots.S5_213Normalization
import SemigroupBasis.CoRoots.S5_213Invariant
import SemigroupBasis.Examples.LeftNormalBandThree
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_13

/-!
# Shared fixed-head M2 normalizer for `S3_13 ∩ S5_213` (msg-0272 lane)

EVIDENCE LABEL: source-staged, NOT compiled here.  Design receipts:
msg-0085 screen (candidate models all five roots; transfer claims;
three-way 123 = 123 exact).

THE THREE-LAW SYSTEM `sigma`:  `xxx = xxxx`, `xxy = xyx`,
`xyyz = xzyy`.  Relation to Edmunds' M2 basis
(`S5_213.basis = {xxx=xxxx, xyx=xxy, xyx=yxx}`): the power laws are
identical, `xxy = xyx` is the left-gather law reversed, and the right
gather `xyx = yxx` — provably underivable unguarded (S3_13 is a
countermodel) — becomes derivable behind ANY nonempty prefix in exactly
two block steps (`derivesGuardedRightGather`).

COMPLETENESS ARCHITECTURE (one uniform route; simplification of the
msg-0271 three-case proposal): for a joint-valid identity with common
head `h`,
  (1) gather-and-cap: each side derives in `sigma` to
      `h^m ++ tail` with `h ∉ tail` and `m = min 3 (count h)`;
      the two `m`s agree because capped multiplicity at cap 3 is an
      `S5_213` invariant;
  (2) strip: evaluating `h` at the identity element `5` of `S5_213`
      shows the tail pair is itself `S5_213`-valid;
  (3) finish: `sameSignature_of_s5_213_valid` +
      `derives_of_sameSignature` give an M2 derivation of the tails,
      and `liftM2BasisUnderPrefixIdentity` replays it behind the
      nonempty guard `h^m`.

THE ONE SEAM: the main theorem takes `headEq` (validity in `S3_13`
forces equal heads) as an explicit hypothesis.  The syntactic half
(`lnbDerives_head_eq`: LNB-derivations preserve heads) is PROVED below;
codex wires the seam through the existing `S3_13` ↔ left-normal-band
identification when generating the five wrappers, per msg-0272's
division of labour.

API RISK FLAGS (patch-loop material, none mathematical): the exact
constructor names of `Derives` are taken from the compiled 66d9f0e06
lift (`fromBasis/refl/symm/trans/prepend/appendRight/subst`);
`Derives.sound`, `FiniteCertificate.checkModels_sound`,
`Word.toList_injective`, `Word.toList_bind`, `List.flatMap_assoc`
spellings mirror compiled modules.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_213M2

open SemigroupBasis
open SemigroupBasis.CoRoots

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-! ## The displayed three-law system -/

def sigmaPowerLaw : Identity Nat := ⟨w 0 [0, 0], w 0 [0, 0, 0]⟩
def sigmaGatherLaw : Identity Nat := ⟨w 0 [0, 1], w 0 [1, 0]⟩
def sigmaTransportLaw : Identity Nat := ⟨w 0 [1, 1, 2], w 0 [2, 1, 1]⟩

def sigma : List (Identity Nat) :=
  [sigmaPowerLaw, sigmaGatherLaw, sigmaTransportLaw]

private theorem sigmaPowerMem : sigmaPowerLaw ∈ sigma := by
  simp [sigma]
private theorem sigmaGatherMem : sigmaGatherLaw ∈ sigma := by
  simp [sigma]
private theorem sigmaTransportMem : sigmaTransportLaw ∈ sigma := by
  simp [sigma]

private def instantiateThree (first second third : Word Nat) :
    Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- `U³ = U⁴` for word blocks. -/
theorem derivesSigmaPower (u : Word Nat) :
    Derives sigma ((u ++ u) ++ u) (((u ++ u) ++ u) ++ u) := by
  have base : Derives sigma sigmaPowerLaw.lhs sigmaPowerLaw.rhs :=
    Derives.fromBasis sigmaPowerMem
  have substituted := Derives.subst base (instantiateThree u u u)
  simpa [sigmaPowerLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `U²V = UVU` for word blocks (the gather law). -/
theorem derivesSigmaGather (u v : Word Nat) :
    Derives sigma ((u ++ u) ++ v) ((u ++ v) ++ u) := by
  have base : Derives sigma sigmaGatherLaw.lhs sigmaGatherLaw.rhs :=
    Derives.fromBasis sigmaGatherMem
  have substituted := Derives.subst base (instantiateThree u v v)
  simpa [sigmaGatherLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `XY²Z = XZY²` for word blocks (the square transport law). -/
theorem derivesSigmaTransport (x y z : Word Nat) :
    Derives sigma (((x ++ y) ++ y) ++ z) (((x ++ z) ++ y) ++ y) := by
  have base : Derives sigma sigmaTransportLaw.lhs sigmaTransportLaw.rhs :=
    Derives.fromBasis sigmaTransportMem
  have substituted := Derives.subst base (instantiateThree x y z)
  simpa [sigmaTransportLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-! ## Finite model proofs for both factors -/

private def basisVariable (value : Nat) : Fin 3 :=
  if value = 0 then 0 else if value = 1 then 1 else 2

theorem modelsS3_13 :
    Models Generated.S3_13.table.semigroup sigma :=
  FiniteCertificate.checkModels_sound
    Generated.S3_13.table sigma basisVariable (by decide)

theorem modelsS5_213 :
    Models Generated.Catalogue.S5_213.table.semigroup sigma :=
  FiniteCertificate.checkModels_sound
    Generated.Catalogue.S5_213.table sigma basisVariable (by decide)

/-! ## The guarded right gather

`P·UVU = P·VUU` for ANY nonempty `P`: gather in reverse under the
prefix, then one transport instance whose `X`-block is the prefix
itself.  This is the entire content the unguarded system lacks. -/

theorem derivesGuardedRightGather (p u v : Word Nat) :
    Derives sigma (p ++ ((u ++ v) ++ u)) (p ++ ((v ++ u) ++ u)) := by
  have gatherStep :
      Derives sigma (p ++ ((u ++ u) ++ v)) (p ++ ((u ++ v) ++ u)) :=
    Derives.prepend p (derivesSigmaGather u v)
  have transportStep :
      Derives sigma (((p ++ u) ++ u) ++ v) (((p ++ v) ++ u) ++ u) :=
    derivesSigmaTransport p u v
  have first : Derives sigma (p ++ ((u ++ v) ++ u)) (p ++ ((u ++ u) ++ v)) :=
    gatherStep.symm
  exact first.trans <| by
    simpa [Word.append_assoc] using transportStep

/-! ## Lifting complete M2 derivations behind a nonempty prefix -/

private theorem bind_append
    (left right : Word Nat) (sigmaMap : Nat → Word Nat) :
    (left ++ right).bind sigmaMap =
      left.bind sigmaMap ++ right.bind sigmaMap := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (tau sigmaMap : Nat → Word Nat) :
    (word.bind tau).bind sigmaMap =
      word.bind (fun letter => (tau letter).bind sigmaMap) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Every axiom of Edmunds' M2 basis replays behind any nonempty
prefix: the power and left-gather laws hold unguarded, and the right
gather is `derivesGuardedRightGather`. -/
theorem liftM2AxiomUnderPrefix
    (identity : Identity Nat)
    (member : identity ∈ S5_213.basis)
    (guard : Word Nat) (sigmaMap : Nat → Word Nat) :
    Derives sigma
      (guard ++ identity.lhs.bind sigmaMap)
      (guard ++ identity.rhs.bind sigmaMap) := by
  simp only [S5_213.basis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl
  · -- powerLaw : xxx = xxxx
    change Derives sigma
      (guard ++ ((sigmaMap 0 ++ sigmaMap 0) ++ sigmaMap 0))
      (guard ++ (((sigmaMap 0 ++ sigmaMap 0) ++ sigmaMap 0) ++ sigmaMap 0))
    exact Derives.prepend guard (derivesSigmaPower (sigmaMap 0))
  · -- leftGatherLaw : xyx = xxy  (gather, reversed orientation)
    change Derives sigma
      (guard ++ ((sigmaMap 0 ++ sigmaMap 1) ++ sigmaMap 0))
      (guard ++ ((sigmaMap 0 ++ sigmaMap 0) ++ sigmaMap 1))
    exact Derives.prepend guard
      (derivesSigmaGather (sigmaMap 0) (sigmaMap 1)).symm
  · -- rightGatherLaw : xyx = yxx  (the guarded step)
    change Derives sigma
      (guard ++ ((sigmaMap 0 ++ sigmaMap 1) ++ sigmaMap 0))
      (guard ++ ((sigmaMap 1 ++ sigmaMap 0) ++ sigmaMap 0))
    exact derivesGuardedRightGather guard (sigmaMap 0) (sigmaMap 1)

/-- Relative deduction: any complete-M2 derivation replays in `sigma`
behind a fixed nonempty prefix.  Mirrors the compiled 66d9f0e06
induction verbatim. -/
theorem liftM2BasisUnderPrefix
    {left right : Word Nat}
    (derivation : Derives S5_213.basis left right)
    (guard : Word Nat) (sigmaMap : Nat → Word Nat) :
    Derives sigma
      (guard ++ left.bind sigmaMap)
      (guard ++ right.bind sigmaMap) := by
  induction derivation generalizing guard sigmaMap with
  | fromBasis member =>
      exact liftM2AxiomUnderPrefix _ member guard sigmaMap
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm (induction guard sigmaMap)
  | trans _ _ firstInduction secondInduction =>
      exact Derives.trans
        (firstInduction guard sigmaMap) (secondInduction guard sigmaMap)
  | prepend prefixWord _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (guard ++ prefixWord.bind sigmaMap) sigmaMap
  | appendRight _ suffix induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (induction guard sigmaMap)
          (suffix.bind sigmaMap)
  | subst _ tau induction =>
      simpa [bind_bind] using
        induction guard (fun letter => (tau letter).bind sigmaMap)

theorem liftM2BasisUnderPrefixIdentity
    {left right : Word Nat}
    (derivation : Derives S5_213.basis left right)
    (guard : Word Nat) :
    Derives sigma (guard ++ left) (guard ++ right) := by
  simpa [bind_singleton] using
    liftM2BasisUnderPrefix derivation guard Word.singleton

/-! ## Head normal form inside `sigma`

This is the first-block scan from the compiled `S5_213` normalizer,
specialized to `sigma`.  It gathers every later copy of the initial
letter into the leading block and contracts that block at exponent three.
-/

private def cappedExponent (count : Nat) : Nat :=
  if count < 3 then count else 3

private theorem cappedExponent_eq_min (count : Nat) :
    cappedExponent count = Nat.min 3 count := by
  unfold cappedExponent
  simp only [Nat.min_def]
  split <;> split <;> omega

private theorem cappedExponent_pos
    {count : Nat} (positive : 0 < count) :
    0 < cappedExponent count := by
  unfold cappedExponent
  split <;> omega

private theorem min_three_min_add (left right : Nat) :
    Nat.min 3 (Nat.min 3 left + right) =
      Nat.min 3 (left + right) := by
  by_cases capped : 3 ≤ left
  · have inner : Nat.min 3 left = 3 := Nat.min_eq_left capped
    calc
      Nat.min 3 (Nat.min 3 left + right) = Nat.min 3 (3 + right) := by
        rw [inner]
      _ = 3 := Nat.min_eq_left (by omega)
      _ = Nat.min 3 (left + right) :=
        (Nat.min_eq_left (by omega)).symm
  · have below : left ≤ 3 := by omega
    have inner : Nat.min 3 left = left := Nat.min_eq_right below
    simpa only [inner]

private theorem cappedExponent_succ_normalized (count : Nat) :
    cappedExponent (cappedExponent count + 1) =
      cappedExponent (count + 1) := by
  simp only [cappedExponent_eq_min]
  exact min_three_min_add count 1

private theorem derivesFirstRepeat
    (x : Nat) (middle suffix : List Nat) :
    Derives sigma
      (w x (middle ++ x :: suffix))
      (w x (x :: middle ++ suffix)) := by
  cases middle with
  | nil => exact Derives.refl _
  | cons y ys =>
      let middleWord := w y ys
      cases suffix with
      | nil =>
          simpa [w, middleWord, Word.append, Word.singleton,
            Word.append_assoc] using
              (derivesSigmaGather (Word.singleton x) middleWord).symm
      | cons z zs =>
          have moved :=
            Derives.appendRight
              (derivesSigmaGather (Word.singleton x) middleWord).symm
              (w z zs)
          simpa [w, middleWord, Word.append, Word.singleton,
            Word.append_assoc] using moved

private theorem derivesThird
    (x : Nat) (middle suffix : List Nat) :
    Derives sigma
      (w x (x :: middle ++ x :: suffix))
      (w x (x :: x :: middle ++ suffix)) := by
  cases middle with
  | nil => exact Derives.refl _
  | cons y ys =>
      let middleWord := w y ys
      have moved :=
        Derives.prepend (Word.singleton x) <|
          (derivesSigmaGather (Word.singleton x) middleWord).symm
      cases suffix with
      | nil =>
          simpa [w, middleWord, Word.append, Word.singleton,
            Word.append_assoc] using moved
      | cons z zs =>
          have movedWithSuffix := Derives.appendRight moved (w z zs)
          simpa [w, middleWord, Word.append, Word.singleton,
            Word.append_assoc] using movedWithSuffix

private theorem derivesFourthToTriple
    (x : Nat) (middle suffix : List Nat) :
    Derives sigma
      (w x (x :: x :: middle ++ x :: suffix))
      (w x (x :: x :: middle ++ suffix)) := by
  cases middle with
  | nil =>
      have contracted :=
        (derivesSigmaPower (Word.singleton x)).symm
      cases suffix with
      | nil =>
          simpa [w, Word.append, Word.singleton,
            Word.append_assoc] using contracted
      | cons z zs =>
          simpa [w, Word.append, Word.singleton,
            Word.append_assoc] using
              Derives.appendRight contracted (w z zs)
  | cons y ys =>
      let middleWord := w y ys
      have moved :=
        Derives.prepend
          ((Word.singleton x) ++ (Word.singleton x)) <|
            (derivesSigmaGather (Word.singleton x) middleWord).symm
      have contracted :=
        Derives.appendRight
          (derivesSigmaPower (Word.singleton x)).symm middleWord
      cases suffix with
      | nil =>
          exact Derives.trans
            (by
              simpa [w, middleWord, Word.append, Word.singleton,
                Word.append_assoc] using moved)
            (by
              simpa [w, middleWord, Word.append, Word.singleton,
                Word.append_assoc] using contracted)
      | cons z zs =>
          have movedWithSuffix := Derives.appendRight moved (w z zs)
          have contractedWithSuffix :=
            Derives.appendRight contracted (w z zs)
          exact Derives.trans
            (by
              simpa [w, middleWord, Word.append, Word.singleton,
                Word.append_assoc] using movedWithSuffix)
            (by
              simpa [w, middleWord, Word.append, Word.singleton,
                Word.append_assoc] using contractedWithSuffix)

private inductive GatherState where
  | one
  | two
  | three
deriving DecidableEq, Repr

private def GatherState.exponent : GatherState → Nat
  | .one => 1
  | .two => 2
  | .three => 3

private def GatherState.next : GatherState → GatherState
  | .one => .two
  | .two => .three
  | .three => .three

private def GatherState.advance : GatherState → Nat → GatherState
  | state, 0 => state
  | state, count + 1 => advance state.next count

private def gatheredTail
    (state : GatherState) (x : Nat)
    (middle suffix : List Nat) : List Nat :=
  List.replicate (state.exponent - 1) x ++ middle ++ suffix

private theorem advance_exponent
    (state : GatherState) (count : Nat) :
    (state.advance count).exponent =
      cappedExponent (state.exponent + count) := by
  induction count generalizing state with
  | zero => cases state <;> decide
  | succ count induction =>
      rw [GatherState.advance, induction]
      cases state <;>
        simp only [GatherState.next, GatherState.exponent] <;>
        unfold cappedExponent <;>
        split <;> split <;> omega

private theorem derivesGatherCap :
    ∀ (state : GatherState) (x : Nat)
      (middle rest : List Nat),
      Derives sigma
        (w x (gatheredTail state x middle rest))
        (w x
          (gatheredTail
            (state.advance (rest.count x)) x middle
            (rest.filter (fun y => decide (y ≠ x)))))
  | state, x, middle, [] => by
      simp [gatheredTail, GatherState.advance]
      exact Derives.refl _
  | state, x, middle, y :: ys => by
      by_cases equal : y = x
      · subst y
        cases state with
        | one =>
            exact (derivesFirstRepeat x middle ys).trans <| by
              simpa [gatheredTail, GatherState.advance] using
                derivesGatherCap .two x middle ys
        | two =>
            exact (derivesThird x middle ys).trans <| by
              simpa [gatheredTail, GatherState.advance] using
                derivesGatherCap .three x middle ys
        | three =>
            exact (derivesFourthToTriple x middle ys).trans <| by
              simpa [gatheredTail, GatherState.advance] using
                derivesGatherCap .three x middle ys
      · have remaining :=
          derivesGatherCap state x (middle ++ [y]) ys
        simpa [gatheredTail, equal, List.count_cons_of_ne equal,
          List.append_assoc] using remaining

/-- `h^(m+1)` as a word. -/
def headPow (h : Nat) : Nat → Word Nat
  | 0 => Word.singleton h
  | m + 1 => headPow h m ++ Word.singleton h

/-- The h-free remainder, in original order. -/
def headFreeTail (h : Nat) (letters : List Nat) : List Nat :=
  letters.filter (fun c => decide (c ≠ h))

/-- The successor-scale exponent of the capped leading block. -/
def capIndex (h : Nat) (word : Word Nat) : Nat :=
  cappedExponent (word.toList.count h) - 1

/-- The deterministic head normal form. -/
def headNormal (word : Word Nat) : Word Nat :=
  w word.head
    (List.replicate (capIndex word.head word) word.head ++
      word.tail.filter (fun c => decide (c ≠ word.head)))

private theorem replicate_append_singleton (h m : Nat) :
    List.replicate m h ++ [h] = h :: List.replicate m h := by
  induction m with
  | zero => rfl
  | succ m induction =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons h) induction

private theorem headPow_eq_w_replicate (h m : Nat) :
    headPow h m = w h (List.replicate m h) := by
  induction m with
  | zero => rfl
  | succ m induction =>
      apply Word.toList_injective
      simpa only [headPow, induction, w, Word.toList,
        Word.toList_append, Word.toList_singleton, List.replicate_succ,
        List.cons_append] using
          congrArg (List.cons h) (replicate_append_singleton h m)

private theorem headNormal_eq_headPow_of_filter_nil
    (word : Word Nat)
    (empty :
      word.tail.filter (fun c => decide (c ≠ word.head)) = []) :
    headNormal word = headPow word.head (capIndex word.head word) := by
  rw [headPow_eq_w_replicate]
  change
    w word.head
        (List.replicate (capIndex word.head word) word.head ++
          word.tail.filter (fun c => decide (c ≠ word.head))) =
      w word.head (List.replicate (capIndex word.head word) word.head)
  rw [empty, List.append_nil]

private theorem headNormal_eq_headPow_append_of_filter_cons
    (word : Word Nat) (first : Nat) (rest : List Nat)
    (shape :
      word.tail.filter (fun c => decide (c ≠ word.head)) =
        first :: rest) :
    headNormal word =
      headPow word.head (capIndex word.head word) ++ w first rest := by
  rw [headPow_eq_w_replicate]
  change
    w word.head
        (List.replicate (capIndex word.head word) word.head ++
          word.tail.filter (fun c => decide (c ≠ word.head))) =
      w word.head
        (List.replicate (capIndex word.head word) word.head ++ first :: rest)
  rw [shape]

private theorem mem_filteredTail_iff
    (word : Word Nat) (letter : Nat) :
    letter ∈ word.tail.filter (fun c => decide (c ≠ word.head)) ↔
      letter ∈ word.toList ∧ letter ≠ word.head := by
  cases word with
  | mk head tail =>
      simp only [List.mem_filter, decide_eq_true_eq, Word.toList,
        List.mem_cons]
      constructor
      · rintro ⟨inTail, different⟩
        exact ⟨Or.inr inTail, different⟩
      · rintro ⟨inHeadOrTail, different⟩
        exact ⟨inHeadOrTail.resolve_left different, different⟩

private theorem head_not_mem_filteredTail (word : Word Nat) :
    word.head ∉
      word.tail.filter (fun c => decide (c ≠ word.head)) := by
  intro member
  exact ((mem_filteredTail_iff word word.head).mp member).2 rfl

private theorem filteredTail_nil_forward
    {left right : Word Nat}
    (same :
      S5_213Syntax.SameCappedSingletonSignature left right)
    (heads : left.head = right.head)
    (leftEmpty :
      left.tail.filter (fun c => decide (c ≠ left.head)) = []) :
    right.tail.filter (fun c => decide (c ≠ right.head)) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter rightMember
  have rightData := (mem_filteredTail_iff right letter).mp rightMember
  have leftSupport : letter ∈ left.toList :=
    (same.support letter).2 rightData.1
  have leftDifferent : letter ≠ left.head := by
    intro equal
    exact rightData.2 (equal.trans heads)
  have leftMember :=
    (mem_filteredTail_iff left letter).mpr
      ⟨leftSupport, leftDifferent⟩
  rw [leftEmpty] at leftMember
  exact List.not_mem_nil leftMember

private theorem filteredTail_nil_iff
    {left right : Word Nat}
    (same :
      S5_213Syntax.SameCappedSingletonSignature left right)
    (heads : left.head = right.head) :
    left.tail.filter (fun c => decide (c ≠ left.head)) = [] ↔
      right.tail.filter (fun c => decide (c ≠ right.head)) = [] := by
  constructor
  · exact filteredTail_nil_forward same heads
  · exact filteredTail_nil_forward same.symm heads.symm

/-- Gather and cap every later occurrence of the initial letter. -/
theorem derivesHeadNormal (word : Word Nat) :
    Derives sigma word (headNormal word) := by
  cases word with
  | mk head tail =>
      have gathered := derivesGatherCap .one head [] tail
      have exponent :
          (GatherState.one.advance (tail.count head)).exponent =
            cappedExponent ((head :: tail).count head) := by
        rw [advance_exponent]
        simp only [GatherState.exponent, List.count_cons_self]
        simpa [Nat.add_comm] using
          cappedExponent_succ_normalized (tail.count head)
      simpa [headNormal, capIndex, w, gatheredTail, exponent,
        Word.toList] using gathered

/-! ## Semantic head stripping in `S5_213` -/

private theorem foldlEvalCongr {S : Type}
    (G : Semigroup S) (phi psi : Nat → S) :
    ∀ (letters : List Nat) (initial : S),
      (∀ c, c ∈ letters → phi c = psi c) →
      letters.foldl (fun value c => G.mul value (phi c)) initial =
        letters.foldl (fun value c => G.mul value (psi c)) initial
  | [], _, _ => rfl
  | c :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree c (List.Mem.head rest)]
      apply foldlEvalCongr G phi psi
      intro tested member
      exact agree tested (List.Mem.tail c member)

/-- Valuations agreeing on a word's letters evaluate equally. -/
private theorem evalCongrOnLetters {S : Type}
    (G : Semigroup S) (word : Word Nat)
    (phi psi : Nat → S)
    (agree : ∀ c ∈ word.toList, phi c = psi c) :
    G.eval phi word = G.eval psi word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [agree head (by simp [Word.toList])]
      apply foldlEvalCongr G phi psi
      intro c member
      exact agree c (List.Mem.tail head member)

private theorem evalHeadPow_eq_identity
    (phi : Nat → Fin 5) (h : Nat) (m : Nat)
    (atIdentity : phi h = (4 : Fin 5)) :
    Generated.Catalogue.S5_213.table.semigroup.eval phi (headPow h m) =
      (4 : Fin 5) := by
  induction m with
  | zero => simpa [headPow] using atIdentity
  | succ m induction =>
      rw [headPow, Semigroup.eval_append, induction]
      simp only [Semigroup.eval_singleton, atIdentity]
      exact (S5_213Invariant.s5_213_element_five_identity (4 : Fin 5)).1

/-- Evaluating the guard letter at the identity element `5` erases a
leading `h`-power. -/
private theorem evalStripHeadPow
    (phi : Nat → Fin 5) (h : Nat) (m : Nat) (tail : Word Nat)
    (atIdentity : phi h = (4 : Fin 5)) :
    Generated.Catalogue.S5_213.table.semigroup.eval phi
        (headPow h m ++ tail) =
      Generated.Catalogue.S5_213.table.semigroup.eval phi tail := by
  rw [Semigroup.eval_append,
    evalHeadPow_eq_identity phi h m atIdentity]
  exact
    (S5_213Invariant.s5_213_element_five_identity
      (Generated.Catalogue.S5_213.table.semigroup.eval phi tail)).1

private def updateValuation
    (phi : Nat → Fin 5) (selected : Nat) (value : Fin 5) : Nat → Fin 5 :=
  fun letter => if letter = selected then value else phi letter

/-- If `⟨h^m·u, h^m·v⟩` is `S5_213`-valid and `h` avoids both tails,
the tail pair is `S5_213`-valid. -/
theorem tailValid_of_headedValid
    (h : Nat) (m : Nat) (u v : Word Nat)
    (hu : h ∉ u.toList) (hv : h ∉ v.toList)
    (valid :
      (Identity.mk (headPow h m ++ u) (headPow h m ++ v)).SatisfiedBy
        Generated.Catalogue.S5_213.table.semigroup) :
    (Identity.mk u v).SatisfiedBy
      Generated.Catalogue.S5_213.table.semigroup := by
  intro phi
  have updated := valid (updateValuation phi h (4 : Fin 5))
  rw [evalStripHeadPow _ h m u (by simp [updateValuation]),
    evalStripHeadPow _ h m v (by simp [updateValuation])] at updated
  calc Generated.Catalogue.S5_213.table.semigroup.eval phi u
      = Generated.Catalogue.S5_213.table.semigroup.eval
          (updateValuation phi h (4 : Fin 5)) u :=
        evalCongrOnLetters _ u _ _ (fun c hc => by
          have : c ≠ h := fun eq => hu (eq ▸ hc)
          simp [updateValuation, this])
    _ = Generated.Catalogue.S5_213.table.semigroup.eval
          (updateValuation phi h (4 : Fin 5)) v := updated
    _ = Generated.Catalogue.S5_213.table.semigroup.eval phi v :=
        (evalCongrOnLetters _ v _ _ (fun c hc => by
          have : c ≠ h := fun eq => hv (eq ▸ hc)
          simp [updateValuation, this])).symm

/-! ## The syntactic head lemma for the S3_13 seam -/

/-- Left-normal-band derivations preserve heads: both LNB laws do, and
every `Derives` constructor transports the equality. -/
theorem lnbDerives_head_eq {left right : Word Nat}
    (derivation :
      Derives Examples.leftNormalBandThreeBasis left right) :
    left.head = right.head := by
  apply Examples.leftNormalBandValid_head_eq (Identity.mk left right)
  intro valuation
  exact derivation.sound
    Examples.leftNormalBandThreeBasis_models valuation

/-! ## The completeness theorem -/

/-- Shared fixed-head M2 completeness after the left factor has supplied
the only fact used from its identity theory: equality of the two heads. -/
theorem intersectionCompleteOfHeadEq
    (id : Identity Nat)
    (heads : id.lhs.head = id.rhs.head)
    (validB :
      id.SatisfiedBy Generated.Catalogue.S5_213.table.semigroup) :
    Derives sigma id.lhs id.rhs := by
  -- head normals on both sides
  have leftNormal := derivesHeadNormal id.lhs
  have rightNormal := derivesHeadNormal id.rhs
  -- the head-normal pair is S5_213-valid (soundness of sigma there)
  have validNormals :
      (Identity.mk (headNormal id.lhs) (headNormal id.rhs)).SatisfiedBy
        Generated.Catalogue.S5_213.table.semigroup := by
    intro phi
    have soundLeft := leftNormal.sound modelsS5_213 phi
    have soundRight := rightNormal.sound modelsS5_213 phi
    have := validB phi
    calc _ = _ := soundLeft.symm
      _ = _ := this
      _ = _ := soundRight
  -- equal cap indices via the S5_213 capped-multiplicity invariant
  have sameSig :=
    S5_213Invariant.sameSignature_of_s5_213_valid id validB
  have capEq : capIndex id.lhs.head id.lhs = capIndex id.rhs.head id.rhs := by
    unfold capIndex
    rw [cappedExponent_eq_min, cappedExponent_eq_min, ← heads]
    simpa [S5_213Syntax.cappedMultiplicity] using
      congrArg (fun count => count - 1)
        (sameSig.capped id.lhs.head)
  have capEqAtRight :
      capIndex id.rhs.head id.lhs = capIndex id.rhs.head id.rhs := by
    simpa only [heads] using capEq
  have emptyIff := filteredTail_nil_iff sameSig heads
  cases leftFilterEq :
      id.lhs.tail.filter
        (fun c => decide (c ≠ id.lhs.head)) with
  | nil =>
      have rightFilterEq :
          id.rhs.tail.filter
              (fun c => decide (c ≠ id.rhs.head)) = [] :=
        emptyIff.mp leftFilterEq
      have leftShape :=
        headNormal_eq_headPow_of_filter_nil id.lhs leftFilterEq
      have rightShape :=
        headNormal_eq_headPow_of_filter_nil id.rhs rightFilterEq
      have normalsEq : headNormal id.lhs = headNormal id.rhs := by
        rw [leftShape, rightShape, heads, capEqAtRight]
      rw [normalsEq] at leftNormal
      exact leftNormal.trans rightNormal.symm
  | cons leftFirst leftRest =>
      have rightNonempty :
          id.rhs.tail.filter
              (fun c => decide (c ≠ id.rhs.head)) ≠ [] := by
        intro rightEmpty
        have leftEmpty := emptyIff.mpr rightEmpty
        exact List.cons_ne_nil leftFirst leftRest
          (leftFilterEq.symm.trans leftEmpty)
      cases rightFilterEq :
          id.rhs.tail.filter
            (fun c => decide (c ≠ id.rhs.head)) with
      | nil =>
          exact False.elim (rightNonempty rightFilterEq)
      | cons rightFirst rightRest =>
          let leftTail : Word Nat := w leftFirst leftRest
          let rightTail : Word Nat := w rightFirst rightRest
          have leftShapeRaw :=
            headNormal_eq_headPow_append_of_filter_cons
              id.lhs leftFirst leftRest leftFilterEq
          have rightShape :=
            headNormal_eq_headPow_append_of_filter_cons
              id.rhs rightFirst rightRest rightFilterEq
          have leftShape :
              headNormal id.lhs =
                headPow id.rhs.head (capIndex id.rhs.head id.rhs) ++
                  leftTail := by
            simpa [leftTail, heads, capEqAtRight] using leftShapeRaw
          have leftAbsent : id.rhs.head ∉ leftTail.toList := by
            have absent : id.lhs.head ∉ leftTail.toList := by
              change id.lhs.head ∉ leftFirst :: leftRest
              rw [← leftFilterEq]
              exact head_not_mem_filteredTail id.lhs
            simpa [heads] using absent
          have rightAbsent : id.rhs.head ∉ rightTail.toList := by
            change id.rhs.head ∉ rightFirst :: rightRest
            rw [← rightFilterEq]
            exact head_not_mem_filteredTail id.rhs
          have headedValid :
              (Identity.mk
                (headPow id.rhs.head (capIndex id.rhs.head id.rhs) ++
                  leftTail)
                (headPow id.rhs.head (capIndex id.rhs.head id.rhs) ++
                  rightTail)).SatisfiedBy
                    Generated.Catalogue.S5_213.table.semigroup := by
            simpa [leftShape, rightShape] using validNormals
          have tailValid :=
            tailValid_of_headedValid id.rhs.head
              (capIndex id.rhs.head id.rhs) leftTail rightTail
              leftAbsent rightAbsent headedValid
          have tailSignature :=
            S5_213Invariant.sameSignature_of_s5_213_valid
              (Identity.mk leftTail rightTail) tailValid
          have tailDerivation :=
            S5_213Normalization.derives_of_sameSignature tailSignature
          have middle :
              Derives sigma (headNormal id.lhs) (headNormal id.rhs) := by
            rw [leftShape, rightShape]
            exact liftM2BasisUnderPrefixIdentity tailDerivation
              (headPow id.rhs.head (capIndex id.rhs.head id.rhs))
          exact leftNormal.trans <| middle.trans rightNormal.symm

/-- Shared fixed-head M2 completeness specialized to `S3_13`.  A caller only
has to identify validity in that table with the fixed-head condition. -/
theorem intersectionComplete
    (headEq :
      ∀ id : Identity Nat,
        id.SatisfiedBy Generated.S3_13.table.semigroup →
          id.lhs.head = id.rhs.head) :
    ∀ id : Identity Nat,
      id.SatisfiedBy Generated.S3_13.table.semigroup →
      id.SatisfiedBy Generated.Catalogue.S5_213.table.semigroup →
      Derives sigma id.lhs id.rhs := by
  intro id validA validB
  exact intersectionCompleteOfHeadEq id (headEq id validA) validB

end SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_213M2
