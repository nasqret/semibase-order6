import SemigroupBasis.CoRoots.Order6Condition8ThreeLawNormal
import SemigroupBasis.Generated.CatalogueOrder5Part07

/-!
# Shared five-law normalizer for the Condition-8 parity pair

The msg-0093 repaired system
`sigma = {xx = xxxx, xy = xyyy, xxy = xxyxx, xyxz = xyxzxx, xxxxy = xxxyx}`
is an exact basis for the joint identity theory of `S3_11 × S5_869` AND of
`S3_11 × S5_871` — the two joint theories are the same word partition, so
one normalizer serves both `S6_11550` and `S6_11554`.

Exact class descriptor (screen-verified 26/237/1380 at 2L<=9 / 3L<=7 /
4L<=6 on both pairs): the event sequence (first occurrences of the letters
in order, with a marker at the head letter's second occurrence) together
with per-letter count classes (head in {1, even, odd >= 3}, other letters
by parity).

Derivational engine (oracle-verified move set): the rotation law
`x³·Q·x = x⁴·Q` (an instance of `xxxxy = xxxyx`) absorbs the last
occurrence of a letter into its previous occurrence across any
intervening block, with `xy = xyyy` and `xx = xxxx` managing block sizes;
no block-length exactness is ever required. Iterating right-to-left
consolidates every letter into its event block, and the count laws then
collapse the blocks to their canonical sizes.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Condition8FiveLaw

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-! ## The displayed five-law system -/

def squareStableLaw : Identity Nat := ⟨w 0 [0], w 0 [0, 0, 0]⟩
def pairAppendLaw : Identity Nat := ⟨w 0 [1], w 0 [1, 1, 1]⟩
def squareEchoLaw : Identity Nat := ⟨w 0 [0, 1], w 0 [0, 1, 0, 0]⟩
def returnEchoLaw : Identity Nat := ⟨w 0 [1, 0, 2], w 0 [1, 0, 2, 0, 0]⟩
def rotationLaw : Identity Nat := ⟨w 0 [0, 0, 0, 1], w 0 [0, 0, 1, 0]⟩

def sigma : List (Identity Nat) :=
  [squareStableLaw, pairAppendLaw, squareEchoLaw, returnEchoLaw,
    rotationLaw]

private theorem squareStableMem : squareStableLaw ∈ sigma := by simp [sigma]
private theorem pairAppendMem : pairAppendLaw ∈ sigma := by simp [sigma]
private theorem squareEchoMem : squareEchoLaw ∈ sigma := by simp [sigma]
private theorem returnEchoMem : returnEchoLaw ∈ sigma := by simp [sigma]
private theorem rotationMem : rotationLaw ∈ sigma := by simp [sigma]

/-! ## Local list lemmas absent from the pinned core -/

private theorem replicate_add_local (n m : Nat) (x : Nat) :
    List.replicate (n + m) x =
      List.replicate n x ++ List.replicate m x := by
  induction n with
  | zero => simp
  | succ k ih =>
      have shift : k + 1 + m = (k + m) + 1 := by omega
      rw [shift, List.replicate_succ, List.replicate_succ,
        List.cons_append, ih]

private theorem nodup_append_singleton {l : List Nat} {x : Nat}
    (nodup : l.Nodup) (absent : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons head tail ih =>
      rw [List.cons_append, List.nodup_cons]
      rw [List.nodup_cons] at nodup
      refine ⟨?_, ih nodup.2
        (fun member => absent (List.mem_cons_of_mem _ member))⟩
      intro member
      rcases List.mem_append.mp member with inTail | inSingleton
      · exact nodup.1 inTail
      · have equal : head = x := by simpa using inSingleton
        exact absent (equal ▸ (by simp : head ∈ head :: tail))

private def instantiateThree (a b c : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | n + 3 => Word.singleton (n + 3)

/-! ## Block instances -/

/-- `X² = X⁴` (law 1). -/
theorem derivesSquareStable (x : Word Nat) :
    Derives sigma (x ++ x) (((x ++ x) ++ x) ++ x) := by
  have base : Derives sigma squareStableLaw.lhs squareStableLaw.rhs :=
    Derives.fromBasis squareStableMem
  have substituted :=
    Derives.subst base (instantiateThree x x x)
  simpa [squareStableLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `XY = XYYY` (law 2). -/
theorem derivesPairAppend (x y : Word Nat) :
    Derives sigma (x ++ y) (((x ++ y) ++ y) ++ y) := by
  have base : Derives sigma pairAppendLaw.lhs pairAppendLaw.rhs :=
    Derives.fromBasis pairAppendMem
  have substituted :=
    Derives.subst base (instantiateThree x y y)
  simpa [pairAppendLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `X²Y = X²YX²` (law 3). -/
theorem derivesSquareEcho (x y : Word Nat) :
    Derives sigma ((x ++ x) ++ y)
      (((((x ++ x) ++ y) ++ x) ++ x)) := by
  have base : Derives sigma squareEchoLaw.lhs squareEchoLaw.rhs :=
    Derives.fromBasis squareEchoMem
  have substituted :=
    Derives.subst base (instantiateThree x y y)
  simpa [squareEchoLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `XYXZ = XYXZX²` (law 4). -/
theorem derivesReturnEcho (x y z : Word Nat) :
    Derives sigma ((((x ++ y) ++ x) ++ z))
      ((((((x ++ y) ++ x) ++ z) ++ x) ++ x)) := by
  have base : Derives sigma returnEchoLaw.lhs returnEchoLaw.rhs :=
    Derives.fromBasis returnEchoMem
  have substituted :=
    Derives.subst base (instantiateThree x y z)
  simpa [returnEchoLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `X³Y X = X⁴Y` reversed reading of law 5: the absorption engine. -/
theorem derivesRotation (x y : Word Nat) :
    Derives sigma ((((x ++ x) ++ x) ++ x) ++ y)
      ((((x ++ x) ++ x) ++ y) ++ x) := by
  have base : Derives sigma rotationLaw.lhs rotationLaw.rhs :=
    Derives.fromBasis rotationMem
  have substituted :=
    Derives.subst base (instantiateThree x y y)
  simpa [rotationLaw, w, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-! ## Factor rewriting inside a word context -/

/-- Rewrite a derivable factor inside any word context. The left context
may be empty (`none`) or a word; the right context is a letter list. -/
private theorem derivesFactor {u v : Word Nat}
    (core : Derives sigma u v) :
    ∀ (left : Option (Word Nat)) (right : List Nat),
      Derives sigma
        (match left with
          | none => (⟨u.head, u.tail ++ right⟩ : Word Nat)
          | some p => p ++ (⟨u.head, u.tail ++ right⟩ : Word Nat))
        (match left with
          | none => (⟨v.head, v.tail ++ right⟩ : Word Nat)
          | some p => p ++ (⟨v.head, v.tail ++ right⟩ : Word Nat)) := by
  intro left right
  have rightExtended : Derives sigma
      (⟨u.head, u.tail ++ right⟩ : Word Nat)
      (⟨v.head, v.tail ++ right⟩ : Word Nat) := by
    cases right with
    | nil =>
        simpa using core
    | cons r rest =>
        have appended := Derives.appendRight core (⟨r, rest⟩ : Word Nat)
        have leftShape :
            u ++ (⟨r, rest⟩ : Word Nat) =
              (⟨u.head, u.tail ++ (r :: rest)⟩ : Word Nat) := rfl
        have rightShape :
            v ++ (⟨r, rest⟩ : Word Nat) =
              (⟨v.head, v.tail ++ (r :: rest)⟩ : Word Nat) := rfl
        rw [leftShape, rightShape] at appended
        exact appended
  cases left with
  | none => exact rightExtended
  | some p => exact Derives.prepend p rightExtended

/-! ## The oracle-verified merge move -/

/-- The merge move: with a nonempty guard before the earlier occurrence,
the last occurrence of `x` crosses the intervening block and doubles the
earlier occurrence: `r x q x ~ r x x q`. -/
theorem derivesMergeLast (r : Word Nat) (x : Nat) (q : Word Nat) :
    Derives sigma
      (((r ++ Word.singleton x) ++ q) ++ Word.singleton x)
      ((r ++ (Word.singleton x ++ Word.singleton x)) ++ q) := by
  -- r·x·q·x ~ r·x³·q·x  (law 2 factor with guard r)
  have growCore := derivesPairAppend r (Word.singleton x)
  have grow : Derives sigma
      (((r ++ Word.singleton x) ++ q) ++ Word.singleton x)
      (((((r ++ Word.singleton x) ++ Word.singleton x) ++
        Word.singleton x) ++ q) ++ Word.singleton x) := by
    have contextual :=
      Derives.appendRight (Derives.appendRight growCore q)
        (Word.singleton x)
    simpa [Word.append_assoc] using contextual
  -- x³·q·x ~ x⁴·q  (law 5 factor, guarded by r)
  have rotateCore := derivesRotation (Word.singleton x) q
  have rotate : Derives sigma
      (((((r ++ Word.singleton x) ++ Word.singleton x) ++
        Word.singleton x) ++ q) ++ Word.singleton x)
      (((((r ++ Word.singleton x) ++ Word.singleton x) ++
        Word.singleton x) ++ Word.singleton x) ++ q) := by
    have contextual := Derives.prepend r rotateCore.symm
    simpa [Word.append_assoc] using contextual
  -- x⁴·q ~ x²·q  (law 1 factor, guarded by r)
  have collapseCore := (derivesSquareStable (Word.singleton x)).symm
  have collapse : Derives sigma
      (((((r ++ Word.singleton x) ++ Word.singleton x) ++
        Word.singleton x) ++ Word.singleton x) ++ q)
      ((r ++ (Word.singleton x ++ Word.singleton x)) ++ q) := by
    have contextual :=
      Derives.appendRight (Derives.prepend r collapseCore) q
    simpa [Word.append_assoc] using contextual
  exact grow.trans (rotate.trans collapse)

/-! ## Block-size collapses -/

/-- A guarded letter run shrinks by a pair: `r·x^(m+3) ~ r·x^(m+1)`
letters (law 2 backwards behind the nonempty guard). -/
theorem derivesBlockCollapse (r : Word Nat) (x : Nat) (m : Nat) :
    Derives sigma
      (r ++ (⟨x, List.replicate (m + 2) x⟩ : Word Nat))
      (r ++ (⟨x, List.replicate m x⟩ : Word Nat)) := by
  cases m with
  | zero =>
      have core := (derivesPairAppend r (Word.singleton x)).symm
      have bigShape :
          ((r ++ Word.singleton x) ++ Word.singleton x) ++
              Word.singleton x =
            r ++ (⟨x, List.replicate 2 x⟩ : Word Nat) := by
        apply Word.toList_injective
        simp [Word.toList_append, Word.toList_singleton, Word.toList]
      have smallShape :
          r ++ Word.singleton x =
            r ++ (⟨x, List.replicate 0 x⟩ : Word Nat) := by
        apply Word.toList_injective
        simp [Word.toList_append, Word.toList_singleton, Word.toList]
      rw [bigShape, smallShape] at core
      exact core
  | succ n =>
      have core := (derivesPairAppend
        (r ++ (⟨x, List.replicate n x⟩ : Word Nat))
        (Word.singleton x)).symm
      have bigShape :
          (((r ++ (⟨x, List.replicate n x⟩ : Word Nat)) ++
                Word.singleton x) ++ Word.singleton x) ++
              Word.singleton x =
            r ++ (⟨x, List.replicate (n + 3) x⟩ : Word Nat) := by
        apply Word.toList_injective
        simp [Word.toList_append, Word.toList_singleton, Word.toList,
          List.replicate_succ']
      have smallShape :
          (r ++ (⟨x, List.replicate n x⟩ : Word Nat)) ++
              Word.singleton x =
            r ++ (⟨x, List.replicate (n + 1) x⟩ : Word Nat) := by
        apply Word.toList_injective
        simp [Word.toList_append, Word.toList_singleton, Word.toList,
          List.replicate_succ']
      rw [bigShape, smallShape] at core
      exact core

/-- The leading head run shrinks by a pair once it has at least three
trailing copies: `x^(m+4)·rest ~ x^(m+2)·rest` as letter counts
(law 1 factor, no guard needed). -/
theorem derivesHeadCollapse (x : Nat) (m : Nat) (rest : List Nat) :
    Derives sigma
      (⟨x, List.replicate (m + 3) x ++ rest⟩ : Word Nat)
      (⟨x, List.replicate (m + 1) x ++ rest⟩ : Word Nat) := by
  have core : Derives sigma
      (⟨x, [x, x, x]⟩ : Word Nat) (⟨x, [x]⟩ : Word Nat) := by
    have base := (derivesSquareStable (Word.singleton x)).symm
    have bigShape :
        ((Word.singleton x ++ Word.singleton x) ++ Word.singleton x) ++
            Word.singleton x = (⟨x, [x, x, x]⟩ : Word Nat) := by
      apply Word.toList_injective
      simp [Word.toList_append, Word.toList_singleton, Word.toList]
    have smallShape :
        Word.singleton x ++ Word.singleton x =
          (⟨x, [x]⟩ : Word Nat) := by
      apply Word.toList_injective
      simp [Word.toList_append, Word.toList_singleton, Word.toList]
    rw [bigShape, smallShape] at base
    exact base
  cases m with
  | zero =>
      have contextual := derivesFactor core none rest
      simpa using contextual
  | succ n =>
      have contextual := derivesFactor core
        (some (⟨x, List.replicate n x⟩ : Word Nat)) rest
      have bigShape :
          (⟨x, List.replicate n x⟩ : Word Nat) ++
              (⟨x, [x, x, x] ++ rest⟩ : Word Nat) =
            (⟨x, List.replicate (n + 4) x ++ rest⟩ : Word Nat) := by
        apply Word.toList_injective
        simp [Word.toList_append, Word.toList, List.replicate_succ',
          replicate_add_local]
      have smallShape :
          (⟨x, List.replicate n x⟩ : Word Nat) ++
              (⟨x, [x] ++ rest⟩ : Word Nat) =
            (⟨x, List.replicate (n + 2) x ++ rest⟩ : Word Nat) := by
        apply Word.toList_injective
        simp [Word.toList_append, Word.toList, List.replicate_succ',
          replicate_add_local]
      have adjusted : Derives sigma
          (⟨x, List.replicate (n + 4) x ++ rest⟩ : Word Nat)
          (⟨x, List.replicate (n + 2) x ++ rest⟩ : Word Nat) := by
        rw [← bigShape, ← smallShape]
        simpa using contextual
      simpa using adjusted

/-! ## Block representation of consolidated words -/

/-- A consolidated word is a run-length block list. -/
def renderBlocks (blocks : List (Nat × Nat)) : List Nat :=
  blocks.flatMap fun block => List.replicate block.2 block.1

@[simp]
theorem renderBlocks_nil : renderBlocks [] = [] := rfl

@[simp]
theorem renderBlocks_cons (block : Nat × Nat) (rest : List (Nat × Nat)) :
    renderBlocks (block :: rest) =
      List.replicate block.2 block.1 ++ renderBlocks rest := by
  simp [renderBlocks]

theorem renderBlocks_append (left right : List (Nat × Nat)) :
    renderBlocks (left ++ right) =
      renderBlocks left ++ renderBlocks right := by
  simp [renderBlocks]

/-- Merge one trailing occurrence into an interior block: with the block
strictly behind a nonempty guard,
`guard · x^n · mid · x ~ guard · x^(n+1) · mid`. -/
theorem derivesMergeBlock (guard : Word Nat) (x : Nat) (n : Nat)
    (mid : Word Nat) :
    Derives sigma
      (((guard ++ (⟨x, List.replicate n x⟩ : Word Nat)) ++ mid) ++
        Word.singleton x)
      ((guard ++ (⟨x, List.replicate (n + 1) x⟩ : Word Nat)) ++ mid) := by
  cases n with
  | zero =>
      have core := derivesMergeLast guard x mid
      have leftShape :
          ((guard ++ Word.singleton x) ++ mid) ++ Word.singleton x =
            ((guard ++ (⟨x, List.replicate 0 x⟩ : Word Nat)) ++ mid) ++
              Word.singleton x := by
        apply Word.toList_injective
        simp [Word.toList_append, Word.toList_singleton, Word.toList]
      have rightShape :
          (guard ++ (Word.singleton x ++ Word.singleton x)) ++ mid =
            (guard ++ (⟨x, List.replicate 1 x⟩ : Word Nat)) ++ mid := by
        apply Word.toList_injective
        simp [Word.toList_append, Word.toList_singleton, Word.toList]
      rw [leftShape, rightShape] at core
      exact core
  | succ m =>
      have core := derivesMergeLast
        (guard ++ (⟨x, List.replicate m x⟩ : Word Nat)) x mid
      have leftShape :
          (((guard ++ (⟨x, List.replicate m x⟩ : Word Nat)) ++
              Word.singleton x) ++ mid) ++ Word.singleton x =
            ((guard ++ (⟨x, List.replicate (m + 1) x⟩ : Word Nat)) ++
              mid) ++ Word.singleton x := by
        apply Word.toList_injective
        simp [Word.toList_append, Word.toList_singleton, Word.toList,
          List.replicate_succ']
      have rightShape :
          ((guard ++ (⟨x, List.replicate m x⟩ : Word Nat)) ++
              (Word.singleton x ++ Word.singleton x)) ++ mid =
            (guard ++ (⟨x, List.replicate (m + 2) x⟩ : Word Nat)) ++
              mid := by
        apply Word.toList_injective
        simp [Word.toList_append, Word.toList_singleton, Word.toList,
          List.replicate_succ']
      rw [leftShape, rightShape] at core
      exact core

/-! ## The canonical form -/

/-- Canonical block size for a non-head letter: its count parity picks
one or two copies. -/
def parityBlock (w : Word Nat) (x : Nat) : Nat :=
  if w.toList.count x % 2 = 0 then 2 else 1

/-- Canonical size of the head-echo block (the head's second-occurrence
event): total head count `C` contributes `C - 1` collapsed to one or two
copies. -/
def headEcho (w : Word Nat) : Nat :=
  if w.toList.count w.head % 2 = 0 then 1 else 2

/-- Scan the tail emitting canonical event blocks: fresh letters emit
their parity block, the head's first reappearance emits the echo block,
every other repeat is silent. -/
def canonicalScan (w : Word Nat) :
    List Nat → Bool → List Nat → List Nat
  | _, _, [] => []
  | seen, true, x :: rest =>
      if x ∈ seen then canonicalScan w seen true rest
      else
        List.replicate (parityBlock w x) x ++
          canonicalScan w (x :: seen) true rest
  | seen, false, x :: rest =>
      if x ∈ seen then
        if x = w.head then
          List.replicate (headEcho w) w.head ++
            canonicalScan w seen true rest
        else canonicalScan w seen false rest
      else
        List.replicate (parityBlock w x) x ++
          canonicalScan w (x :: seen) false rest

/-- The canonical representative of a word's descriptor class. -/
def canonicalize (w : Word Nat) : Word Nat :=
  ⟨w.head, canonicalScan w [w.head] false w.tail⟩

/-- The verified pair-class descriptor: equal canonical forms. -/
def SamePairClass (u v : Word Nat) : Prop :=
  canonicalize u = canonicalize v

/-! ## Consolidation: every word derives to its block form -/

/-- Letters carried by a block list. -/
def blockLetters (blocks : List (Nat × Nat)) : List Nat :=
  blocks.map Prod.fst

/-- Bump the first block of a letter. -/
def bumpBlock (x : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(x, 1)]
  | (y, n) :: rest =>
      if y = x then (y, n + 1) :: rest else (y, n) :: bumpBlock x rest

/-- One event step of the block fold. A fresh letter — including the
head's first reappearance — opens a new block at the end; a seen letter
bumps its existing block. -/
def stepBlocks (x : Nat) (blocks : List (Nat × Nat)) :
    List (Nat × Nat) :=
  if x ∈ blockLetters blocks then bumpBlock x blocks
  else blocks ++ [(x, 1)]

/-- The full block fold over a tail. -/
def foldBlocks (tail : List Nat) : List (Nat × Nat) :=
  tail.foldl (fun blocks x => stepBlocks x blocks) []

private theorem bumpBlock_split {pre post : List (Nat × Nat)}
    {x : Nat} {size : Nat}
    (absent : x ∉ blockLetters pre) :
    bumpBlock x (pre ++ (x, size) :: post) =
      pre ++ (x, size + 1) :: post := by
  induction pre with
  | nil => simp [bumpBlock]
  | cons block rest ih =>
      have blockMiss : block.1 ≠ x := by
        intro equal
        exact absent (by simp [blockLetters, equal])
      have restAbsent : x ∉ blockLetters rest := by
        intro member
        apply absent
        simp only [blockLetters, List.map_cons, List.mem_cons]
        exact Or.inr (by simpa [blockLetters] using member)
      cases block with
      | mk y n =>
          simp only [List.cons_append, bumpBlock]
          rw [if_neg (by simpa using blockMiss)]
          rw [ih restAbsent]

/-- Split a block list at the first block of a present letter. -/
private theorem split_at_letter {blocks : List (Nat × Nat)} {x : Nat}
    (present : x ∈ blockLetters blocks) :
    ∃ pre size post,
      blocks = pre ++ (x, size) :: post ∧ x ∉ blockLetters pre := by
  induction blocks with
  | nil => simp [blockLetters] at present
  | cons block rest ih =>
      by_cases hit : block.1 = x
      · refine ⟨[], block.2, rest, ?_, by simp [blockLetters]⟩
        cases block with
        | mk y n =>
            have yx : y = x := hit
            simp [yx]
      · have hit' : x ≠ block.1 := fun equal => hit equal.symm
        have tailPresent : x ∈ blockLetters rest := by
          simpa [blockLetters, hit, hit'] using present
        obtain ⟨pre, size, post, shape, absent⟩ := ih tailPresent
        refine ⟨block :: pre, size, post, by simp [shape], ?_⟩
        intro member
        simp only [blockLetters, List.map_cons, List.mem_cons] at member
        rcases member with headHit | preHit
        · exact hit headHit.symm
        · exact absent preHit

/-- Rendered block words are nonempty as soon as a block exists. -/
private theorem renderBlocks_positive_ne_nil
    {blocks : List (Nat × Nat)}
    (positive : ∀ block ∈ blocks, 1 ≤ block.2)
    (nonempty : blocks ≠ []) :
    renderBlocks blocks ≠ [] := by
  cases blocks with
  | nil => exact absurd rfl nonempty
  | cons block rest =>
      have blockPositive := positive block (by simp)
      cases block with
      | mk y n =>
          cases n with
          | zero => omega
          | succ m =>
              simp [renderBlocks, List.replicate_succ]

private theorem stepBlocks_positive {blocks : List (Nat × Nat)} {x : Nat}
    (positive : ∀ block ∈ blocks, 1 ≤ block.2) :
    ∀ block ∈ stepBlocks x blocks, 1 ≤ block.2 := by
  intro block member
  rw [stepBlocks] at member
  by_cases present : x ∈ blockLetters blocks
  · rw [if_pos present] at member
    obtain ⟨pre, size, post, shape, absent⟩ := split_at_letter present
    rw [shape, bumpBlock_split absent] at member
    rw [shape] at positive
    rcases List.mem_append.mp member with preMember | consMember
    · exact positive block (List.mem_append_left _ preMember)
    · rcases List.mem_cons.mp consMember with bumped | postMember
      · rw [bumped]
        omega
      · exact positive block
          (List.mem_append_right _ (List.mem_cons_of_mem _ postMember))
  · rw [if_neg present] at member
    rcases List.mem_append.mp member with old | fresh
    · exact positive block old
    · simp only [List.mem_singleton] at fresh
      simp [fresh]

/-- Shifting a letter across its own replicate block. -/
private theorem cons_replicate_shift (x m : Nat) (L : List Nat) :
    x :: (List.replicate m x ++ L) = List.replicate m x ++ x :: L := by
  induction m with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [← ih]

/-- Phase 1: every word derives to its consolidated block form. -/
private theorem derivesConsolidateAux (h : Nat) :
    ∀ (rest : List Nat) (blocks : List (Nat × Nat)),
      (∀ block ∈ blocks, 1 ≤ block.2) →
      Derives sigma
        (⟨h, renderBlocks blocks ++ rest⟩ : Word Nat)
        (⟨h, renderBlocks
          (rest.foldl (fun state x => stepBlocks x state) blocks)⟩ :
          Word Nat)
  | [], blocks, _ => by
      simpa using Derives.refl (⟨h, renderBlocks blocks⟩ : Word Nat)
  | x :: rest, blocks, positive => by
      have tailPositive := stepBlocks_positive (x := x) positive
      have tailStep := derivesConsolidateAux h rest
        (stepBlocks x blocks) tailPositive
      have headStep : Derives sigma
          (⟨h, renderBlocks blocks ++ (x :: rest)⟩ : Word Nat)
          (⟨h, renderBlocks (stepBlocks x blocks) ++ rest⟩ : Word Nat) := by
        by_cases present : x ∈ blockLetters blocks
        · obtain ⟨pre, size, post, shape, absent⟩ := split_at_letter present
          have sizePositive : 1 ≤ size := by
            have := positive (x, size) (by rw [shape]; simp)
            simpa using this
          obtain ⟨m, sizeShape⟩ : ∃ m, size = m + 1 :=
            ⟨size - 1, by omega⟩
          rw [stepBlocks, if_pos present, shape, bumpBlock_split absent]
          cases post with
          | nil =>
              -- the block is last: pure reassociation
              have shapeEq :
                  renderBlocks (pre ++ [(x, size)]) ++ (x :: rest) =
                    renderBlocks (pre ++ [(x, size + 1)]) ++ rest := by
                simp [renderBlocks_append, renderBlocks,
                  List.append_assoc, List.replicate_succ']
              rw [shapeEq]
              exact Derives.refl _
          | cons postHead postTail =>
              -- interior block: the merge move under a right context
              have postPositive :
                  ∀ block ∈ postHead :: postTail, 1 ≤ block.2 := by
                intro block member
                exact positive block (by
                  rw [shape]
                  exact List.mem_append_right _
                    (List.mem_cons_of_mem _ member))
              have postNonempty :
                  renderBlocks (postHead :: postTail) ≠ [] :=
                renderBlocks_positive_ne_nil postPositive (by simp)
              rcases midShape : renderBlocks (postHead :: postTail) with
                _ | ⟨midHead, midTail⟩
              · exact absurd midShape postNonempty
              have core := derivesMergeBlock
                (⟨h, renderBlocks pre⟩ : Word Nat) x m
                (⟨midHead, midTail⟩ : Word Nat)
              have contextual := derivesFactor core none rest
              have leftShape :
                  (⟨((((⟨h, renderBlocks pre⟩ : Word Nat) ++
                        (⟨x, List.replicate m x⟩ : Word Nat)) ++
                        (⟨midHead, midTail⟩ : Word Nat)) ++
                        Word.singleton x).head,
                      ((((⟨h, renderBlocks pre⟩ : Word Nat) ++
                        (⟨x, List.replicate m x⟩ : Word Nat)) ++
                        (⟨midHead, midTail⟩ : Word Nat)) ++
                        Word.singleton x).tail ++ rest⟩ : Word Nat) =
                    (⟨h, renderBlocks
                      (pre ++ (x, size) :: postHead :: postTail) ++
                        (x :: rest)⟩ : Word Nat) := by
                apply Word.toList_injective
                have midFlat :
                    List.replicate postHead.2 postHead.1 ++
                        postTail.flatMap
                          (fun block =>
                            List.replicate block.2 block.1) =
                      midHead :: midTail := by
                  simpa [renderBlocks] using midShape
                simp [Word.toList, Word.toList_append,
                  Word.toList_singleton, renderBlocks_append,
                  renderBlocks, sizeShape, List.replicate_succ',
                  List.append_assoc, midShape]
                rw [cons_replicate_shift, ← List.append_assoc,
                  midFlat, List.cons_append]
              have rightShape :
                  (⟨(((⟨h, renderBlocks pre⟩ : Word Nat) ++
                        (⟨x, List.replicate (m + 1) x⟩ : Word Nat)) ++
                        (⟨midHead, midTail⟩ : Word Nat)).head,
                      (((⟨h, renderBlocks pre⟩ : Word Nat) ++
                        (⟨x, List.replicate (m + 1) x⟩ : Word Nat)) ++
                        (⟨midHead, midTail⟩ : Word Nat)).tail ++ rest⟩ :
                    Word Nat) =
                    (⟨h, renderBlocks
                      (pre ++ (x, size + 1) :: postHead :: postTail) ++
                        rest⟩ : Word Nat) := by
                apply Word.toList_injective
                have midFlat :
                    List.replicate postHead.2 postHead.1 ++
                        postTail.flatMap
                          (fun block =>
                            List.replicate block.2 block.1) =
                      midHead :: midTail := by
                  simpa [renderBlocks] using midShape
                simp [Word.toList, Word.toList_append,
                  renderBlocks_append, renderBlocks, sizeShape,
                  List.replicate_succ', List.append_assoc, midShape]
                rw [cons_replicate_shift, ← List.append_assoc,
                  midFlat, List.cons_append]
              rw [leftShape, rightShape] at contextual
              exact contextual
        · rw [stepBlocks, if_neg present]
          have shapeEq :
              renderBlocks blocks ++ (x :: rest) =
                renderBlocks (blocks ++ [(x, 1)]) ++ rest := by
            simp [renderBlocks_append, renderBlocks, List.append_assoc]
          rw [shapeEq]
          exact Derives.refl _
      exact headStep.trans tailStep

/-- Phase 1, top level. -/
theorem derivesConsolidate (h : Nat) (tail : List Nat) :
    Derives sigma (⟨h, tail⟩ : Word Nat)
      (⟨h, renderBlocks (foldBlocks tail)⟩ : Word Nat) := by
  have aux := derivesConsolidateAux h tail [] (by simp)
  simpa [foldBlocks, renderBlocks] using aux

/-! ## Phase 2: collapse block sizes to their parity classes -/

/-- The canonical size of every block — echo blocks included — is two for
even sizes and one for odd sizes. -/
def canonSize (n : Nat) : Nat :=
  if n % 2 = 0 then 2 else 1

def canonBlocks (blocks : List (Nat × Nat)) : List (Nat × Nat) :=
  blocks.map fun block => (block.1, canonSize block.2)

/-- Collapse one guarded block to its parity class, inside a right
context. -/
private theorem derivesCollapseOne (h : Nat) (pre : List Nat) (x : Nat)
    (post : List Nat) :
    ∀ n, 1 ≤ n →
      Derives sigma
        (⟨h, (pre ++ List.replicate n x) ++ post⟩ : Word Nat)
        (⟨h, (pre ++ List.replicate (canonSize n) x) ++ post⟩ : Word Nat)
  | 1, _ => by
      simpa [canonSize] using
        Derives.refl
          (⟨h, (pre ++ List.replicate 1 x) ++ post⟩ : Word Nat)
  | 2, _ => by
      simpa [canonSize] using
        Derives.refl
          (⟨h, (pre ++ List.replicate 2 x) ++ post⟩ : Word Nat)
  | n + 3, _ => by
      have core := derivesBlockCollapse (⟨h, pre⟩ : Word Nat) x n
      have contextual := derivesFactor core none post
      have bigShape :
          (⟨((⟨h, pre⟩ : Word Nat) ++
                (⟨x, List.replicate (n + 2) x⟩ : Word Nat)).head,
              ((⟨h, pre⟩ : Word Nat) ++
                (⟨x, List.replicate (n + 2) x⟩ : Word Nat)).tail ++
                post⟩ : Word Nat) =
            (⟨h, (pre ++ List.replicate (n + 3) x) ++ post⟩ : Word Nat) := by
        apply Word.toList_injective
        simp [Word.toList, Word.toList_append, List.append_assoc,
          List.replicate_succ]
      have smallShape :
          (⟨((⟨h, pre⟩ : Word Nat) ++
                (⟨x, List.replicate n x⟩ : Word Nat)).head,
              ((⟨h, pre⟩ : Word Nat) ++
                (⟨x, List.replicate n x⟩ : Word Nat)).tail ++
                post⟩ : Word Nat) =
            (⟨h, (pre ++ List.replicate (n + 1) x) ++ post⟩ : Word Nat) := by
        apply Word.toList_injective
        simp [Word.toList, Word.toList_append, List.append_assoc,
          List.replicate_succ]
      have step : Derives sigma
          (⟨h, (pre ++ List.replicate (n + 3) x) ++ post⟩ : Word Nat)
          (⟨h, (pre ++ List.replicate (n + 1) x) ++ post⟩ : Word Nat) := by
        rw [← bigShape, ← smallShape]
        simpa using contextual
      have parity : canonSize (n + 3) = canonSize (n + 1) := by
        simp only [canonSize]
        by_cases even : (n + 1) % 2 = 0
        · rw [if_pos (by omega : (n + 3) % 2 = 0), if_pos even]
        · rw [if_neg (by omega : ¬(n + 3) % 2 = 0), if_neg even]
      have rest := derivesCollapseOne h pre x post (n + 1) (by omega)
      rw [parity]
      exact step.trans rest

/-- Phase 2, whole block list: collapse every block, left to right. -/
private theorem derivesCollapseAll (h : Nat) :
    ∀ (blocks : List (Nat × Nat)) (pre : List Nat),
      (∀ block ∈ blocks, 1 ≤ block.2) →
      Derives sigma
        (⟨h, pre ++ renderBlocks blocks⟩ : Word Nat)
        (⟨h, pre ++ renderBlocks (canonBlocks blocks)⟩ : Word Nat)
  | [], pre, _ => by
      simpa [canonBlocks, renderBlocks] using
        (Derives.refl (⟨h, pre⟩ : Word Nat) : Derives sigma _ _)
  | (x, n) :: rest, pre, positive => by
      have blockPositive : 1 ≤ n := by
        simpa using positive (x, n) (by simp)
      have first : Derives sigma
          (⟨h, pre ++ renderBlocks ((x, n) :: rest)⟩ : Word Nat)
          (⟨h, pre ++
            (List.replicate (canonSize n) x ++ renderBlocks rest)⟩ :
            Word Nat) := by
        have collapsed := derivesCollapseOne h pre x
          (renderBlocks rest) n blockPositive
        have leftShape :
            (pre ++ List.replicate n x) ++ renderBlocks rest =
              pre ++ renderBlocks ((x, n) :: rest) := by
          simp [renderBlocks_cons, List.append_assoc]
        have rightShape :
            (pre ++ List.replicate (canonSize n) x) ++
                renderBlocks rest =
              pre ++
                (List.replicate (canonSize n) x ++ renderBlocks rest) := by
          simp [List.append_assoc]
        rw [leftShape, rightShape] at collapsed
        exact collapsed
      have rest' := derivesCollapseAll h rest
        (pre ++ List.replicate (canonSize n) x)
        (fun block member => positive block (List.mem_cons_of_mem _ member))
      have restShaped : Derives sigma
          (⟨h, pre ++
            (List.replicate (canonSize n) x ++ renderBlocks rest)⟩ :
            Word Nat)
          (⟨h, pre ++
            renderBlocks (canonBlocks ((x, n) :: rest))⟩ : Word Nat) := by
        have canonShape :
            renderBlocks (canonBlocks ((x, n) :: rest)) =
              List.replicate (canonSize n) x ++
                renderBlocks (canonBlocks rest) := by
          simp [canonBlocks, renderBlocks_cons]
        rw [canonShape]
        have reassoc :
            pre ++ (List.replicate (canonSize n) x ++
              renderBlocks (canonBlocks rest)) =
              (pre ++ List.replicate (canonSize n) x) ++
                renderBlocks (canonBlocks rest) := by
          simp [List.append_assoc]
        have reassoc' :
            pre ++ (List.replicate (canonSize n) x ++
              renderBlocks rest) =
              (pre ++ List.replicate (canonSize n) x) ++
                renderBlocks rest := by
          simp [List.append_assoc]
        rw [reassoc, reassoc']
        exact rest'
      exact first.trans restShaped

/-- Phases 1 + 2 combined. -/
theorem derivesToCanonBlocks (h : Nat) (tail : List Nat) :
    Derives sigma (⟨h, tail⟩ : Word Nat)
      (⟨h, renderBlocks (canonBlocks (foldBlocks tail))⟩ : Word Nat) := by
  have phase1 := derivesConsolidate h tail
  have positive : ∀ block ∈ foldBlocks tail, 1 ≤ block.2 := by
    have general :
        ∀ (letters : List Nat) (start : List (Nat × Nat)),
          (∀ block ∈ start, 1 ≤ block.2) →
          ∀ block ∈ letters.foldl
            (fun state x => stepBlocks x state) start, 1 ≤ block.2 := by
      intro letters
      induction letters with
      | nil => intro start ok; simpa using ok
      | cons x rest ih =>
          intro start ok
          exact ih (stepBlocks x start) (stepBlocks_positive ok)
    exact general tail [] (by simp)
  have phase2 := derivesCollapseAll h (foldBlocks tail) [] positive
  have shaped : Derives sigma
      (⟨h, renderBlocks (foldBlocks tail)⟩ : Word Nat)
      (⟨h, renderBlocks (canonBlocks (foldBlocks tail))⟩ : Word Nat) := by
    simpa using phase2
  exact phase1.trans shaped

/-! ## Phase 3: the collapsed block form is the canonical scan -/

/-- The bare event list of the canonical scan. -/
def scanEvents (h : Nat) : List Nat → Bool → List Nat → List Nat
  | _, _, [] => []
  | seen, true, x :: rest =>
      if x ∈ seen then scanEvents h seen true rest
      else x :: scanEvents h (x :: seen) true rest
  | seen, false, x :: rest =>
      if x ∈ seen then
        if x = h then h :: scanEvents h seen true rest
        else scanEvents h seen false rest
      else x :: scanEvents h (x :: seen) false rest

/-- The size emitted for each event letter. -/
def eventSize (w : Word Nat) (x : Nat) : Nat :=
  if x = w.head then headEcho w else parityBlock w x

/-- The canonical scan renders its event list. -/
private theorem canonicalScan_eq_flatMap (w : Word Nat) :
    ∀ (rest : List Nat) (seen : List Nat) (head2Done : Bool),
      w.head ∈ seen →
      canonicalScan w seen head2Done rest =
        (scanEvents w.head seen head2Done rest).flatMap
          (fun x => List.replicate (eventSize w x) x)
  | [], seen, true, _ => by simp [canonicalScan, scanEvents]
  | [], seen, false, _ => by simp [canonicalScan, scanEvents]
  | x :: rest, seen, true, headSeen => by
      rw [canonicalScan, scanEvents]
      by_cases seenCase : x ∈ seen
      · rw [if_pos seenCase, if_pos seenCase]
        exact canonicalScan_eq_flatMap w rest seen true headSeen
      · rw [if_neg seenCase, if_neg seenCase]
        rw [canonicalScan_eq_flatMap w rest (x :: seen) true
          (List.mem_cons_of_mem _ headSeen)]
        have headMiss : x ≠ w.head := fun equal =>
          seenCase (equal ▸ headSeen)
        simp [List.flatMap_cons, eventSize, headMiss]
  | x :: rest, seen, false, headSeen => by
      rw [canonicalScan, scanEvents]
      by_cases seenCase : x ∈ seen
      · rw [if_pos seenCase, if_pos seenCase]
        by_cases headCase : x = w.head
        · rw [if_pos headCase, if_pos headCase]
          rw [canonicalScan_eq_flatMap w rest seen true headSeen]
          simp [List.flatMap_cons, eventSize]
        · rw [if_neg headCase, if_neg headCase]
          exact canonicalScan_eq_flatMap w rest seen false headSeen
      · rw [if_neg seenCase, if_neg seenCase]
        rw [canonicalScan_eq_flatMap w rest (x :: seen) false
          (List.mem_cons_of_mem _ headSeen)]
        have headMiss : x ≠ w.head := fun equal =>
          seenCase (equal ▸ headSeen)
        simp [List.flatMap_cons, eventSize, headMiss]

/-- Every event letter is the head or outside the running seen set. -/
private theorem scanEvents_mem (h : Nat) :
    ∀ (rest : List Nat) (seen : List Nat) (head2Done : Bool) (y : Nat),
      y ∈ scanEvents h seen head2Done rest → y = h ∨ y ∉ seen
  | [], _, true, _ => by simp [scanEvents]
  | [], _, false, _ => by simp [scanEvents]
  | x :: rest, seen, true, y => by
      rw [scanEvents]
      by_cases seenCase : x ∈ seen
      · rw [if_pos seenCase]
        exact scanEvents_mem h rest seen true y
      · rw [if_neg seenCase]
        intro member
        rcases List.mem_cons.mp member with equal | inner
        · exact Or.inr (equal ▸ seenCase)
        · rcases scanEvents_mem h rest (x :: seen) true y inner with
            headHit | notSeen
          · exact Or.inl headHit
          · exact Or.inr fun inSeen =>
              notSeen (List.mem_cons_of_mem _ inSeen)
  | x :: rest, seen, false, y => by
      rw [scanEvents]
      by_cases seenCase : x ∈ seen
      · rw [if_pos seenCase]
        by_cases headCase : x = h
        · rw [if_pos headCase]
          intro member
          rcases List.mem_cons.mp member with equal | inner
          · exact Or.inl equal
          · exact scanEvents_mem h rest seen true y inner
        · rw [if_neg headCase]
          exact scanEvents_mem h rest seen false y
      · rw [if_neg seenCase]
        intro member
        rcases List.mem_cons.mp member with equal | inner
        · exact Or.inr (equal ▸ seenCase)
        · rcases scanEvents_mem h rest (x :: seen) false y inner with
            headHit | notSeen
          · exact Or.inl headHit
          · exact Or.inr fun inSeen =>
              notSeen (List.mem_cons_of_mem _ inSeen)

/-- With the echo already emitted, every event letter is outside the
running seen set. -/
private theorem scanEvents_mem_true (h : Nat) :
    ∀ (rest : List Nat) (seen : List Nat) (y : Nat),
      y ∈ scanEvents h seen true rest → y ∉ seen
  | [], _, _ => by simp [scanEvents]
  | x :: rest, seen, y => by
      rw [scanEvents]
      by_cases seenCase : x ∈ seen
      · rw [if_pos seenCase]
        exact scanEvents_mem_true h rest seen y
      · rw [if_neg seenCase]
        intro member inSeen
        rcases List.mem_cons.mp member with equal | inner
        · exact seenCase (equal ▸ inSeen)
        · exact scanEvents_mem_true h rest (x :: seen) y inner
            (List.mem_cons_of_mem _ inSeen)

/-- Pointwise count transfer over a block list with a unique bumped
block. -/
private theorem map_count_bump
    {pre post : List (Nat × Nat)} {x : Nat} {size : Nat}
    (rest : List Nat)
    (preMiss : x ∉ blockLetters pre)
    (postMiss : x ∉ blockLetters post) :
    (pre ++ (x, size + 1) :: post).map
        (fun block => (block.1, block.2 + rest.count block.1)) =
      (pre ++ (x, size) :: post).map
        (fun block => (block.1, block.2 + (x :: rest).count block.1)) := by
  simp only [List.map_append, List.map_cons]
  congr 1
  · apply List.map_congr_left
    intro block member
    have blockMiss : block.1 ≠ x := by
      intro equal
      exact preMiss (by
        simp only [blockLetters, List.mem_map]
        exact ⟨block, member, equal⟩)
    have blockMiss' : x ≠ block.1 := fun equal => blockMiss equal.symm
    have countEq : (x :: rest).count block.1 = rest.count block.1 := by
      simp [List.count_cons, blockMiss, blockMiss']
    rw [countEq]
  · congr 1
    · have countEq : (x :: rest).count x = rest.count x + 1 := by
        simp [List.count_cons]
      rw [countEq]
      simp only [Prod.mk.injEq, true_and]
      omega
    · apply List.map_congr_left
      intro block member
      have blockMiss : block.1 ≠ x := by
        intro equal
        exact postMiss (by
          simp only [blockLetters, List.mem_map]
          exact ⟨block, member, equal⟩)
      have blockMiss' : x ≠ block.1 := fun equal => blockMiss equal.symm
      have countEq : (x :: rest).count block.1 = rest.count block.1 := by
        simp [List.count_cons, blockMiss, blockMiss']
      rw [countEq]

/-- Pointwise count transfer over an event list avoiding the consumed
letter. -/
private theorem map_count_avoid
    {events : List Nat} {x : Nat} (rest : List Nat)
    (avoid : ∀ y ∈ events, y ≠ x) :
    events.map (fun y => (y, (x :: rest).count y)) =
      events.map (fun y => (y, rest.count y)) := by
  apply List.map_congr_left
  intro y member
  have yxMiss : y ≠ x := avoid y member
  have xyMiss : x ≠ y := fun equal => yxMiss equal.symm
  have countEq : (x :: rest).count y = rest.count y := by
    simp [List.count_cons, yxMiss, xyMiss]
  rw [countEq]

/-- Unfolding equation for a scan step with the flag left abstract,
in the nested-if shape used by the fold characterization. -/
private theorem scanEvents_cons (h x : Nat) (seen rest : List Nat)
    (done : Bool) :
    scanEvents h seen done (x :: rest) =
      if x ∈ seen then
        if x = h then
          if done then scanEvents h seen true rest
          else h :: scanEvents h seen true rest
        else scanEvents h seen done rest
      else x :: scanEvents h (x :: seen) done rest := by
  cases done with
  | true =>
      rw [scanEvents]
      by_cases seenCase : x ∈ seen
      · rw [if_pos seenCase, if_pos seenCase]
        by_cases headCase : x = h
        · rw [if_pos headCase, if_pos rfl]
        · rw [if_neg headCase]
      · rw [if_neg seenCase, if_neg seenCase]
  | false =>
      rw [scanEvents]
      by_cases seenCase : x ∈ seen
      · rw [if_pos seenCase, if_pos seenCase]
        by_cases headCase : x = h
        · rw [if_neg Bool.false_ne_true, if_pos headCase]
        · rw [if_neg headCase, if_neg headCase]
      · rw [if_neg seenCase, if_neg seenCase]

/-- Fold characterization: the block fold is the scan-event list paired
with total counts. -/
private theorem foldBlocks_eq_events (h : Nat) :
    ∀ (rest : List Nat) (blocks : List (Nat × Nat)) (seen : List Nat)
      (head2Done : Bool),
      (blockLetters blocks).Nodup →
      (∀ x, x ∈ seen ↔ (x = h ∨ x ∈ blockLetters blocks)) →
      (head2Done = true ↔ h ∈ blockLetters blocks) →
      rest.foldl (fun state x => stepBlocks x state) blocks =
        blocks.map (fun block => (block.1, block.2 + rest.count block.1)) ++
          (scanEvents h seen head2Done rest).map
            (fun x => (x, rest.count x))
  | [], blocks, seen, head2Done, _, _, _ => by
      simp [scanEvents]
  | x :: rest, blocks, seen, head2Done, nodup, seenCorr, doneCorr => by
      rw [List.foldl_cons, scanEvents_cons]
      by_cases present : x ∈ blockLetters blocks
      · have seenHit : x ∈ seen := (seenCorr x).mpr (Or.inr present)
        rw [if_pos seenHit]
        obtain ⟨pre, size, post, shape, preMiss⟩ := split_at_letter present
        have postMiss : x ∉ blockLetters post := by
          intro member
          have expanded : blockLetters blocks =
              blockLetters pre ++ x :: blockLetters post := by
            rw [shape]
            simp [blockLetters]
          rw [expanded] at nodup
          have tailNodup :
              (x :: blockLetters post).Nodup :=
            (List.nodup_append.mp nodup).2.1
          exact (List.nodup_cons.mp tailNodup).1 member
        have stepShape : stepBlocks x blocks =
            pre ++ (x, size + 1) :: post := by
          rw [stepBlocks, if_pos present, shape, bumpBlock_split preMiss]
        have stepLetters :
            blockLetters (stepBlocks x blocks) = blockLetters blocks := by
          rw [stepShape, shape]
          simp [blockLetters]
        have nodup' : (blockLetters (stepBlocks x blocks)).Nodup := by
          rw [stepLetters]; exact nodup
        have seenCorr' : ∀ y, y ∈ seen ↔
            (y = h ∨ y ∈ blockLetters (stepBlocks x blocks)) := by
          intro y
          rw [stepLetters]
          exact seenCorr y
        by_cases headCase : x = h
        · have doneTrue : head2Done = true :=
            doneCorr.mpr (headCase ▸ present)
          subst doneTrue
          rw [if_pos headCase, if_pos rfl]
          have doneCorr' : (true = true) ↔
              h ∈ blockLetters (stepBlocks x blocks) := by
            rw [stepLetters]; exact doneCorr
          have ih := foldBlocks_eq_events h rest (stepBlocks x blocks)
            seen true nodup' seenCorr' doneCorr'
          rw [ih, stepShape]
          have blocksBridge :
              (pre ++ (x, size + 1) :: post).map
                  (fun block => (block.1, block.2 + rest.count block.1)) =
                blocks.map
                  (fun block =>
                    (block.1, block.2 + (x :: rest).count block.1)) := by
            rw [shape]
            exact map_count_bump rest preMiss postMiss
          have eventsBridge :
              (scanEvents h seen true rest).map
                  (fun y => (y, rest.count y)) =
                (scanEvents h seen true rest).map
                  (fun y => (y, (x :: rest).count y)) := by
            refine (map_count_avoid rest ?_).symm
            intro y member equal
            exact scanEvents_mem_true h rest seen y member
              (equal ▸ seenHit)
          rw [blocksBridge, eventsBridge]
        · rw [if_neg headCase]
          have doneCorr' : head2Done = true ↔
              h ∈ blockLetters (stepBlocks x blocks) := by
            rw [stepLetters]; exact doneCorr
          have ih := foldBlocks_eq_events h rest (stepBlocks x blocks)
            seen head2Done nodup' seenCorr' doneCorr'
          rw [ih, stepShape]
          have blocksBridge :
              (pre ++ (x, size + 1) :: post).map
                  (fun block => (block.1, block.2 + rest.count block.1)) =
                blocks.map
                  (fun block =>
                    (block.1, block.2 + (x :: rest).count block.1)) := by
            rw [shape]
            exact map_count_bump rest preMiss postMiss
          have eventsBridge :
              (scanEvents h seen head2Done rest).map
                  (fun y => (y, rest.count y)) =
                (scanEvents h seen head2Done rest).map
                  (fun y => (y, (x :: rest).count y)) := by
            refine (map_count_avoid rest ?_).symm
            intro y member equal
            rcases scanEvents_mem h rest seen head2Done y member with
              headHit | notSeen
            · exact headCase (equal ▸ headHit)
            · exact notSeen (equal ▸ seenHit)
          rw [blocksBridge, eventsBridge]
      · -- fresh letter (including the head's first reappearance)
        have stepShape : stepBlocks x blocks = blocks ++ [(x, 1)] := by
          rw [stepBlocks, if_neg present]
        have stepLetters :
            blockLetters (stepBlocks x blocks) =
              blockLetters blocks ++ [x] := by
          rw [stepShape]
          simp [blockLetters]
        have nodup' : (blockLetters (stepBlocks x blocks)).Nodup := by
          rw [stepLetters]
          exact nodup_append_singleton nodup present
        have blocksBridge :
            blocks.map (fun block => (block.1, block.2 + rest.count block.1)) =
              blocks.map
                (fun block =>
                  (block.1, block.2 + (x :: rest).count block.1)) := by
          apply List.map_congr_left
          intro block member
          have blockMiss : block.1 ≠ x := by
            intro equal
            exact present (by
              simp only [blockLetters, List.mem_map]
              exact ⟨block, member, equal⟩)
          have blockMiss' : x ≠ block.1 := fun equal => blockMiss equal.symm
          have countEq : (x :: rest).count block.1 = rest.count block.1 := by
            simp [List.count_cons, blockMiss, blockMiss']
          rw [countEq]
        have selfCount : (x :: rest).count x = rest.count x + 1 := by
          simp [List.count_cons]
        by_cases headCase : x = h
        · have seenHit : x ∈ seen := (seenCorr x).mpr (Or.inl headCase)
          have doneFalse : head2Done = false := by
            cases head2Done with
            | false => rfl
            | true =>
                exact absurd (headCase ▸ doneCorr.mp rfl) present
          subst doneFalse
          rw [if_pos seenHit, if_pos headCase,
            if_neg Bool.false_ne_true]
          have seenCorr' : ∀ y, y ∈ seen ↔
              (y = h ∨ y ∈ blockLetters (stepBlocks x blocks)) := by
            intro y
            rw [stepLetters]
            constructor
            · intro member
              rcases (seenCorr y).mp member with headHit | old
              · exact Or.inl headHit
              · exact Or.inr (List.mem_append_left _ old)
            · intro cases
              rcases cases with headHit | member
              · exact (seenCorr y).mpr (Or.inl headHit)
              · rcases List.mem_append.mp member with old | fresh
                · exact (seenCorr y).mpr (Or.inr old)
                · simp only [List.mem_singleton] at fresh
                  exact (seenCorr y).mpr (Or.inl (fresh.trans headCase))
          have doneCorr' : (true = true) ↔
              h ∈ blockLetters (stepBlocks x blocks) := by
            rw [stepLetters]
            constructor
            · intro _
              exact List.mem_append_right _
                ((by simp [headCase.symm] : h ∈ [x]))
            · intro _
              rfl
          have ih := foldBlocks_eq_events h rest (stepBlocks x blocks)
            seen true nodup' seenCorr' doneCorr'
          rw [ih, stepShape]
          have eventsBridge :
              (scanEvents h seen true rest).map
                  (fun y => (y, rest.count y)) =
                (scanEvents h seen true rest).map
                  (fun y => (y, (x :: rest).count y)) := by
            refine (map_count_avoid rest ?_).symm
            intro y member equal
            exact scanEvents_mem_true h rest seen y member
              (equal ▸ seenHit)
          rw [List.map_append, blocksBridge, eventsBridge]
          have countBridge : (1 : Nat) + rest.count x =
              (x :: rest).count x := by
            rw [selfCount]
            omega
          have countBridgeH : (1 : Nat) + rest.count h =
              (h :: rest).count h := by
            rw [← headCase]
            exact countBridge
          simp only [List.map_cons, List.map_nil,
            List.append_assoc, List.singleton_append, countBridge,
            countBridgeH, headCase]
        · have seenMiss : x ∉ seen := by
            intro member
            rcases (seenCorr x).mp member with headHit | old
            · exact headCase headHit
            · exact present old
          rw [if_neg seenMiss]
          have seenCorr' : ∀ y, y ∈ x :: seen ↔
              (y = h ∨ y ∈ blockLetters (stepBlocks x blocks)) := by
            intro y
            rw [stepLetters]
            constructor
            · intro member
              rcases List.mem_cons.mp member with equal | old
              · exact Or.inr (List.mem_append_right _
                  (equal ▸ List.mem_singleton_self x))
              · rcases (seenCorr y).mp old with headHit | inBlocks
                · exact Or.inl headHit
                · exact Or.inr (List.mem_append_left _ inBlocks)
            · intro cases
              rcases cases with headHit | member
              · exact List.mem_cons_of_mem _
                  ((seenCorr y).mpr (Or.inl headHit))
              · rcases List.mem_append.mp member with old | fresh
                · exact List.mem_cons_of_mem _
                    ((seenCorr y).mpr (Or.inr old))
                · simp only [List.mem_singleton] at fresh
                  exact fresh ▸ (by simp : x ∈ x :: seen)
          have doneCorr' : head2Done = true ↔
              h ∈ blockLetters (stepBlocks x blocks) := by
            rw [stepLetters]
            constructor
            · intro done
              exact List.mem_append_left _ (doneCorr.mp done)
            · intro member
              rcases List.mem_append.mp member with old | fresh
              · exact doneCorr.mpr old
              · simp only [List.mem_singleton] at fresh
                exact absurd fresh.symm headCase
          have ih := foldBlocks_eq_events h rest (stepBlocks x blocks)
            (x :: seen) head2Done nodup' seenCorr' doneCorr'
          rw [ih, stepShape]
          have eventsBridge :
              (scanEvents h (x :: seen) head2Done rest).map
                  (fun y => (y, rest.count y)) =
                (scanEvents h (x :: seen) head2Done rest).map
                  (fun y => (y, (x :: rest).count y)) := by
            refine (map_count_avoid rest ?_).symm
            intro y member equal
            rcases scanEvents_mem h rest (x :: seen) head2Done y member with
              headHit | notSeen
            · exact headCase (equal ▸ headHit)
            · exact notSeen (equal ▸ (by simp : x ∈ x :: seen))
          rw [List.map_append, blocksBridge, eventsBridge]
          have countBridge : (1 : Nat) + rest.count x =
              (x :: rest).count x := by
            rw [selfCount]
            omega
          simp only [List.map_cons, List.map_nil,
            List.append_assoc, List.singleton_append, countBridge]

/-- Phase 3, assembled: the collapsed block form is the canonical scan. -/
private theorem canonBlocks_render_eq_scan (w : Word Nat) :
    renderBlocks (canonBlocks (foldBlocks w.tail)) =
      canonicalScan w [w.head] false w.tail := by
  have characterization := foldBlocks_eq_events w.head w.tail []
    [w.head] false (by simp [blockLetters])
    (fun x => by simp [blockLetters])
    (by simp [blockLetters])
  have scanFlat := canonicalScan_eq_flatMap w w.tail [w.head] false
    (by simp)
  rw [foldBlocks, characterization, scanFlat]
  simp only [List.map_nil, List.nil_append]
  have renderMap :
      renderBlocks (canonBlocks
        ((scanEvents w.head [w.head] false w.tail).map
          (fun x => (x, w.tail.count x)))) =
        (scanEvents w.head [w.head] false w.tail).flatMap
          (fun x => List.replicate (canonSize (w.tail.count x)) x) := by
    simp [renderBlocks, canonBlocks, List.map_map, List.flatMap_map,
      Function.comp_def]
  rw [renderMap]
  have sizeBridge :
      (fun x => List.replicate (canonSize (w.tail.count x)) x) =
        (fun x => List.replicate (eventSize w x) x) := by
    funext x
    congr 1
    by_cases headCase : x = w.head
    · have countShape : w.toList.count w.head = w.tail.count w.head + 1 := by
        cases w with
        | mk head tail =>
            simp [Word.toList]
      rw [headCase, eventSize, if_pos rfl, headEcho, canonSize,
        countShape]
      by_cases parity : w.tail.count w.head % 2 = 0
      · rw [if_pos parity,
          if_neg (by omega : ¬ ((w.tail.count w.head + 1) % 2 = 0))]
      · rw [if_neg parity,
          if_pos (by omega : (w.tail.count w.head + 1) % 2 = 0)]
    · have headCase' : ¬ w.head = x := fun equal => headCase equal.symm
      have countShape : w.toList.count x = w.tail.count x := by
        cases w with
        | mk head tail =>
            simp only [Word.head] at headCase headCase'
            simp [Word.toList, List.count_cons, headCase, headCase']
      simp [eventSize, if_neg headCase, parityBlock, canonSize,
        countShape]
  rw [sizeBridge]

/-- The full canonicalization derivation. -/
theorem derivesToCanonical (w : Word Nat) :
    Derives sigma w (canonicalize w) := by
  have blocks := derivesToCanonBlocks w.head w.tail
  rw [canonicalize, ← canonBlocks_render_eq_scan w]
  exact blocks

/-- Completeness of the five-law system for the pair descriptor. -/
theorem derivesOfSamePairClass {u v : Word Nat}
    (same : SamePairClass u v) : Derives sigma u v := by
  have du := derivesToCanonical u
  have dv := derivesToCanonical v
  rw [SamePairClass] at same
  exact du.trans (same ▸ dv.symm)

/-! ## Semantic extraction: the race gadget -/

section RaceExtraction

variable {S : Type} {G : Semigroup S}

/-- Folding letters whose images freeze the accumulator, restricted to a
member list. -/
private theorem foldl_frozen_mem (valuation : Nat → S) {acc : S} :
    ∀ letters : List Nat,
      (∀ z ∈ letters, G.mul acc (valuation z) = acc) →
      letters.foldl (fun current z => G.mul current (valuation z)) acc =
        acc
  | [], _ => rfl
  | z :: rest, frozen => by
      rw [List.foldl_cons, frozen z (by simp)]
      exact foldl_frozen_mem valuation rest
        fun y member => frozen y (List.mem_cons_of_mem _ member)

/-- Split a list at the first occurrence of a member. -/
private theorem firstSplit {l : List Nat} {x : Nat} (member : x ∈ l) :
    ∃ p s, l = p ++ x :: s ∧ x ∉ p ∧ p.length = l.idxOf x := by
  induction l with
  | nil => simp at member
  | cons y rest ih =>
      by_cases hit : y = x
      · exact ⟨[], rest, by simp [hit], by simp,
          by simp [List.idxOf_cons, hit]⟩
      · have inner : x ∈ rest := by
          rcases List.mem_cons.mp member with equal | tail
          · exact absurd equal.symm hit
          · exact tail
        obtain ⟨p, s, shape, absent, length⟩ := ih inner
        refine ⟨y :: p, s, by simp [shape], ?_, ?_⟩
        · intro inCons
          rcases List.mem_cons.mp inCons with equal | inP
          · exact hit equal.symm
          · exact absent inP
        · have yxMiss : y ≠ x := hit
          have missBeq : (y == x) = false := by simp [yxMiss]
          simp [List.idxOf_cons, missBeq, length]

/-- A member of the strict prefix has a strictly smaller first index. -/
private theorem idxOf_lt_of_mem_prefix {l p s : List Nat} {x y : Nat}
    (shape : l = p ++ x :: s) (absent : x ∉ p) (member : y ∈ p) :
    l.idxOf y < l.idxOf x := by
  induction p generalizing l with
  | nil => simp at member
  | cons z rest ih =>
      subst shape
      by_cases hit : z = y
      · have zxMiss : z ≠ x := by
          intro equal
          exact absent (by simp [equal])
        have hitBeq : (z == y) = true := by simp [hit]
        have missBeqZ : (z == x) = false := by simp [zxMiss]
        simp only [List.cons_append, List.idxOf_cons, hitBeq, missBeqZ,
          cond_true, cond_false]
        omega
      · have innerMember : y ∈ rest := by
          rcases List.mem_cons.mp member with equal | tail
          · exact absurd equal.symm hit
          · exact tail
        have innerAbsent : x ∉ rest := fun inner =>
          absent (List.mem_cons_of_mem _ inner)
        have inner := ih (l := rest ++ x :: s) rfl innerAbsent innerMember
        have missY : (z == y) = false := by simp [hit]
        have zxMiss : z ≠ x := fun equal => absent (by simp [equal])
        have missX : (z == x) = false := by simp [zxMiss]
        simp only [List.cons_append, List.idxOf_cons, missY, missX,
          cond_false]
        omega

/-- The race evaluation: with contestants `a ↦ fourE` and `b ↦ oneE` and
everything else neutral, evaluation is decided by whichever trigger
occurs first. The trigger letter, its transition, and the start state are
parameters, so one lemma serves win-first, death-first, and both start
states. -/
private theorem race_eval_trigger {a b trigger : Nat}
    {threeE oneE fourE : S} {start outcome : S}
    (neutral : ∀ z, z ≠ a → z ≠ b → G.mul start
      (if z = a then fourE else if z = b then oneE else threeE) = start)
    (triggerStep :
      G.mul start
        (if trigger = a then fourE else
          if trigger = b then oneE else threeE) = outcome)
    (outcomeDead : ∀ z, G.mul outcome z = outcome)
    {head : Nat} {t : List Nat}
    (startState :
      (if head = a then fourE else if head = b then oneE else threeE) =
        start)
    {p s : List Nat}
    (shape : t = p ++ trigger :: s)
    (aFresh : a ∉ p) (bFresh : b ∉ p) :
    G.eval (fun z => if z = a then fourE else if z = b then oneE else threeE)
        (⟨head, t⟩ : Word Nat) = outcome := by
  show t.foldl _ _ = outcome
  rw [shape, List.foldl_append]
  have prefixFold :
      p.foldl (fun current z => G.mul current
        (if z = a then fourE else if z = b then oneE else threeE))
        (if head = a then fourE else if head = b then oneE else threeE) =
      start := by
    rw [startState]
    exact foldl_frozen_mem _ p fun z member =>
      neutral z (fun equal => aFresh (equal ▸ member))
        (fun equal => bFresh (equal ▸ member))
  rw [prefixFold, List.foldl_cons, triggerStep]
  exact foldl_frozen_mem _ s fun z _ => outcomeDead _

/-- The descriptor's order datum: both letters occur in the commuting
tail, with the first occurrence of `x` strictly earlier. For the head
letter, its first tail occurrence is exactly the head2 event, so this
definition is uniform. -/
def eventOrder (x y : Nat) (w : Word Nat) : Prop :=
  x ∈ w.tail ∧ y ∈ w.tail ∧ w.tail.idxOf x < w.tail.idxOf y

/-- First index over an append avoiding the prefix. -/
private theorem idxOf_append_absent {p rest : List Nat} {y : Nat}
    (absent : y ∉ p) :
    (p ++ rest).idxOf y = p.length + rest.idxOf y := by
  induction p with
  | nil => simp
  | cons z q ih =>
      have yzMiss : y ≠ z := fun equal => absent (by simp [equal])
      have zyMiss : z ≠ y := fun equal => yzMiss equal.symm
      have zMiss : (z == y) = false := by simp [zyMiss]
      have qAbsent : y ∉ q := fun m => absent (List.mem_cons_of_mem _ m)
      simp only [List.cons_append, List.idxOf_cons, zMiss, cond_false,
        ih qAbsent, List.length_cons]
      omega

/-- Members with equal first indices coincide. -/
private theorem eq_of_idxOf_eq {l : List Nat} {x y : Nat}
    (xMember : x ∈ l) (yMember : y ∈ l)
    (equal : l.idxOf x = l.idxOf y) : x = y := by
  obtain ⟨p, s, shape, absent, length⟩ := firstSplit xMember
  by_cases yInPrefix : y ∈ p
  · have := idxOf_lt_of_mem_prefix shape absent yInPrefix
    omega
  · have yIdx : l.idxOf y = p.length + (x :: s).idxOf y := by
      rw [shape]
      exact idxOf_append_absent yInPrefix
    have zeroIdx : (x :: s).idxOf y = 0 := by omega
    by_cases hit : y = x
    · exact hit.symm
    · exfalso
      have xyNe : x ≠ y := fun equal => hit equal.symm
      have missBeq : (x == y) = false := by simp [xyNe]
      simp [List.idxOf_cons, missBeq] at zeroIdx

/-- Split a word tail at the earlier contestant, with both contestants
absent from the prefix. -/
private theorem raceSplit {t : List Nat} {x y : Nat}
    (xMember : x ∈ t) (yMember : y ∈ t)
    (before : t.idxOf x < t.idxOf y) :
    ∃ p s, t = p ++ x :: s ∧ x ∉ p ∧ y ∉ p := by
  obtain ⟨p, s, shape, absent, length⟩ := firstSplit xMember
  refine ⟨p, s, shape, absent, ?_⟩
  intro yInPrefix
  have := idxOf_lt_of_mem_prefix shape absent yInPrefix
  omega

/-- One direction of the order extraction: an order in the left word
transfers to the right word, given the race transition table. -/
theorem eventOrder_transfer
    {threeE oneE fourE winN deathN winS deathS : S}
    (t33 : G.mul threeE threeE = threeE)
    (t13 : G.mul oneE threeE = oneE)
    (tNW : G.mul threeE fourE = winN)
    (tND : G.mul threeE oneE = deathN)
    (tSW : G.mul oneE fourE = winS)
    (tSD : G.mul oneE oneE = deathS)
    (dWinN : ∀ z, G.mul winN z = winN)
    (dDeathN : ∀ z, G.mul deathN z = deathN)
    (dWinS : ∀ z, G.mul winS z = winS)
    (dDeathS : ∀ z, G.mul deathS z = deathS)
    (separateN : winN ≠ deathN) (separateS : winS ≠ deathS)
    (e : Identity Nat) (valid : e.SatisfiedBy G)
    (heads : e.lhs.head = e.rhs.head)
    {x y : Nat} (distinct : x ≠ y)
    (xRight : x ∈ e.rhs.tail) (yRight : y ∈ e.rhs.tail)
    (ordered : eventOrder x y e.lhs) :
    eventOrder x y e.rhs := by
  obtain ⟨xLeft, yLeft, before⟩ := ordered
  refine ⟨xRight, yRight, ?_⟩
  apply Classical.byContradiction
  intro notBefore
  have flipped : e.rhs.tail.idxOf y < e.rhs.tail.idxOf x := by
    have notEqual : e.rhs.tail.idxOf x ≠ e.rhs.tail.idxOf y :=
      fun equal => distinct (eq_of_idxOf_eq xRight yRight equal)
    omega
  obtain ⟨pL, sL, shapeL, xFreshL, yFreshL⟩ := raceSplit xLeft yLeft before
  obtain ⟨pR, sR, shapeR, yFreshR, xFreshR⟩ :=
    raceSplit yRight xRight flipped
  have lhsEta : e.lhs = (⟨e.lhs.head, e.lhs.tail⟩ : Word Nat) := rfl
  have rhsEta : e.rhs = (⟨e.lhs.head, e.rhs.tail⟩ : Word Nat) := by
    have eta : e.rhs = (⟨e.rhs.head, e.rhs.tail⟩ : Word Nat) := rfl
    rw [eta]
    exact congrArg (fun letter => (⟨letter, e.rhs.tail⟩ : Word Nat))
      heads.symm
  by_cases xHead : x = e.lhs.head
  · -- the head races as the death contestant against y
    have yMiss : y ≠ e.lhs.head := fun equal =>
      distinct (xHead.trans equal.symm)
    have startState :
        (if e.lhs.head = y then fourE else
          if e.lhs.head = x then oneE else threeE) = oneE := by
      rw [if_neg (fun equal => yMiss equal.symm), if_pos xHead.symm]
    have neutral : ∀ z, z ≠ y → z ≠ x → G.mul oneE
        (if z = y then fourE else if z = x then oneE else threeE) =
          oneE := by
      intro z zy zx
      rw [if_neg zy, if_neg zx]
      exact t13
    have evalL := race_eval_trigger (a := y) (b := x)
      (trigger := x) (start := oneE) (outcome := deathS)
      neutral (by
        rw [if_neg distinct, if_pos rfl]
        exact tSD)
      dDeathS startState shapeL yFreshL xFreshL
    have evalR := race_eval_trigger (a := y) (b := x)
      (trigger := y) (start := oneE) (outcome := winS)
      neutral (by
        rw [if_pos rfl]
        exact tSW)
      dWinS startState shapeR yFreshR xFreshR
    have evaluated := valid
      (fun z => if z = y then fourE else if z = x then oneE else threeE)
    rw [lhsEta] at evaluated
    rw [rhsEta] at evaluated
    rw [evalL, evalR] at evaluated
    exact (separateS evaluated.symm).elim
  · by_cases yHead : y = e.lhs.head
    · -- y is the head: x races as the win contestant
      have startState :
          (if e.lhs.head = x then fourE else
            if e.lhs.head = y then oneE else threeE) = oneE := by
        rw [if_neg (fun equal => xHead equal.symm),
          if_pos yHead.symm]
      have neutral : ∀ z, z ≠ x → z ≠ y → G.mul oneE
          (if z = x then fourE else if z = y then oneE else threeE) =
            oneE := by
        intro z zx zy
        rw [if_neg zx, if_neg zy]
        exact t13
      have evalL := race_eval_trigger (a := x) (b := y)
        (trigger := x) (start := oneE) (outcome := winS)
        neutral (by
          rw [if_pos rfl]
          exact tSW)
        dWinS startState shapeL xFreshL yFreshL
      have evalR := race_eval_trigger (a := x) (b := y)
        (trigger := y) (start := oneE) (outcome := deathS)
        neutral (by
          rw [if_neg (fun equal => distinct equal.symm), if_pos rfl]
          exact tSD)
        dDeathS startState shapeR xFreshR yFreshR
      have evaluated := valid
        (fun z => if z = x then fourE else if z = y then oneE else threeE)
      rw [lhsEta] at evaluated
      rw [rhsEta] at evaluated
      rw [evalL, evalR] at evaluated
      exact separateS evaluated |>.elim
    · -- neither contestant is the head: neutral start
      have startState :
          (if e.lhs.head = x then fourE else
            if e.lhs.head = y then oneE else threeE) = threeE := by
        rw [if_neg (fun equal => xHead equal.symm),
          if_neg (fun equal => yHead equal.symm)]
      have neutral : ∀ z, z ≠ x → z ≠ y → G.mul threeE
          (if z = x then fourE else if z = y then oneE else threeE) =
            threeE := by
        intro z zx zy
        rw [if_neg zx, if_neg zy]
        exact t33
      have evalL := race_eval_trigger (a := x) (b := y)
        (trigger := x) (start := threeE) (outcome := winN)
        neutral (by
          rw [if_pos rfl]
          exact tNW)
        dWinN startState shapeL xFreshL yFreshL
      have evalR := race_eval_trigger (a := x) (b := y)
        (trigger := y) (start := threeE) (outcome := deathN)
        neutral (by
          rw [if_neg (fun equal => distinct equal.symm), if_pos rfl]
          exact tND)
        dDeathN startState shapeR xFreshR yFreshR
      have evaluated := valid
        (fun z => if z = x then fourE else if z = y then oneE else threeE)
      rw [lhsEta] at evaluated
      rw [rhsEta] at evaluated
      rw [evalL, evalR] at evaluated
      exact separateN evaluated |>.elim

/-- The head2-presence gadget: the head reoccurring in the tail is a
semantic invariant. -/
theorem head2_presence_transfer {threeE oneE deathS : S}
    (t13 : G.mul oneE threeE = oneE)
    (tSD : G.mul oneE oneE = deathS)
    (dDeathS : ∀ z, G.mul deathS z = deathS)
    (separate : oneE ≠ deathS)
    (e : Identity Nat) (valid : e.SatisfiedBy G)
    (heads : e.lhs.head = e.rhs.head) :
    (e.lhs.head ∈ e.lhs.tail ↔ e.lhs.head ∈ e.rhs.tail) := by
  let valuation : Nat → S :=
    fun z => if z = e.lhs.head then oneE else threeE
  have evalShape : ∀ t : List Nat,
      (⟨e.lhs.head, t⟩ : Word Nat).toList = e.lhs.head :: t →
      G.eval valuation (⟨e.lhs.head, t⟩ : Word Nat) =
        (if e.lhs.head ∈ t then deathS else oneE) := by
    intro t _
    show t.foldl _ _ = _
    have startImage : valuation e.lhs.head = oneE := by
      simp [valuation]
    by_cases present : e.lhs.head ∈ t
    · obtain ⟨p, s, shape, absent, _⟩ := firstSplit present
      rw [if_pos present, shape, List.foldl_append, startImage]
      have prefixFold :
          p.foldl (fun current z => G.mul current (valuation z)) oneE =
            oneE := by
        exact foldl_frozen_mem _ p fun z member => by
          have miss : z ≠ e.lhs.head := fun equal =>
            absent (equal ▸ member)
          simp only [valuation, if_neg miss]
          exact t13
      rw [prefixFold, List.foldl_cons]
      have step : G.mul oneE (valuation e.lhs.head) = deathS := by
        rw [startImage]
        exact tSD
      rw [step]
      exact foldl_frozen_mem _ s fun z _ => dDeathS _
    · rw [if_neg present, startImage]
      exact foldl_frozen_mem _ t fun z member => by
        have miss : z ≠ e.lhs.head := fun equal =>
          present (equal ▸ member)
        simp only [valuation, if_neg miss]
        exact t13
  have lhsEta : e.lhs = (⟨e.lhs.head, e.lhs.tail⟩ : Word Nat) := rfl
  have rhsEta : e.rhs = (⟨e.lhs.head, e.rhs.tail⟩ : Word Nat) := by
    have eta : e.rhs = (⟨e.rhs.head, e.rhs.tail⟩ : Word Nat) := rfl
    rw [eta]
    exact congrArg (fun letter => (⟨letter, e.rhs.tail⟩ : Word Nat))
      heads.symm
  have evaluated := valid valuation
  rw [lhsEta] at evaluated
  rw [rhsEta] at evaluated
  rw [evalShape e.lhs.tail rfl, evalShape e.rhs.tail rfl] at evaluated
  by_cases leftPresent : e.lhs.head ∈ e.lhs.tail <;>
    by_cases rightPresent : e.lhs.head ∈ e.rhs.tail <;>
      simp [leftPresent, rightPresent] at evaluated ⊢
  · exact separate evaluated.symm
  · exact separate evaluated

end RaceExtraction

/-! ## Scan combinatorics and the descriptor bridge -/

/-- Members of a done-scan are exactly the unseen letters of the tail. -/
private theorem scanEvents_mem_true_iff (h : Nat) :
    ∀ (t : List Nat) (seen : List Nat) (y : Nat),
      y ∈ scanEvents h seen true t ↔ (y ∈ t ∧ y ∉ seen)
  | [], seen, y => by simp [scanEvents]
  | x :: rest, seen, y => by
      rw [scanEvents]
      by_cases seenCase : x ∈ seen
      · rw [if_pos seenCase]
        rw [scanEvents_mem_true_iff h rest seen y]
        constructor
        · rintro ⟨inRest, notSeen⟩
          exact ⟨List.mem_cons_of_mem _ inRest, notSeen⟩
        · rintro ⟨inCons, notSeen⟩
          rcases List.mem_cons.mp inCons with equal | inRest
          · exact absurd (equal ▸ seenCase) notSeen
          · exact ⟨inRest, notSeen⟩
      · rw [if_neg seenCase]
        constructor
        · intro member
          rcases List.mem_cons.mp member with equal | inner
          · exact ⟨equal ▸ (by simp : x ∈ x :: rest), equal ▸ seenCase⟩
          · obtain ⟨inRest, notSeen⟩ :=
              (scanEvents_mem_true_iff h rest (x :: seen) y).mp inner
            exact ⟨List.mem_cons_of_mem _ inRest,
              fun inSeen => notSeen (List.mem_cons_of_mem _ inSeen)⟩
        · rintro ⟨inCons, notSeen⟩
          rcases List.mem_cons.mp inCons with equal | inRest
          · exact equal ▸ (by simp : x ∈ x :: _)
          · by_cases fresh : y = x
            · exact fresh ▸ (by simp : x ∈ x :: _)
            · exact List.mem_cons_of_mem _
                ((scanEvents_mem_true_iff h rest (x :: seen) y).mpr
                  ⟨inRest, fun inSeen => by
                    rcases List.mem_cons.mp inSeen with equal | old
                    · exact fresh equal
                    · exact notSeen old⟩)

/-- Membership in a pending-echo scan: the head appears iff it recurs in
the tail; other letters appear iff present and unseen. -/
private theorem scanEvents_false_mem_iff (h : Nat) :
    ∀ (t seen : List Nat), h ∈ seen → ∀ y,
      y ∈ scanEvents h seen false t ↔
        ((y = h ∧ h ∈ t) ∨ (y ≠ h ∧ y ∈ t ∧ y ∉ seen))
  | [], seen, _, y => by simp [scanEvents]
  | x :: rest, seen, headSeen, y => by
      rw [scanEvents]
      by_cases seenCase : x ∈ seen
      · rw [if_pos seenCase]
        by_cases headCase : x = h
        · rw [if_pos headCase, List.mem_cons,
            scanEvents_mem_true_iff h rest seen y]
          constructor
          · intro member
            rcases member with equal | ⟨inRest, notSeen⟩
            · exact Or.inl ⟨equal,
                headCase ▸ (by simp : x ∈ x :: rest)⟩
            · by_cases yHead : y = h
              · exact Or.inl ⟨yHead, headCase ▸ (by simp : x ∈ x :: rest)⟩
              · exact Or.inr ⟨yHead, List.mem_cons_of_mem _ inRest,
                  notSeen⟩
          · intro cases
            rcases cases with ⟨equal, _⟩ | ⟨yHead, inCons, notSeen⟩
            · exact Or.inl equal
            · rcases List.mem_cons.mp inCons with hit | inRest
              · exact absurd (hit ▸ seenCase) notSeen
              · exact Or.inr ⟨inRest, notSeen⟩
        · rw [if_neg headCase,
            scanEvents_false_mem_iff h rest seen headSeen y]
          constructor
          · intro cases
            rcases cases with ⟨yHead, inRest⟩ | ⟨yHead, inRest, notSeen⟩
            · exact Or.inl ⟨yHead, List.mem_cons_of_mem _ inRest⟩
            · exact Or.inr ⟨yHead, List.mem_cons_of_mem _ inRest,
                notSeen⟩
          · intro cases
            rcases cases with ⟨yHead, inCons⟩ | ⟨yHead, inCons, notSeen⟩
            · rcases List.mem_cons.mp inCons with hit | inRest
              · exact absurd hit.symm headCase
              · exact Or.inl ⟨yHead, inRest⟩
            · rcases List.mem_cons.mp inCons with hit | inRest
              · exact absurd (hit ▸ seenCase) notSeen
              · exact Or.inr ⟨yHead, inRest, notSeen⟩
      · rw [if_neg seenCase]
        have xHead : x ≠ h := fun equal => seenCase (equal ▸ headSeen)
        rw [List.mem_cons,
          scanEvents_false_mem_iff h rest (x :: seen)
            (List.mem_cons_of_mem _ headSeen) y]
        constructor
        · intro member
          rcases member with equal | cases
          · exact Or.inr ⟨equal ▸ xHead,
              equal ▸ (by simp : x ∈ x :: rest), equal ▸ seenCase⟩
          · rcases cases with ⟨yHead, inRest⟩ | ⟨yHead, inRest, notSeen⟩
            · exact Or.inl ⟨yHead, List.mem_cons_of_mem _ inRest⟩
            · exact Or.inr ⟨yHead, List.mem_cons_of_mem _ inRest,
                fun inSeen => notSeen (List.mem_cons_of_mem _ inSeen)⟩
        · intro cases
          rcases cases with ⟨yHead, inCons⟩ | ⟨yHead, inCons, notSeen⟩
          · rcases List.mem_cons.mp inCons with hit | inRest
            · exact absurd hit.symm xHead
            · exact Or.inr (Or.inl ⟨yHead, inRest⟩)
          · rcases List.mem_cons.mp inCons with hit | inRest
            · exact Or.inl hit
            · by_cases fresh : y = x
              · exact Or.inl fresh
              · exact Or.inr (Or.inr ⟨yHead, inRest, fun inSeen => by
                  rcases List.mem_cons.mp inSeen with equal | old
                  · exact fresh equal
                  · exact notSeen old⟩)

/-- Top-level membership: the events are exactly the tail letters. -/
private theorem scanEvents_top_mem_iff (h : Nat) (t : List Nat) (y : Nat) :
    y ∈ scanEvents h [h] false t ↔ y ∈ t := by
  rw [scanEvents_false_mem_iff h t [h] (by simp) y]
  constructor
  · intro cases
    rcases cases with ⟨equal, inT⟩ | ⟨_, inT, _⟩
    · exact equal ▸ inT
    · exact inT
  · intro inT
    by_cases headCase : y = h
    · exact Or.inl ⟨headCase, headCase ▸ inT⟩
    · exact Or.inr ⟨headCase, inT, by simp [headCase]⟩

/-- Scans never repeat an event. -/
private theorem scanEvents_nodup (h : Nat) :
    ∀ (t seen : List Nat) (done : Bool), h ∈ seen →
      (scanEvents h seen done t).Nodup
  | [], _, true, _ => by simp [scanEvents]
  | [], _, false, _ => by simp [scanEvents]
  | x :: rest, seen, true, headSeen => by
      rw [scanEvents]
      by_cases seenCase : x ∈ seen
      · rw [if_pos seenCase]
        exact scanEvents_nodup h rest seen true headSeen
      · rw [if_neg seenCase]
        rw [List.nodup_cons]
        refine ⟨?_, scanEvents_nodup h rest (x :: seen) true
          (List.mem_cons_of_mem _ headSeen)⟩
        intro member
        exact scanEvents_mem_true h rest (x :: seen) x member
          (by simp : x ∈ x :: seen)
  | x :: rest, seen, false, headSeen => by
      rw [scanEvents]
      by_cases seenCase : x ∈ seen
      · rw [if_pos seenCase]
        by_cases headCase : x = h
        · rw [if_pos headCase]
          rw [List.nodup_cons]
          refine ⟨?_, scanEvents_nodup h rest seen true headSeen⟩
          intro member
          exact scanEvents_mem_true h rest seen h member headSeen
        · rw [if_neg headCase]
          exact scanEvents_nodup h rest seen false headSeen
      · rw [if_neg seenCase]
        rw [List.nodup_cons]
        refine ⟨?_, scanEvents_nodup h rest (x :: seen) false
          (List.mem_cons_of_mem _ headSeen)⟩
        intro member
        rcases scanEvents_mem h rest (x :: seen) false x member with
          headHit | notSeen
        · exact seenCase (headHit ▸ headSeen)
        · exact notSeen (by simp : x ∈ x :: seen)

/-- Event order in the scan reflects first-occurrence order in the
tail. -/
private theorem scanEvents_order (h : Nat) :
    ∀ (t seen : List Nat) (done : Bool) (y z : Nat), h ∈ seen →
      y ∈ scanEvents h seen done t → z ∈ scanEvents h seen done t →
      (scanEvents h seen done t).idxOf y <
        (scanEvents h seen done t).idxOf z →
      t.idxOf y < t.idxOf z
  | [], _, true, _, _, _ => by simp [scanEvents]
  | [], _, false, _, _, _ => by simp [scanEvents]
  | x :: rest, seen, true, y, z, headSeen => by
      intro yMember zMember scanOrder
      rw [scanEvents] at yMember zMember scanOrder
      by_cases seenCase : x ∈ seen
      · rw [if_pos seenCase] at yMember zMember scanOrder
        have yAvoid : y ≠ x := fun equal =>
          scanEvents_mem_true h rest seen y yMember (equal ▸ seenCase)
        have zAvoid : z ≠ x := fun equal =>
          scanEvents_mem_true h rest seen z zMember (equal ▸ seenCase)
        have inner := scanEvents_order h rest seen true y z
          headSeen yMember zMember scanOrder
        have xyNe : x ≠ y := fun equal => yAvoid equal.symm
        have xzNe : x ≠ z := fun equal => zAvoid equal.symm
        have yBeq : (x == y) = false := by simp [xyNe]
        have zBeq : (x == z) = false := by simp [xzNe]
        simp only [List.idxOf_cons, yBeq, zBeq, cond_false]
        omega
      · rw [if_neg seenCase] at yMember zMember scanOrder
        by_cases yFirst : y = x
        · have zTail : z ∈ scanEvents h (x :: seen) true rest := by
            rcases List.mem_cons.mp zMember with equal | inner
            · exfalso
              have yIdx :
                  (x :: scanEvents h (x :: seen) true rest).idxOf y =
                    0 := by
                simp [List.idxOf_cons, yFirst]
              have zIdx :
                  (x :: scanEvents h (x :: seen) true rest).idxOf z =
                    0 := by
                simp [List.idxOf_cons, equal]
              omega
            · exact inner
          have zAvoid : z ≠ x := fun equal =>
            scanEvents_mem_true h rest (x :: seen) z zTail
              (equal ▸ (by simp : x ∈ x :: seen))
          have yIdx : (x :: rest).idxOf y = 0 := by
            simp [List.idxOf_cons, yFirst]
          have xzNe : x ≠ z := fun equal => zAvoid equal.symm
          have zBeq : (x == z) = false := by simp [xzNe]
          have zIdx : (x :: rest).idxOf z = rest.idxOf z + 1 := by
            simp [List.idxOf_cons, zBeq]
          omega
        · have yTail : y ∈ scanEvents h (x :: seen) true rest := by
            rcases List.mem_cons.mp yMember with equal | inner
            · exact absurd equal yFirst
            · exact inner
          have zTail : z ∈ scanEvents h (x :: seen) true rest := by
            rcases List.mem_cons.mp zMember with equal | inner
            · exfalso
              have zIdxZero :
                  (x :: scanEvents h (x :: seen) true rest).idxOf z =
                    0 := by
                simp [List.idxOf_cons, equal]
              omega
            · exact inner
          have zAvoid : z ≠ x := fun equal =>
            scanEvents_mem_true h rest (x :: seen) z zTail
              (equal ▸ (by simp : x ∈ x :: seen))
          have xyNe : x ≠ y := fun equal => yFirst equal.symm
          have xzNe : x ≠ z := fun equal => zAvoid equal.symm
          have yScanBeq : (x == y) = false := by simp [xyNe]
          have zScanBeq : (x == z) = false := by simp [xzNe]
          have shifted := scanOrder
          simp only [List.idxOf_cons, yScanBeq, zScanBeq,
            cond_false] at shifted
          have inner := scanEvents_order h rest (x :: seen) true y z
            (List.mem_cons_of_mem _ headSeen) yTail zTail (by omega)
          simp only [List.idxOf_cons, yScanBeq, zScanBeq, cond_false]
          omega
  | x :: rest, seen, false, y, z, headSeen => by
      intro yMember zMember scanOrder
      rw [scanEvents] at yMember zMember scanOrder
      by_cases seenCase : x ∈ seen
      · rw [if_pos seenCase] at yMember zMember scanOrder
        by_cases headCase : x = h
        · rw [if_pos headCase] at yMember zMember scanOrder
          by_cases yHead : y = h
          · have zTail : z ∈ scanEvents h seen true rest := by
              rcases List.mem_cons.mp zMember with equal | inner
              · exfalso
                have yIdx :
                    (h :: scanEvents h seen true rest).idxOf y = 0 := by
                  simp [List.idxOf_cons, yHead]
                have zIdx :
                    (h :: scanEvents h seen true rest).idxOf z = 0 := by
                  simp [List.idxOf_cons, equal]
                omega
              · exact inner
            have zNotSeen :=
              scanEvents_mem_true h rest seen z zTail
            have zAvoid : z ≠ x := fun equal =>
              zNotSeen (equal ▸ seenCase)
            have yIdx : (x :: rest).idxOf y = 0 := by
              have xyEq : x = y := headCase.trans yHead.symm
              simp [List.idxOf_cons, xyEq]
            have xzNe : x ≠ z := fun equal => zAvoid equal.symm
            have zBeq : (x == z) = false := by simp [xzNe]
            have zIdx : (x :: rest).idxOf z = rest.idxOf z + 1 := by
              simp [List.idxOf_cons, zBeq]
            omega
          · have yTail : y ∈ scanEvents h seen true rest := by
              rcases List.mem_cons.mp yMember with equal | inner
              · exact absurd equal yHead
              · exact inner
            have zTail : z ∈ scanEvents h seen true rest := by
              rcases List.mem_cons.mp zMember with equal | inner
              · exfalso
                have zIdxZero :
                    (h :: scanEvents h seen true rest).idxOf z = 0 := by
                  simp [List.idxOf_cons, equal]
                omega
              · exact inner
            have yNotSeen := scanEvents_mem_true h rest seen y yTail
            have zNotSeen := scanEvents_mem_true h rest seen z zTail
            have yAvoid : y ≠ x := fun equal =>
              yNotSeen (equal ▸ seenCase)
            have zAvoid : z ≠ x := fun equal =>
              zNotSeen (equal ▸ seenCase)
            have hyNe : h ≠ y := fun equal => yHead equal.symm
            have yScanBeq : (h == y) = false := by simp [hyNe]
            have zScanBeq : (h == z) = false := by
              have zHead : z ≠ h := fun equal =>
                zAvoid (equal.trans headCase.symm)
              have hzNe : h ≠ z := fun equal => zHead equal.symm
              simp [hzNe]
            have shifted := scanOrder
            simp only [List.idxOf_cons, yScanBeq, zScanBeq,
              cond_false] at shifted
            have inner := scanEvents_order h rest seen true y z
              headSeen yTail zTail (by omega)
            have xyNe : x ≠ y := fun equal => yAvoid equal.symm
            have xzNe : x ≠ z := fun equal => zAvoid equal.symm
            have yBeq : (x == y) = false := by simp [xyNe]
            have zBeq : (x == z) = false := by simp [xzNe]
            simp only [List.idxOf_cons, yBeq, zBeq, cond_false]
            omega
        · rw [if_neg headCase] at yMember zMember scanOrder
          have yAvoid : y ≠ x := by
            intro equal
            rcases scanEvents_mem h rest seen false y yMember with
              headHit | notSeen
            · exact headCase (equal.symm.trans headHit)
            · exact notSeen (equal ▸ seenCase)
          have zAvoid : z ≠ x := by
            intro equal
            rcases scanEvents_mem h rest seen false z zMember with
              headHit | notSeen
            · exact headCase (equal.symm.trans headHit)
            · exact notSeen (equal ▸ seenCase)
          have inner := scanEvents_order h rest seen false y z headSeen
            yMember zMember scanOrder
          have xyNe : x ≠ y := fun equal => yAvoid equal.symm
          have xzNe : x ≠ z := fun equal => zAvoid equal.symm
          have yBeq : (x == y) = false := by simp [xyNe]
          have zBeq : (x == z) = false := by simp [xzNe]
          simp only [List.idxOf_cons, yBeq, zBeq, cond_false]
          omega
      · rw [if_neg seenCase] at yMember zMember scanOrder
        have xHead : x ≠ h := fun equal => seenCase (equal ▸ headSeen)
        by_cases yFirst : y = x
        · have zTail : z ∈ scanEvents h (x :: seen) false rest := by
            rcases List.mem_cons.mp zMember with equal | inner
            · exfalso
              have yIdx :
                  (x :: scanEvents h (x :: seen) false rest).idxOf y =
                    0 := by
                simp [List.idxOf_cons, yFirst]
              have zIdx :
                  (x :: scanEvents h (x :: seen) false rest).idxOf z =
                    0 := by
                simp [List.idxOf_cons, equal]
              omega
            · exact inner
          have zAvoid : z ≠ x := by
            intro equal
            rcases scanEvents_mem h rest (x :: seen) false z zTail with
              headHit | notSeen
            · exact xHead (equal.symm.trans headHit)
            · exact notSeen (equal ▸ (by simp : x ∈ x :: seen))
          have yIdx : (x :: rest).idxOf y = 0 := by
            simp [List.idxOf_cons, yFirst]
          have xzNe : x ≠ z := fun equal => zAvoid equal.symm
          have zBeq : (x == z) = false := by simp [xzNe]
          have zIdx : (x :: rest).idxOf z = rest.idxOf z + 1 := by
            simp [List.idxOf_cons, zBeq]
          omega
        · have yTail : y ∈ scanEvents h (x :: seen) false rest := by
            rcases List.mem_cons.mp yMember with equal | inner
            · exact absurd equal yFirst
            · exact inner
          have zTail : z ∈ scanEvents h (x :: seen) false rest := by
            rcases List.mem_cons.mp zMember with equal | inner
            · exfalso
              have zIdxZero :
                  (x :: scanEvents h (x :: seen) false rest).idxOf z =
                    0 := by
                simp [List.idxOf_cons, equal]
              omega
            · exact inner
          have zAvoid : z ≠ x := by
            intro equal
            rcases scanEvents_mem h rest (x :: seen) false z zTail with
              headHit | notSeen
            · exact xHead (equal.symm.trans headHit)
            · exact notSeen (equal ▸ (by simp : x ∈ x :: seen))
          have xyNe : x ≠ y := fun equal => yFirst equal.symm
          have xzNe : x ≠ z := fun equal => zAvoid equal.symm
          have yScanBeq : (x == y) = false := by simp [xyNe]
          have zScanBeq : (x == z) = false := by simp [xzNe]
          have shifted := scanOrder
          simp only [List.idxOf_cons, yScanBeq, zScanBeq,
            cond_false] at shifted
          have inner := scanEvents_order h rest (x :: seen) false y z
            (List.mem_cons_of_mem _ headSeen) yTail zTail (by omega)
          simp only [List.idxOf_cons, yScanBeq, zScanBeq, cond_false]
          omega

/-- Two duplicate-free lists with the same members and agreeing relative
order are equal. -/
private theorem nodup_eq_of_mem_and_order :
    ∀ (L1 L2 : List Nat), L1.Nodup → L2.Nodup →
      (∀ y, y ∈ L1 ↔ y ∈ L2) →
      (∀ y z, y ∈ L1 → z ∈ L1 →
        (L1.idxOf y < L1.idxOf z ↔ L2.idxOf y < L2.idxOf z)) →
      L1 = L2
  | [], [], _, _, _, _ => rfl
  | [], b :: R2, _, _, mem, _ => by
      have := (mem b).mpr ((by simp : b ∈ b :: R2))
      simp at this
  | a :: R1, [], _, _, mem, _ => by
      have := (mem a).mp ((by simp : a ∈ a :: R1))
      simp at this
  | a :: R1, b :: R2, n1, n2, mem, order => by
      have headEq : b = a := by
        apply Classical.byContradiction
        intro different
        have bIn1 : b ∈ a :: R1 :=
          (mem b).mpr ((by simp : b ∈ b :: R2))
        have aIdxOne : (a :: R1).idxOf a = 0 := by
          simp [List.idxOf_cons]
        have bIdxOne : 0 < (a :: R1).idxOf b := by
          have abNe : a ≠ b := fun equal => different equal.symm
          have abBeq : (a == b) = false := by simp [abNe]
          simp only [List.idxOf_cons, abBeq, cond_false]
          omega
        have transferred :=
          (order a b ((by simp : a ∈ a :: R1)) bIn1).mp (by omega)
        have aIdxTwo : (b :: R2).idxOf a > 0 := by
          have baBeq : (b == a) = false := by simp [different]
          simp only [List.idxOf_cons, baBeq, cond_false]
          omega
        have bIdxTwo : (b :: R2).idxOf b = 0 := by
          simp [List.idxOf_cons]
        omega
      subst b
      have aMissOne : a ∉ R1 := (List.nodup_cons.mp n1).1
      have aMissTwo : a ∉ R2 := (List.nodup_cons.mp n2).1
      congr 1
      apply nodup_eq_of_mem_and_order R1 R2
        (List.nodup_cons.mp n1).2 (List.nodup_cons.mp n2).2
      · intro y
        constructor
        · intro yOne
          have yInTwo : y ∈ a :: R2 :=
            (mem y).mp (List.mem_cons_of_mem _ yOne)
          rcases List.mem_cons.mp yInTwo with equal | inner
          · exact absurd (equal ▸ yOne) aMissOne
          · exact inner
        · intro yTwo
          have yInOne : y ∈ a :: R1 :=
            (mem y).mpr (List.mem_cons_of_mem _ yTwo)
          rcases List.mem_cons.mp yInOne with equal | inner
          · exact absurd (equal ▸ yTwo) aMissTwo
          · exact inner
      · intro y z yOne zOne
        have yMiss : y ≠ a := fun equal => aMissOne (equal ▸ yOne)
        have zMiss : z ≠ a := fun equal => aMissOne (equal ▸ zOne)
        have ayNe : a ≠ y := fun equal => yMiss equal.symm
        have azNe : a ≠ z := fun equal => zMiss equal.symm
        have yBeq : (a == y) = false := by simp [ayNe]
        have zBeq : (a == z) = false := by simp [azNe]
        have inherited := order y z (List.mem_cons_of_mem _ yOne)
          (List.mem_cons_of_mem _ zOne)
        simp only [List.idxOf_cons, yBeq, zBeq, cond_false] at inherited
        constructor
        · intro lt
          have := inherited.mp (by omega)
          omega
        · intro lt
          have := inherited.mpr (by omega)
          omega

/-! ## The coordinate descriptor and its bridge -/

/-- The independently extractable coordinates of the pair descriptor. -/
structure PairClassData (u v : Word Nat) : Prop where
  heads : u.head = v.head
  support : ∀ x, x ∈ u.toList ↔ x ∈ v.toList
  parity : ∀ x, u.toList.count x % 2 = v.toList.count x % 2
  head2 : u.head ∈ u.tail ↔ v.head ∈ v.tail
  order : ∀ x y, x ∈ u.tail → y ∈ u.tail → x ∈ v.tail → y ∈ v.tail →
    x ≠ y →
    (u.tail.idxOf x < u.tail.idxOf y ↔ v.tail.idxOf x < v.tail.idxOf y)

/-- The coordinates determine the canonical form. -/
theorem samePairClass_of_data {u v : Word Nat}
    (data : PairClassData u v) : SamePairClass u v := by
  obtain ⟨heads, support, parity, head2, order⟩ := data
  have toListShapeU : u.toList = u.head :: u.tail := rfl
  have toListShapeV : v.toList = v.head :: v.tail := rfl
  have tailMem : ∀ x, x ∈ u.tail ↔ x ∈ v.tail := by
    intro x
    by_cases headCase : x = u.head
    · subst headCase
      have transported := head2
      rw [← heads] at transported
      exact transported
    · have expanded := support x
      rw [toListShapeU, toListShapeV] at expanded
      simp only [List.mem_cons] at expanded
      have vHeadMiss : x ≠ v.head := fun equal =>
        headCase (equal.trans heads.symm)
      constructor
      · intro inU
        rcases expanded.mp (Or.inr inU) with equal | inV
        · exact absurd equal vHeadMiss
        · exact inV
      · intro inV
        rcases expanded.mpr (Or.inr inV) with equal | inU
        · exact absurd equal headCase
        · exact inU
  have scansEq : scanEvents u.head [u.head] false u.tail =
      scanEvents u.head [u.head] false v.tail := by
    apply nodup_eq_of_mem_and_order
    · exact scanEvents_nodup u.head u.tail [u.head] false (by simp)
    · exact scanEvents_nodup u.head v.tail [u.head] false (by simp)
    · intro y
      rw [scanEvents_top_mem_iff, scanEvents_top_mem_iff]
      exact tailMem y
    · intro y z yScan zScan
      have yTailU : y ∈ u.tail :=
        (scanEvents_top_mem_iff _ _ _).mp yScan
      have zTailU : z ∈ u.tail :=
        (scanEvents_top_mem_iff _ _ _).mp zScan
      have yTailV := (tailMem y).mp yTailU
      have zTailV := (tailMem z).mp zTailU
      have yScanV : y ∈ scanEvents u.head [u.head] false v.tail :=
        (scanEvents_top_mem_iff _ _ _).mpr yTailV
      have zScanV : z ∈ scanEvents u.head [u.head] false v.tail :=
        (scanEvents_top_mem_iff _ _ _).mpr zTailV
      by_cases distinct : y = z
      · subst distinct
        omega
      constructor
      · intro scanLt
        have tailLtU := scanEvents_order u.head u.tail [u.head] false
          y z (by simp) yScan zScan scanLt
        have tailLtV :=
          (order y z yTailU zTailU yTailV zTailV distinct).mp tailLtU
        rcases Nat.lt_trichotomy
          ((scanEvents u.head [u.head] false v.tail).idxOf y)
          ((scanEvents u.head [u.head] false v.tail).idxOf z) with
          lt | eq | gt
        · exact lt
        · exact absurd (eq_of_idxOf_eq yScanV zScanV eq) distinct
        · have flipped := scanEvents_order u.head v.tail [u.head] false
            z y (by simp) zScanV yScanV gt
          omega
      · intro scanLt
        have tailLtV := scanEvents_order u.head v.tail [u.head] false
          y z (by simp) yScanV zScanV scanLt
        have tailLtU :=
          (order y z yTailU zTailU yTailV zTailV distinct).mpr tailLtV
        rcases Nat.lt_trichotomy
          ((scanEvents u.head [u.head] false u.tail).idxOf y)
          ((scanEvents u.head [u.head] false u.tail).idxOf z) with
          lt | eq | gt
        · exact lt
        · exact absurd (eq_of_idxOf_eq yScan zScan eq) distinct
        · have flipped := scanEvents_order u.head u.tail [u.head] false
            z y (by simp) zScan yScan gt
          omega
  have sizesEq : eventSize u = eventSize v := by
    funext x
    have countEq := parity x
    simp only [eventSize, headEcho, parityBlock, ← heads]
    by_cases headCase : x = u.head
    · have countHead := parity u.head
      by_cases even : u.toList.count u.head % 2 = 0
      · rw [if_pos headCase, if_pos headCase, if_pos even,
          if_pos (by omega : v.toList.count u.head % 2 = 0)]
      · rw [if_pos headCase, if_pos headCase, if_neg even,
          if_neg (by omega : ¬ v.toList.count u.head % 2 = 0)]
    · by_cases even : u.toList.count x % 2 = 0
      · rw [if_neg headCase, if_neg headCase, if_pos even,
          if_pos (by omega : v.toList.count x % 2 = 0)]
      · rw [if_neg headCase, if_neg headCase, if_neg even,
          if_neg (by omega : ¬ v.toList.count x % 2 = 0)]
  rw [SamePairClass, canonicalize, canonicalize, ← heads]
  have scanU := canonicalScan_eq_flatMap u u.tail [u.head] false
    (by simp)
  have scanV := canonicalScan_eq_flatMap v v.tail [v.head] false
    (by simp)
  rw [scanU]
  rw [show canonicalScan v [u.head] false v.tail =
      canonicalScan v [v.head] false v.tail from by rw [heads]]
  rw [scanV]
  rw [show scanEvents v.head [v.head] false v.tail =
      scanEvents u.head [u.head] false v.tail from by rw [heads]]
  rw [← scansEq, sizesEq]

/-! ## The two intersection instances -/

abbrev threeTable : FiniteTable := Generated.Catalogue.S3_11.table
abbrev table869 : FiniteTable := Generated.Catalogue.S5_869.table
abbrev table871 : FiniteTable := Generated.Catalogue.S5_871.table

private def sigmaVariable (value : Nat) : Fin 3 :=
  if value = 0 then 0 else if value = 1 then 1 else 2

theorem modelsS3_11 : Models threeTable.semigroup sigma :=
  FiniteCertificate.checkModels_sound threeTable sigma sigmaVariable
    (by decide)

theorem modelsS5_869 : Models table869.semigroup sigma :=
  FiniteCertificate.checkModels_sound table869 sigma sigmaVariable
    (by decide)

theorem modelsS5_871 : Models table871.semigroup sigma :=
  FiniteCertificate.checkModels_sound table871 sigma sigmaVariable
    (by decide)

/-- Coordinate extraction for the `S3_11 × S5_869` pair. -/
theorem pairData_of_valid_869 (e : Identity Nat)
    (validThree : e.SatisfiedBy threeTable.semigroup)
    (validFive : e.SatisfiedBy table869.semigroup) :
    PairClassData e.lhs e.rhs := by
  have headsFact :=
    Order6Condition8ThreeLaw.head_eq_of_band_valid
      (p := (0 : Fin 5)) (q := (2 : Fin 5))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      e validFive
  refine ⟨headsFact, ?_, ?_, ?_, ?_⟩
  · exact fun x =>
      Order6Condition8ThreeLaw.support_iff_of_valid
        (zeroE := (0 : Fin 3)) (hitE := (2 : Fin 3))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        e validThree x
  · exact fun x =>
      Order6Condition8ThreeLaw.parity_eq_of_valid
        (zeroE := (0 : Fin 3)) (oneE := (1 : Fin 3))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        e validThree x
  · have transfer := head2_presence_transfer
      (threeE := (3 : Fin 5)) (oneE := (1 : Fin 5))
      (deathS := (0 : Fin 5))
      (by decide) (by decide) (by decide) (by decide)
      e validFive headsFact
    constructor
    · intro member
      exact headsFact ▸ transfer.mp member
    · intro member
      exact transfer.mpr (headsFact.symm ▸ member)
  · intro x y xU yU xV yV distinct
    constructor
    · intro lt
      exact (eventOrder_transfer
        (threeE := (3 : Fin 5)) (oneE := (1 : Fin 5))
        (fourE := (4 : Fin 5)) (winN := (4 : Fin 5))
        (deathN := (0 : Fin 5)) (winS := (2 : Fin 5))
        (deathS := (0 : Fin 5))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
        e validFive headsFact distinct xV yV ⟨xU, yU, lt⟩).2.2
    · intro lt
      have swappedValid :
          (Identity.mk e.rhs e.lhs).SatisfiedBy table869.semigroup :=
        fun valuation => (validFive valuation).symm
      exact (eventOrder_transfer
        (threeE := (3 : Fin 5)) (oneE := (1 : Fin 5))
        (fourE := (4 : Fin 5)) (winN := (4 : Fin 5))
        (deathN := (0 : Fin 5)) (winS := (2 : Fin 5))
        (deathS := (0 : Fin 5))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
        (Identity.mk e.rhs e.lhs) swappedValid headsFact.symm distinct
        xU yU ⟨xV, yV, lt⟩).2.2

/-- Coordinate extraction for the `S3_11 × S5_871` pair. The only
transition that differs from `S5_869` is the neutral death landing in
`2` rather than `0`. -/
theorem pairData_of_valid_871 (e : Identity Nat)
    (validThree : e.SatisfiedBy threeTable.semigroup)
    (validFive : e.SatisfiedBy table871.semigroup) :
    PairClassData e.lhs e.rhs := by
  have headsFact :=
    Order6Condition8ThreeLaw.head_eq_of_band_valid
      (p := (0 : Fin 5)) (q := (2 : Fin 5))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      e validFive
  refine ⟨headsFact, ?_, ?_, ?_, ?_⟩
  · exact fun x =>
      Order6Condition8ThreeLaw.support_iff_of_valid
        (zeroE := (0 : Fin 3)) (hitE := (2 : Fin 3))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        e validThree x
  · exact fun x =>
      Order6Condition8ThreeLaw.parity_eq_of_valid
        (zeroE := (0 : Fin 3)) (oneE := (1 : Fin 3))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        e validThree x
  · have transfer := head2_presence_transfer
      (threeE := (3 : Fin 5)) (oneE := (1 : Fin 5))
      (deathS := (0 : Fin 5))
      (by decide) (by decide) (by decide) (by decide)
      e validFive headsFact
    constructor
    · intro member
      exact headsFact ▸ transfer.mp member
    · intro member
      exact transfer.mpr (headsFact.symm ▸ member)
  · intro x y xU yU xV yV distinct
    constructor
    · intro lt
      exact (eventOrder_transfer
        (threeE := (3 : Fin 5)) (oneE := (1 : Fin 5))
        (fourE := (4 : Fin 5)) (winN := (4 : Fin 5))
        (deathN := (2 : Fin 5)) (winS := (2 : Fin 5))
        (deathS := (0 : Fin 5))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
        e validFive headsFact distinct xV yV ⟨xU, yU, lt⟩).2.2
    · intro lt
      have swappedValid :
          (Identity.mk e.rhs e.lhs).SatisfiedBy table871.semigroup :=
        fun valuation => (validFive valuation).symm
      exact (eventOrder_transfer
        (threeE := (3 : Fin 5)) (oneE := (1 : Fin 5))
        (fourE := (4 : Fin 5)) (winN := (4 : Fin 5))
        (deathN := (2 : Fin 5)) (winS := (2 : Fin 5))
        (deathS := (0 : Fin 5))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)
        (Identity.mk e.rhs e.lhs) swappedValid headsFact.symm distinct
        xU yU ⟨xV, yV, lt⟩).2.2

theorem intersectionComplete_S3_11_S5_869 (e : Identity Nat)
    (validThree : e.SatisfiedBy threeTable.semigroup)
    (validFive : e.SatisfiedBy table869.semigroup) :
    Derives sigma e.lhs e.rhs :=
  derivesOfSamePairClass
    (samePairClass_of_data (pairData_of_valid_869 e validThree validFive))

theorem intersectionComplete_S3_11_S5_871 (e : Identity Nat)
    (validThree : e.SatisfiedBy threeTable.semigroup)
    (validFive : e.SatisfiedBy table871.semigroup) :
    Derives sigma e.lhs e.rhs :=
  derivesOfSamePairClass
    (samePairClass_of_data (pairData_of_valid_871 e validThree validFive))

theorem intersectionBasisS3_11S5_869 :
    IntersectionBasis threeTable.semigroup table869.semigroup sigma where
  leftModels := modelsS3_11
  rightModels := modelsS5_869
  complete := intersectionComplete_S3_11_S5_869

theorem intersectionBasisS3_11S5_871 :
    IntersectionBasis threeTable.semigroup table871.semigroup sigma where
  leftModels := modelsS3_11
  rightModels := modelsS5_871
  complete := intersectionComplete_S3_11_S5_871

end SemigroupBasis.CoRoots.Order6Condition8FiveLaw
