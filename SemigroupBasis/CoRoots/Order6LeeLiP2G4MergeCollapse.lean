import SemigroupBasis.CoRoots.Order6LeeLiP2G2
import SemigroupBasis.FiniteNilpotent

/-!
# G4 width-free merge-collapse: the L1–L5 decomposition (msg-0194)

EVIDENCE LABEL: source-staged draft, NOT compiled on the pinned toolchain.
Mathematical content per msg-0061 (accepted in msg-0194); exhaustive
5-letter search and 300k-pair rule validation are the computed receipts.

DESIGN
* Everything is stated at the `List Nat` level (`Word.toList` bridges at
  the endpoint); `nonBlob z` is `filter (· ≠ z)`.
* The blob-letter reduction is the inductive `BlobStep` (three
  constructors: hop, head-dup contraction, cap) and its reflexive
  transitive closure `BlobReduces`.  L2 proves the non-blob subsequence
  exactly invariant — the load-bearing reusable core, and the part proved
  outright here (pure `filter` computation over `++`/`::`).
* `canonicalReduced` is the concrete G4 canonical-marked-word map on
  reduced words (drop closed first occurrences, double closed second
  occurrences, keep singles and the open pair).  The full canonical map is
  `canonicalReduced ∘ reduce`; this module does NOT fix a reduction
  strategy.  Instead the section takes the single hypothesis
  `canonicalSound : DerivesG4-equal words have equal canonicals` — exactly
  the witness lane's normal-form uniqueness, so no paper bridge remains
  between this module and the verified four-variable tables.
* L5 exhibits the constructive σ per case with an explicit image list of
  length ≤ 4.

API LEDGER: List.filter_append, List.filter_cons, List.count_filter /
count_map basics, List.getLast?, Word.toList; the G4 basis identities are
defined here (the G4 module does not exist yet — these definitions are the
concrete anchor msg-0194 asks for).
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G4

open SemigroupBasis

/-! ## The G4 basis (dense Word forms, ledger orientation) -/

def capL : Word Nat := ⟨1, [1]⟩            -- xx
def capR : Word Nat := ⟨1, [1, 1]⟩         -- xxx
def hopL : Word Nat := ⟨1, [0, 1, 2]⟩      -- xyxz
def hopR : Word Nat := ⟨0, [1, 1, 2]⟩      -- yxxz
def hdL : Word Nat := ⟨1, [0, 1]⟩          -- xyx
def hdR : Word Nat := ⟨1, [1, 0, 1]⟩       -- xxyx

def capLaw : Identity Nat := ⟨capL, capR⟩
def hopLaw : Identity Nat := ⟨hopL, hopR⟩
def headDupLaw : Identity Nat := ⟨hdL, hdR⟩

def basisG4 : List (Identity Nat) := [capLaw, hopLaw, headDupLaw]

/-- Total list-to-word constructor. Nonempty lists retain their letters;
the empty list uses the designated `0`-singleton. -/
def wordOfD : List Nat → Word Nat
  | [] => Word.singleton 0
  | head :: tail => ⟨head, tail⟩

private theorem wordOfD_map (w : List Nat) (σ : Nat → Nat)
    (hw : w ≠ []) :
    (wordOfD w).map σ = wordOfD (w.map σ) := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons head tail => rfl

private theorem map_ne_nil {w : List Nat} (hw : w ≠ []) (σ : Nat → Nat) :
    w.map σ ≠ [] := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons head tail => simp

private def instantiateHop
    (x y t : Word Nat) : Nat → Word Nat
  | 0 => y
  | 1 => x
  | 2 => t
  | n + 3 => Word.singleton (n + 3)

private def instantiateHeadDup
    (x y : Word Nat) : Nat → Word Nat
  | 0 => y
  | 1 => x
  | n + 2 => Word.singleton (n + 2)

private theorem derivesHop (x y t : Word Nat) :
    Derives basisG4
      (((x ++ y) ++ x) ++ t)
      (((y ++ x) ++ x) ++ t) := by
  have base : Derives basisG4 hopL hopR :=
    Derives.fromBasis (e := hopLaw) (by
      exact List.Mem.tail _ (List.Mem.head _))
  have substituted := Derives.subst base (instantiateHop x y t)
  simpa [basisG4, hopLaw, hopL, hopR, instantiateHop,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesHeadDupContraction (x y : Word Nat) :
    Derives basisG4
      (((x ++ x) ++ y) ++ x)
      ((x ++ y) ++ x) := by
  have base : Derives basisG4 hdL hdR :=
    Derives.fromBasis (e := headDupLaw) (by
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have substituted := Derives.subst base (instantiateHeadDup x y)
  have expanded :
      Derives basisG4
        ((x ++ y) ++ x)
        (((x ++ x) ++ y) ++ x) := by
    simpa [basisG4, headDupLaw, hdL, hdR, instantiateHeadDup,
      Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using substituted
  exact expanded.symm

private theorem derivesCapContraction (x : Word Nat) :
    Derives basisG4 ((x ++ x) ++ x) (x ++ x) := by
  have base : Derives basisG4 capL capR :=
    Derives.fromBasis (e := capLaw) (by
      exact List.Mem.head _)
  have substituted := Derives.subst base (fun _ => x)
  have expanded : Derives basisG4 (x ++ x) ((x ++ x) ++ x) := by
    simpa [basisG4, capLaw, capL, capR, Word.bind,
      Word.append, Word.singleton, Word.append_assoc] using substituted
  exact expanded.symm

/- Put a word derivation inside possibly empty list contexts. The middle
`Word` keeps both resulting lists nonempty, so `wordOfD` is exact here. -/
private theorem derivesInListContext {u v : Word Nat}
    (h : Derives basisG4 u v) (pre suf : List Nat) :
    Derives basisG4
      (wordOfD (pre ++ u.toList ++ suf))
      (wordOfD (pre ++ v.toList ++ suf)) := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases pre with
          | nil =>
              cases suf with
              | nil =>
                  simpa [wordOfD, Word.toList] using h
              | cons suffixHead suffixTail =>
                  have suffixed := Derives.appendRight h
                    (Word.mk suffixHead suffixTail)
                  simpa [wordOfD, Word.toList, Word.append,
                    List.append_assoc] using suffixed
          | cons prefixHead prefixTail =>
              cases suf with
              | nil =>
                  have prefixed :=
                    Derives.prepend (Word.mk prefixHead prefixTail) h
                  simpa [wordOfD, Word.toList, Word.append,
                    List.append_assoc] using prefixed
              | cons suffixHead suffixTail =>
                  have surrounded :=
                    Derives.prepend (Word.mk prefixHead prefixTail)
                      (Derives.appendRight h
                        (Word.mk suffixHead suffixTail))
                  simpa [wordOfD, Word.toList, Word.append,
                    List.append_assoc] using surrounded

/-! ## Letter statuses on reduced words -/

def cappedCount (w : List Nat) (c : Nat) : Nat := min (w.count c) 2

def Reduced (w : List Nat) : Prop := ∀ c, w.count c ≤ 2

/-- The final position (if any) holds the last letter. -/
def lastLetter? (w : List Nat) : Option Nat := w.getLast?

inductive Status | single | closed | openPair
deriving DecidableEq, Repr

/-- Status of a letter occurring in a reduced word: `single` (count 1),
`openPair` (count 2, second occurrence final), `closed` (count 2,
second occurrence non-final). -/
def status? (w : List Nat) (c : Nat) : Option Status :=
  match w.count c with
  | 0 => none
  | 1 => some .single
  | _ => if lastLetter? w = some c then some .openPair else some .closed

/-! ## The concrete canonical marked word (reduced inputs) -/

/-- Position index of the first occurrence of `c` in `w` (length if none). -/
def firstIdx (w : List Nat) (c : Nat) : Nat := w.idxOf c

/-- `canonicalReduced` drops the FIRST occurrence of every closed letter and
doubles its SECOND occurrence; singles and the open pair stay in place. -/
def canonicalReduced (w : List Nat) : List Nat :=
  (w.zipIdx.map (fun ic =>
      match status? w ic.1 with
      | some .closed =>
          if ic.2 = firstIdx w ic.1 then ([] : List Nat)
          else [ic.1, ic.1]
      | _ => [ic.1])).flatten

/-! ## The blob reduction and L2 -/

def nonBlob (z : Nat) (w : List Nat) : List Nat := w.filter (fun c => c ≠ z)

/-- One blob-letter reduction step.  All three shapes are instances of the
G4 laws at the blob letter `z` with word-valued interlopers. -/
inductive BlobStep (z : Nat) : List Nat → List Nat → Prop
  | hop (p B s : List Nat) (hB : B ≠ []) (hs : s ≠ []) (hzB : z ∉ B) :
      BlobStep z (p ++ z :: (B ++ z :: s)) (p ++ B ++ z :: z :: s)
  | contract (p B s : List Nat) (hB : B ≠ []) (hzB : z ∉ B) :
      BlobStep z (p ++ z :: z :: (B ++ z :: s)) (p ++ z :: (B ++ z :: s))
  | cap (p s : List Nat) :
      BlobStep z (p ++ z :: z :: z :: s) (p ++ z :: z :: s)

inductive BlobReduces (z : Nat) : List Nat → List Nat → Prop
  | refl (w) : BlobReduces z w w
  | step {w w' w''} : BlobStep z w w' → BlobReduces z w' w'' →
      BlobReduces z w w''

/-- **L2, single step**: a blob step fixes the non-blob subsequence. -/
theorem L2_step {z : Nat} {w w' : List Nat} (h : BlobStep z w w') :
    nonBlob z w' = nonBlob z w := by
  cases h with
  | hop p B s hB hs hzB =>
      simp [nonBlob, List.filter_append, List.filter_cons]
  | contract p B s hB hzB =>
      simp [nonBlob, List.filter_append, List.filter_cons]
  | cap p s =>
      simp [nonBlob, List.filter_append, List.filter_cons]

/-- **L2, closure**: the whole blob reduction fixes the non-blob
subsequence. -/
theorem L2_closure {z : Nat} {w w' : List Nat}
    (h : BlobReduces z w w') : nonBlob z w' = nonBlob z w := by
  induction h with
  | refl w => rfl
  | step hstep _ ih => exact ih.trans (L2_step hstep)

/-- Every blob step is a derivation in the G4 basis (hop = hopLaw with the
interloper as the y-word; contract = headDupLaw reversed; cap = capLaw). -/
theorem blobStep_derives {z : Nat} {w w' : List Nat}
    (h : BlobStep z w w') :
    Derives basisG4 (wordOfD w) (wordOfD w') := by
  cases h with
  | hop p B s hB hs hzB =>
      cases B with
      | nil => exact False.elim (hB rfl)
      | cons b Btail =>
          cases s with
          | nil => exact False.elim (hs rfl)
          | cons sHead sTail =>
              have step := derivesHop
                (Word.singleton z) (Word.mk b Btail)
                (Word.mk sHead sTail)
              have contextual := derivesInListContext step p []
              simpa [wordOfD, Word.toList, Word.append, Word.singleton,
                List.append_assoc] using contextual
  | contract p B s hB hzB =>
      cases B with
      | nil => exact False.elim (hB rfl)
      | cons b Btail =>
          have step := derivesHeadDupContraction
            (Word.singleton z) (Word.mk b Btail)
          have contextual := derivesInListContext step p s
          simpa [wordOfD, Word.toList, Word.append, Word.singleton,
            List.append_assoc] using contextual
  | cap p s =>
      have step := derivesCapContraction (Word.singleton z)
      have contextual := derivesInListContext step p s
      simpa [wordOfD, Word.toList, Word.append, Word.singleton,
        List.append_assoc] using contextual

/-- A complete blob-reduction chain is a derivation in the G4 basis. -/
theorem blobReduces_derives {z : Nat} {w w' : List Nat}
    (h : BlobReduces z w w') :
    Derives basisG4 (wordOfD w) (wordOfD w') := by
  induction h with
  | refl current => exact Derives.refl (wordOfD current)
  | step first _ tail =>
      exact (blobStep_derives first).trans tail

/-! ## L1: kept-letter preservation -/

/-- σ is faithful on the kept letters `K` relative to `w`: injective on K,
maps K-letters to themselves-or-injectively, and no other letter of `w`
lands on a K-image. -/
def FaithfulOn (σ : Nat → Nat) (K : List Nat) (w : List Nat) : Prop :=
  (∀ x ∈ K, ∀ y ∈ K, σ x = σ y → x = y) ∧
  (∀ c ∈ w, c ∉ K → ∀ x ∈ K, σ c ≠ σ x)

private theorem count_map_of_fiber_on (σ : Nat → Nat) (target : Nat) :
    ∀ letters : List Nat,
      (∀ letter, letter ∈ letters →
        σ letter = σ target → letter = target) →
      (letters.map σ).count (σ target) = letters.count target
  | [] => by simp
  | head :: tail => by
      intro fiber
      have tailFiber :
          ∀ letter, letter ∈ tail →
            σ letter = σ target → letter = target := by
        intro letter member imageEq
        exact fiber letter (by simp [member]) imageEq
      have tailCount := count_map_of_fiber_on σ target tail tailFiber
      by_cases headEq : head = target
      · subst head
        simp [tailCount]
      · have imageNe : σ head ≠ σ target := by
          intro imageEq
          exact headEq (fiber head (by simp) imageEq)
        simp [headEq, imageNe, tailCount]

private theorem lastLetter_map (σ : Nat → Nat) :
    ∀ letters : List Nat,
      lastLetter? (letters.map σ) = (lastLetter? letters).map σ
  | [] => rfl
  | head :: tail => by
      cases tail with
      | nil => rfl
      | cons next rest =>
          simpa only [List.map_cons, lastLetter?, List.getLast?_cons] using
            lastLetter_map σ (next :: rest)

private theorem filter_map_of_no_collision (σ : Nat → Nat) (K : List Nat) :
    ∀ letters : List Nat,
      (∀ c ∈ letters, c ∉ K → ∀ x ∈ K, σ c ≠ σ x) →
      ((letters.filter (· ∈ K)).map σ =
        (letters.map σ).filter (· ∈ K.map σ))
  | [] => by simp
  | head :: tail => by
      intro noCollision
      have tailNoCollision :
          ∀ c ∈ tail, c ∉ K → ∀ x ∈ K, σ c ≠ σ x := by
        intro c member notKept x kept
        exact noCollision c (by simp [member]) notKept x kept
      have tailEq := filter_map_of_no_collision σ K tail tailNoCollision
      have headPredicate :
          decide (σ head ∈ K.map σ) = decide (head ∈ K) := by
        rw [decide_eq_decide]
        constructor
        · intro imageMember
          by_cases headKept : head ∈ K
          · exact headKept
          · rcases List.mem_map.mp imageMember with
              ⟨source, sourceKept, sourceImage⟩
            exact False.elim
              ((noCollision head (by simp) headKept source sourceKept)
                sourceImage.symm)
        · intro headKept
          exact List.mem_map.mpr ⟨head, headKept, rfl⟩
      simp only [List.map_cons, List.filter_cons]
      rw [headPredicate]
      split
      · simp only [List.map_cons]
        rw [tailEq]
      · exact tailEq

/-- **L1**: under a faithful σ that keeps the last letter, every kept
letter's count, status, and the mutual order of kept-letter occurrences
are preserved in the mapped word. -/
theorem L1_statusPreservation {σ : Nat → Nat} {K w : List Nat}
    (hf : FaithfulOn σ K w) (hlast : ∀ t, lastLetter? w = some t → t ∈ K) :
    (∀ c ∈ K, (w.map σ).count (σ c) = w.count c) ∧
    (∀ c ∈ K, status? (w.map σ) (σ c) = status? w c) ∧
    ((w.filter (· ∈ K)).map σ = (w.map σ).filter (· ∈ K.map σ)) := by
  rcases hf with ⟨injectiveKept, noCollision⟩
  have fiber :
      ∀ c ∈ K, ∀ x ∈ w, σ x = σ c → x = c := by
    intro c cKept x xMember imageEq
    by_cases xKept : x ∈ K
    · exact injectiveKept x xKept c cKept imageEq
    · exact False.elim
        (noCollision x xMember xKept c cKept imageEq)
  have countEq :
      ∀ c ∈ K, (w.map σ).count (σ c) = w.count c := by
    intro c cKept
    exact count_map_of_fiber_on σ c w (fiber c cKept)
  have lastEq :
      ∀ c ∈ K,
        lastLetter? (w.map σ) = some (σ c) ↔
          lastLetter? w = some c := by
    intro c cKept
    constructor
    · intro mapped
      rw [lastLetter_map] at mapped
      cases sourceEq : lastLetter? w with
      | none => simp [sourceEq] at mapped
      | some t =>
          have tKept : t ∈ K := hlast t sourceEq
          have imageEq : σ t = σ c := by
            simpa [sourceEq] using mapped
          have tc : t = c :=
            injectiveKept t tKept c cKept imageEq
          simpa [tc] using sourceEq
    · intro source
      simpa [lastLetter_map, source]
  have statusEq :
      ∀ c ∈ K, status? (w.map σ) (σ c) = status? w c := by
    intro c cKept
    have mappedCount := countEq c cKept
    have sameLast := lastEq c cKept
    unfold status?
    rw [mappedCount]
    cases count : w.count c with
    | zero => rfl
    | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
            by_cases sourceLast : lastLetter? w = some c
            · have mappedLast := sameLast.mpr sourceLast
              simp [sourceLast, mappedLast]
            · have mappedLast :
                  lastLetter? (w.map σ) ≠ some (σ c) := by
                intro mapped
                exact sourceLast (sameLast.mp mapped)
              simp [sourceLast, mappedLast]
  refine ⟨countEq, statusEq, ?_⟩
  exact filter_map_of_no_collision σ K w noCollision

/-! ## L3: canonical factorization under renaming -/

section CanonicalInterface

/- The full canonical map (reduction strategy left to the witness lane). -/
variable (canonical : List Nat → List Nat)
/- Canonical soundness: derivably-equal words have equal canonicals, and
canonical agrees with `canonicalReduced` on reduced words.  BOTH are
witness-lane obligations; this module consumes them as hypotheses so that
no paper bridge remains. -/
variable
  (canonicalSound :
    ∀ {a b : List Nat},
      a ≠ [] → b ≠ [] →
      Derives basisG4 (wordOfD a) (wordOfD b) →
        canonical a = canonical b)
  (canonicalReduced_eq :
    ∀ {a : List Nat}, Reduced a → canonical a = canonicalReduced a)
  (derives_canonical :
    ∀ a : List Nat, a ≠ [] →
      Derives basisG4 (wordOfD a) (wordOfD (canonical a)))
  (canonical_ne : ∀ a, a ≠ [] → canonical a ≠ [])
  (canonical_normal :
    ∀ a, Reduced (canonical a) ∧
      canonicalReduced (canonical a) = canonical a)
  (canonical_blob_reduces :
    ∀ {a : List Nat} {K : List Nat} {z : Nat} {σ : Nat → Nat},
      Reduced a → canonicalReduced a = a →
      FaithfulOn σ K a →
      (∀ t, lastLetter? a = some t → t ∈ K) →
      (∀ c, c ∈ a → c ∉ K → σ c = z) →
      z ∉ K.map σ →
      BlobReduces z (a.map σ) (canonical (a.map σ)))

include canonicalSound derives_canonical canonical_ne
/-- **L3**: `canonical (map σ w) = canonical (map σ (canonical w))` — laws
are closed under renaming, so `w ~ canonical w` maps to
`σw ~ σ(canonical w)`, and `canonicalSound` finishes. -/
theorem L3_canonFactor (σ : Nat → Nat) (w : List Nat) (hw : w ≠ []) :
    canonical (w.map σ) = canonical ((canonical w).map σ) := by
  apply canonicalSound (map_ne_nil hw σ)
    (map_ne_nil (canonical_ne w hw) σ)
  have renamed := Derives.rename (derives_canonical w hw) σ
  rw [wordOfD_map w σ hw] at renamed
  rw [wordOfD_map (canonical w) σ (canonical_ne w hw)] at renamed
  exact renamed
omit canonicalSound derives_canonical canonical_ne

/-! ## L4: pairwise reconstruction -/

/-- Projection to the letters `{x, y, t}`. -/
def proj3 (w : List Nat) (x y t : Nat) : List Nat :=
  w.filter (fun c => c = x ∨ c = y ∨ c = t)

private theorem eq_of_proj3_eq (t : Nat) :
    ∀ u v : List Nat,
      (∀ x y, proj3 u x y t = proj3 v x y t) →
      u = v
  | [], [], _ => rfl
  | [], head :: tail, projections => by
      have projected : (none : Option Nat) = some head := by
        simpa [proj3] using congrArg List.head? (projections head head)
      cases projected
  | head :: tail, [], projections => by
      have projected : some head = (none : Option Nat) := by
        simpa [proj3] using congrArg List.head? (projections head head)
      cases projected
  | leftHead :: leftTail, rightHead :: rightTail, projections => by
      have heads : leftHead = rightHead := by
        have projected : some leftHead = some rightHead := by
          simpa [proj3] using
            congrArg List.head? (projections leftHead rightHead)
        exact Option.some.inj projected
      subst rightHead
      have tailProjections :
          ∀ x y, proj3 leftTail x y t = proj3 rightTail x y t := by
        intro x y
        have projected := projections x y
        by_cases kept : leftHead = x ∨ leftHead = y ∨ leftHead = t
        · simpa [proj3, kept] using projected
        · simpa [proj3, kept] using projected
      exact congrArg (List.cons leftHead)
        (eq_of_proj3_eq t leftTail rightTail tailProjections)

/-- **L4**: canonical marked words with equal capped counts, equal last
letter, and equal `{x,y,last}`-projections for every pair are equal.
(A linear order is determined by its pairwise restrictions; the open
pair's two pieces are covered by pairs containing the last letter.) -/
theorem L4_pairReconstruction {u v : List Nat}
    (hu : Reduced u) (hv : Reduced v)
    (hcu : canonicalReduced u = u) (hcv : canonicalReduced v = v)
    (hcnt : ∀ c, cappedCount u c = cappedCount v c)
    (hlast : lastLetter? u = lastLetter? v)
    (hproj : ∀ x y t, lastLetter? u = some t →
        proj3 u x y t = proj3 v x y t) :
    u = v := by
  cases sourceLast : lastLetter? u with
  | none =>
      have uNil : u = [] := List.getLast?_eq_none_iff.mp sourceLast
      have targetLast : lastLetter? v = none := hlast.symm.trans sourceLast
      have vNil : v = [] := List.getLast?_eq_none_iff.mp targetLast
      exact uNil.trans vNil.symm
  | some t =>
      apply eq_of_proj3_eq t u v
      intro x y
      exact hproj x y t sourceLast

/-! ## L5: the constructive merge-collapse -/

/-- Image bound: σ maps every letter of `u ++ v` into `img`. -/
def ImageBound (σ : Nat → Nat) (u v img : List Nat) : Prop :=
  ∀ c ∈ u ++ v, σ c ∈ img

/-- Keep the letters in `K` fixed and merge every other letter into `z`. -/
private def collapseOutside (K : List Nat) (z c : Nat) : Nat :=
  if c ∈ K then c else z

/-- A fresh natural-number letter for a finite keep list. -/
private def freshOutside : List Nat → Nat
  | [] => 0
  | c :: K => max (c + 1) (freshOutside K)

private theorem mem_lt_freshOutside {c : Nat} :
    ∀ K : List Nat, c ∈ K → c < freshOutside K
  | [], member => by simp at member
  | head :: tail, member => by
      rcases List.mem_cons.mp member with equal | member
      · subst c
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self head)
          (Nat.le_max_left (head + 1) (freshOutside tail))
      · exact Nat.lt_of_lt_of_le (mem_lt_freshOutside tail member)
          (Nat.le_max_right (head + 1) (freshOutside tail))

private theorem freshOutside_not_mem (K : List Nat) : freshOutside K ∉ K := by
  intro member
  exact (Nat.lt_irrefl (freshOutside K)) (mem_lt_freshOutside K member)

private theorem collapseOutside_faithful (K w : List Nat) (z : Nat)
    (hz : z ∉ K) : FaithfulOn (collapseOutside K z) K w := by
  constructor
  · intro x hx y hy imageEq
    simpa [collapseOutside, hx, hy] using imageEq
  · intro c _ hc x hx
    have hzx : z ≠ x := by
      intro equality
      subst x
      exact hz hx
    simpa [collapseOutside, hc, hx] using hzx

private theorem collapseOutside_unkept (K : List Nat) (z : Nat) :
    ∀ c, c ∉ K → collapseOutside K z c = z := by
  intro c hc
  simp [collapseOutside, hc]

private theorem freshOutside_not_mem_keptImage (K : List Nat) :
    freshOutside K ∉ K.map (collapseOutside K (freshOutside K)) := by
  intro member
  rcases List.mem_map.mp member with ⟨c, hc, imageEq⟩
  have fixed : collapseOutside K (freshOutside K) c = c := by
    simp [collapseOutside, hc]
  have equal : c = freshOutside K := fixed.symm.trans imageEq
  exact freshOutside_not_mem K (equal ▸ hc)

private theorem nonBlob_map_collapseOutside (w K : List Nat) (z : Nat)
    (hz : z ∉ K) :
    nonBlob z (w.map (collapseOutside K z)) = w.filter (· ∈ K) := by
  unfold nonBlob
  induction w with
  | nil => rfl
  | cons c tail ih =>
      have ih' := ih
      simp only [decide_not] at ih'
      by_cases hc : c ∈ K
      · have hcz : c ≠ z := by
          intro equality
          subst c
          exact hz hc
        simp [collapseOutside, hc, hcz, ih']
      · simp [collapseOutside, hc, ih']

private theorem imageBound_collapseOutside (u v K : List Nat) (z : Nat) :
    ImageBound (collapseOutside K z) u v (K ++ [z]) := by
  intro c _
  by_cases hc : c ∈ K
  · simp [collapseOutside, hc]
  · simp [collapseOutside, hc]

private theorem lastLetter_filter_eq_some_of_mem {w K : List Nat} {t : Nat}
    (hlast : lastLetter? w = some t) (ht : t ∈ K) :
    lastLetter? (w.filter (· ∈ K)) = some t := by
  rcases List.getLast?_eq_some_iff.mp hlast with ⟨pre, rfl⟩
  simp [lastLetter?, List.filter_append, ht]

private theorem count_filter_membership_of_mem (w K : List Nat) (c : Nat)
    (hc : c ∈ K) : (w.filter (· ∈ K)).count c = w.count c := by
  exact List.count_filter (p := fun x => decide (x ∈ K)) (by simp [hc])

/-- Two distinct canonical marked words have a distinguishing projection on
at most three kept letters, and the keep set contains both final letters. -/
private theorem exists_small_kept_projection {u v : List Nat}
    (hu : u ≠ []) (hv : v ≠ [])
    (hru : Reduced u) (hrv : Reduced v)
    (hcu : canonicalReduced u = u) (hcv : canonicalReduced v = v)
    (hne : u ≠ v) :
    ∃ K : List Nat, K.length ≤ 3 ∧
      (∀ t, lastLetter? u = some t → t ∈ K) ∧
      (∀ t, lastLetter? v = some t → t ∈ K) ∧
      u.filter (· ∈ K) ≠ v.filter (· ∈ K) := by
  classical
  by_cases hlast : lastLetter? u = lastLetter? v
  · by_cases hcnt : ∀ c, cappedCount u c = cappedCount v c
    · have hproj :
          ¬ ∀ x y t, lastLetter? u = some t →
              proj3 u x y t = proj3 v x y t := by
        intro projections
        exact hne
          (L4_pairReconstruction hru hrv hcu hcv hcnt hlast projections)
      have witness :
          ∃ x y t, lastLetter? u = some t ∧
            proj3 u x y t ≠ proj3 v x y t := by
        apply Classical.byContradiction
        intro noWitness
        apply hproj
        intro x y t ht
        apply Classical.byContradiction
        intro different
        exact noWitness ⟨x, y, t, ht, different⟩
      rcases witness with ⟨x, y, t, ht, hxy⟩
      refine ⟨[x, y, t], by simp, ?_, ?_, ?_⟩
      · intro s hs
        have : s = t := Option.some.inj (hs.symm.trans ht)
        subst s
        simp
      · intro s hs
        have sourceLast : lastLetter? u = some s := hlast.trans hs
        have : s = t := Option.some.inj (sourceLast.symm.trans ht)
        subst s
        simp
      · intro projected
        apply hxy
        simpa [proj3] using projected
    · have witness : ∃ c, cappedCount u c ≠ cappedCount v c := by
        apply Classical.byContradiction
        intro noWitness
        apply hcnt
        intro c
        apply Classical.byContradiction
        intro different
        exact noWitness ⟨c, different⟩
      rcases witness with ⟨c, hc⟩
      cases ht : lastLetter? u with
      | none =>
          have uNil : u = [] := List.getLast?_eq_none_iff.mp ht
          exact False.elim (hu uNil)
      | some t =>
          refine ⟨[c, t], by simp, ?_, ?_, ?_⟩
          · intro s hs
            have : t = s := Option.some.inj hs
            subst s
            simp
          · intro s hs
            have sourceLast : lastLetter? u = some s := hlast.trans hs
            have : t = s := Option.some.inj (ht.symm.trans sourceLast)
            subst s
            simp
          · intro projected
            apply hc
            have counted := congrArg (List.count c) projected
            have countEq : u.count c = v.count c := by
              rw [count_filter_membership_of_mem u [c, t] c (by simp),
                count_filter_membership_of_mem v [c, t] c (by simp)] at counted
              exact counted
            simp [cappedCount, countEq]
  · cases huLast : lastLetter? u with
    | none =>
        have uNil : u = [] := List.getLast?_eq_none_iff.mp huLast
        exact False.elim (hu uNil)
    | some tu =>
        cases hvLast : lastLetter? v with
        | none =>
            have vNil : v = [] := List.getLast?_eq_none_iff.mp hvLast
            exact False.elim (hv vNil)
        | some tv =>
            have htuv : tu ≠ tv := by
              intro equality
              apply hlast
              simpa [huLast, hvLast, equality]
            refine ⟨[tu, tv], by simp, ?_, ?_, ?_⟩
            · intro s hs
              have : tu = s := Option.some.inj hs
              subst s
              simp
            · intro s hs
              have : tv = s := Option.some.inj hs
              subst s
              simp
            · intro projected
              have lastEq := congrArg lastLetter? projected
              rw [lastLetter_filter_eq_some_of_mem huLast (by simp),
                lastLetter_filter_eq_some_of_mem hvLast (by simp)] at lastEq
              exact htuv (Option.some.inj lastEq)

include canonicalSound derives_canonical canonical_ne canonical_normal
  canonical_blob_reduces
/-- **L5 (main theorem)**: distinct canonicals have a σ with image of
size ≤ 4 keeping the canonicals of the images distinct.  Constructive
cases (msg-0061): last letters differ (image 3); a capped count differs
(image 2); otherwise a pair of items is oppositely ordered and
σ = id on {x, y, t}, blob z elsewhere (image 4), closed by L1 + L2 + L4
via L3. -/
theorem L5_mergeCollapse {u v : List Nat}
    (hu : u ≠ []) (hv : v ≠ []) (h : canonical u ≠ canonical v) :
    ∃ σ : Nat → Nat, ∃ img : List Nat, img.length ≤ 4 ∧
      ImageBound σ u v img ∧
      canonical (u.map σ) ≠ canonical (v.map σ) := by
  classical
  let U := canonical u
  let V := canonical v
  have hUne : U ≠ [] := by
    simpa [U] using canonical_ne u hu
  have hVne : V ≠ [] := by
    simpa [V] using canonical_ne v hv
  have hUV : U ≠ V := by
    simpa [U, V] using h
  obtain ⟨hUr, hUc⟩ := canonical_normal u
  obtain ⟨hVr, hVc⟩ := canonical_normal v
  obtain ⟨K, hK, hlastU, hlastV, hprojection⟩ :=
    exists_small_kept_projection hUne hVne hUr hVr hUc hVc hUV
  let z := freshOutside K
  let σ := collapseOutside K z
  have hz : z ∉ K := by
    simpa [z] using freshOutside_not_mem K
  have hzImage : z ∉ K.map σ := by
    simpa [z, σ] using freshOutside_not_mem_keptImage K
  have hfaithU : FaithfulOn σ K U := by
    simpa [σ] using collapseOutside_faithful K U z hz
  have hfaithV : FaithfulOn σ K V := by
    simpa [σ] using collapseOutside_faithful K V z hz
  have houtsideU : ∀ c, c ∈ U → c ∉ K → σ c = z := by
    intro c _ hc
    simpa [σ] using collapseOutside_unkept K z c hc
  have houtsideV : ∀ c, c ∈ V → c ∉ K → σ c = z := by
    intro c _ hc
    simpa [σ] using collapseOutside_unkept K z c hc
  have reducesU :
      BlobReduces z (U.map σ) (canonical (U.map σ)) :=
    canonical_blob_reduces hUr hUc hfaithU hlastU houtsideU hzImage
  have reducesV :
      BlobReduces z (V.map σ) (canonical (V.map σ)) :=
    canonical_blob_reduces hVr hVc hfaithV hlastV houtsideV hzImage
  have keepsU :
      nonBlob z (canonical (U.map σ)) = U.filter (· ∈ K) :=
    (L2_closure reducesU).trans
      (by simpa [σ] using nonBlob_map_collapseOutside U K z hz)
  have keepsV :
      nonBlob z (canonical (V.map σ)) = V.filter (· ∈ K) :=
    (L2_closure reducesV).trans
      (by simpa [σ] using nonBlob_map_collapseOutside V K z hz)
  have collapsedDifferent :
      canonical (U.map σ) ≠ canonical (V.map σ) := by
    intro equal
    apply hprojection
    calc
      U.filter (· ∈ K) = nonBlob z (canonical (U.map σ)) := keepsU.symm
      _ = nonBlob z (canonical (V.map σ)) := congrArg (nonBlob z) equal
      _ = V.filter (· ∈ K) := keepsV
  refine ⟨σ, K ++ [z], ?_, ?_, ?_⟩
  · simpa using Nat.add_le_add_right hK 1
  · exact imageBound_collapseOutside u v K z
  · intro mappedEqual
    apply collapsedDifferent
    calc
      canonical (U.map σ) = canonical (u.map σ) :=
        (L3_canonFactor (canonical := canonical)
          (canonicalSound := canonicalSound)
          (derives_canonical := derives_canonical)
          (canonical_ne := canonical_ne) σ u hu).symm
      _ = canonical (v.map σ) := mappedEqual
      _ = canonical (V.map σ) :=
        L3_canonFactor (canonical := canonical)
          (canonicalSound := canonicalSound)
          (derives_canonical := derives_canonical)
          (canonical_ne := canonical_ne) σ v hv

end CanonicalInterface

end SemigroupBasis.CoRoots.Order6LeeLiP2G4
