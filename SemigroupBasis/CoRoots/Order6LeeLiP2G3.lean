import SemigroupBasis.CoRoots.Order6LeeLiP2G2
import SemigroupBasis.CoRoots.Order6LeeLiP2G4MergeCollapse

/-!
# Lee--Li P2 group G3: shared source contract (msg-0197)

EVIDENCE LABEL: source-staged draft, NOT compiled here; statement-level
design is the independently replayed msg-0054 G3 dossier (basis, tuple
invariant, canonical forms, saturated free objects 16/102/544).  No class
is claimed; endpoints are unconditional theorem SHAPES consumed by the v3
pipeline after codex compiles, axiom-gates, and seals.

STRUCTURE
* Basis {xx=xxx, xyzw=yxzw, xyx=xxyx}.  Law A (interior commutation) is
  the SAME identity as the compiled G2 law; the split-pair hop is
  derivable from A, so G3's count-reduction steps are exactly the
  `BlobStep` shapes of `Order6LeeLiP2G4MergeCollapse` — that module's
  `L2_step/L2_closure` (compiled at 084d60532) are reused verbatim, which
  is the shared-lemma-file plan of msg-0061 §next.
* Tuple invariant on reduced words: (sorted capped profile,
  occurrence-tagged second-to-last, occurrence-tagged last).
* Canonical: sorted interior ++ the two boundary letters.  The interior
  MULTISET is determined by (profile, boundary), so normalization has TWO
  stages only — count-reduce, then interior sort; there is no padding
  stage (unlike G2, whose repeat-case stem is the full support).
* Separation: the bounded merge-collapse (image ≤ 4) is the strictly
  easier tuple-invariant instance of the proved G4 theorem; the
  per-member fingerprint data modules are emitted separately by the v3
  emitter generalized to the 544 four-letter G3 canonicals.

API LEDGER: everything used is either defined here, in the compiled G2
module (`Derives`, `Identity`, `Word`, `Models`, `BasisFor`,
`InvariantSeparation` pattern), or in the G4 merge-collapse module
(`BlobStep`, `BlobReduces`, `L2_closure`, `wordOfD`-policy).
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G3

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6LeeLiP2G4 (BlobStep BlobReduces L2_step L2_closure nonBlob)

/-! ## The three laws -/

def xx : Word Nat := ⟨1, [1]⟩
def xxx : Word Nat := ⟨1, [1, 1]⟩
def xyzw : Word Nat := ⟨1, [0, 2, 3]⟩
def yxzw : Word Nat := ⟨0, [1, 2, 3]⟩
def xyx : Word Nat := ⟨1, [0, 1]⟩
def xxyx : Word Nat := ⟨1, [1, 0, 1]⟩

def capLaw : Identity Nat := ⟨xx, xxx⟩
def interiorCommutationLaw : Identity Nat := ⟨xyzw, yxzw⟩
def headDupLaw : Identity Nat := ⟨xyx, xxyx⟩

def basis : List (Identity Nat) :=
  [capLaw, interiorCommutationLaw, headDupLaw]

private def instantiateFour (u v z w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | 3 => w
  | n + 4 => Word.singleton (n + 4)

private def instantiateTwo (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- Law A: swap two adjacent nonempty factors with two nonempty factors to
their right — the same statement as the compiled G2 lemma, over `basis`. -/
theorem derivesInteriorSwap (u v z w : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ w) (((v ++ u) ++ z) ++ w) := by
  have base : Derives basis xyzw yxzw :=
    Derives.fromBasis (e := interiorCommutationLaw) (by
      exact List.Mem.tail _ (List.Mem.head _))
  have substituted := Derives.subst base (instantiateFour v u z w)
  simpa [basis, interiorCommutationLaw, xyzw, yxzw, instantiateFour,
    Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using substituted

/-- Head duplication `a·B·a → a·a·B·a` (and its reverse contraction):
the headDupLaw instance with x := u, y := v. -/
theorem derivesHeadDup (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have base : Derives basis xyx xxyx :=
    Derives.fromBasis (e := headDupLaw) (by
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have substituted := Derives.subst base (instantiateTwo v u)
  simpa [basis, headDupLaw, xyx, xxyx, instantiateTwo,
    Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using substituted

/-- Cap `u·u → u·u·u` (reverse gives the contraction used in
count reduction). -/
theorem derivesCap (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis xx xxx :=
    Derives.fromBasis (e := capLaw) (by exact List.Mem.head _)
  have substituted := Derives.subst base (instantiateTwo u u)
  simpa [basis, capLaw, xx, xxx, instantiateTwo,
    Word.bind, Word.append, Word.singleton, Word.append_assoc]
    using substituted

/-! ## The tuple invariant (reduced words) -/

def Reduced (w : List Nat) : Prop := ∀ c, w.count c ≤ 2

/-- Occurrence tag of position `i`: `false` = first occurrence of its
letter, `true` = second. -/
def occTag (w : List Nat) (i : Nat) : Bool :=
  decide ((w.take i).count (w.getD i 0) ≠ 0)

/-- Sorted capped profile: (letter, isDoubled) for each support letter. -/
def profile (w : List Nat) : List (Nat × Bool) :=
  ((SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport w).mergeSort
      (fun a b => decide (a ≤ b))).map
    (fun c => (c, decide (w.count c = 2)))

/-- The sorted support specialized to the fixed four-letter alphabet used by
the finite G3 fingerprint inventory. -/
def supportFour (w : List Nat) : List Nat :=
  ([0, 1, 2, 3].filter fun c => decide (c ∈ w))

/-- A reduction-friendly form of `profile` on four-bounded words.  Keeping
`mergeSort` out of the finite inventory lets the ordinary kernel check the
generated certificates without a native reduction oracle. -/
def profileFour (w : List Nat) : List (Nat × Bool) :=
  (supportFour w).map fun c => (c, decide (w.count c = 2))

structure G3Inv where
  profile : List (Nat × Bool)
  p2 : Option (Nat × Bool)
  p1 : Option (Nat × Bool)
deriving DecidableEq, Repr

def invariant (w : List Nat) : G3Inv :=
  { profile := profile w
    p2 :=
      if h : 2 ≤ w.length then
        some (w.getD (w.length - 2) 0, occTag w (w.length - 2))
      else none
    p1 :=
      if h : 1 ≤ w.length then
        some (w.getD (w.length - 1) 0, occTag w (w.length - 1))
      else none }

/-! ## Canonical form -/

def interiorMultiplicity (key : G3Inv) (letter : Nat)
    (doubled : Bool) : Nat :=
  let total : Nat := if doubled then 2 else 1
  let consumed : Nat :=
    (if (key.p2.map Prod.fst) = some letter then 1 else 0) +
    (if (key.p1.map Prod.fst) = some letter then 1 else 0)
  total - consumed

def interiorBlock (key : G3Inv) (entry : Nat × Bool) : List Nat :=
  List.replicate (interiorMultiplicity key entry.1 entry.2) entry.1

/-- Interior multiset: each profile letter contributes its count minus the
boundary occurrences it supplies. -/
def interiorList (key : G3Inv) : List Nat :=
  key.profile.flatMap (interiorBlock key)

/-- Canonical word: sorted interior, then the two boundary letters. -/
def canonical (key : G3Inv) : List Nat :=
  match key.p2, key.p1 with
  | some q2, some q1 => interiorList key ++ [q2.1, q1.1]
  | none, some q1 => [q1.1]
  | _, _ => []

/-- Canonical renderer for a reduced word.  Raw words must first pass through
the `countReduce` field of a `G3NormalizationWitness`; the displayed invariant
is not stable under count reduction on unreduced words. -/
def normalForm (w : List Nat) : List Nat := canonical (invariant w)

/-! ## Two-stage normalization contract -/

/-- G3 normalization witness: count reduction (BlobStep shapes at each
over-doubled letter — hop derivable from law A, contraction from
headDupLaw, cap from capLaw), then interior sorting (law A permutations).
There is no padding stage: the interior multiset is invariant-determined. -/
structure G3NormalizationWitness where
  countReduce : List Nat → List Nat
  sortInterior : List Nat → List Nat
  reduce_reduced : ∀ w, Reduced (countReduce w)
  reduce_nonempty : ∀ w, w ≠ [] → countReduce w ≠ []
  reduce_derives : ∀ w, w ≠ [] →
    Derives basis
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD w)
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD (countReduce w))
  sort_derives : ∀ w, w ≠ [] →
    Derives basis
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD (countReduce w))
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD
        (sortInterior (countReduce w)))
  sort_eq_normalForm : ∀ w,
    sortInterior (countReduce w) = normalForm (countReduce w)

namespace G3NormalizationWitness

theorem derives_normalForm (witness : G3NormalizationWitness)
    (w : List Nat) (hw : w ≠ []) :
    Derives basis
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD w)
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD
        (normalForm (witness.countReduce w))) := by
  have first := witness.reduce_derives w hw
  have second := witness.sort_derives w hw
  rw [witness.sort_eq_normalForm w] at second
  exact first.trans second

end G3NormalizationWitness

/-! ## Separation interface and endpoint -/

/-- The G3 invariant separates valid identities between nonempty reduced
words.  Count reduction is deliberately outside this contract: the raw
invariant is not preserved by `xxx → xx`. -/
def InvariantSeparation (G : Semigroup S) : Prop :=
  ∀ {u v : List Nat},
    u ≠ [] → v ≠ [] → Reduced u → Reduced v →
      ({ lhs := SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD u
         rhs := SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD v } :
          Identity Nat).SatisfiedBy G →
        invariant u = invariant v

/-! ### Finite-colour separation lemmas -/

private def profileSupport (w : List Nat) : List Nat :=
  (SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport w).mergeSort
    (fun a b => decide (a ≤ b))

private theorem deduplicateSupport_mem (letter : Nat) (letters : List Nat) :
    letter ∈
        SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport letters ↔
      letter ∈ letters := by
  induction letters with
  | nil =>
      simp [SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport]
  | cons head tail ih =>
      by_cases h : head ∈ tail
      · have headCase : letter = head → letter ∈ tail := by
          intro letterEq
          simpa [letterEq] using h
        simpa [SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport,
          h, ih] using headCase
      · simp [SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport,
          h, ih]

private theorem deduplicateSupport_nodup (letters : List Nat) :
    (SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport letters).Nodup := by
  induction letters with
  | nil =>
      simp [SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport]
  | cons head tail ih =>
      by_cases h : head ∈ tail
      · simpa [SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport,
          h] using ih
      · simp [SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport,
          h, ih, deduplicateSupport_mem]

private theorem profileSupport_mem (w : List Nat) (letter : Nat) :
    letter ∈ profileSupport w ↔ letter ∈ w := by
  simp [profileSupport, deduplicateSupport_mem]

private theorem profileSupport_nodup (w : List Nat) :
    (profileSupport w).Nodup := by
  exact (List.mergeSort_perm
      (SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport w)
      (fun a b : Nat => decide (a ≤ b))).nodup_iff.mpr
    (deduplicateSupport_nodup w)

private theorem profileSupport_sorted (w : List Nat) :
    (profileSupport w).Pairwise (· ≤ ·) := by
  unfold profileSupport
  have sorted := List.pairwise_mergeSort
    (le := fun a b : Nat => decide (a ≤ b))
    (fun _ _ _ => by simp; omega)
    (fun _ _ => by simp; omega)
    (SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport w)
  exact sorted.imp (by intro _ _ h; simpa using h)

private theorem sortedNodup_eq_of_mem_iff
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (member : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have : head ∈ ([] : List Nat) := (member head).mpr (by simp)
          simp at this
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          have : leftHead ∈ ([] : List Nat) :=
            (member leftHead).mp (by simp)
          simp at this
      | cons rightHead rightTail =>
          have leftHeadMem : leftHead ∈ rightHead :: rightTail :=
            (member leftHead).mp (by simp)
          have rightHeadMem : rightHead ∈ leftHead :: leftTail :=
            (member rightHead).mpr (by simp)
          have leftLeRight : leftHead ≤ rightHead := by
            simp only [List.mem_cons] at rightHeadMem
            rcases rightHeadMem with rfl | memberTail
            · exact Nat.le_refl _
            · exact (List.pairwise_cons.mp leftSorted).1 _ memberTail
          have rightLeLeft : rightHead ≤ leftHead := by
            simp only [List.mem_cons] at leftHeadMem
            rcases leftHeadMem with rfl | memberTail
            · exact Nat.le_refl _
            · exact (List.pairwise_cons.mp rightSorted).1 _ memberTail
          have headsEq : leftHead = rightHead :=
            Nat.le_antisymm leftLeRight rightLeLeft
          subst rightHead
          congr 1
          apply ih
          · exact (List.pairwise_cons.mp leftSorted).2
          · exact (List.pairwise_cons.mp rightSorted).2
          · exact (List.nodup_cons.mp leftNodup).2
          · exact (List.nodup_cons.mp rightNodup).2
          · intro letter
            have leftFresh := (List.nodup_cons.mp leftNodup).1
            have rightFresh := (List.nodup_cons.mp rightNodup).1
            constructor
            · intro memberLeft
              have letterNe : letter ≠ leftHead := by
                intro letterEq
                exact leftFresh (letterEq ▸ memberLeft)
              have memberFull : letter ∈ leftHead :: leftTail := by
                simp [memberLeft]
              have := (member letter).mp memberFull
              simpa [letterNe] using this
            · intro memberRight
              have letterNe : letter ≠ leftHead := by
                intro letterEq
                exact rightFresh (letterEq ▸ memberRight)
              have memberFull : letter ∈ leftHead :: rightTail := by
                simp [memberRight]
              have := (member letter).mpr memberFull
              simpa [letterNe] using this

/-- On the fixed alphabet `{0,1,2,3}`, the general merge-sorted profile is the
explicit four-letter profile used by finite certificate computation. -/
theorem profile_eq_profileFour_of_bound {w : List Nat}
    (bounded : ∀ c, c ∈ w → c < 4) :
    profile w = profileFour w := by
  have supportEq : profileSupport w = supportFour w := by
    apply sortedNodup_eq_of_mem_iff
    · exact profileSupport_sorted w
    · by_cases h0 : 0 ∈ w <;>
        by_cases h1 : 1 ∈ w <;>
        by_cases h2 : 2 ∈ w <;>
        by_cases h3 : 3 ∈ w <;>
        simp [supportFour, h0, h1, h2, h3]
    · exact profileSupport_nodup w
    · unfold supportFour
      exact List.filter_sublist.nodup (by decide)
    · intro c
      constructor
      · intro member
        have inWord : c ∈ w := (profileSupport_mem w c).mp member
        have lessFour : c < 4 := bounded c inWord
        have cases : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
        rcases cases with rfl | rfl | rfl | rfl <;>
          simp [supportFour, inWord]
      · intro member
        apply (profileSupport_mem w c).mpr
        exact of_decide_eq_true (List.mem_filter.mp member).2
  change
    (profileSupport w).map (fun c => (c, decide (w.count c = 2))) =
      (supportFour w).map (fun c => (c, decide (w.count c = 2)))
  rw [supportEq]

private theorem profile_eq_of_support_flags {u v : List Nat}
    (supportEq : ∀ c, c ∈ u ↔ c ∈ v)
    (flagEq : ∀ c, c ∈ u →
      decide (u.count c = 2) = decide (v.count c = 2)) :
    profile u = profile v := by
  have sortedSupportEq : profileSupport u = profileSupport v := by
    apply sortedNodup_eq_of_mem_iff
    · exact profileSupport_sorted u
    · exact profileSupport_sorted v
    · exact profileSupport_nodup u
    · exact profileSupport_nodup v
    · intro c
      simpa [profileSupport_mem] using supportEq c
  change
    (profileSupport u).map (fun c => (c, decide (u.count c = 2))) =
      (profileSupport v).map (fun c => (c, decide (v.count c = 2)))
  rw [sortedSupportEq]
  apply List.map_congr_left
  intro c hc
  have hcv : c ∈ v := (profileSupport_mem v c).mp hc
  have hcu : c ∈ u := (supportEq c).mpr hcv
  exact congrArg (fun b : Bool => (c, b)) (flagEq c hcu)

private theorem profile_first_mem (w : List Nat) (c : Nat) :
    c ∈ (profile w).map Prod.fst ↔ c ∈ w := by
  change c ∈
      ((profileSupport w).map
        (fun d => (d, decide (w.count d = 2)))).map Prod.fst ↔ c ∈ w
  simp [profileSupport_mem]

private theorem profile_pair_mem (w : List Nat) (c : Nat) (b : Bool) :
    (c, b) ∈ profile w ↔
      c ∈ w ∧ b = decide (w.count c = 2) := by
  change (c, b) ∈
      (profileSupport w).map
        (fun d => (d, decide (w.count d = 2))) ↔ _
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨d, hd, pairEq⟩
    have dc : d = c := congrArg Prod.fst pairEq
    subst d
    exact ⟨(profileSupport_mem w c).mp hd,
      (congrArg Prod.snd pairEq).symm⟩
  · rintro ⟨hc, rfl⟩
    exact List.mem_map.mpr
      ⟨c, (profileSupport_mem w c).mpr hc, rfl⟩

private theorem count_map_of_fiber (sigma : Nat → Nat) (target : Nat)
    (fiber : ∀ letter, sigma letter = sigma target → letter = target) :
    ∀ letters : List Nat,
      (letters.map sigma).count (sigma target) = letters.count target
  | [] => by simp
  | head :: tail => by
      by_cases headEq : head = target
      · subst head
        simp [count_map_of_fiber sigma target fiber tail]
      · have imageNe : sigma head ≠ sigma target := by
          intro imageEq
          exact headEq (fiber head imageEq)
        simp [headEq, imageNe,
          count_map_of_fiber sigma target fiber tail]

private def collapseAt (chosen letter : Nat) : Nat :=
  if letter = chosen then 1 else 0

private theorem collapseAt_fiber (chosen letter : Nat)
    (imageEq : collapseAt chosen letter = collapseAt chosen chosen) :
    letter = chosen := by
  by_cases equal : letter = chosen
  · exact equal
  · simp [collapseAt, equal] at imageEq

private theorem collapseAt_image (chosen letter : Nat) :
    collapseAt chosen letter ∈ [0, 1] := by
  by_cases equal : letter = chosen
  · simp [collapseAt, equal]
  · simp [collapseAt, equal]

private def separatePair (left right letter : Nat) : Nat :=
  if letter = left then 1 else if letter = right then 2 else 0

private theorem separatePair_fiber_left (left right letter : Nat)
    (imageEq :
      separatePair left right letter = separatePair left right left) :
    letter = left := by
  by_cases rightEq : right = left
  · subst right
    by_cases equal : letter = left
    · exact equal
    · simp [separatePair, equal] at imageEq
  · by_cases equal : letter = left
    · exact equal
    · by_cases rightEqual : letter = right
      · simp [separatePair, equal, rightEqual, rightEq] at imageEq
      · simp [separatePair, equal, rightEqual] at imageEq

private theorem separatePair_fiber_right (left right letter : Nat)
    (imageEq :
      separatePair left right letter = separatePair left right right) :
    letter = right := by
  by_cases rightEq : right = left
  · subst right
    exact separatePair_fiber_left left left letter imageEq
  · by_cases equal : letter = right
    · exact equal
    · by_cases leftEqual : letter = left
      · simp [separatePair, equal, leftEqual, rightEq] at imageEq
      · simp [separatePair, equal, leftEqual, rightEq] at imageEq

private theorem separatePair_image (left right letter : Nat) :
    separatePair left right letter ∈ [0, 1, 2] := by
  by_cases leftEqual : letter = left
  · simp [separatePair, leftEqual]
  · by_cases rightEqual : letter = right
    · subst letter
      by_cases equal : right = left
      · simp [separatePair, equal]
      · simp [separatePair, equal, Ne.symm equal]
    · simp [separatePair, leftEqual, rightEqual]

private theorem getD_map_of_lt (sigma : Nat → Nat) :
    ∀ (w : List Nat) (i : Nat), i < w.length →
      (w.map sigma).getD i 0 = sigma (w.getD i 0)
  | [], i, small => by simp at small
  | _ :: _, 0, _ => rfl
  | _ :: tail, i + 1, small => by
      have tailSmall : i < tail.length := by simpa using small
      simpa using getD_map_of_lt sigma tail i tailSmall

private theorem occTag_map_of_fiber (sigma : Nat → Nat)
    (w : List Nat) (i : Nat) (small : i < w.length)
    (fiber : ∀ letter,
      sigma letter = sigma (w.getD i 0) → letter = w.getD i 0) :
    occTag (w.map sigma) i = occTag w i := by
  unfold occTag
  rw [getD_map_of_lt sigma w i small]
  rw [← List.map_take]
  rw [count_map_of_fiber sigma (w.getD i 0) fiber (w.take i)]

private theorem p2_map_of_some (sigma : Nat → Nat)
    {w : List Nat} {letter : Nat} {tag : Bool}
    (source : (invariant w).p2 = some (letter, tag))
    (fiber : ∀ c, sigma c = sigma letter → c = letter) :
    (invariant (w.map sigma)).p2 = some (sigma letter, tag) := by
  have long : 2 ≤ w.length := by
    by_cases candidate : 2 ≤ w.length
    · exact candidate
    · have none : (invariant w).p2 = none := by
        simp [invariant, candidate]
      rw [none] at source
      cases source
  have sourceValue :
      (invariant w).p2 =
        some (w.getD (w.length - 2) 0, occTag w (w.length - 2)) := by
    simp [invariant, long]
  have pairEq :
      (w.getD (w.length - 2) 0, occTag w (w.length - 2)) =
        (letter, tag) :=
    Option.some.inj (sourceValue.symm.trans source)
  have letterEq : w.getD (w.length - 2) 0 = letter :=
    congrArg Prod.fst pairEq
  have tagEq : occTag w (w.length - 2) = tag :=
    congrArg Prod.snd pairEq
  have small : w.length - 2 < w.length := by omega
  have localFiber : ∀ c,
      sigma c = sigma (w.getD (w.length - 2) 0) →
        c = w.getD (w.length - 2) 0 := by
    intro c imageEq
    rw [letterEq] at imageEq
    exact (fiber c imageEq).trans letterEq.symm
  have mappedTag := occTag_map_of_fiber sigma w (w.length - 2)
    small localFiber
  have mappedValue := getD_map_of_lt sigma w (w.length - 2) small
  have targetValue :
      (invariant (w.map sigma)).p2 =
        some ((w.map sigma).getD (w.length - 2) 0,
          occTag (w.map sigma) (w.length - 2)) := by
    simp [invariant, List.length_map, long]
  rw [targetValue]
  apply congrArg some
  apply Prod.ext
  · exact mappedValue.trans (congrArg sigma letterEq)
  · exact mappedTag.trans tagEq

private theorem p2_map_none (sigma : Nat → Nat) {w : List Nat}
    (source : (invariant w).p2 = none) :
    (invariant (w.map sigma)).p2 = none := by
  have short : ¬ 2 ≤ w.length := by
    intro long
    have some : (invariant w).p2 =
        some (w.getD (w.length - 2) 0, occTag w (w.length - 2)) := by
      simp [invariant, long]
    rw [some] at source
    cases source
  simp [invariant, short]

private theorem p2_map_exists (sigma : Nat → Nat) {w : List Nat}
    {pair : Nat × Bool} (source : (invariant w).p2 = some pair) :
    ∃ mappedPair, (invariant (w.map sigma)).p2 = some mappedPair := by
  have long : 2 ≤ w.length := by
    by_cases candidate : 2 ≤ w.length
    · exact candidate
    · have none : (invariant w).p2 = none := by
        simp [invariant, candidate]
      rw [none] at source
      cases source
  exact ⟨((w.map sigma).getD (w.length - 2) 0,
      occTag (w.map sigma) (w.length - 2)), by
    simp [invariant, List.length_map, long]⟩

private theorem p1_map_of_some (sigma : Nat → Nat)
    {w : List Nat} {letter : Nat} {tag : Bool}
    (source : (invariant w).p1 = some (letter, tag))
    (fiber : ∀ c, sigma c = sigma letter → c = letter) :
    (invariant (w.map sigma)).p1 = some (sigma letter, tag) := by
  have nonempty : 1 ≤ w.length := by
    by_cases candidate : 1 ≤ w.length
    · exact candidate
    · have none : (invariant w).p1 = none := by
        simp [invariant, candidate]
      rw [none] at source
      cases source
  have sourceValue :
      (invariant w).p1 =
        some (w.getD (w.length - 1) 0, occTag w (w.length - 1)) := by
    simp [invariant, nonempty]
  have pairEq :
      (w.getD (w.length - 1) 0, occTag w (w.length - 1)) =
        (letter, tag) :=
    Option.some.inj (sourceValue.symm.trans source)
  have letterEq : w.getD (w.length - 1) 0 = letter :=
    congrArg Prod.fst pairEq
  have tagEq : occTag w (w.length - 1) = tag :=
    congrArg Prod.snd pairEq
  have small : w.length - 1 < w.length := by omega
  have localFiber : ∀ c,
      sigma c = sigma (w.getD (w.length - 1) 0) →
        c = w.getD (w.length - 1) 0 := by
    intro c imageEq
    rw [letterEq] at imageEq
    exact (fiber c imageEq).trans letterEq.symm
  have mappedTag := occTag_map_of_fiber sigma w (w.length - 1)
    small localFiber
  have mappedValue := getD_map_of_lt sigma w (w.length - 1) small
  have targetValue :
      (invariant (w.map sigma)).p1 =
        some ((w.map sigma).getD (w.length - 1) 0,
          occTag (w.map sigma) (w.length - 1)) := by
    simp [invariant, List.length_map, nonempty]
  rw [targetValue]
  apply congrArg some
  apply Prod.ext
  · exact mappedValue.trans (congrArg sigma letterEq)
  · exact mappedTag.trans tagEq

private theorem p1_exists_of_nonempty (w : List Nat) (hw : w ≠ []) :
    ∃ pair, (invariant w).p1 = some pair := by
  have nonempty : 1 ≤ w.length := by
    simpa [Nat.one_le_iff_ne_zero, List.length_eq_zero_iff] using hw
  exact ⟨(w.getD (w.length - 1) 0, occTag w (w.length - 1)), by
    simp [invariant, nonempty]⟩

/-- Bounded merge-collapse (tuple-invariant instance of the proved G4
theorem, msg-0061/0063): an invariant disagreement survives a renaming
with image of size ≤ 4 — profile-diff keeps one letter (image 2), a
boundary letter/tag diff keeps the ≤ 2 boundary letters and the last
letter (image ≤ 4); the L2 blob core preserves kept projections. -/
theorem mergeCollapse {u v : List Nat}
    (hu : u ≠ []) (hv : v ≠ [])
    (h : invariant u ≠ invariant v) :
    ∃ σ : Nat → Nat, ∃ img : List Nat, img.length ≤ 4 ∧
      (∀ c ∈ u ++ v, σ c ∈ img) ∧
      invariant (u.map σ) ≠ invariant (v.map σ) := by
  classical
  by_cases profileEq : (invariant u).profile = (invariant v).profile
  · by_cases p2Eq : (invariant u).p2 = (invariant v).p2
    · have p1Ne : (invariant u).p1 ≠ (invariant v).p1 := by
        intro p1Eq
        apply h
        cases leftEq : invariant u
        cases rightEq : invariant v
        simp_all
      obtain ⟨leftPair, leftP1⟩ := p1_exists_of_nonempty u hu
      obtain ⟨rightPair, rightP1⟩ := p1_exists_of_nonempty v hv
      rcases leftPair with ⟨left, leftTag⟩
      rcases rightPair with ⟨right, rightTag⟩
      have pairNe : (left, leftTag) ≠ (right, rightTag) := by
        intro pairEq
        exact p1Ne (leftP1.trans (pairEq ▸ rightP1.symm))
      let sigma := separatePair left right
      have mappedLeft := p1_map_of_some sigma leftP1
        (separatePair_fiber_left left right)
      have mappedRight := p1_map_of_some sigma rightP1
        (separatePair_fiber_right left right)
      have mappedPairNe :
          (sigma left, leftTag) ≠ (sigma right, rightTag) := by
        by_cases letterEq : left = right
        · subst right
          simpa using pairNe
        · simp [sigma, separatePair, letterEq, Ne.symm letterEq]
      refine ⟨sigma, [0, 1, 2], by simp, ?_, ?_⟩
      · intro c _
        exact separatePair_image left right c
      · intro mappedEq
        apply mappedPairNe
        exact Option.some.inj <| mappedLeft.symm.trans <|
          (congrArg G3Inv.p1 mappedEq).trans mappedRight
    · cases leftP2 : (invariant u).p2 with
      | none =>
          cases rightP2 : (invariant v).p2 with
          | none =>
              exact False.elim (p2Eq (leftP2.trans rightP2.symm))
          | some rightPair =>
              let sigma : Nat → Nat := fun _ => 0
              obtain ⟨mappedRight, mappedRightP2⟩ :=
                p2_map_exists sigma rightP2
              have mappedLeftP2 := p2_map_none sigma leftP2
              refine ⟨sigma, [0], by simp, ?_, ?_⟩
              · intro c _
                simp [sigma]
              · intro mappedEq
                have fieldEq := congrArg G3Inv.p2 mappedEq
                rw [mappedLeftP2, mappedRightP2] at fieldEq
                cases fieldEq
      | some leftPair =>
          cases rightP2 : (invariant v).p2 with
          | none =>
              let sigma : Nat → Nat := fun _ => 0
              obtain ⟨mappedLeft, mappedLeftP2⟩ :=
                p2_map_exists sigma leftP2
              have mappedRightP2 := p2_map_none sigma rightP2
              refine ⟨sigma, [0], by simp, ?_, ?_⟩
              · intro c _
                simp [sigma]
              · intro mappedEq
                have fieldEq := congrArg G3Inv.p2 mappedEq
                rw [mappedLeftP2, mappedRightP2] at fieldEq
                cases fieldEq
          | some rightPair =>
              rcases leftPair with ⟨left, leftTag⟩
              rcases rightPair with ⟨right, rightTag⟩
              have pairNe : (left, leftTag) ≠ (right, rightTag) := by
                intro pairEq
                exact p2Eq (leftP2.trans (pairEq ▸ rightP2.symm))
              let sigma := separatePair left right
              have mappedLeft := p2_map_of_some sigma leftP2
                (separatePair_fiber_left left right)
              have mappedRight := p2_map_of_some sigma rightP2
                (separatePair_fiber_right left right)
              have mappedPairNe :
                  (sigma left, leftTag) ≠ (sigma right, rightTag) := by
                by_cases letterEq : left = right
                · subst right
                  simpa using pairNe
                · simp [sigma, separatePair, letterEq, Ne.symm letterEq]
              refine ⟨sigma, [0, 1, 2], by simp, ?_, ?_⟩
              · intro c _
                exact separatePair_image left right c
              · intro mappedEq
                apply mappedPairNe
                exact Option.some.inj <| mappedLeft.symm.trans <|
                  (congrArg G3Inv.p2 mappedEq).trans mappedRight
  · by_cases supportEq : ∀ c, c ∈ u ↔ c ∈ v
    · have flagWitness : ∃ c, c ∈ u ∧
          decide (u.count c = 2) ≠ decide (v.count c = 2) := by
        apply Classical.byContradiction
        intro noWitness
        apply profileEq
        apply profile_eq_of_support_flags supportEq
        intro c hc
        apply Classical.byContradiction
        intro different
        exact noWitness ⟨c, hc, different⟩
      rcases flagWitness with ⟨chosen, chosenU, flagNe⟩
      have chosenV : chosen ∈ v := (supportEq chosen).mp chosenU
      let sigma := collapseAt chosen
      have fiber : ∀ c, sigma c = sigma chosen → c = chosen := by
        intro c imageEq
        exact collapseAt_fiber chosen c imageEq
      have countU := count_map_of_fiber sigma chosen fiber u
      have countV := count_map_of_fiber sigma chosen fiber v
      refine ⟨sigma, [0, 1], by simp, ?_, ?_⟩
      · intro c _
        exact collapseAt_image chosen c
      · intro mappedEq
        have mappedProfileEq := congrArg G3Inv.profile mappedEq
        have chosenMappedU : sigma chosen ∈ u.map sigma :=
          List.mem_map.mpr ⟨chosen, chosenU, rfl⟩
        have leftPair :
            (sigma chosen,
              decide ((u.map sigma).count (sigma chosen) = 2)) ∈
                profile (u.map sigma) :=
          (profile_pair_mem _ _ _).mpr ⟨chosenMappedU, rfl⟩
        have rightPair :
            (sigma chosen,
              decide ((u.map sigma).count (sigma chosen) = 2)) ∈
                profile (v.map sigma) := by
          change (sigma chosen,
              decide ((u.map sigma).count (sigma chosen) = 2)) ∈
            (invariant (v.map sigma)).profile
          rw [← mappedProfileEq]
          exact leftPair
        have rightFlag := (profile_pair_mem _ _ _).mp rightPair |>.2
        apply flagNe
        rw [← countU, ← countV]
        exact rightFlag
    · have supportWitness : ∃ c, ¬ (c ∈ u ↔ c ∈ v) :=
        Classical.not_forall.mp supportEq
      rcases supportWitness with ⟨chosen, chosenDiff⟩
      by_cases chosenU : chosen ∈ u
      · have chosenV : chosen ∉ v := by
          intro member
          exact chosenDiff ⟨fun _ => member, fun _ => chosenU⟩
        let sigma := collapseAt chosen
        refine ⟨sigma, [0, 1], by simp, ?_, ?_⟩
        · intro c _
          exact collapseAt_image chosen c
        · intro mappedEq
          have mappedProfileEq := congrArg G3Inv.profile mappedEq
          have imagePresent :
              sigma chosen ∈ (profile (u.map sigma)).map Prod.fst :=
            (profile_first_mem _ _).mpr <|
              List.mem_map.mpr ⟨chosen, chosenU, rfl⟩
          have imageAbsent :
              sigma chosen ∉ (profile (v.map sigma)).map Prod.fst := by
            intro member
            have wordMember := (profile_first_mem _ _).mp member
            rcases List.mem_map.mp wordMember with ⟨source, sourceV, imageEq⟩
            exact chosenV <| (collapseAt_fiber chosen source imageEq) ▸ sourceV
          apply imageAbsent
          change sigma chosen ∈
            ((invariant (v.map sigma)).profile).map Prod.fst
          rw [← mappedProfileEq]
          exact imagePresent
      · have chosenV : chosen ∈ v := by
          by_cases member : chosen ∈ v
          · exact member
          · exact False.elim <| chosenDiff
              ⟨fun present => False.elim (chosenU present),
                fun present => False.elim (member present)⟩
        let sigma := collapseAt chosen
        refine ⟨sigma, [0, 1], by simp, ?_, ?_⟩
        · intro c _
          exact collapseAt_image chosen c
        · intro mappedEq
          have mappedProfileEq := congrArg G3Inv.profile mappedEq
          have imagePresent :
              sigma chosen ∈ (profile (v.map sigma)).map Prod.fst :=
            (profile_first_mem _ _).mpr <|
              List.mem_map.mpr ⟨chosen, chosenV, rfl⟩
          have imageAbsent :
              sigma chosen ∉ (profile (u.map sigma)).map Prod.fst := by
            intro member
            have wordMember := (profile_first_mem _ _).mp member
            rcases List.mem_map.mp wordMember with ⟨source, sourceU, imageEq⟩
            exact chosenU <| (collapseAt_fiber chosen source imageEq) ▸ sourceU
          apply imageAbsent
          change sigma chosen ∈
            ((invariant (u.map sigma)).profile).map Prod.fst
          rw [mappedProfileEq]
          exact imagePresent

/-- The generic endpoint, mirroring the compiled
`basisFor_of_models_invariantSeparation` of the G2 module. -/
theorem basisFor_of_models_invariantSeparation
    {G : Semigroup S}
    (models : Models G basis)
    (witness : G3NormalizationWitness)
    (separates : InvariantSeparation G) :
    BasisFor G basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  let lhsReduced := witness.countReduce identity.lhs.toList
  let rhsReduced := witness.countReduce identity.rhs.toList
  have lhsNonempty : identity.lhs.toList ≠ [] := by
    simp [Word.toList]
  have rhsNonempty : identity.rhs.toList ≠ [] := by
    simp [Word.toList]
  have lhsReducedNonempty : lhsReduced ≠ [] := by
    exact witness.reduce_nonempty identity.lhs.toList lhsNonempty
  have rhsReducedNonempty : rhsReduced ≠ [] := by
    exact witness.reduce_nonempty identity.rhs.toList rhsNonempty
  have lhsReduction := witness.reduce_derives identity.lhs.toList lhsNonempty
  have rhsReduction := witness.reduce_derives identity.rhs.toList rhsNonempty
  have reducedValid :
      ({ lhs := SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD lhsReduced
         rhs := SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD rhsReduced } :
          Identity Nat).SatisfiedBy G := by
    intro valuation
    exact (lhsReduction.sound models valuation).symm.trans <|
      (valid valuation).trans (rhsReduction.sound models valuation)
  have sameInvariant := separates
    lhsReducedNonempty rhsReducedNonempty
    (witness.reduce_reduced identity.lhs.toList)
    (witness.reduce_reduced identity.rhs.toList)
    reducedValid
  have sameNormal :
      normalForm lhsReduced = normalForm rhsReduced :=
    congrArg canonical sameInvariant
  have lhsDerives :
      Derives basis identity.lhs
        (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD
          (normalForm lhsReduced)) := by
    simpa [SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD, Word.toList] using
      witness.derives_normalForm identity.lhs.toList lhsNonempty
  have rhsDerives :
      Derives basis identity.rhs
        (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD
          (normalForm rhsReduced)) := by
    simpa [SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD, Word.toList] using
      witness.derives_normalForm identity.rhs.toList rhsNonempty
  exact lhsDerives.trans <| by
    rw [sameNormal]
    exact rhsDerives.symm

/-! ## Concrete normalization witness

The first stage reuses the G4 `BlobStep` relation, but interprets every step
in the G3 basis.  The only difference is the hop: G3 obtains it by
specializing interior commutation with the third factor equal to the blob
letter. -/

private theorem derivesInListContextG3 {u v : Word Nat}
    (derivation : Derives basis u v) (pre suf : List Nat) :
    Derives basis
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD
        (pre ++ u.toList ++ suf))
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD
        (pre ++ v.toList ++ suf)) := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases pre with
          | nil =>
              cases suf with
              | nil =>
                  simpa [SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD,
                    Word.toList] using derivation
              | cons suffixHead suffixTail =>
                  have suffixed := Derives.appendRight derivation
                    (Word.mk suffixHead suffixTail)
                  simpa [SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD,
                    Word.toList, Word.append, List.append_assoc] using suffixed
          | cons prefixHead prefixTail =>
              cases suf with
              | nil =>
                  have prefixed :=
                    Derives.prepend (Word.mk prefixHead prefixTail) derivation
                  simpa [SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD,
                    Word.toList, Word.append, List.append_assoc] using prefixed
              | cons suffixHead suffixTail =>
                  have surrounded :=
                    Derives.prepend (Word.mk prefixHead prefixTail)
                      (Derives.appendRight derivation
                        (Word.mk suffixHead suffixTail))
                  simpa [SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD,
                    Word.toList, Word.append, List.append_assoc] using surrounded

private theorem blobStep_derives {z : Nat} {w w' : List Nat}
    (step : BlobStep z w w') :
    Derives basis
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD w)
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD w') := by
  cases step with
  | hop p B s hB hs hzB =>
      cases B with
      | nil => exact False.elim (hB rfl)
      | cons b Btail =>
          cases s with
          | nil => exact False.elim (hs rfl)
          | cons sHead sTail =>
              have stepDerivation := derivesInteriorSwap
                (Word.singleton z) (Word.mk b Btail)
                (Word.singleton z) (Word.mk sHead sTail)
              have contextual := derivesInListContextG3 stepDerivation p []
              simpa [SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD,
                Word.toList, Word.append, Word.singleton,
                List.append_assoc] using contextual
  | contract p B s hB hzB =>
      cases B with
      | nil => exact False.elim (hB rfl)
      | cons b Btail =>
          have stepDerivation :=
            (derivesHeadDup (Word.singleton z) (Word.mk b Btail)).symm
          have contextual := derivesInListContextG3 stepDerivation p s
          simpa [SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD,
            Word.toList, Word.append, Word.singleton,
            List.append_assoc] using contextual
  | cap p s =>
      have stepDerivation := (derivesCap (Word.singleton z)).symm
      have contextual := derivesInListContextG3 stepDerivation p s
      simpa [SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD,
        Word.toList, Word.append, Word.singleton,
        List.append_assoc] using contextual

private theorem blobReduces_derives {z : Nat} {w w' : List Nat}
    (reduction : BlobReduces z w w') :
    Derives basis
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD w)
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD w') := by
  induction reduction with
  | refl current =>
      exact Derives.refl
        (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD current)
  | step first tail ih => exact (blobStep_derives first).trans ih

private theorem blobStep_target_nonempty {z : Nat} {w w' : List Nat}
    (step : BlobStep z w w') : w' ≠ [] := by
  cases step <;> simp

private theorem blobReduces_nonempty {z : Nat} {w w' : List Nat}
    (reduction : BlobReduces z w w') (sourceNonempty : w ≠ []) :
    w' ≠ [] := by
  induction reduction with
  | refl current => exact sourceNonempty
  | step first tail ih => exact ih (blobStep_target_nonempty first)

private theorem splitFirstOccurrence (c : Nat) :
    ∀ {w : List Nat}, c ∈ w →
      ∃ p s, c ∉ p ∧ w = p ++ c :: s
  | [], member => by simp at member
  | x :: xs, member => by
      by_cases hxc : x = c
      · subst x
        exact ⟨[], xs, by simp, by simp⟩
      · have tailMember : c ∈ xs := by
          simpa [Ne.symm hxc] using member
        obtain ⟨p, s, hp, shape⟩ := splitFirstOccurrence c tailMember
        exact ⟨x :: p, s, by simp [Ne.symm hxc, hp], by simp [shape]⟩

private theorem splitFirstThreeOccurrences (c : Nat) {w : List Nat}
    (count : 3 ≤ w.count c) :
    ∃ p U V s,
      c ∉ p ∧ c ∉ U ∧ c ∉ V ∧
        w = p ++ c :: (U ++ c :: (V ++ c :: s)) := by
  have firstMember : c ∈ w := List.count_pos_iff.mp (by omega)
  obtain ⟨p, firstTail, hp, firstShape⟩ :=
    splitFirstOccurrence c firstMember
  have hpCount : p.count c = 0 := List.count_eq_zero.mpr hp
  have firstTailCount : 2 ≤ firstTail.count c := by
    rw [firstShape, List.count_append, hpCount,
      List.count_cons_self] at count
    omega
  have secondMember : c ∈ firstTail := List.count_pos_iff.mp (by omega)
  obtain ⟨U, secondTail, hU, secondShape⟩ :=
    splitFirstOccurrence c secondMember
  have hUCount : U.count c = 0 := List.count_eq_zero.mpr hU
  have secondTailCount : 1 ≤ secondTail.count c := by
    rw [secondShape, List.count_append, hUCount,
      List.count_cons_self] at firstTailCount
    omega
  have thirdMember : c ∈ secondTail := List.count_pos_iff.mp (by omega)
  obtain ⟨V, s, hV, thirdShape⟩ :=
    splitFirstOccurrence c thirdMember
  refine ⟨p, U, V, s, hp, hU, hV, ?_⟩
  rw [firstShape, secondShape, thirdShape]

private theorem deleteFirstOfThree
    (p U V s : List Nat) (c : Nat) (hcU : c ∉ U) (hcV : c ∉ V) :
    BlobReduces c
      (p ++ c :: (U ++ c :: (V ++ c :: s)))
      (p ++ U ++ c :: (V ++ c :: s)) := by
  cases U with
  | nil =>
      cases V with
      | nil =>
          exact BlobReduces.step (by
            simpa [List.append_assoc] using BlobStep.cap p s)
            (BlobReduces.refl _)
      | cons v vs =>
          have hV : v :: vs ≠ [] := by simp
          exact BlobReduces.step (by
            simpa [List.append_assoc] using
              BlobStep.contract p (v :: vs) s hV hcV)
            (BlobReduces.refl _)
  | cons u us =>
      have hU : u :: us ≠ [] := by simp
      have hSuffix : V ++ c :: s ≠ [] := by simp
      refine BlobReduces.step (by
        simpa [List.append_assoc] using
          BlobStep.hop p (u :: us) (V ++ c :: s) hU hSuffix hcU) ?_
      cases V with
      | nil =>
          exact BlobReduces.step (by
            simpa [List.append_assoc] using BlobStep.cap (p ++ u :: us) s)
            (BlobReduces.refl _)
      | cons v vs =>
          have hV : v :: vs ≠ [] := by simp
          exact BlobReduces.step (by
            simpa [List.append_assoc] using
              BlobStep.contract (p ++ u :: us) (v :: vs) s hV hcV)
            (BlobReduces.refl _)

private theorem reduceOneOverCap {w : List Nat} {c : Nat}
    (count : 3 ≤ w.count c) :
    ∃ w', BlobReduces c w w' ∧ w'.length < w.length := by
  obtain ⟨p, U, V, s, hp, hU, hV, shape⟩ :=
    splitFirstThreeOccurrences c count
  let w' := p ++ U ++ c :: (V ++ c :: s)
  refine ⟨w', ?_, ?_⟩
  · rw [shape]
    exact deleteFirstOfThree p U V s c hU hV
  · rw [shape]
    simp [w', List.append_assoc]

private theorem existsReducedDerivation :
    ∀ w : List Nat,
      ∃ r,
        Reduced r ∧
        (w ≠ [] → r ≠ []) ∧
        Derives basis
          (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD w)
          (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD r)
  | w => by
      classical
      by_cases reduced : Reduced w
      · exact ⟨w, reduced, fun nonempty => nonempty,
          Derives.refl
            (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD w)⟩
      · rw [Reduced] at reduced
        have existsOverCap : ∃ c, ¬w.count c ≤ 2 := by
          apply Classical.byContradiction
          intro none
          apply reduced
          intro c
          apply Classical.byContradiction
          intro overCap
          exact none ⟨c, overCap⟩
        obtain ⟨c, overCap⟩ := existsOverCap
        have count : 3 ≤ w.count c := by omega
        obtain ⟨w', reduction, shorter⟩ := reduceOneOverCap count
        obtain ⟨r, rReduced, rNonempty, tail⟩ :=
          existsReducedDerivation w'
        exact ⟨r, rReduced,
          fun sourceNonempty =>
            rNonempty (blobReduces_nonempty reduction sourceNonempty),
          (blobReduces_derives reduction).trans tail⟩
termination_by w => w.length
decreasing_by exact shorter

noncomputable def countReduce (w : List Nat) : List Nat :=
  Classical.choose (existsReducedDerivation w)

private theorem countReduce_reduced (w : List Nat) :
    Reduced (countReduce w) :=
  (Classical.choose_spec (existsReducedDerivation w)).1

private theorem countReduce_nonempty (w : List Nat) (nonempty : w ≠ []) :
    countReduce w ≠ [] :=
  (Classical.choose_spec (existsReducedDerivation w)).2.1 nonempty

private theorem countReduce_derives (w : List Nat) :
    Derives basis
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD w)
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD (countReduce w)) :=
  (Classical.choose_spec (existsReducedDerivation w)).2.2

/-! The second stage follows the G2 interior-permutation motif.  Its concrete
implementation and the final witness are below. -/

private def renderInterior (stem : List Nat) (p2 p1 : Nat) : Word Nat :=
  match stem with
  | [] => ⟨p2, [p1]⟩
  | head :: tail => ⟨head, tail ++ [p2, p1]⟩

private theorem renderInterior_toList (stem : List Nat) (p2 p1 : Nat) :
    (renderInterior stem p2 p1).toList = stem ++ [p2, p1] := by
  cases stem <;> simp [renderInterior, Word.toList]

private theorem wordOfD_renderInterior (stem : List Nat) (p2 p1 : Nat) :
    SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD
        (stem ++ [p2, p1]) =
      renderInterior stem p2 p1 := by
  cases stem <;> rfl

private def wordOfInterior : List Nat → Nat → Word Nat
  | [], fallback => Word.singleton fallback
  | head :: tail, _ => ⟨head, tail⟩

private theorem singleton_append_renderInterior (head : Nat)
    (stem : List Nat) (p2 p1 : Nat) :
    Word.singleton head ++ renderInterior stem p2 p1 =
      renderInterior (head :: stem) p2 p1 := by
  apply Word.toList_injective
  simp only [Word.toList_append, Word.toList_singleton,
    renderInterior_toList]
  rfl

private theorem wordOfInterior_append_singleton_toList
    (letters : List Nat) (last : Nat) :
    (wordOfInterior (letters ++ [last]) last).toList =
      letters ++ [last] := by
  cases letters <;> simp [wordOfInterior, Word.toList]

/-- The G2 `derivesRenderPerm` motif, interpreted in the G3 basis.  The two
fixed terminal letters supply the nonempty factors required by every adjacent
swap. -/
private theorem derivesRenderPerm {stem stem' : List Nat}
    (permutation : stem.Perm stem') (p2 p1 : Nat) :
    Derives basis
      (renderInterior stem p2 p1)
      (renderInterior stem' p2 p1) := by
  induction permutation with
  | nil => exact Derives.refl _
  | cons head _ ih =>
      simpa only [singleton_append_renderInterior] using
        Derives.prepend (Word.singleton head) ih
  | swap a b rest =>
      have step := derivesInteriorSwap
        (Word.singleton b) (Word.singleton a)
        (wordOfInterior (rest ++ [p2]) p2) (Word.singleton p1)
      have sourceEq :
          (((Word.singleton b ++ Word.singleton a) ++
              wordOfInterior (rest ++ [p2]) p2) ++ Word.singleton p1) =
            renderInterior (b :: a :: rest) p2 p1 := by
        apply Word.toList_injective
        simp only [Word.toList_append, Word.toList_singleton,
          wordOfInterior_append_singleton_toList, renderInterior_toList]
        simp [List.append_assoc]
      have targetEq :
          (((Word.singleton a ++ Word.singleton b) ++
              wordOfInterior (rest ++ [p2]) p2) ++ Word.singleton p1) =
            renderInterior (a :: b :: rest) p2 p1 := by
        apply Word.toList_injective
        simp only [Word.toList_append, Word.toList_singleton,
          wordOfInterior_append_singleton_toList, renderInterior_toList]
        simp [List.append_assoc]
      simpa only [sourceEq, targetEq] using step
  | trans _ _ first second => exact first.trans second

private def splitLastTwo (letters : List Nat) :
    Option (List Nat × Nat × Nat) :=
  match letters.reverse with
  | p1 :: p2 :: reversedStem => some (reversedStem.reverse, p2, p1)
  | _ => none

private theorem splitLastTwo_render {letters stem : List Nat} {p2 p1 : Nat}
    (split : splitLastTwo letters = some (stem, p2, p1)) :
    letters = stem ++ [p2, p1] := by
  unfold splitLastTwo at split
  generalize reversedEq : letters.reverse = reversed at split
  cases reversed with
  | nil => simp at split
  | cons last rest =>
      cases rest with
      | nil => simp at split
      | cons penult reversedStem =>
          simp only [Option.some.injEq, Prod.mk.injEq] at split
          rcases split with ⟨stemEq, p2Eq, p1Eq⟩
          subst stem
          subst p2
          subst p1
          have restored := congrArg List.reverse reversedEq
          simpa [List.reverse_cons, List.append_assoc] using restored

private theorem count_replicate_of_ne {x z : Nat} (hzx : z ≠ x) :
    ∀ n : Nat, (List.replicate n x).count z = 0
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm hzx),
        count_replicate_of_ne hzx n]

private theorem count_flatMap_replicate_of_nodup
    (amount : Nat → Nat) (tested : Nat) :
    ∀ {support : List Nat}, support.Nodup →
      (support.flatMap (fun letter =>
        List.replicate (amount letter) letter)).count tested =
        if tested ∈ support then amount tested else 0
  | [], _ => by simp
  | head :: tail, nodup => by
      have headFresh := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      rw [List.flatMap_cons, List.count_append,
        count_flatMap_replicate_of_nodup amount tested tailNodup]
      by_cases testedEq : tested = head
      · subst tested
        simp [List.count_replicate_self, headFresh]
      · rw [count_replicate_of_ne testedEq]
        simp [testedEq]

private theorem interiorList_count (letters : List Nat) (tested : Nat) :
    (interiorList (invariant letters)).count tested =
      if tested ∈ letters then
        interiorMultiplicity (invariant letters) tested
          (decide (letters.count tested = 2))
      else 0 := by
  have blocks := count_flatMap_replicate_of_nodup
    (fun letter => interiorMultiplicity (invariant letters) letter
      (decide (letters.count letter = 2)))
    tested (profileSupport_nodup letters)
  simp only [profileSupport_mem] at blocks
  change
    ((profile letters).flatMap
      (interiorBlock (invariant letters))).count tested = _
  simpa [profile, profileSupport, interiorBlock,
    List.flatMap_map, Function.comp_def] using blocks

private theorem getD_append_pair_left (stem : List Nat) (p2 p1 : Nat) :
    (stem ++ [p2, p1]).getD stem.length 0 = p2 := by
  induction stem with
  | nil => rfl
  | cons head tail ih => simpa using ih

private theorem getD_append_pair_right (stem : List Nat) (p2 p1 : Nat) :
    (stem ++ [p2, p1]).getD (stem.length + 1) 0 = p1 := by
  induction stem with
  | nil => rfl
  | cons head tail ih => simpa [Nat.add_assoc] using ih

private theorem invariant_p2_render (stem : List Nat) (p2 p1 : Nat) :
    (invariant (stem ++ [p2, p1])).p2 =
      some (p2, occTag (stem ++ [p2, p1]) stem.length) := by
  have long : 2 ≤ (stem ++ [p2, p1]).length := by simp
  have index : (stem ++ [p2, p1]).length - 2 = stem.length := by
    simp
  change
    (if h : 2 ≤ (stem ++ [p2, p1]).length then
      some ((stem ++ [p2, p1]).getD
        ((stem ++ [p2, p1]).length - 2) 0,
        occTag (stem ++ [p2, p1])
          ((stem ++ [p2, p1]).length - 2))
    else none) = _
  rw [dif_pos long, index, getD_append_pair_left]

private theorem invariant_p1_render (stem : List Nat) (p2 p1 : Nat) :
    (invariant (stem ++ [p2, p1])).p1 =
      some (p1, occTag (stem ++ [p2, p1]) (stem.length + 1)) := by
  have nonempty : 1 ≤ (stem ++ [p2, p1]).length := by simp
  have index : (stem ++ [p2, p1]).length - 1 = stem.length + 1 := by
    simp
  change
    (if h : 1 ≤ (stem ++ [p2, p1]).length then
      some ((stem ++ [p2, p1]).getD
        ((stem ++ [p2, p1]).length - 1) 0,
        occTag (stem ++ [p2, p1])
          ((stem ++ [p2, p1]).length - 1))
    else none) = _
  rw [dif_pos nonempty, index, getD_append_pair_right]

private theorem normalForm_render (stem : List Nat) (p2 p1 : Nat) :
    normalForm (stem ++ [p2, p1]) =
      interiorList (invariant (stem ++ [p2, p1])) ++ [p2, p1] := by
  unfold normalForm canonical
  rw [invariant_p2_render, invariant_p1_render]

private theorem interiorMultiplicity_render_of_mem
    (stem : List Nat) (p2 p1 tested : Nat)
    (reduced : Reduced (stem ++ [p2, p1]))
    (member : tested ∈ stem ++ [p2, p1]) :
    interiorMultiplicity (invariant (stem ++ [p2, p1])) tested
        (decide ((stem ++ [p2, p1]).count tested = 2)) =
      stem.count tested := by
  have atMostTwo := reduced tested
  have positive : 0 < (stem ++ [p2, p1]).count tested :=
    List.count_pos_iff.mpr member
  have totalEq :
      (if decide ((stem ++ [p2, p1]).count tested = 2) then 2 else 1) =
        (stem ++ [p2, p1]).count tested := by
    by_cases countTwo : (stem ++ [p2, p1]).count tested = 2
    · simp [countTwo]
    · have countOne : (stem ++ [p2, p1]).count tested = 1 := by omega
      simp [countTwo, countOne]
  have p2Field :
      (invariant (stem ++ [p2, p1])).p2.map Prod.fst = some p2 := by
    rw [invariant_p2_render]
    rfl
  have p1Field :
      (invariant (stem ++ [p2, p1])).p1.map Prod.fst = some p1 := by
    rw [invariant_p1_render]
    rfl
  unfold interiorMultiplicity
  rw [totalEq, p2Field, p1Field]
  by_cases p2Eq : p2 = tested <;>
    by_cases p1Eq : p1 = tested <;>
      simp [p2Eq, p1Eq, List.count_append] at atMostTwo positive ⊢ <;>
      omega

private theorem interiorList_render_count
    (stem : List Nat) (p2 p1 tested : Nat)
    (reduced : Reduced (stem ++ [p2, p1])) :
    (interiorList (invariant (stem ++ [p2, p1]))).count tested =
      stem.count tested := by
  rw [interiorList_count]
  by_cases member : tested ∈ stem ++ [p2, p1]
  · rw [if_pos member]
    exact interiorMultiplicity_render_of_mem stem p2 p1 tested reduced member
  · rw [if_neg member]
    have notStem : tested ∉ stem := by
      intro stemMember
      exact member (by simp [stemMember])
    exact (List.count_eq_zero.mpr notStem).symm

private theorem interiorList_render_perm
    (stem : List Nat) (p2 p1 : Nat)
    (reduced : Reduced (stem ++ [p2, p1])) :
    stem.Perm (interiorList (invariant (stem ++ [p2, p1]))) := by
  apply List.perm_iff_count.mpr
  intro tested
  exact (interiorList_render_count stem p2 p1 tested reduced).symm

private theorem normalForm_nil : normalForm [] = [] := by
  rfl

private theorem normalForm_singleton (letter : Nat) :
    normalForm [letter] = [letter] := by
  simp [normalForm, canonical, invariant, interiorList, interiorBlock,
    interiorMultiplicity, profile,
    SemigroupBasis.CoRoots.Order6LeeLiP2G2.deduplicateSupport, occTag]

/-- On a reduced word the canonical map changes only the interior order, so
the G3 commutation law derives it directly. -/
private theorem derives_normalForm_of_reduced (letters : List Nat)
    (nonempty : letters ≠ []) (reduced : Reduced letters) :
    Derives basis
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD letters)
      (SemigroupBasis.CoRoots.Order6LeeLiP2G4.wordOfD
        (normalForm letters)) := by
  cases split : splitLastTwo letters with
  | none =>
      unfold splitLastTwo at split
      generalize reversedEq : letters.reverse = reversed at split
      cases reversed with
      | nil =>
          have restored := congrArg List.reverse reversedEq
          have empty : letters = [] := by simpa using restored
          exact False.elim (nonempty empty)
      | cons last rest =>
          cases rest with
          | nil =>
              have restored := congrArg List.reverse reversedEq
              have singleton : letters = [last] := by
                simpa [List.reverse_cons] using restored
              rw [singleton, normalForm_singleton]
              exact Derives.refl _
          | cons penult reversedStem => simp at split
  | some triple =>
      obtain ⟨stem, p2, p1⟩ := triple
      have shape := splitLastTwo_render split
      have reducedRendered : Reduced (stem ++ [p2, p1]) := by
        simpa [shape] using reduced
      have permutation :=
        interiorList_render_perm stem p2 p1 reducedRendered
      rw [shape, normalForm_render]
      simpa only [wordOfD_renderInterior] using
        derivesRenderPerm permutation p2 p1

def sortInterior (letters : List Nat) : List Nat := normalForm letters

/-- Concrete two-stage G3 normalizer.  `countReduce` is chosen from the
well-founded reduction above; `sortInterior` is the invariant renderer, proved
to be an interior permutation on every reduced output. -/
noncomputable def normalizationWitness : G3NormalizationWitness where
  countReduce := countReduce
  sortInterior := sortInterior
  reduce_reduced := countReduce_reduced
  reduce_nonempty := countReduce_nonempty
  reduce_derives := by
    intro letters _
    exact countReduce_derives letters
  sort_derives := by
    intro letters nonempty
    exact derives_normalForm_of_reduced (countReduce letters)
      (countReduce_nonempty letters nonempty)
      (countReduce_reduced letters)
  sort_eq_normalForm := by
    intro letters
    rfl

end SemigroupBasis.CoRoots.Order6LeeLiP2G3
