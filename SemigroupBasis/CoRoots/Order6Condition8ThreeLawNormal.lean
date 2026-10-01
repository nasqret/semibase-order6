import SemigroupBasis.Generated.CatalogueOrder2
import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Generated.CatalogueOrder5Part08
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Subdirect

/-!
# Shared three-law normalizer for the Condition-8 six-root lane

The msg-0288 candidate `{xy = xyyy, xyxx = xy, xyzt = xytz}` is an exact
basis for the joint identity theory of `S3_11 × S4_77` AND of
`S2_2 × S5_904` — the two joint theories are the same word partition, so
one normalizer serves all six roots of the msg-0294 tail.

Exact class descriptor (screen-verified at 2L<=8 / 3L<=7 / 4L<=6 on both
factor pairs, 22/129/536 classes): head letter, second letter, whole-word
support, and per-letter count parity.

Completeness architecture: the zone beyond the two-letter prefix is
commutative (`xyzt = xytz` block instances); `xy = xyyy` appends pairs of
the trailing letter; one backwards `xyxx = xy` application appends a copy
of the two-letter prefix INTO the commuting zone, after which every
support letter admits independent even count increments; both sides then
derive to extensions with identical letter counts, and the commuting zone
closes the resulting permutation.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Condition8ThreeLaw

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-! ## The displayed three-law system -/

def growLaw : Identity Nat := ⟨w 0 [1], w 0 [1, 1, 1]⟩
def cancelLaw : Identity Nat := ⟨w 0 [1, 0, 0], w 0 [1]⟩
def swapLaw : Identity Nat := ⟨w 0 [1, 2, 3], w 0 [1, 3, 2]⟩

def sigma : List (Identity Nat) := [growLaw, cancelLaw, swapLaw]

private theorem growMem : growLaw ∈ sigma := by simp [sigma]
private theorem cancelMem : cancelLaw ∈ sigma := by simp [sigma]
private theorem swapMem : swapLaw ∈ sigma := by simp [sigma]

private def instantiateFour (a b c d : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | n + 4 => Word.singleton (n + 4)

/-! ## Block instances -/

/-- `UV = UVVV` (law 1). -/
theorem derivesGrow (u v : Word Nat) :
    Derives sigma (u ++ v) (((u ++ v) ++ v) ++ v) := by
  have base : Derives sigma growLaw.lhs growLaw.rhs :=
    Derives.fromBasis growMem
  have substituted := Derives.subst base (instantiateFour u v v v)
  simpa [growLaw, w, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `UVUU = UV` (law 2). -/
theorem derivesCancel (u v : Word Nat) :
    Derives sigma (((u ++ v) ++ u) ++ u) (u ++ v) := by
  have base : Derives sigma cancelLaw.lhs cancelLaw.rhs :=
    Derives.fromBasis cancelMem
  have substituted := Derives.subst base (instantiateFour u v v v)
  simpa [cancelLaw, w, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `UVXY = UVYX` (law 3): blocks commute behind any two-block prefix. -/
theorem derivesSwapBlocks (u v x y : Word Nat) :
    Derives sigma (((u ++ v) ++ x) ++ y) (((u ++ v) ++ y) ++ x) := by
  have base : Derives sigma swapLaw.lhs swapLaw.rhs :=
    Derives.fromBasis swapMem
  have substituted := Derives.subst base (instantiateFour u v x y)
  simpa [swapLaw, w, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-! ## Extension layer (compiled S6_5680 pattern; `rfl` where definitional) -/

private def extend (p : Word Nat) (xs : List Nat) : Word Nat :=
  ⟨p.head, p.tail ++ xs⟩

private theorem extend_toList (p : Word Nat) (xs : List Nat) :
    (extend p xs).toList = p.toList ++ xs := by
  cases p with
  | mk head tail => simp [extend, Word.toList]

private theorem extend_nil (p : Word Nat) : extend p [] = p := by
  apply Word.toList_injective
  simp [extend_toList]

private theorem extend_cons (p : Word Nat) (x : Nat) (xs : List Nat) :
    extend p (x :: xs) = extend (p ++ Word.singleton x) xs := by
  apply Word.toList_injective
  simp [extend_toList, Word.toList_append, Word.toList_singleton]

private theorem extend_word (p : Word Nat) (x : Nat) (xs : List Nat) :
    extend p (x :: xs) = p ++ (⟨x, xs⟩ : Word Nat) := rfl

private theorem extend_pair (p : Word Nat) (a b : Nat) (l : List Nat) :
    extend ((p ++ Word.singleton a) ++ Word.singleton b) l =
      extend p (a :: b :: l) := by
  apply Word.toList_injective
  simp [extend_toList, Word.toList_append, Word.toList_singleton]

private theorem extend_hs (h s : Nat) (t : List Nat) :
    extend (Word.singleton h ++ Word.singleton s) t =
      (⟨h, s :: t⟩ : Word Nat) := rfl

/-- Extending both sides of a derivation by a common letter list. -/
private theorem derivesExtend {u v : Word Nat}
    (derivation : Derives sigma u v) (xs : List Nat) :
    Derives sigma (extend u xs) (extend v xs) := by
  cases xs with
  | nil => simpa [extend_nil] using derivation
  | cons x rest =>
      have appended :=
        Derives.appendRight derivation (⟨x, rest⟩ : Word Nat)
      rw [← extend_word, ← extend_word] at appended
      exact appended

/-- Behind any two-block prefix, appended letter lists derive to every
permutation (law 3 closes adjacent transpositions). -/
theorem derivesTailPerm2 (u v : Word Nat) {t1 t2 : List Nat}
    (permutation : t1.Perm t2) :
    Derives sigma (extend (u ++ v) t1) (extend (u ++ v) t2) := by
  induction permutation generalizing v with
  | nil => exact Derives.refl _
  | cons x _ ih =>
      rw [extend_cons, extend_cons, Word.append_assoc]
      have tailStep := ih (v ++ Word.singleton x)
      simpa only [Word.append_assoc] using tailStep
  | swap x y l =>
      have base := derivesSwapBlocks u v (Word.singleton y) (Word.singleton x)
      have extended := derivesExtend base l
      rw [extend_pair, extend_pair] at extended
      exact extended
  | trans _ _ ihFirst ihSecond =>
      exact (ihFirst v).trans (ihSecond v)

/-- Head-and-second anchored form of the tail permutation lemma. -/
theorem derivesTailPermHS (h s : Nat) {t1 t2 : List Nat}
    (permutation : t1.Perm t2) :
    Derives sigma (⟨h, s :: t1⟩ : Word Nat) (⟨h, s :: t2⟩ : Word Nat) := by
  have derived :=
    derivesTailPerm2 (Word.singleton h) (Word.singleton s) permutation
  rwa [extend_hs, extend_hs] at derived

/-! ## Even count increments -/

private theorem word_snoc (h s : Nat) (t : List Nat) (x : Nat) :
    (⟨h, s :: (t ++ [x])⟩ : Word Nat) =
      (⟨h, s :: t⟩ : Word Nat) ++ Word.singleton x := by
  apply Word.toList_injective
  simp [Word.toList, Word.toList_append, Word.toList_singleton]

/-- Append a pair of the trailing letter (law 1). -/
private theorem derivesEndPair (h s : Nat) (t : List Nat) (x : Nat) :
    Derives sigma
      (⟨h, s :: (t ++ [x])⟩ : Word Nat)
      (⟨h, s :: (t ++ [x, x, x])⟩ : Word Nat) := by
  have grow := derivesGrow (⟨h, s :: t⟩ : Word Nat) (Word.singleton x)
  have leftShape :
      (⟨h, s :: (t ++ [x])⟩ : Word Nat) =
        (⟨h, s :: t⟩ : Word Nat) ++ Word.singleton x :=
    word_snoc h s t x
  have rightShape :
      (⟨h, s :: (t ++ [x, x, x])⟩ : Word Nat) =
        (((⟨h, s :: t⟩ : Word Nat) ++ Word.singleton x) ++
          Word.singleton x) ++ Word.singleton x := by
    apply Word.toList_injective
    simp [Word.toList, Word.toList_append, Word.toList_singleton]
  rw [leftShape, rightShape]
  exact grow

/-- Append one pair of any letter present in the commuting zone. -/
private theorem derivesTailPair (h s : Nat) {t : List Nat} {x : Nat}
    (member : x ∈ t) :
    Derives sigma
      (⟨h, s :: t⟩ : Word Nat)
      (⟨h, s :: (t ++ [x, x])⟩ : Word Nat) := by
  have rotate : t.Perm (t.erase x ++ [x]) := by
    have front : t.Perm (x :: t.erase x) := List.perm_cons_erase member
    have swap : (x :: t.erase x).Perm (t.erase x ++ [x]) := by
      simpa using
        List.perm_append_comm (l₁ := [x]) (l₂ := t.erase x)
    exact front.trans swap
  have toEnd := derivesTailPermHS h s rotate
  have grow := derivesEndPair h s (t.erase x) x
  have positive : 0 < t.count x := List.count_pos_iff.mpr member
  have back : (t.erase x ++ [x, x, x]).Perm (t ++ [x, x]) := by
    rw [List.perm_iff_count]
    intro letter
    by_cases equal : letter = x
    · subst letter
      simp only [List.count_append, List.count_erase_self]
      have three : [x, x, x].count x = 3 := by simp
      have two : [x, x].count x = 2 := by simp
      rw [three, two]
      omega
    · simp only [List.count_append,
        List.count_erase_of_ne equal]
      congr 1
      have reverse : ¬ x = letter := fun same => equal same.symm
      simp [equal, reverse]
  have sortBack := derivesTailPermHS h s back
  exact (toEnd.trans grow).trans sortBack

/-- Append `2 * k` copies of any letter present in the commuting zone. -/
private theorem derivesTailPairs (h s : Nat) (k : Nat) :
    ∀ {t : List Nat} {x : Nat}, x ∈ t →
      Derives sigma
        (⟨h, s :: t⟩ : Word Nat)
        (⟨h, s :: (t ++ List.replicate (2 * k) x)⟩ : Word Nat) := by
  induction k with
  | zero =>
      intro t x _
      simpa using Derives.refl (⟨h, s :: t⟩ : Word Nat)
  | succ n ih =>
      intro t x member
      have first := derivesTailPair h s member
      have rest := ih (t := t ++ [x, x]) (x := x)
        (List.mem_append_right t (by simp))
      have reshaped :
          (t ++ [x, x]) ++ List.replicate (2 * n) x =
            t ++ List.replicate (2 * (n + 1)) x := by
        rw [List.append_assoc]
        congr 1
      rw [reshaped] at rest
      exact first.trans rest

/-- The boost: one backwards `xyxx = xy` appends the two-letter prefix
into the commuting zone. -/
private theorem derivesBoost (h s y : Nat) (rest : List Nat) :
    Derives sigma
      (⟨h, s :: y :: rest⟩ : Word Nat)
      (⟨h, s :: ((y :: rest) ++ [h, s, h, s])⟩ : Word Nat) := by
  have cancel :=
    (derivesCancel (⟨h, [s]⟩ : Word Nat) (⟨y, rest⟩ : Word Nat)).symm
  have leftShape :
      (⟨h, [s]⟩ : Word Nat) ++ (⟨y, rest⟩ : Word Nat) =
        (⟨h, s :: y :: rest⟩ : Word Nat) := by
    apply Word.toList_injective
    simp [Word.toList, Word.toList_append]
  have rightShape :
      (((⟨h, [s]⟩ : Word Nat) ++ (⟨y, rest⟩ : Word Nat)) ++
          (⟨h, [s]⟩ : Word Nat)) ++ (⟨h, [s]⟩ : Word Nat) =
        (⟨h, s :: ((y :: rest) ++ [h, s, h, s])⟩ : Word Nat) := by
    apply Word.toList_injective
    simp [Word.toList, Word.toList_append]
  rw [rightShape, leftShape] at cancel
  exact cancel

/-- Growing the length-two word into the nonempty-zone regime. -/
private theorem derivesGrowShort (h s : Nat) :
    Derives sigma (⟨h, [s]⟩ : Word Nat) (⟨h, [s, s, s]⟩ : Word Nat) := by
  have grow := derivesGrow (Word.singleton h) (Word.singleton s)
  have leftShape :
      Word.singleton h ++ Word.singleton s = (⟨h, [s]⟩ : Word Nat) := by
    apply Word.toList_injective
    simp [Word.toList, Word.toList_append, Word.toList_singleton]
  have rightShape :
      ((Word.singleton h ++ Word.singleton s) ++ Word.singleton s) ++
          Word.singleton s = (⟨h, [s, s, s]⟩ : Word Nat) := by
    apply Word.toList_injective
    simp [Word.toList, Word.toList_append, Word.toList_singleton]
  rw [rightShape, leftShape] at grow
  exact grow

/-! ## Schedules of even increments -/

/-- Append even increments for a whole schedule of letters. -/
private theorem derivesSchedule (h s : Nat) :
    ∀ (schedule : List (Nat × Nat)) (t : List Nat),
      (∀ pair ∈ schedule, pair.1 ∈ t) →
      Derives sigma
        (⟨h, s :: t⟩ : Word Nat)
        (⟨h, s :: (t ++ schedule.flatMap
          (fun pair => List.replicate (2 * pair.2) pair.1))⟩ : Word Nat)
  | [], t, _ => by
      simpa using Derives.refl (⟨h, s :: t⟩ : Word Nat)
  | (x, k) :: rest, t, members => by
      have first := derivesTailPairs h s k
        (t := t) (x := x) (members (x, k) (by simp))
      have restStep := derivesSchedule h s rest
        (t ++ List.replicate (2 * k) x)
        (fun pair member =>
          List.mem_append_left _ (members pair (by simp [member])))
      have reshaped :
          (t ++ List.replicate (2 * k) x) ++ rest.flatMap
              (fun pair => List.replicate (2 * pair.2) pair.1) =
            t ++ ((x, k) :: rest).flatMap
              (fun pair => List.replicate (2 * pair.2) pair.1) := by
        simp [List.flatMap_cons, List.append_assoc]
      rw [reshaped] at restStep
      exact first.trans restStep

/-- Counting inside a deduplicated schedule of replicated pairs. -/
private theorem count_schedule (increments : Nat → Nat) :
    ∀ (letters : List Nat), letters.Nodup → ∀ x,
      (letters.flatMap
        (fun y => List.replicate (2 * increments y) y)).count x =
        if x ∈ letters then 2 * increments x else 0
  | [], _, x => by simp
  | y :: rest, nodup, x => by
      have restCount := count_schedule increments rest
        (List.nodup_cons.mp nodup).2 x
      simp only [List.flatMap_cons, List.count_append, restCount]
      by_cases equal : x = y
      · subst equal
        have absent : x ∉ rest := (List.nodup_cons.mp nodup).1
        simp [List.count_replicate, absent]
      · simp [List.count_replicate, equal, Ne.symm equal]

private theorem mem_eraseDups_iff [BEq α] [LawfulBEq α] :
    ∀ (entry : α) (entries : List α),
      entry ∈ entries.eraseDups ↔ entry ∈ entries
  | entry, [] => by simp
  | entry, head :: tail => by
      rw [List.eraseDups_cons]
      simp only [List.mem_cons]
      rw [mem_eraseDups_iff entry
        (tail.filter fun candidate => !candidate == head)]
      by_cases same : entry = head
      · subst entry
        simp
      · simp [same]
termination_by
  _ entries => entries.length
decreasing_by
  have filteredLength :
      (tail.filter fun candidate => !candidate == head).length ≤
        tail.length := List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le filteredLength

private theorem nodup_eraseDups [BEq α] [LawfulBEq α] :
    ∀ entries : List α, entries.eraseDups.Nodup
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro member
        have filteredMember :=
          (mem_eraseDups_iff head
            (tail.filter fun candidate => !candidate == head)).mp member
        simpa using filteredMember
      · exact nodup_eraseDups
          (tail.filter fun candidate => !candidate == head)
termination_by
  entries => entries.length
decreasing_by
  have filteredLength :
      (tail.filter fun candidate => !candidate == head).length ≤
        tail.length := List.filter_sublist.length_le
  simpa only [List.length_cons] using Nat.lt_succ_of_le filteredLength

/-! ## The class descriptor -/

/-- The verified Condition-8 class data: head, second letter, whole-word
support, and per-letter count parity. -/
def SameC8Class (u v : Word Nat) : Prop :=
  u.head = v.head ∧
    u.tail.head? = v.tail.head? ∧
    (∀ x, x ∈ u.toList ↔ x ∈ v.toList) ∧
    (∀ x, u.toList.count x % 2 = v.toList.count x % 2)

/-! ## Completeness -/

/-- The two-sided core: words with nonempty commuting zones, shared
two-letter prefix, equal support, and equal count parities derive to a
common even extension. -/
private theorem derivesZones (h s y1 : Nat) (r1 : List Nat)
    (y2 : Nat) (r2 : List Nat)
    (supportEq : ∀ x, x ∈ h :: s :: y1 :: r1 ↔ x ∈ h :: s :: y2 :: r2)
    (parityEq : ∀ x,
      (h :: s :: y1 :: r1).count x % 2 =
        (h :: s :: y2 :: r2).count x % 2) :
    Derives sigma
      (⟨h, s :: y1 :: r1⟩ : Word Nat) (⟨h, s :: y2 :: r2⟩ : Word Nat) := by
  let Z1 : List Nat := (y1 :: r1) ++ [h, s, h, s]
  let Z2 : List Nat := (y2 :: r2) ++ [h, s, h, s]
  have Z1Def : Z1 = (y1 :: r1) ++ [h, s, h, s] := rfl
  have Z2Def : Z2 = (y2 :: r2) ++ [h, s, h, s] := rfl
  have boost1 := derivesBoost h s y1 r1
  have boost2 := derivesBoost h s y2 r2
  -- support transfer to the boosted zones
  have zoneSupport : ∀ x, x ∈ Z1 ↔ x ∈ Z2 := by
    intro x
    have expand1 : x ∈ Z1 ↔ x ∈ h :: s :: y1 :: r1 := by
      simp [Z1Def, List.mem_append, or_assoc, or_left_comm, or_comm]
    have expand2 : x ∈ Z2 ↔ x ∈ h :: s :: y2 :: r2 := by
      simp [Z2Def, List.mem_append, or_assoc, or_left_comm, or_comm]
    rw [expand1, expand2]
    exact supportEq x
  -- parity transfer to the boosted zones
  have zoneParity : ∀ x, Z1.count x % 2 = Z2.count x % 2 := by
    intro x
    have expand1 : Z1.count x =
        (y1 :: r1).count x + [h, s, h, s].count x := by
      rw [Z1Def, List.count_append]
    have expand2 : Z2.count x =
        (y2 :: r2).count x + [h, s, h, s].count x := by
      rw [Z2Def, List.count_append]
    have whole1 : (h :: s :: y1 :: r1).count x =
        [h, s].count x + (y1 :: r1).count x := by
      have shape : h :: s :: y1 :: r1 = [h, s] ++ (y1 :: r1) := rfl
      rw [shape, List.count_append]
    have whole2 : (h :: s :: y2 :: r2).count x =
        [h, s].count x + (y2 :: r2).count x := by
      have shape : h :: s :: y2 :: r2 = [h, s] ++ (y2 :: r2) := rfl
      rw [shape, List.count_append]
    have doubled : [h, s, h, s].count x = 2 * [h, s].count x := by
      have shape : ([h, s, h, s] : List Nat) = [h, s] ++ [h, s] := rfl
      rw [shape, List.count_append]
      omega
    have given := parityEq x
    rw [whole1, whole2] at given
    rw [expand1, expand2, doubled]
    omega
  -- the common target and the two schedules
  let target : Nat → Nat := fun x => max (Z1.count x) (Z2.count x)
  have targetDef : target = fun x => max (Z1.count x) (Z2.count x) := rfl
  let inc1 : Nat → Nat := fun x => (target x - Z1.count x) / 2
  have inc1Def : inc1 = fun x => (target x - Z1.count x) / 2 := rfl
  let inc2 : Nat → Nat := fun x => (target x - Z2.count x) / 2
  have inc2Def : inc2 = fun x => (target x - Z2.count x) / 2 := rfl
  let E1 : List Nat :=
    Z1.eraseDups.flatMap (fun x => List.replicate (2 * inc1 x) x)
  have E1Def : E1 =
      Z1.eraseDups.flatMap (fun x => List.replicate (2 * inc1 x) x) := rfl
  let E2 : List Nat :=
    Z2.eraseDups.flatMap (fun x => List.replicate (2 * inc2 x) x)
  have E2Def : E2 =
      Z2.eraseDups.flatMap (fun x => List.replicate (2 * inc2 x) x) := rfl
  have schedule1 : Derives sigma
      (⟨h, s :: Z1⟩ : Word Nat) (⟨h, s :: (Z1 ++ E1)⟩ : Word Nat) := by
    have := derivesSchedule h s
      (Z1.eraseDups.map (fun x => (x, inc1 x))) Z1
      (fun pair member => by
        rcases List.mem_map.mp member with ⟨x, xMem, shape⟩
        have : pair.1 = x := by rw [← shape]
        rw [this]
        exact (mem_eraseDups_iff x Z1).mp xMem)
    have flatEq :
        (Z1.eraseDups.map (fun x => (x, inc1 x))).flatMap
            (fun pair => List.replicate (2 * pair.2) pair.1) = E1 := by
      simp [E1Def, List.flatMap_map]
    rwa [flatEq] at this
  have schedule2 : Derives sigma
      (⟨h, s :: Z2⟩ : Word Nat) (⟨h, s :: (Z2 ++ E2)⟩ : Word Nat) := by
    have := derivesSchedule h s
      (Z2.eraseDups.map (fun x => (x, inc2 x))) Z2
      (fun pair member => by
        rcases List.mem_map.mp member with ⟨x, xMem, shape⟩
        have : pair.1 = x := by rw [← shape]
        rw [this]
        exact (mem_eraseDups_iff x Z2).mp xMem)
    have flatEq :
        (Z2.eraseDups.map (fun x => (x, inc2 x))).flatMap
            (fun pair => List.replicate (2 * pair.2) pair.1) = E2 := by
      simp [E2Def, List.flatMap_map]
    rwa [flatEq] at this
  -- both extensions realize the target counts
  have evenGap1 : ∀ x, (target x - Z1.count x) % 2 = 0 := by
    intro x
    have parities := zoneParity x
    by_cases le : Z1.count x ≤ Z2.count x
    · have : target x = Z2.count x := by
        simp [targetDef, Nat.max_eq_right le]
      rw [this]
      omega
    · have reverse : Z2.count x ≤ Z1.count x := by omega
      have : target x = Z1.count x := by
        rw [targetDef]
        exact Nat.max_eq_left reverse
      rw [this]
      omega
  have evenGap2 : ∀ x, (target x - Z2.count x) % 2 = 0 := by
    intro x
    have parities := zoneParity x
    by_cases le : Z2.count x ≤ Z1.count x
    · have : target x = Z1.count x := by
        simp [targetDef, Nat.max_eq_left le]
      rw [this]
      omega
    · have reverse : Z1.count x ≤ Z2.count x := by omega
      have : target x = Z2.count x := by
        rw [targetDef]
        exact Nat.max_eq_right reverse
      rw [this]
      omega
  have counts1 : ∀ x, (Z1 ++ E1).count x = target x := by
    intro x
    have scheduleCount := count_schedule inc1 Z1.eraseDups
      (nodup_eraseDups Z1) x
    rw [List.count_append, E1Def, scheduleCount]
    by_cases member : x ∈ Z1
    · have inDedup : x ∈ Z1.eraseDups :=
        (mem_eraseDups_iff x Z1).mpr member
      simp only [if_pos inDedup, inc1Def]
      have gapEven := evenGap1 x
      have ceiling : Z1.count x ≤ target x := Nat.le_max_left _ _
      omega
    · have notDedup : x ∉ Z1.eraseDups := fun inD =>
        member ((mem_eraseDups_iff x Z1).mp inD)
      have zero1 : Z1.count x = 0 :=
        List.count_eq_zero.mpr member
      have zero2 : Z2.count x = 0 := by
        apply List.count_eq_zero.mpr
        intro inZ2
        exact member ((zoneSupport x).mpr inZ2)
      simp [if_neg notDedup, zero1, targetDef, zero2]
  have counts2 : ∀ x, (Z2 ++ E2).count x = target x := by
    intro x
    have scheduleCount := count_schedule inc2 Z2.eraseDups
      (nodup_eraseDups Z2) x
    rw [List.count_append, E2Def, scheduleCount]
    by_cases member : x ∈ Z2
    · have inDedup : x ∈ Z2.eraseDups :=
        (mem_eraseDups_iff x Z2).mpr member
      simp only [if_pos inDedup, inc2Def]
      have gapEven := evenGap2 x
      have ceiling : Z2.count x ≤ target x := Nat.le_max_right _ _
      omega
    · have notDedup : x ∉ Z2.eraseDups := fun inD =>
        member ((mem_eraseDups_iff x Z2).mp inD)
      have zero2 : Z2.count x = 0 :=
        List.count_eq_zero.mpr member
      have zero1 : Z1.count x = 0 := by
        apply List.count_eq_zero.mpr
        intro inZ1
        exact member ((zoneSupport x).mp inZ1)
      simp [if_neg notDedup, zero2, targetDef, zero1]
  have extensionsPerm : (Z1 ++ E1).Perm (Z2 ++ E2) := by
    rw [List.perm_iff_count]
    intro x
    rw [counts1 x, counts2 x]
  have middle := derivesTailPermHS h s extensionsPerm
  exact boost1.trans (schedule1.trans
    (middle.trans (schedule2.symm.trans boost2.symm)))

/-- Completeness of the three-law system for the verified class data. -/
theorem derivesOfSameC8Class {u v : Word Nat}
    (same : SameC8Class u v) : Derives sigma u v := by
  obtain ⟨heads, seconds, support, parity⟩ := same
  rcases u with ⟨uh, utail⟩
  rcases v with ⟨vh, vtail⟩
  simp only [Word.head] at heads
  subst heads
  rcases utail with _ | ⟨us, ut⟩
  · rcases vtail with _ | ⟨vs, vt⟩
    · exact Derives.refl _
    · simp [Word.tail] at seconds
  · rcases vtail with _ | ⟨vs, vt⟩
    · simp [Word.tail] at seconds
    · simp only [Word.tail, List.head?_cons, Option.some.injEq] at seconds
      subst seconds
      simp only [Word.toList] at support parity
      rcases ut with _ | ⟨uy, ur⟩
      · rcases vt with _ | ⟨vy, vr⟩
        · exact Derives.refl _
        · -- grow the short left side, then run the core
          have grow := derivesGrowShort uh us
          have supportGrown : ∀ x,
              x ∈ uh :: us :: us :: [us] ↔ x ∈ uh :: us :: vy :: vr := by
            intro x
            simpa [List.mem_cons, or_assoc] using support x
          have parityGrown : ∀ x,
              (uh :: us :: us :: [us]).count x % 2 =
                (uh :: us :: vy :: vr).count x % 2 := by
            intro x
            have decompose : (uh :: us :: us :: [us]).count x =
                (uh :: us :: ([] : List Nat)).count x +
                  ([us, us] : List Nat).count x := by
              have shape : uh :: us :: us :: [us] =
                  (uh :: us :: ([] : List Nat)) ++ [us, us] := rfl
              rw [shape, List.count_append]
            have evenPart : (([us, us] : List Nat).count x) % 2 = 0 := by
              by_cases equal : x = us
              · simp [equal]
              · have reverse : ¬ us = x := fun same => equal same.symm
                simp [equal, reverse]
            have given := parity x
            rw [decompose]
            omega
          have core :=
            derivesZones uh us us [us] vy vr supportGrown parityGrown
          exact grow.trans core
      · rcases vt with _ | ⟨vy, vr⟩
        · -- grow the short right side, then run the core
          have grow := derivesGrowShort uh us
          have supportGrown : ∀ x,
              x ∈ uh :: us :: uy :: ur ↔ x ∈ uh :: us :: us :: [us] := by
            intro x
            simpa [List.mem_cons, or_assoc] using support x
          have parityGrown : ∀ x,
              (uh :: us :: uy :: ur).count x % 2 =
                (uh :: us :: us :: [us]).count x % 2 := by
            intro x
            have decompose : (uh :: us :: us :: [us]).count x =
                (uh :: us :: ([] : List Nat)).count x +
                  ([us, us] : List Nat).count x := by
              have shape : uh :: us :: us :: [us] =
                  (uh :: us :: ([] : List Nat)) ++ [us, us] := rfl
              rw [shape, List.count_append]
            have evenPart : (([us, us] : List Nat).count x) % 2 = 0 := by
              by_cases equal : x = us
              · simp [equal]
              · have reverse : ¬ us = x := fun same => equal same.symm
                simp [equal, reverse]
            have given := parity x
            rw [decompose]
            omega
          have core :=
            derivesZones uh us uy ur us [us] supportGrown parityGrown
          exact core.trans grow.symm
        · exact derivesZones uh us uy ur vy vr support parity

/-! ## Semantic extraction: generic valuation lemmas -/

section GenericExtraction

variable {S : Type} {G : Semigroup S}

/-- Left-zero-band evaluation: with both accumulator states absorbing on
the right, evaluation returns the image of the head letter. -/
private theorem foldl_band {p q : S}
    (pp : G.mul p p = p) (pq : G.mul p q = p)
    (qp : G.mul q p = q) (qq : G.mul q q = q)
    (valuation : Nat → S)
    (range : ∀ x, valuation x = p ∨ valuation x = q) :
    ∀ (letters : List Nat) (acc : S), acc = p ∨ acc = q →
      letters.foldl (fun current x => G.mul current (valuation x)) acc =
        acc := by
  intro letters
  induction letters with
  | nil => intro acc _; rfl
  | cons x rest ih =>
      intro acc accRange
      have step : G.mul acc (valuation x) = acc := by
        rcases accRange with rfl | rfl <;>
          rcases range x with hx | hx <;> rw [hx] <;> assumption
      rw [List.foldl_cons, step]
      exact ih acc accRange

/-- Two mutually left-zero idempotents force equal heads. -/
theorem head_eq_of_band_valid {p q : S}
    (pp : G.mul p p = p) (pq : G.mul p q = p)
    (qp : G.mul q p = q) (qq : G.mul q q = q)
    (distinct : p ≠ q)
    (e : Identity Nat) (valid : e.SatisfiedBy G) :
    e.lhs.head = e.rhs.head := by
  by_cases same : e.lhs.head = e.rhs.head
  · exact same
  · have range : ∀ x : Nat,
        (if x = e.lhs.head then p else q) = p ∨
          (if x = e.lhs.head then p else q) = q := by
      intro x
      by_cases hx : x = e.lhs.head <;> simp [hx]
    have evalWord : ∀ word : Word Nat,
        G.eval (fun x => if x = e.lhs.head then p else q) word =
          (if word.head = e.lhs.head then p else q) := by
      intro word
      exact foldl_band pp pq qp qq _ range word.tail _ (range word.head)
    have evaluated := valid (fun x => if x = e.lhs.head then p else q)
    rw [evalWord e.lhs, evalWord e.rhs, if_pos rfl,
      if_neg (fun equal => same equal.symm)] at evaluated
    exact (distinct evaluated).elim

/-- Hit-detector evaluation: `zeroE` holds until the target letter maps
the accumulator to the absorbing `hitE`. -/
private theorem foldl_support [DecidableEq S] {zeroE hitE : S}
    (zz : G.mul zeroE zeroE = zeroE) (zh : G.mul zeroE hitE = hitE)
    (hz : G.mul hitE zeroE = hitE) (hh : G.mul hitE hitE = hitE)
    (distinct : zeroE ≠ hitE) (x : Nat) :
    ∀ (letters : List Nat) (acc : S), acc = zeroE ∨ acc = hitE →
      letters.foldl
          (fun current z =>
            G.mul current (if z = x then hitE else zeroE)) acc =
        if acc = hitE ∨ x ∈ letters then hitE else zeroE := by
  intro letters
  induction letters with
  | nil =>
      intro acc accRange
      rcases accRange with rfl | rfl
      · simp [distinct]
      · simp
  | cons y rest ih =>
      intro acc accRange
      rw [List.foldl_cons]
      by_cases hit : y = x
      · have step : G.mul acc (if y = x then hitE else zeroE) = hitE := by
          rcases accRange with rfl | rfl <;> simp [hit, zh, hh]
        rw [step, ih hitE (Or.inr rfl)]
        simp [hit]
      · have step : G.mul acc (if y = x then hitE else zeroE) = acc := by
          rcases accRange with rfl | rfl <;> simp [hit, zz, hz]
        rw [step, ih acc accRange]
        have conditions :
            (acc = hitE ∨ x ∈ rest) ↔ (acc = hitE ∨ x ∈ y :: rest) := by
          have notFirst : ¬ x = y := fun equal => hit equal.symm
          simp [List.mem_cons, notFirst]
        by_cases present : acc = hitE ∨ x ∈ rest
        · rw [if_pos present, if_pos (conditions.mp present)]
        · rw [if_neg present,
            if_neg (fun member => present (conditions.mpr member))]

/-- Word form of the hit detector: evaluation reports membership. -/
theorem eval_support [DecidableEq S] {zeroE hitE : S}
    (zz : G.mul zeroE zeroE = zeroE) (zh : G.mul zeroE hitE = hitE)
    (hz : G.mul hitE zeroE = hitE) (hh : G.mul hitE hitE = hitE)
    (distinct : zeroE ≠ hitE) (x : Nat) (word : Word Nat) :
    G.eval (fun z => if z = x then hitE else zeroE) word =
      if x ∈ word.toList then hitE else zeroE := by
  have base :
      (if word.head = x then hitE else zeroE) = zeroE ∨
        (if word.head = x then hitE else zeroE) = hitE := by
    by_cases hx : word.head = x <;> simp [hx]
  have folded := foldl_support (G := G) zz zh hz hh distinct x
    word.tail (if word.head = x then hitE else zeroE) base
  show word.tail.foldl _ _ = _
  rw [folded]
  have conditions :
      ((if word.head = x then hitE else zeroE) = hitE ∨ x ∈ word.tail) ↔
        x ∈ word.toList := by
    cases word with
    | mk head tail =>
        by_cases hx : head = x
        · subst hx
          simp [Word.toList]
        · have headMiss : ¬ x = head := fun equal => hx equal.symm
          simp [Word.toList, hx, distinct, headMiss]
  by_cases present :
      (if word.head = x then hitE else zeroE) = hitE ∨ x ∈ word.tail
  · rw [if_pos present, if_pos (conditions.mp present)]
  · rw [if_neg present,
      if_neg (fun included => present (conditions.mpr included))]

/-- Membership extraction from a factor with a hit detector. -/
theorem support_iff_of_valid [DecidableEq S] {zeroE hitE : S}
    (zz : G.mul zeroE zeroE = zeroE) (zh : G.mul zeroE hitE = hitE)
    (hz : G.mul hitE zeroE = hitE) (hh : G.mul hitE hitE = hitE)
    (distinct : zeroE ≠ hitE)
    (e : Identity Nat) (valid : e.SatisfiedBy G) (x : Nat) :
    x ∈ e.lhs.toList ↔ x ∈ e.rhs.toList := by
  have evaluated := valid (fun z => if z = x then hitE else zeroE)
  rw [eval_support zz zh hz hh distinct x e.lhs,
    eval_support zz zh hz hh distinct x e.rhs] at evaluated
  by_cases leftMember : x ∈ e.lhs.toList <;>
    by_cases rightMember : x ∈ e.rhs.toList <;>
      simp [leftMember, rightMember] at evaluated ⊢
  · exact distinct evaluated.symm
  · exact distinct evaluated

/-- Parity evaluation over a two-element group component. -/
private theorem foldl_parity {zeroE oneE : S}
    (zz : G.mul zeroE zeroE = zeroE) (zo : G.mul zeroE oneE = oneE)
    (oz : G.mul oneE zeroE = oneE) (oo : G.mul oneE oneE = zeroE)
    (x : Nat) :
    ∀ (letters : List Nat) (k : Nat),
      letters.foldl
          (fun current z =>
            G.mul current (if z = x then oneE else zeroE))
          (if k % 2 = 0 then zeroE else oneE) =
        if (k + letters.count x) % 2 = 0 then zeroE else oneE := by
  intro letters
  induction letters with
  | nil =>
      intro k
      simp
  | cons y rest ih =>
      intro k
      rw [List.foldl_cons]
      by_cases hit : y = x
      · have step :
            G.mul (if k % 2 = 0 then zeroE else oneE)
                (if y = x then oneE else zeroE) =
              (if (k + 1) % 2 = 0 then zeroE else oneE) := by
          by_cases parity : k % 2 = 0 <;>
            simp [hit, parity, zo, oo] <;> omega
        rw [step, ih (k + 1)]
        have expand : (y :: rest).count x = rest.count x + 1 := by
          simp [List.count_cons, hit]
        have counts : (k + 1) + rest.count x = k + (y :: rest).count x := by
          omega
        rw [counts]
      · have step :
            G.mul (if k % 2 = 0 then zeroE else oneE)
                (if y = x then oneE else zeroE) =
              (if k % 2 = 0 then zeroE else oneE) := by
          by_cases parity : k % 2 = 0 <;> simp [hit, parity, zz, oz]
        rw [step, ih k]
        have expand : (y :: rest).count x = rest.count x := by
          simp [hit]
        have counts : k + rest.count x = k + (y :: rest).count x := by
          omega
        rw [counts]

/-- Word form of the parity detector. -/
theorem eval_parity {zeroE oneE : S}
    (zz : G.mul zeroE zeroE = zeroE) (zo : G.mul zeroE oneE = oneE)
    (oz : G.mul oneE zeroE = oneE) (oo : G.mul oneE oneE = zeroE)
    (x : Nat) (word : Word Nat) :
    G.eval (fun z => if z = x then oneE else zeroE) word =
      if word.toList.count x % 2 = 0 then zeroE else oneE := by
  cases word with
  | mk head tail =>
      by_cases hx : head = x
      · have start :
            (if head = x then oneE else zeroE) =
              (if (1 : Nat) % 2 = 0 then zeroE else oneE) := by
          simp [hx]
        change
          tail.foldl
              (fun current z =>
                G.mul current (if z = x then oneE else zeroE))
              (if head = x then oneE else zeroE) = _
        rw [start, foldl_parity zz zo oz oo x tail 1]
        simp [Word.toList, hx, Nat.add_comm]
      · have start :
            (if head = x then oneE else zeroE) =
              (if (0 : Nat) % 2 = 0 then zeroE else oneE) := by
          simp [hx]
        change
          tail.foldl
              (fun current z =>
                G.mul current (if z = x then oneE else zeroE))
              (if head = x then oneE else zeroE) = _
        rw [start, foldl_parity zz zo oz oo x tail 0]
        simp [Word.toList, hx]

/-- Count-parity extraction from a factor with a parity detector. -/
theorem parity_eq_of_valid {zeroE oneE : S}
    (zz : G.mul zeroE zeroE = zeroE) (zo : G.mul zeroE oneE = oneE)
    (oz : G.mul oneE zeroE = oneE) (oo : G.mul oneE oneE = zeroE)
    (distinct : zeroE ≠ oneE)
    (e : Identity Nat) (valid : e.SatisfiedBy G) (x : Nat) :
    e.lhs.toList.count x % 2 = e.rhs.toList.count x % 2 := by
  have evaluated := valid (fun z => if z = x then oneE else zeroE)
  rw [eval_parity zz zo oz oo x e.lhs,
    eval_parity zz zo oz oo x e.rhs] at evaluated
  have leftBound :=
    Nat.mod_lt (e.lhs.toList.count x) (by decide : 0 < 2)
  have rightBound :=
    Nat.mod_lt (e.rhs.toList.count x) (by decide : 0 < 2)
  by_cases leftEven : e.lhs.toList.count x % 2 = 0
  · by_cases rightEven : e.rhs.toList.count x % 2 = 0
    · exact leftEven.trans rightEven.symm
    · have equality : zeroE = oneE := by
        simpa [leftEven, rightEven] using evaluated
      exact (distinct equality).elim
  · by_cases rightEven : e.rhs.toList.count x % 2 = 0
    · have equality : oneE = zeroE := by
        simpa [leftEven, rightEven] using evaluated
      exact (distinct equality.symm).elim
    · omega

/-- Folding over letters whose images freeze the accumulator. -/
private theorem foldl_frozen (valuation : Nat → S) {acc : S}
    (frozen : ∀ z : Nat, G.mul acc (valuation z) = acc) :
    ∀ letters : List Nat,
      letters.foldl (fun current z => G.mul current (valuation z)) acc =
        acc
  | [] => rfl
  | y :: rest => by
      rw [List.foldl_cons, frozen y]
      exact foldl_frozen valuation frozen rest

/-- Second-letter extraction through a marker transition: the head maps
to `startE`, the candidate to `candE`, every other letter to `missE`; the
first product lands in one of two range-absorbing states. -/
theorem second_eq_of_marker_valid {startE candE missE hitAcc missAcc : S}
    (hitStep : G.mul startE candE = hitAcc)
    (missStep : G.mul startE missE = missAcc)
    (selfStep : G.mul startE startE = missAcc)
    (hitStable : ∀ z, (z = startE ∨ z = candE ∨ z = missE) →
      G.mul hitAcc z = hitAcc)
    (missStable : ∀ z, (z = startE ∨ z = candE ∨ z = missE) →
      G.mul missAcc z = missAcc)
    (separate : hitAcc ≠ missAcc)
    (startHit : startE ≠ hitAcc) (startMiss : startE ≠ missAcc)
    (e : Identity Nat) (valid : e.SatisfiedBy G)
    (heads : e.lhs.head = e.rhs.head) :
    e.lhs.tail.head? = e.rhs.tail.head? := by
  let h0 : Nat := e.lhs.head
  have h0Fresh : ∀ cand : Nat, cand ≠ h0 → ¬ h0 = cand := by
    intro cand candFresh equal
    exact candFresh equal.symm
  have evalShape : ∀ (cand : Nat), cand ≠ h0 → ∀ (t : List Nat),
      G.eval
          (fun z => if z = cand then candE else
            if z = h0 then startE else missE)
          (⟨h0, t⟩ : Word Nat) =
        (match t with
          | [] => startE
          | y :: _ => if y = cand then hitAcc else missAcc) := by
    intro cand candFresh t
    have range : ∀ z : Nat,
        (if z = cand then candE else if z = h0 then startE else missE)
          = startE ∨
        (if z = cand then candE else if z = h0 then startE else missE)
          = candE ∨
        (if z = cand then candE else if z = h0 then startE else missE)
          = missE := by
      intro z
      by_cases zc : z = cand
      · exact Or.inr (Or.inl (by simp [zc]))
      · by_cases zh : z = h0
        · exact Or.inl (by simp [zc, zh, h0Fresh cand candFresh])
        · exact Or.inr (Or.inr (by simp [zc, zh]))
    have startImage :
        (if h0 = cand then candE else if h0 = h0 then startE else missE)
          = startE := by
      simp [h0Fresh cand candFresh]
    cases t with
    | nil =>
        show (if h0 = cand then candE else
          if h0 = h0 then startE else missE) = _
        simpa using startImage
    | cons y rest =>
        show List.foldl _ _ (y :: rest) = _
        rw [List.foldl_cons]
        change List.foldl
            (fun current z =>
              G.mul current
                (if z = cand then candE else
                  if z = h0 then startE else missE))
            (G.mul
              (if h0 = cand then candE else
                if h0 = h0 then startE else missE)
              (if y = cand then candE else
                if y = h0 then startE else missE))
            rest = _
        by_cases hit : y = cand
        · have step :
              G.mul
                  (if h0 = cand then candE else
                    if h0 = h0 then startE else missE)
                  (if y = cand then candE else
                    if y = h0 then startE else missE) = hitAcc := by
            rw [startImage]
            simp [hit, hitStep]
          rw [step]
          have frozen : ∀ z : Nat,
              G.mul hitAcc
                  (if z = cand then candE else
                    if z = h0 then startE else missE) = hitAcc := by
            intro z
            rcases range z with image | image | image
            · rw [image]
              exact hitStable _ (Or.inl rfl)
            · rw [image]
              exact hitStable _ (Or.inr (Or.inl rfl))
            · rw [image]
              exact hitStable _ (Or.inr (Or.inr rfl))
          rw [foldl_frozen _ frozen rest]
          simp [hit]
        · have step :
              G.mul
                  (if h0 = cand then candE else
                    if h0 = h0 then startE else missE)
                  (if y = cand then candE else
                    if y = h0 then startE else missE) = missAcc := by
            rw [startImage]
            by_cases yh : y = h0
            · simpa [hit, yh, h0Fresh cand candFresh] using selfStep
            · simpa [hit, yh] using missStep
          rw [step]
          have frozen : ∀ z : Nat,
              G.mul missAcc
                  (if z = cand then candE else
                    if z = h0 then startE else missE) = missAcc := by
            intro z
            rcases range z with image | image | image
            · rw [image]
              exact missStable _ (Or.inl rfl)
            · rw [image]
              exact missStable _ (Or.inr (Or.inl rfl))
            · rw [image]
              exact missStable _ (Or.inr (Or.inr rfl))
          rw [foldl_frozen _ frozen rest]
          simp [hit]
  have rhsEta : e.rhs = (⟨h0, e.rhs.tail⟩ : Word Nat) := by
    have eta : e.rhs = (⟨e.rhs.head, e.rhs.tail⟩ : Word Nat) := rfl
    rw [eta]
    exact congrArg (fun letter => (⟨letter, e.rhs.tail⟩ : Word Nat))
      heads.symm
  have evalBoth : ∀ (cand : Nat), cand ≠ h0 →
      (match e.lhs.tail with
        | [] => startE
        | y :: _ => if y = cand then hitAcc else missAcc) =
      (match e.rhs.tail with
        | [] => startE
        | y :: _ => if y = cand then hitAcc else missAcc) := by
    intro cand candFresh
    have evaluated := valid
      (fun z => if z = cand then candE else
        if z = h0 then startE else missE)
    rw [rhsEta] at evaluated
    exact (evalShape cand candFresh e.lhs.tail).symm.trans
      (evaluated.trans (evalShape cand candFresh e.rhs.tail))
  rcases ltailShape : e.lhs.tail with _ | ⟨u1, ur⟩ <;>
    rcases rtailShape : e.rhs.tail with _ | ⟨v1, vr⟩
  · rfl
  · -- left tail empty, right tail nonempty: contradiction
    exfalso
    by_cases v1h : v1 = h0
    · have compared := evalBoth (h0 + 1) (by omega)
      rw [ltailShape, rtailShape] at compared
      simp only at compared
      rw [if_neg (by omega : ¬ v1 = h0 + 1)] at compared
      exact startMiss compared
    · have compared := evalBoth v1 v1h
      rw [ltailShape, rtailShape] at compared
      simp only at compared
      simp only [ite_true] at compared
      exact startHit compared
  · -- left tail nonempty, right tail empty: contradiction
    exfalso
    by_cases u1h : u1 = h0
    · have compared := evalBoth (h0 + 1) (by omega)
      rw [ltailShape, rtailShape] at compared
      simp only at compared
      rw [if_neg (by omega : ¬ u1 = h0 + 1)] at compared
      exact startMiss compared.symm
    · have compared := evalBoth u1 u1h
      rw [ltailShape, rtailShape] at compared
      simp only at compared
      simp only [ite_true] at compared
      exact startHit compared.symm
  · -- both nonempty: the second letters agree
    simp only [List.head?_cons, Option.some.injEq]
    by_cases same : u1 = v1
    · exact same
    · by_cases u1h : u1 = h0
      · have v1h : ¬ v1 = h0 := fun equal =>
          same (u1h.trans equal.symm)
        have compared := evalBoth v1 v1h
        rw [ltailShape, rtailShape] at compared
        simp only at compared
        rw [if_neg (fun equal => same equal)] at compared
        simp only [ite_true] at compared
        exact (separate compared.symm).elim
      · have compared := evalBoth u1 u1h
        rw [ltailShape, rtailShape] at compared
        simp only at compared
        simp only [ite_true] at compared
        rw [if_neg (fun equal => same equal.symm)] at compared
        exact (separate compared).elim

end GenericExtraction

/-! ## The four pinned factor tables -/

abbrev threeTable : FiniteTable := Generated.Catalogue.S3_11.table
abbrev fourTable : FiniteTable := Generated.Catalogue.S4_77.table
abbrev twoTable : FiniteTable := Generated.Catalogue.S2_2.table
abbrev nineTable : FiniteTable := Generated.Catalogue.S5_904.table

private def sigmaVariable (value : Nat) : Fin 4 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 2 else 3

theorem modelsS3_11 : Models threeTable.semigroup sigma :=
  FiniteCertificate.checkModels_sound threeTable sigma sigmaVariable
    (by decide)

theorem modelsS4_77 : Models fourTable.semigroup sigma :=
  FiniteCertificate.checkModels_sound fourTable sigma sigmaVariable
    (by decide)

theorem modelsS2_2 : Models twoTable.semigroup sigma :=
  FiniteCertificate.checkModels_sound twoTable sigma sigmaVariable
    (by decide)

theorem modelsS5_904 : Models nineTable.semigroup sigma :=
  FiniteCertificate.checkModels_sound nineTable sigma sigmaVariable
    (by decide)

/-! ## Intersection completeness for both factor pairs -/

theorem intersectionComplete_S3_11_S4_77 (e : Identity Nat)
    (leftValid : e.SatisfiedBy threeTable.semigroup)
    (rightValid : e.SatisfiedBy fourTable.semigroup) :
    Derives sigma e.lhs e.rhs := by
  have heads :=
    head_eq_of_band_valid (p := (2 : Fin 4)) (q := (3 : Fin 4))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      e rightValid
  refine derivesOfSameC8Class ⟨heads, ?_, ?_, ?_⟩
  · exact second_eq_of_marker_valid
      (startE := (1 : Fin 4)) (candE := (3 : Fin 4))
      (missE := (2 : Fin 4)) (hitAcc := (2 : Fin 4))
      (missAcc := (0 : Fin 4))
      (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by decide) (by decide) (by decide)
      e rightValid heads
  · exact fun x =>
      support_iff_of_valid (zeroE := (0 : Fin 3)) (hitE := (2 : Fin 3))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        e leftValid x
  · exact fun x =>
      parity_eq_of_valid (zeroE := (0 : Fin 3)) (oneE := (1 : Fin 3))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        e leftValid x

theorem intersectionComplete_S2_2_S5_904 (e : Identity Nat)
    (leftValid : e.SatisfiedBy twoTable.semigroup)
    (rightValid : e.SatisfiedBy nineTable.semigroup) :
    Derives sigma e.lhs e.rhs := by
  have heads :=
    head_eq_of_band_valid (p := (2 : Fin 5)) (q := (3 : Fin 5))
      (by decide) (by decide) (by decide) (by decide) (by decide)
      e rightValid
  refine derivesOfSameC8Class ⟨heads, ?_, ?_, ?_⟩
  · exact second_eq_of_marker_valid
      (startE := (1 : Fin 5)) (candE := (3 : Fin 5))
      (missE := (0 : Fin 5)) (hitAcc := (2 : Fin 5))
      (missAcc := (0 : Fin 5))
      (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by decide) (by decide) (by decide)
      e rightValid heads
  · exact fun x =>
      support_iff_of_valid (zeroE := (2 : Fin 5)) (hitE := (4 : Fin 5))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        e rightValid x
  · exact fun x =>
      parity_eq_of_valid (zeroE := (0 : Fin 2)) (oneE := (1 : Fin 2))
        (by decide) (by decide) (by decide) (by decide) (by decide)
        e leftValid x

/-! ## The three intersection-basis instances -/

theorem intersectionBasisS3_11S4_77 :
    IntersectionBasis threeTable.semigroup fourTable.semigroup sigma where
  leftModels := modelsS3_11
  rightModels := modelsS4_77
  complete := intersectionComplete_S3_11_S4_77

/-- Swapped orientation for the `S6_9073` wrapper. -/
theorem intersectionBasisS4_77S3_11 :
    IntersectionBasis fourTable.semigroup threeTable.semigroup sigma where
  leftModels := modelsS4_77
  rightModels := modelsS3_11
  complete := fun e rightValid leftValid =>
    intersectionComplete_S3_11_S4_77 e leftValid rightValid

theorem intersectionBasisS2_2S5_904 :
    IntersectionBasis twoTable.semigroup nineTable.semigroup sigma where
  leftModels := modelsS2_2
  rightModels := modelsS5_904
  complete := intersectionComplete_S2_2_S5_904

end SemigroupBasis.CoRoots.Order6Condition8ThreeLaw
