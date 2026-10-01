import SemigroupBasis.CoRoots.S5_215Family
import SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_213M2Transfers

/-!
# Shared four-law normalizer for `S3_13 ∩ S5_215` (msg-0279 lane)

EVIDENCE LABEL: source-staged, NOT compiled here.  Design receipts:
msg-0274 (corrected candidate + descriptor), msg-0088 screen (all four
laws model both factors and all five leaves; three-way exactness
36 = 36 at the bounded regime; `xyzt = xxyzt` independently confirmed
underivable from the stored three).

THE FOUR-LAW SYSTEM `sigma` (msg-0279 order):
  1. `xxy = xyx`      (head gather)
  2. `xxy = xyy`      (head transfer)
  3. `xyz = xzy`      (tail swap)
  4. `xyzt = xxyzt`   (square-free insertion — literally
                       `S5_215.squarefreeInsertionLaw`)

EXACT DESCRIPTOR (msg-0274): joint validity in `S3_13 × S5_215` is
governed by equal head + equal support + total length capped at four.
`S3_13` supplies the head half (`headEq_s3_13`, kernel-verified in the
M2 transfer layer), `S5_215` supplies support and capped length
(`S5_215Family.S5_215.valid_support` / `valid_capped_length`, both
kernel-verified).

COMPLETENESS ARCHITECTURE (all inside `sigma`):
  length 1  — equal words outright (heads agree);
  length 2  — support + head force syntactic equality (no derivation);
  length 3  — classification by support: laws 1–3 connect every tail
              over a fixed head with fixed support (`36 = 36` screen);
  length ≥4 — no capping needed: law 4 inserts a fresh head copy
              behind any ≥3-letter tail, law 2 converts it into a copy
              of any exposed supported letter, so each side appends the
              other side's full letter list and the two extensions are
              tail-permutations of each other (law 3 closes).
This is strictly leaner than the `S5_215Normalization` cap-four route:
with heads pinned, common-extension + tail permutation replaces the
quadruple-support canonical form entirely.

API RISK FLAGS (patch-loop material, none mathematical): `Derives`
constructor names mirror the compiled M2 modules
(`fromBasis/refl/symm/trans/prepend/appendRight/subst`); the
`simp [wordOfCons, Word.singleton, Word.append, Word.append_assoc]`
normal forms and the `List.count_* … omega` permutation pattern are
taken verbatim from the compiled `S5_215Normalization`; `List` lemma
spellings (`perm_cons_erase`, `perm_iff_count`, `mem_append_left`)
mirror compiled uses.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_215FourLaw

open SemigroupBasis
open SemigroupBasis.CoRoots
open SemigroupBasis.CoRoots.S5_215Normalization (wordOfCons SameSupport)

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-! ## The displayed four-law system -/

def headGatherLaw : Identity Nat := ⟨w 0 [0, 1], w 0 [1, 0]⟩
def headTransferLaw : Identity Nat := ⟨w 0 [0, 1], w 0 [1, 1]⟩
def tailSwapLaw : Identity Nat := ⟨w 0 [1, 2], w 0 [2, 1]⟩

/-- The corrected four-law candidate, in the msg-0279 order; the fourth
law is definitionally `S5_215.squarefreeInsertionLaw`. -/
def sigma : List (Identity Nat) :=
  [headGatherLaw, headTransferLaw, tailSwapLaw,
    S5_215.squarefreeInsertionLaw]

private theorem headGatherMem : headGatherLaw ∈ sigma := by
  simp [sigma]
private theorem headTransferMem : headTransferLaw ∈ sigma := by
  simp [sigma]
private theorem tailSwapMem : tailSwapLaw ∈ sigma := by
  simp [sigma]
private theorem insertionMem : S5_215.squarefreeInsertionLaw ∈ sigma := by
  simp [sigma]

private def instantiateFour (a b c d : Word Nat) : Nat → Word Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | n + 4 => Word.singleton (n + 4)

/-! ## Block instances of the four laws -/

/-- `U²V = UVU` for word blocks (law 1). -/
theorem derivesHeadGather (u v : Word Nat) :
    Derives sigma ((u ++ u) ++ v) ((u ++ v) ++ u) := by
  have base : Derives sigma headGatherLaw.lhs headGatherLaw.rhs :=
    Derives.fromBasis headGatherMem
  have substituted := Derives.subst base (instantiateFour u v v v)
  simpa [headGatherLaw, w, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `U²V = UV²` for word blocks (law 2). -/
theorem derivesHeadTransfer (u v : Word Nat) :
    Derives sigma ((u ++ u) ++ v) ((u ++ v) ++ v) := by
  have base : Derives sigma headTransferLaw.lhs headTransferLaw.rhs :=
    Derives.fromBasis headTransferMem
  have substituted := Derives.subst base (instantiateFour u v v v)
  simpa [headTransferLaw, w, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- `UVX = UXV` for word blocks (law 3): blocks commute behind any
nonempty prefix. -/
theorem derivesTailSwap (u v x : Word Nat) :
    Derives sigma ((u ++ v) ++ x) ((u ++ x) ++ v) := by
  have base : Derives sigma tailSwapLaw.lhs tailSwapLaw.rhs :=
    Derives.fromBasis tailSwapMem
  have substituted := Derives.subst base (instantiateFour u v x x)
  simpa [tailSwapLaw, w, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Every product of four nonempty blocks permits duplication of its
first block (law 4; mirrors
`S5_215Normalization.correctedDerivesLongDuplication`). -/
theorem derivesLongDuplication (u v x q : Word Nat) :
    Derives sigma
      (((u ++ v) ++ x) ++ q)
      ((((u ++ u) ++ v) ++ x) ++ q) := by
  have base :
      Derives sigma S5_215.squarefreeInsertionLaw.lhs
        S5_215.squarefreeInsertionLaw.rhs :=
    Derives.fromBasis insertionMem
  have substituted := Derives.subst base (instantiateFour u v x q)
  simpa [S5_215.squarefreeInsertionLaw, S5_215.xyzt, S5_215.xxyzt,
    S5_215.w, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-! ## Single-letter instances over a fixed head -/

/-- `h·hx = h·xh` as words. -/
theorem derivesPairGather (h x : Nat) :
    Derives sigma (wordOfCons h [h, x]) (wordOfCons h [x, h]) := by
  simpa [wordOfCons, Word.singleton, Word.append] using
    derivesHeadGather (Word.singleton h) (Word.singleton x)

/-- `h·hx = h·xx` as words. -/
theorem derivesPairTransfer (h x : Nat) :
    Derives sigma (wordOfCons h [h, x]) (wordOfCons h [x, x]) := by
  simpa [wordOfCons, Word.singleton, Word.append] using
    derivesHeadTransfer (Word.singleton h) (Word.singleton x)

/-- `h·xy = h·yx` as words. -/
theorem derivesPairSwap (h x y : Nat) :
    Derives sigma (wordOfCons h [x, y]) (wordOfCons h [y, x]) := by
  simpa [wordOfCons, Word.singleton, Word.append] using
    derivesTailSwap (Word.singleton h) (Word.singleton x)
      (Word.singleton y)

/-! ## Tail permutations behind a fixed prefix

`extend p xs` appends the letter list `xs` to the word `p`; law 3 makes
the appended zone fully commutative. -/

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
    extend p (x :: xs) = p ++ (⟨x, xs⟩ : Word Nat) := by
  rfl

private theorem extend_head (h : Nat) (xs : List Nat) :
    extend (Word.singleton h) xs = wordOfCons h xs := by
  rfl

private theorem extend_pair (p : Word Nat) (a b : Nat) (l : List Nat) :
    extend ((p ++ Word.singleton a) ++ Word.singleton b) l =
      extend p (a :: b :: l) := by
  apply Word.toList_injective
  simp [extend_toList, Word.toList_append, Word.toList_singleton]

private theorem extend_pairWord (h a b : Nat) (l : List Nat) :
    extend (wordOfCons h [a, b]) l = wordOfCons h (a :: b :: l) := by
  rfl

/-- Extending both sides of a derivation by a common letter list. -/
private theorem derivesExtend {u v : Word Nat}
    (derivation : Derives sigma u v) (xs : List Nat) :
    Derives sigma (extend u xs) (extend v xs) := by
  cases xs with
  | nil =>
      simpa [extend_nil] using derivation
  | cons x rest =>
      have appended :=
        Derives.appendRight derivation (⟨x, rest⟩ : Word Nat)
      rw [← extend_word, ← extend_word] at appended
      exact appended

/-- Behind any nonempty prefix, appended letter lists derive to every
permutation (law 3 closes adjacent transpositions). -/
theorem derivesTailPerm (p : Word Nat) {t1 t2 : List Nat}
    (permutation : t1.Perm t2) :
    Derives sigma (extend p t1) (extend p t2) := by
  induction permutation generalizing p with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      rw [extend_cons, extend_cons]
      exact ih (p ++ Word.singleton x)
  | swap x y l =>
      have base :=
        derivesTailSwap p (Word.singleton y) (Word.singleton x)
      have extended := derivesExtend base l
      rw [extend_pair, extend_pair] at extended
      exact extended
  | trans _ _ ihFirst ihSecond =>
      exact (ihFirst p).trans (ihSecond p)

/-- Head-anchored form of the tail permutation lemma. -/
theorem derivesTailPermHead (h : Nat) {t1 t2 : List Nat}
    (permutation : t1.Perm t2) :
    Derives sigma (wordOfCons h t1) (wordOfCons h t2) := by
  have derived := derivesTailPerm (Word.singleton h) permutation
  rwa [extend_head, extend_head] at derived

/-! ## Head insertion and append-member for long words -/

/-- Law 4 with singleton head block: any word whose tail has at least
three letters absorbs a fresh copy of its head. -/
theorem derivesInsertHead (h a b c : Nat) (rest : List Nat) :
    Derives sigma
      (wordOfCons h (a :: b :: c :: rest))
      (wordOfCons h (h :: a :: b :: c :: rest)) := by
  simpa [wordOfCons, Word.singleton, Word.append, Word.append_assoc]
    using derivesLongDuplication (Word.singleton h) (Word.singleton a)
      (Word.singleton b) (⟨c, rest⟩ : Word Nat)

/-- In a word with head `h` and tail of length at least three, any
already-supported letter can be appended: insert a head copy (law 4),
transfer it onto the target letter (law 2), and re-sort (law 3). -/
theorem derivesAppendMember (h x : Nat) (t : List Nat)
    (hlong : 3 ≤ t.length) (hx : x ∈ h :: t) :
    Derives sigma (wordOfCons h t) (wordOfCons h (t ++ [x])) := by
  rcases List.mem_cons.mp hx with hxh | hxt
  · -- the appended letter is the head itself
    subst hxh
    obtain ⟨a, b, c, rest, rfl⟩ :
        ∃ a b c rest, t = a :: b :: c :: rest := by
      rcases t with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · simp only [List.length_nil] at hlong; omega
      · simp only [List.length_cons, List.length_nil] at hlong; omega
      · simp only [List.length_cons, List.length_nil] at hlong; omega
      · exact ⟨a, b, c, rest, rfl⟩
    have inserted := derivesInsertHead x a b c rest
    have rotated :
        (x :: a :: b :: c :: rest).Perm
          ((a :: b :: c :: rest) ++ [x]) := by
      rw [List.perm_iff_count]
      intro z
      simp only [List.count_append, List.count_cons, List.count_nil]
      omega
    exact inserted.trans (derivesTailPermHead x rotated)
  · -- the appended letter sits in the tail
    have sourcePerm : t.Perm (x :: t.erase x) :=
      List.perm_cons_erase hxt
    have eraseLong : 2 ≤ (t.erase x).length := by
      have lengths := sourcePerm.length_eq
      simp only [List.length_cons] at lengths
      omega
    obtain ⟨b, c, rest, eraseEq⟩ :
        ∃ b c rest, t.erase x = b :: c :: rest := by
      rcases hErase : t.erase x with _ | ⟨b, _ | ⟨c, rest⟩⟩
      · rw [hErase] at eraseLong
        simp only [List.length_nil] at eraseLong; omega
      · rw [hErase] at eraseLong
        simp only [List.length_cons, List.length_nil] at eraseLong
        omega
      · exact ⟨b, c, rest, rfl⟩
    rw [eraseEq] at sourcePerm
    have arrange :
        Derives sigma (wordOfCons h t)
          (wordOfCons h (x :: b :: c :: rest)) :=
      derivesTailPermHead h sourcePerm
    have inserted := derivesInsertHead h x b c rest
    have transferred :
        Derives sigma
          (wordOfCons h (h :: x :: b :: c :: rest))
          (wordOfCons h (x :: x :: b :: c :: rest)) := by
      have base := derivesExtend
        (derivesPairTransfer h x) (b :: c :: rest)
      rw [extend_pairWord, extend_pairWord] at base
      exact base
    have finishPerm :
        (x :: x :: b :: c :: rest).Perm (t ++ [x]) := by
      rw [List.perm_iff_count]
      intro z
      have sourceCounts := (List.perm_iff_count.mp sourcePerm) z
      simp only [List.count_append, List.count_cons,
        List.count_nil] at sourceCounts ⊢
      omega
    exact arrange.trans <| inserted.trans <|
      transferred.trans (derivesTailPermHead h finishPerm)

/-- Append an entire letter list drawn from the word's support. -/
theorem derivesAppendList (h : Nat) (t xs : List Nat)
    (hlong : 3 ≤ t.length)
    (hcontent : ∀ x, x ∈ xs → x ∈ h :: t) :
    Derives sigma (wordOfCons h t) (wordOfCons h (t ++ xs)) := by
  induction xs generalizing t with
  | nil =>
      simpa using Derives.refl (wordOfCons h t)
  | cons x rest ih =>
      have firstStep :=
        derivesAppendMember h x t hlong
          (hcontent x (List.Mem.head rest))
      have nextLong : 3 ≤ (t ++ [x]).length := by
        simp only [List.length_append, List.length_cons,
          List.length_nil]
        omega
      have nextContent :
          ∀ y, y ∈ rest → y ∈ h :: (t ++ [x]) := by
        intro y hy
        rcases List.mem_cons.mp
            (hcontent y (List.Mem.tail x hy)) with hyh | hyt
        · exact hyh ▸ List.Mem.head _
        · exact List.mem_cons_of_mem h (List.mem_append_left _ hyt)
      have restStep := ih (t ++ [x]) nextLong nextContent
      exact firstStep.trans <| by
        simpa [List.append_assoc] using restStep

/-- Two long words with equal head and equal support derive to each
other: each appends the other's full letter list, and the two
extensions are tail-permutations. -/
theorem derivesLongOfSupportEq (h : Nat) (t1 t2 : List Nat)
    (h1 : 3 ≤ t1.length) (h2 : 3 ≤ t2.length)
    (support : ∀ z, z ∈ h :: t1 ↔ z ∈ h :: t2) :
    Derives sigma (wordOfCons h t1) (wordOfCons h t2) := by
  have leftStep :=
    derivesAppendList h t1 (h :: t2) h1
      (fun x hx => (support x).mpr hx)
  have rightStep :=
    derivesAppendList h t2 (h :: t1) h2
      (fun x hx => (support x).mp hx)
  have middlePerm :
      (t1 ++ (h :: t2)).Perm (t2 ++ (h :: t1)) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append, List.count_cons, List.count_nil]
    omega
  exact leftStep.trans <|
    (derivesTailPermHead h middlePerm).trans rightStep.symm

/-! ## Length-three classification by support -/

/-- Over head `h`, every length-two tail supported by `{h, x}` and
containing `x` derives to the square tail `[x, x]`. -/
private theorem derivesTripleTwoSupport (h x a b : Nat)
    (ha : a = h ∨ a = x) (hb : b = h ∨ b = x)
    (hxh : x ≠ h) (hpresent : x ∈ [a, b]) :
    Derives sigma (wordOfCons h [a, b]) (wordOfCons h [x, x]) := by
  rcases ha with hah | hax
  · rcases hb with hbh | hbx
    · -- tail letters both equal `h`, yet `x ≠ h` occurs among them
      exfalso
      simp only [List.mem_cons, List.not_mem_nil, or_false]
        at hpresent
      rcases hpresent with h' | h'
      · exact hxh (h'.trans hah)
      · exact hxh (h'.trans hbh)
    · rw [hah, hbx]
      exact derivesPairTransfer h x
  · rcases hb with hbh | hbx
    · rw [hax, hbh]
      exact (derivesPairSwap h x h).trans (derivesPairTransfer h x)
    · rw [hax, hbx]
      exact Derives.refl _

/-- Two-sided reduction to the shared square tail `[x, x]` when both
tails are supported by `{h, x}`. -/
private theorem derivesTripleViaWitness (h a b c d x : Nat)
    (hax : a = h ∨ a = x) (hbx : b = h ∨ b = x)
    (hxh : x ≠ h) (hpresent : x ∈ [a, b])
    (support : ∀ z, z ∈ [h, a, b] ↔ z ∈ [h, c, d])
    (hcSource : c = h ∨ c = a ∨ c = b)
    (hdSource : d = h ∨ d = a ∨ d = b) :
    Derives sigma (wordOfCons h [a, b]) (wordOfCons h [c, d]) := by
  have hcx : c = h ∨ c = x := by
    rcases hcSource with h' | h' | h'
    · exact Or.inl h'
    · rcases hax with h'' | h''
      · exact Or.inl (h'.trans h'')
      · exact Or.inr (h'.trans h'')
    · rcases hbx with h'' | h''
      · exact Or.inl (h'.trans h'')
      · exact Or.inr (h'.trans h'')
  have hdx : d = h ∨ d = x := by
    rcases hdSource with h' | h' | h'
    · exact Or.inl h'
    · rcases hax with h'' | h''
      · exact Or.inl (h'.trans h'')
      · exact Or.inr (h'.trans h'')
    · rcases hbx with h'' | h''
      · exact Or.inl (h'.trans h'')
      · exact Or.inr (h'.trans h'')
  have hTargetPresent : x ∈ [c, d] := by
    have := (support x).mp (List.mem_cons_of_mem h hpresent)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
      at this ⊢
    rcases this with h' | h' | h'
    · exact absurd h' hxh
    · exact Or.inl h'
    · exact Or.inr h'
  have left := derivesTripleTwoSupport h x a b hax hbx hxh hpresent
  have right :=
    derivesTripleTwoSupport h x c d hcx hdx hxh hTargetPresent
  exact left.trans right.symm

/-- Length-three words over a common head are classified exactly by
support (the `36 = 36` bounded screen, now in derivational form). -/
theorem derivesTripleOfSupportEq (h a b c d : Nat)
    (support : ∀ z, z ∈ [h, a, b] ↔ z ∈ [h, c, d]) :
    Derives sigma (wordOfCons h [a, b]) (wordOfCons h [c, d]) := by
  have hcSource : c = h ∨ c = a ∨ c = b := by
    have := (support c).mpr (by simp)
    simpa using this
  have hdSource : d = h ∨ d = a ∨ d = b := by
    have := (support d).mpr (by simp)
    simpa using this
  have haTarget : a = h ∨ a = c ∨ a = d := by
    have := (support a).mp (by simp)
    simpa using this
  have hbTarget : b = h ∨ b = c ∨ b = d := by
    have := (support b).mp (by simp)
    simpa using this
  by_cases hah : a = h
  · by_cases hbh : b = h
    · -- support {h}: all four letters are forced to `h`
      have hc : c = h := by
        rcases hcSource with h' | h' | h'
        · exact h'
        · exact h'.trans hah
        · exact h'.trans hbh
      have hd : d = h := by
        rcases hdSource with h' | h' | h'
        · exact h'
        · exact h'.trans hah
        · exact h'.trans hbh
      rw [hah, hbh, hc, hd]
      exact Derives.refl _
    · -- support {h, b}: witness x := b
      exact derivesTripleViaWitness h a b c d b
        (Or.inl hah) (Or.inr rfl) hbh (by simp)
        support hcSource hdSource
  · by_cases hbh : b = h
    · -- support {h, a}: witness x := a
      exact derivesTripleViaWitness h a b c d a
        (Or.inr rfl) (Or.inl hbh) hah (by simp)
        support hcSource hdSource
    · by_cases hab : a = b
      · -- support {h, a} with tail [a, a]: witness x := a
        exact derivesTripleViaWitness h a b c d a
          (Or.inr rfl) (Or.inr hab.symm) hah (by simp)
          support hcSource hdSource
      · -- support {h, a, b}, all distinct: the target tail is a
        -- permutation of the source tail
        have hcNe : c ≠ h := by
          intro hch
          have haCD : a = c ∨ a = d := by
            rcases haTarget with h' | h' | h'
            · exact absurd h' hah
            · exact Or.inl h'
            · exact Or.inr h'
          have hbCD : b = c ∨ b = d := by
            rcases hbTarget with h' | h' | h'
            · exact absurd h' hbh
            · exact Or.inl h'
            · exact Or.inr h'
          rcases haCD with h1 | h1
          · exact hah (h1.trans hch)
          · rcases hbCD with h2 | h2
            · exact hbh (h2.trans hch)
            · exact hab (h1.trans h2.symm)
        have hdNe : d ≠ h := by
          intro hdh
          have haCD : a = c ∨ a = d := by
            rcases haTarget with h' | h' | h'
            · exact absurd h' hah
            · exact Or.inl h'
            · exact Or.inr h'
          have hbCD : b = c ∨ b = d := by
            rcases hbTarget with h' | h' | h'
            · exact absurd h' hbh
            · exact Or.inl h'
            · exact Or.inr h'
          rcases haCD with h1 | h1
          · rcases hbCD with h2 | h2
            · exact hab (h1.trans h2.symm)
            · exact hbh (h2.trans hdh)
          · exact hah (h1.trans hdh)
        have hcAB : c = a ∨ c = b := by
          rcases hcSource with h' | h' | h'
          · exact absurd h' hcNe
          · exact Or.inl h'
          · exact Or.inr h'
        rcases hcAB with hca | hcb
        · -- c = a forces d = b
          have hdb : d = b := by
            rcases hbTarget with h' | h' | h'
            · exact absurd h' hbh
            · exact absurd (h'.trans hca).symm hab
            · exact h'.symm
          rw [hca, hdb]
          exact Derives.refl _
        · -- c = b forces d = a
          have hda : d = a := by
            rcases haTarget with h' | h' | h'
            · exact absurd h' hah
            · exact absurd (h'.trans hcb) hab
            · exact h'.symm
          rw [hcb, hda]
          exact derivesPairSwap h a b

/-! ## Length-two rigidity -/

/-- Two-letter words with equal head and equal support are equal. -/
theorem eq_of_pair_support (h a b : Nat)
    (support : ∀ z, z ∈ [h, a] ↔ z ∈ [h, b]) : a = b := by
  by_cases hah : a = h
  · have hb := (support b).mpr (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with hb | hb
    · exact hah.trans hb.symm
    · exact hb.symm
  · have ha := (support a).mp (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | ha
    · exact absurd ha hah
    · exact ha

/-! ## The completeness theorem -/

/-- Equal head, equal support, and equal length capped at four are
sufficient for derivability from the four-law system. -/
theorem derivesOfClass (u v : Word Nat)
    (headEq : u.head = v.head)
    (support : SameSupport u v)
    (cappedLength :
      min u.toList.length 4 = min v.toList.length 4) :
    Derives sigma u v := by
  cases u with
  | mk h t1 =>
      cases v with
      | mk h' t2 =>
          have hh : h = h' := headEq
          subst hh
          have supportList :
              ∀ z, z ∈ h :: t1 ↔ z ∈ h :: t2 := by
            intro z
            have := support z
            simpa [Word.toList] using this
          have lengthList :
              min (t1.length + 1) 4 = min (t2.length + 1) 4 := by
            simpa [Word.toList] using cappedLength
          rcases t1 with _ | ⟨a, _ | ⟨b, _ | ⟨c1, rest1⟩⟩⟩
          · -- length 1
            rcases t2 with _ | ⟨x, xs⟩
            · exact Derives.refl _
            · exfalso
              simp only [List.length_nil, List.length_cons]
                at lengthList
              omega
          · -- length 2
            rcases t2 with _ | ⟨x, _ | ⟨y, ys⟩⟩
            · exfalso
              simp only [List.length_nil, List.length_cons]
                at lengthList
              omega
            · have := eq_of_pair_support h a x supportList
              subst this
              exact Derives.refl _
            · exfalso
              simp only [List.length_cons, List.length_nil]
                at lengthList
              omega
          · -- length 3
            rcases t2 with _ | ⟨x, _ | ⟨y, _ | ⟨z2, zs⟩⟩⟩
            · exfalso
              simp only [List.length_nil, List.length_cons]
                at lengthList
              omega
            · exfalso
              simp only [List.length_cons, List.length_nil]
                at lengthList
              omega
            · simpa [wordOfCons] using
                derivesTripleOfSupportEq h a b x y supportList
            · exfalso
              simp only [List.length_cons, List.length_nil]
                at lengthList
              omega
          · -- length at least 4
            rcases t2 with _ | ⟨x, _ | ⟨y, _ | ⟨z2, zs⟩⟩⟩
            · exfalso
              simp only [List.length_nil, List.length_cons]
                at lengthList
              omega
            · exfalso
              simp only [List.length_cons, List.length_nil]
                at lengthList
              omega
            · exfalso
              simp only [List.length_cons, List.length_nil]
                at lengthList
              omega
            · simpa [wordOfCons] using
                derivesLongOfSupportEq h
                  (a :: b :: c1 :: rest1) (x :: y :: z2 :: zs)
                  (by simp only [List.length_cons]; omega)
                  (by simp only [List.length_cons]; omega)
                  supportList

/-! ## Intersection completeness through the factor exports -/

/-- Given equal heads, `S5_215`-validity alone forces derivability:
support and capped length are its kernel-verified invariants. -/
theorem intersectionCompleteOfHeadEq
    (id : Identity Nat)
    (headEq : id.lhs.head = id.rhs.head)
    (validRight :
      id.SatisfiedBy Generated.Catalogue.S5_215.table.semigroup) :
    Derives sigma id.lhs id.rhs :=
  derivesOfClass id.lhs id.rhs headEq
    (S5_215Family.S5_215.valid_support id validRight)
    (S5_215Family.S5_215.valid_capped_length id validRight)

/-- Joint completeness for `S3_13 × S5_215`: the head seam is the
kernel-verified `headEq_s3_13` from the M2 transfer layer. -/
theorem intersectionComplete_s3_13 :
    ∀ id : Identity Nat,
      id.SatisfiedBy Generated.S3_13.table.semigroup →
      id.SatisfiedBy Generated.Catalogue.S5_215.table.semigroup →
      Derives sigma id.lhs id.rhs := by
  intro id validA validB
  exact intersectionCompleteOfHeadEq id
    (Order6FactorPairS3_13S5_213M2.headEq_s3_13 id validA) validB

/-- Joint completeness for `S3_15 × S5_215` via `headEq_s3_15`. -/
theorem intersectionComplete_s3_15 :
    ∀ id : Identity Nat,
      id.SatisfiedBy Generated.S3_15.table.semigroup →
      id.SatisfiedBy Generated.Catalogue.S5_215.table.semigroup →
      Derives sigma id.lhs id.rhs := by
  intro id validA validB
  exact intersectionCompleteOfHeadEq id
    (Order6FactorPairS3_13S5_213M2.headEq_s3_15 id validA) validB

/-! ## Finite model proofs and intersection-basis instances -/

private def sigmaVariable (value : Nat) : Fin 4 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 2
  else 3

theorem modelsS3_13_fourLaw :
    Models Generated.S3_13.table.semigroup sigma :=
  FiniteCertificate.checkModels_sound
    Generated.S3_13.table sigma sigmaVariable (by decide)

theorem modelsS3_15_fourLaw :
    Models Generated.S3_15.table.semigroup sigma :=
  FiniteCertificate.checkModels_sound
    Generated.S3_15.table sigma sigmaVariable (by decide)

theorem modelsS5_215_fourLaw :
    Models Generated.Catalogue.S5_215.table.semigroup sigma :=
  FiniteCertificate.checkModels_sound
    Generated.Catalogue.S5_215.table sigma sigmaVariable (by decide)

def intersectionBasisS3_13S5_215 :
    IntersectionBasis Generated.S3_13.table.semigroup
      Generated.Catalogue.S5_215.table.semigroup sigma where
  leftModels := modelsS3_13_fourLaw
  rightModels := modelsS5_215_fourLaw
  complete := intersectionComplete_s3_13

def intersectionBasisS3_15S5_215 :
    IntersectionBasis Generated.S3_15.table.semigroup
      Generated.Catalogue.S5_215.table.semigroup sigma where
  leftModels := modelsS3_15_fourLaw
  rightModels := modelsS5_215_fourLaw
  complete := intersectionComplete_s3_15

end SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_215FourLaw
