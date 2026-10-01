import SemigroupBasis.CoRoots.Order6LeeLiP2G4Endpoint
import SemigroupBasis.CoRoots.Order6LeeLiP2G4SeparationDataS6_8233
import SemigroupBasis.FiniteCertificate

/-!
# Lee--Li P2 group G4: finite-fingerprint injection bridge

`L5_mergeCollapse` reduces any pair of distinct G4 canonical forms to words
using at most four letters.  This module relabels that finite image into the
fixed alphabet `{0, 1, 2, 3}` and turns injective semantic fingerprints on the
resulting finite canonical inventory into `CanonicalSeparation`.

Concrete order-six members provide only:

* `Models G basisG4` (normally an exhaustive finite-table check),
* a finite list of separator valuations, and
* `Nodup` for the fingerprints of `canonicalInventory`.

The merge-collapse, relabeling, inventory completeness, semantic transport,
and final `BasisFor` assembly are shared here.
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G4.Injection

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6LeeLiP2G4

/-! ## The fixed four-generator canonical inventory -/

/-- All words of one fixed length over the alphabet `{0, 1, 2, 3}`. -/
def wordsOfLengthFour : Nat → List (List Nat)
  | 0 => [[]]
  | length + 1 =>
      (List.range 4).flatMap fun head =>
        ((wordsOfLengthFour length).filter fun tail =>
          decide (tail.count head < 2)).map (List.cons head)

/-- Fixed G4 canonical words of one length over four generators. -/
def canonicalInventoryAtLength (length : Nat) : List (List Nat) :=
  (wordsOfLengthFour length).filter fun word =>
    decide (canonicalG4 word = word)

/--
The fixed G4 fingerprint inventory.  A G4 canonical uses each of at most four
letters no more than twice, hence has length at most eight.  Filtering the
four-generator words by the fixed-point predicate gives the 1,424 canonical
forms used by every concrete G4 member.
-/
def canonicalInventory : List (List Nat) :=
  (List.range 8).flatMap fun offset =>
    canonicalInventoryAtLength (offset + 1)

private theorem mem_wordsOfLengthFour_of_bound
    {length : Nat} {letters : List Nat}
    (lengthEq : letters.length = length)
    (bounded : ∀ letter, letter ∈ letters → letter < 4)
    (reduced : Reduced letters) :
    letters ∈ wordsOfLengthFour length := by
  induction length generalizing letters with
  | zero =>
      have lettersEq : letters = [] :=
        List.eq_nil_of_length_eq_zero lengthEq
      subst letters
      simp [wordsOfLengthFour]
  | succ length ih =>
      cases letters with
      | nil => simp at lengthEq
      | cons head tail =>
          have headBound : head < 4 := bounded head (by simp)
          have tailBound : ∀ letter, letter ∈ tail → letter < 4 := by
            intro letter member
            exact bounded letter (by simp [member])
          have tailLength : tail.length = length := by
            simpa using Nat.succ.inj lengthEq
          have tailReduced : Reduced tail := by
            intro letter
            have countBound := reduced letter
            by_cases same : letter = head
            · subst letter
              rw [List.count_cons_self] at countBound
              omega
            · simpa only [List.count_cons_of_ne (Ne.symm same)] using countBound
          have headCount : tail.count head < 2 := by
            have countBound := reduced head
            rw [List.count_cons_self] at countBound
            omega
          rw [wordsOfLengthFour]
          apply List.mem_flatMap.mpr
          refine ⟨head, List.mem_range.mpr headBound, ?_⟩
          apply List.mem_map.mpr
          refine ⟨tail, List.mem_filter.mpr ⟨?_, decide_eq_true headCount⟩, rfl⟩
          exact ih tailLength tailBound tailReduced

private theorem emitAt_member_source
    {word : List Nat} {site letter output : Nat}
    (member : output ∈ emitAt word site letter) :
    output = letter := by
  unfold emitAt at member
  split at member
  · simpa using member
  · split at member
    · split at member <;> simp_all
    · split at member <;> simp_all

private theorem canonicalG4_member_source
    {word : List Nat} {letter : Nat}
    (member : letter ∈ canonicalG4 word) :
    letter ∈ word := by
  unfold canonicalG4 at member
  rcases List.mem_flatten.mp member with ⟨emitted, emittedMember, member⟩
  rcases List.mem_map.mp emittedMember with ⟨site, siteMember, rfl⟩
  have letterEq := emitAt_member_source member
  subst letter
  exact List.fst_mem_of_mem_zipIdx siteMember

private theorem length_eq_four_counts
    (letters : List Nat)
    (bounded : ∀ letter, letter ∈ letters → letter < 4) :
    letters.length =
      letters.count 0 + letters.count 1 +
        letters.count 2 + letters.count 3 := by
  induction letters with
  | nil => simp
  | cons head tail ih =>
      have headBound : head < 4 := bounded head (by simp)
      have tailBound : ∀ letter, letter ∈ tail → letter < 4 := by
        intro letter member
        exact bounded letter (by simp [member])
      have headCases : head = 0 ∨ head = 1 ∨ head = 2 ∨ head = 3 := by
        omega
      rcases headCases with rfl | rfl | rfl | rfl <;>
        simp [ih tailBound, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm]

private theorem length_le_eight_of_reduced_four
    {letters : List Nat} (reduced : Reduced letters)
    (bounded : ∀ letter, letter ∈ letters → letter < 4) :
    letters.length ≤ 8 := by
  have lengthEq := length_eq_four_counts letters bounded
  have count0 := reduced 0
  have count1 := reduced 1
  have count2 := reduced 2
  have count3 := reduced 3
  omega

private theorem canonicalG4_idempotent (word : List Nat) :
    canonicalG4 (canonicalG4 word) = canonicalG4 word := by
  obtain ⟨reduced, fixed⟩ := canonical_normal word
  calc
    canonicalG4 (canonicalG4 word) =
        canonicalReduced (canonicalG4 word) :=
      canonicalReduced_eq reduced
    _ = canonicalG4 word := fixed

/-- Every nonempty word over `{0,1,2,3}` has its G4 canonical in the fixed
inventory. -/
theorem canonicalG4_mem_canonicalInventory
    (word : List Nat) (nonempty : word ≠ [])
    (bounded : ∀ letter, letter ∈ word → letter < 4) :
    canonicalG4 word ∈ canonicalInventory := by
  have canonicalNonempty : canonicalG4 word ≠ [] :=
    canonical_ne word nonempty
  have canonicalReduced : Reduced (canonicalG4 word) :=
    (canonical_normal word).1
  have canonicalBounded :
      ∀ letter, letter ∈ canonicalG4 word → letter < 4 := by
    intro letter member
    exact bounded letter (canonicalG4_member_source member)
  have lengthPositive : 0 < (canonicalG4 word).length :=
    List.length_pos_iff.mpr canonicalNonempty
  have lengthBound : (canonicalG4 word).length ≤ 8 :=
    length_le_eight_of_reduced_four canonicalReduced canonicalBounded
  have offsetBound : (canonicalG4 word).length - 1 < 8 := by omega
  have lengthEq :
      (canonicalG4 word).length =
        ((canonicalG4 word).length - 1) + 1 := by omega
  unfold canonicalInventory
  apply List.mem_flatMap.mpr
  refine ⟨(canonicalG4 word).length - 1,
    List.mem_range.mpr offsetBound, ?_⟩
  unfold canonicalInventoryAtLength
  apply List.mem_filter.mpr
  exact ⟨mem_wordsOfLengthFour_of_bound lengthEq canonicalBounded
      canonicalReduced,
    decide_eq_true (canonicalG4_idempotent word)⟩

/-! ## Kernel bridge to the generated finite inventory -/

/-- The nonempty word represented by one entry of the G4 inventory. -/
abbrev canonicalWord (letters : List Nat) : Word Nat :=
  wordOfD letters

section InventoryKernelChecks

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

private theorem canonicalWords_length_one :
    (canonicalInventoryAtLength 1).map canonicalWord =
      S6_8233Data.canonicalsLength1 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8233Data.canonicalsLength1,
      S6_8233Data.canonicalsLength1Chunk0, canonicalG4, emitAt,
      lastIdx, sndLastIdx, wordOfD, List.flatMap, List.flatten,
      List.filter, List.map, List.range, List.range.loop, List.count,
      Function.comp_def]

private theorem canonicalWords_length_two :
    (canonicalInventoryAtLength 2).map canonicalWord =
      S6_8233Data.canonicalsLength2 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8233Data.canonicalsLength2,
      S6_8233Data.canonicalsLength2Chunk0, canonicalG4, emitAt,
      lastIdx, sndLastIdx, wordOfD, List.flatMap, List.flatten,
      List.filter, List.map, List.range, List.range.loop, List.count,
      Function.comp_def]

private theorem canonicalWords_length_three :
    (canonicalInventoryAtLength 3).map canonicalWord =
      S6_8233Data.canonicalsLength3 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8233Data.canonicalsLength3,
      S6_8233Data.canonicalsLength3Chunk0, canonicalG4, emitAt,
      lastIdx, sndLastIdx, wordOfD, List.flatMap, List.flatten,
      List.filter, List.map, List.range, List.range.loop, List.count,
      Function.comp_def]

private theorem canonicalWords_length_four :
    (canonicalInventoryAtLength 4).map canonicalWord =
      S6_8233Data.canonicalsLength4 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8233Data.canonicalsLength4,
      S6_8233Data.canonicalsLength4Chunk0,
      S6_8233Data.canonicalsLength4Chunk1, canonicalG4, emitAt,
      lastIdx, sndLastIdx, wordOfD, List.flatMap, List.flatten,
      List.filter, List.map, List.range, List.range.loop, List.count,
      Function.comp_def]

private theorem canonicalWords_length_five :
    (canonicalInventoryAtLength 5).map canonicalWord =
      S6_8233Data.canonicalsLength5 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8233Data.canonicalsLength5,
      S6_8233Data.canonicalsLength5Chunk0,
      S6_8233Data.canonicalsLength5Chunk1,
      S6_8233Data.canonicalsLength5Chunk2, canonicalG4, emitAt,
      lastIdx, sndLastIdx, wordOfD, List.flatMap, List.flatten,
      List.filter, List.map, List.range, List.range.loop, List.count,
      Function.comp_def]

private theorem canonicalWords_length_six :
    (canonicalInventoryAtLength 6).map canonicalWord =
      S6_8233Data.canonicalsLength6 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8233Data.canonicalsLength6,
      S6_8233Data.canonicalsLength6Chunk0,
      S6_8233Data.canonicalsLength6Chunk1,
      S6_8233Data.canonicalsLength6Chunk2,
      S6_8233Data.canonicalsLength6Chunk3, canonicalG4, emitAt,
      lastIdx, sndLastIdx, wordOfD, List.flatMap, List.flatten,
      List.filter, List.map, List.range, List.range.loop, List.count,
      Function.comp_def]

private theorem canonicalWords_length_seven :
    (canonicalInventoryAtLength 7).map canonicalWord =
      S6_8233Data.canonicalsLength7 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8233Data.canonicalsLength7,
      S6_8233Data.canonicalsLength7Chunk0,
      S6_8233Data.canonicalsLength7Chunk1,
      S6_8233Data.canonicalsLength7Chunk2, canonicalG4, emitAt,
      lastIdx, sndLastIdx, wordOfD, List.flatMap, List.flatten,
      List.filter, List.map, List.range, List.range.loop, List.count,
      Function.comp_def]

private theorem canonicalWords_length_eight :
    (canonicalInventoryAtLength 8).map canonicalWord =
      S6_8233Data.canonicalsLength8 := by
  simp (config := { maxSteps := 5000000 }) +decide
    [canonicalInventoryAtLength, canonicalWord, wordsOfLengthFour,
      S6_8233Data.canonicalsLength8,
      S6_8233Data.canonicalsLength8Chunk0, canonicalG4, emitAt,
      lastIdx, sndLastIdx, wordOfD, List.flatMap, List.flatten,
      List.filter, List.map, List.range, List.range.loop, List.count,
      Function.comp_def]

theorem canonicalWords_eq_separationData :
    canonicalInventory.map canonicalWord = S6_8233Data.canonicals := by
  have inventory_eq :
      canonicalInventory =
        canonicalInventoryAtLength 1 ++
          canonicalInventoryAtLength 2 ++
          canonicalInventoryAtLength 3 ++
          canonicalInventoryAtLength 4 ++
          canonicalInventoryAtLength 5 ++
          canonicalInventoryAtLength 6 ++
          canonicalInventoryAtLength 7 ++
          canonicalInventoryAtLength 8 := by
    rfl
  rw [inventory_eq]
  simp only [List.map_append]
  rw [canonicalWords_length_one, canonicalWords_length_two,
    canonicalWords_length_three, canonicalWords_length_four,
    canonicalWords_length_five, canonicalWords_length_six,
    canonicalWords_length_seven, canonicalWords_length_eight]
  rfl

end InventoryKernelChecks

/-! ## Relabel an L5 image into the fixed four-generator alphabet -/

/-- Encode a letter by its first position in the finite L5 image list. -/
def encodeImage (image : List Nat) (letter : Nat) : Nat :=
  List.idxOf letter image

/-- Decode an in-range image position; out-of-range values are irrelevant. -/
def decodeImage : List Nat → Nat → Nat
  | [], _ => 0
  | head :: _, 0 => head
  | _ :: tail, code + 1 => decodeImage tail code

private theorem decodeImage_encodeImage_of_mem
    {image : List Nat} {letter : Nat} (member : letter ∈ image) :
    decodeImage image (encodeImage image letter) = letter := by
  induction image with
  | nil => simp at member
  | cons head tail ih =>
      by_cases same : letter = head
      · subst letter
        simp [encodeImage, decodeImage, List.idxOf_cons]
      · have tailMember : letter ∈ tail := by
          exact (List.mem_cons.mp member).resolve_left same
        have different : head ≠ letter := fun equality =>
          same equality.symm
        have indexEq :
            List.idxOf letter (head :: tail) =
              List.idxOf letter tail + 1 := by
          rw [List.idxOf_cons,
            beq_eq_false_iff_ne.mpr different]
          rfl
        change decodeImage (head :: tail)
          (List.idxOf letter (head :: tail)) = letter
        rw [indexEq]
        simpa only [decodeImage, encodeImage] using ih tailMember

private theorem map_decodeImage_encodeImage
    (image letters : List Nat)
    (covered : ∀ letter, letter ∈ letters → letter ∈ image) :
    (letters.map (encodeImage image)).map (decodeImage image) = letters := by
  induction letters with
  | nil => rfl
  | cons head tail ih =>
      have headCovered : head ∈ image := covered head (by simp)
      have tailCovered : ∀ letter, letter ∈ tail → letter ∈ image := by
        intro letter member
        exact covered letter (by simp [member])
      simp only [List.map_cons]
      rw [decodeImage_encodeImage_of_mem headCovered]
      exact congrArg (List.cons head) (ih tailCovered)

private theorem map_ne_nil {letters : List Nat} (nonempty : letters ≠ [])
    (rename : Nat → Nat) :
    letters.map rename ≠ [] := by
  cases letters with
  | nil => exact (nonempty rfl).elim
  | cons head tail => simp

private theorem mapped_left_covered
    {sigma : Nat → Nat} {left right image : List Nat}
    (bounded : ImageBound sigma left right image) :
    ∀ letter, letter ∈ left.map sigma → letter ∈ image := by
  intro letter member
  rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
  exact bounded source (by simp [sourceMember])

private theorem mapped_right_covered
    {sigma : Nat → Nat} {left right image : List Nat}
    (bounded : ImageBound sigma left right image) :
    ∀ letter, letter ∈ right.map sigma → letter ∈ image := by
  intro letter member
  rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
  exact bounded source (by simp [sourceMember])

private theorem encoded_lt_four
    {image letters : List Nat} (imageLength : image.length ≤ 4)
    (covered : ∀ letter, letter ∈ letters → letter ∈ image) :
    ∀ code, code ∈ letters.map (encodeImage image) → code < 4 := by
  intro code member
  rcases List.mem_map.mp member with ⟨letter, letterMember, rfl⟩
  exact Nat.lt_of_lt_of_le
    (List.idxOf_lt_length_of_mem (covered letter letterMember)) imageLength

private theorem canonical_ne_after_image_encoding
    {left right image : List Nat} {sigma : Nat → Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (imageBound : ImageBound sigma left right image)
    (different :
      canonicalG4 (left.map sigma) ≠ canonicalG4 (right.map sigma)) :
    canonicalG4 ((left.map sigma).map (encodeImage image)) ≠
      canonicalG4 ((right.map sigma).map (encodeImage image)) := by
  intro encodedEqual
  apply different
  have leftMappedNonempty := map_ne_nil leftNonempty sigma
  have rightMappedNonempty := map_ne_nil rightNonempty sigma
  have leftEncodedNonempty :=
    map_ne_nil leftMappedNonempty (encodeImage image)
  have rightEncodedNonempty :=
    map_ne_nil rightMappedNonempty (encodeImage image)
  have leftRoundTrip :
      ((left.map sigma).map (encodeImage image)).map (decodeImage image) =
        left.map sigma :=
    map_decodeImage_encodeImage image (left.map sigma)
      (mapped_left_covered imageBound)
  have rightRoundTrip :
      ((right.map sigma).map (encodeImage image)).map (decodeImage image) =
        right.map sigma :=
    map_decodeImage_encodeImage image (right.map sigma)
      (mapped_right_covered imageBound)
  have decodedEqual :=
    congrArg (List.map (decodeImage image)) encodedEqual
  calc
    canonicalG4 (left.map sigma) =
        canonicalG4
          (((left.map sigma).map (encodeImage image)).map
            (decodeImage image)) := by rw [leftRoundTrip]
    _ = canonicalG4
          ((canonicalG4
            ((left.map sigma).map (encodeImage image))).map
              (decodeImage image)) :=
      L3_canonFactor
        (canonical := canonicalG4)
        (canonicalSound := canonicalSound)
        (derives_canonical := derives_canonical)
        (canonical_ne := canonical_ne)
        (decodeImage image)
        ((left.map sigma).map (encodeImage image)) leftEncodedNonempty
    _ = canonicalG4
          ((canonicalG4
            ((right.map sigma).map (encodeImage image))).map
              (decodeImage image)) := congrArg canonicalG4 decodedEqual
    _ = canonicalG4
          (((right.map sigma).map (encodeImage image)).map
            (decodeImage image)) :=
      (L3_canonFactor
        (canonical := canonicalG4)
        (canonicalSound := canonicalSound)
        (derives_canonical := derives_canonical)
        (canonical_ne := canonical_ne)
        (decodeImage image)
        ((right.map sigma).map (encodeImage image))
        rightEncodedNonempty).symm
    _ = canonicalG4 (right.map sigma) := by rw [rightRoundTrip]

/-! ## Semantic fingerprints and the generic endpoint -/

/-- Interpret a stored list of table values as a valuation on `Nat`. -/
def separatorValuation (values : List Nat) (letter : Nat) : Fin 6 :=
  ⟨values.getD letter 0 % 6, Nat.mod_lt _ (by decide)⟩

/-- Semantic fingerprint of one nonempty G4 canonical form. -/
def memberFingerprint (G : Semigroup (Fin 6))
    (separatorValuations : List (List Nat))
    (letters : List Nat) : List Nat :=
  separatorValuations.map fun values =>
    (G.eval (separatorValuation values) (wordOfD letters)).val

private theorem map_injective_on_of_nodup
    {entries : List α} {project : α → β}
    (mappedNodup : (entries.map project).Nodup)
    {left right : α}
    (leftMember : left ∈ entries) (rightMember : right ∈ entries)
    (sameImage : project left = project right) :
    left = right := by
  induction entries with
  | nil => simp at leftMember
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at mappedNodup
      rcases mappedNodup with ⟨headAbsent, tailNodup⟩
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember <;>
        rcases rightMember with rfl | rightMember
      · rfl
      · exfalso
        apply headAbsent
        rw [sameImage]
        exact List.mem_map.mpr ⟨right, rightMember, rfl⟩
      · exfalso
        apply headAbsent
        rw [← sameImage]
        exact List.mem_map.mpr ⟨left, leftMember, rfl⟩
      · exact ih tailNodup leftMember rightMember

private theorem exists_separator_of_memberFingerprint_ne
    (G : Semigroup (Fin 6)) (separatorValuations : List (List Nat))
    {left right : List Nat}
    (different :
      memberFingerprint G separatorValuations left ≠
        memberFingerprint G separatorValuations right) :
    ∃ values, values ∈ separatorValuations ∧
      G.eval (separatorValuation values) (wordOfD left) ≠
        G.eval (separatorValuation values) (wordOfD right) := by
  apply Classical.byContradiction
  intro noSeparator
  apply different
  unfold memberFingerprint
  apply List.map_congr_left
  intro values member
  by_cases sameValue :
      G.eval (separatorValuation values) (wordOfD left) =
        G.eval (separatorValuation values) (wordOfD right)
  · exact congrArg Fin.val sameValue
  · exact False.elim <| noSeparator ⟨values, member, sameValue⟩

private theorem wordOfD_map
    (letters : List Nat) (rename : Nat → Nat) (nonempty : letters ≠ []) :
    (wordOfD letters).map rename = wordOfD (letters.map rename) := by
  cases letters with
  | nil => exact (nonempty rfl).elim
  | cons head tail => rfl

/-- Fingerprint injectivity on the fixed inventory implies G4 canonical
separation for a concrete order-six semigroup. -/
theorem canonicalSeparation_of_fingerprints
    (G : Semigroup (Fin 6)) (models : Models G basisG4)
    (separatorValuations : List (List Nat))
    (fingerprintsNodup :
      (canonicalInventory.map
        (memberFingerprint G separatorValuations)).Nodup) :
    CanonicalSeparation G := by
  intro left right leftNonempty rightNonempty valid
  apply Classical.byContradiction
  intro different
  obtain ⟨sigma, image, imageLength, imageBound, mappedDifferent⟩ :=
    L5_mergeCollapse
      (canonical := canonicalG4)
      (canonicalSound := canonicalSound)
      (derives_canonical := derives_canonical)
      (canonical_ne := canonical_ne)
      (canonical_normal := canonical_normal)
      (canonical_blob_reduces := canonical_blob_reduces)
      leftNonempty rightNonempty different
  let encodedLeft := (left.map sigma).map (encodeImage image)
  let encodedRight := (right.map sigma).map (encodeImage image)
  have mappedLeftNonempty := map_ne_nil leftNonempty sigma
  have mappedRightNonempty := map_ne_nil rightNonempty sigma
  have encodedLeftNonempty : encodedLeft ≠ [] := by
    exact map_ne_nil mappedLeftNonempty (encodeImage image)
  have encodedRightNonempty : encodedRight ≠ [] := by
    exact map_ne_nil mappedRightNonempty (encodeImage image)
  have encodedDifferent :
      canonicalG4 encodedLeft ≠ canonicalG4 encodedRight := by
    simpa only [encodedLeft, encodedRight] using
      canonical_ne_after_image_encoding leftNonempty rightNonempty
        imageBound mappedDifferent
  have leftCovered := mapped_left_covered imageBound
  have rightCovered := mapped_right_covered imageBound
  have encodedLeftBounded :
      ∀ letter, letter ∈ encodedLeft → letter < 4 := by
    simpa only [encodedLeft] using
      encoded_lt_four imageLength leftCovered
  have encodedRightBounded :
      ∀ letter, letter ∈ encodedRight → letter < 4 := by
    simpa only [encodedRight] using
      encoded_lt_four imageLength rightCovered
  have leftMember : canonicalG4 encodedLeft ∈ canonicalInventory :=
    canonicalG4_mem_canonicalInventory encodedLeft encodedLeftNonempty
      encodedLeftBounded
  have rightMember : canonicalG4 encodedRight ∈ canonicalInventory :=
    canonicalG4_mem_canonicalInventory encodedRight encodedRightNonempty
      encodedRightBounded
  have fingerprintsDifferent :
      memberFingerprint G separatorValuations (canonicalG4 encodedLeft) ≠
        memberFingerprint G separatorValuations
          (canonicalG4 encodedRight) := by
    intro sameFingerprint
    apply encodedDifferent
    exact map_injective_on_of_nodup fingerprintsNodup
      leftMember rightMember sameFingerprint
  obtain ⟨values, _, separatedValues⟩ :=
    exists_separator_of_memberFingerprint_ne G separatorValuations
      fingerprintsDifferent
  have firstMappedValid :
      ({ lhs := wordOfD (left.map sigma)
         rhs := wordOfD (right.map sigma) } : Identity Nat).SatisfiedBy G := by
    simpa only [Identity.map,
      wordOfD_map left sigma leftNonempty,
      wordOfD_map right sigma rightNonempty] using
      Identity.satisfiedBy_map
        ({ lhs := wordOfD left, rhs := wordOfD right } : Identity Nat)
        sigma G valid
  have encodedValid :
      ({ lhs := wordOfD encodedLeft
         rhs := wordOfD encodedRight } : Identity Nat).SatisfiedBy G := by
    simpa only [Identity.map, encodedLeft, encodedRight,
      wordOfD_map (left.map sigma) (encodeImage image) mappedLeftNonempty,
      wordOfD_map (right.map sigma) (encodeImage image)
        mappedRightNonempty] using
      Identity.satisfiedBy_map
        ({ lhs := wordOfD (left.map sigma)
           rhs := wordOfD (right.map sigma) } : Identity Nat)
        (encodeImage image) G firstMappedValid
  have validValues := encodedValid (separatorValuation values)
  have leftSound := Derives.sound models
    (derives_canonical encodedLeft encodedLeftNonempty)
    (separatorValuation values)
  have rightSound := Derives.sound models
    (derives_canonical encodedRight encodedRightNonempty)
    (separatorValuation values)
  exact separatedValues
    (leftSound.symm.trans (validValues.trans rightSound))

/-- Final reusable endpoint: finite table validity plus one finite fingerprint
certificate proves the displayed G4 laws are a basis. -/
theorem basisFor_of_fingerprints
    (G : Semigroup (Fin 6)) (models : Models G basisG4)
    (separatorValuations : List (List Nat))
    (fingerprintsNodup :
      (canonicalInventory.map
        (memberFingerprint G separatorValuations)).Nodup) :
    BasisFor G basisG4 :=
  basisFor_of_models_canonicalSeparation models
    (canonicalSeparation_of_fingerprints G models separatorValuations
      fingerprintsNodup)

end SemigroupBasis.CoRoots.Order6LeeLiP2G4.Injection
