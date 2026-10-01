import SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_240Obstruction
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_240

open SemigroupBasis
open SemigroupBasis.Examples

private def word (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private theorem retargetDerives
    {source target newSource newTarget : Word Nat}
    (derivation : Derives basis source target)
    (sourceToList : source.toList = newSource.toList)
    (targetToList : target.toList = newTarget.toList) :
    Derives basis newSource newTarget := by
  have sourceEq : source = newSource :=
    Word.toList_injective sourceToList
  have targetEq : target = newTarget :=
    Word.toList_injective targetToList
  cases sourceEq
  cases targetEq
  exact derivation

private def instantiateFourWords
    (x y z t : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

private theorem powerLaw_mem :
    Identity.mk (word 0 [0]) (word 0 [0, 0]) ∈ basis := by
  simp [basis, recordedBasis, word, w]

private theorem eraseLeadingFinalLaw_mem :
    Identity.mk (word 0 [0, 1, 0]) (word 0 [1, 0]) ∈ basis := by
  simp [basis, recordedBasis, word, w]

private theorem squareInterleaveLaw_mem :
    Identity.mk (word 0 [0, 1, 1]) (word 0 [1, 0, 1]) ∈ basis := by
  simp [basis, recordedBasis, word, w]

private theorem squareFinalLaw_mem :
    Identity.mk (word 0 [0, 1, 1]) (word 0 [1, 1, 0]) ∈ basis := by
  simp [basis, recordedBasis, word, w]

private theorem finalSquareInsertionLaw_mem :
    Identity.mk (word 0 [1, 1]) (word 1 [0, 1, 1]) ∈ basis := by
  simp [basis, recordedBasis, word, w]

private theorem prefixSwapLaw_mem : prefixSwapLaw ∈ basis := by
  simp [basis]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis (word 0 [0]) (word 0 [0, 0]) :=
    Derives.fromBasis powerLaw_mem
  have substituted :=
    Derives.subst base (instantiateFourWords u u u u)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

/-- Delete one copy of a block which occurs twice at the left and once at the
right of a nonempty middle block. -/
theorem derivesEraseLeadingFinal (u middle : Word Nat) :
    Derives basis (((u ++ u) ++ middle) ++ u) ((u ++ middle) ++ u) := by
  have base :
      Derives basis (word 0 [0, 1, 0]) (word 0 [1, 0]) :=
    Derives.fromBasis eraseLeadingFinalLaw_mem
  have substituted :=
    Derives.subst base (instantiateFourWords u middle middle middle)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareInterleave (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ u) ++ v) := by
  have base :
      Derives basis (word 0 [0, 1, 1]) (word 0 [1, 0, 1]) :=
    Derives.fromBasis squareInterleaveLaw_mem
  have substituted :=
    Derives.subst base (instantiateFourWords u v v v)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesSquareFinal (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      (((u ++ v) ++ v) ++ u) := by
  have base :
      Derives basis (word 0 [0, 1, 1]) (word 0 [1, 1, 0]) :=
    Derives.fromBasis squareFinalLaw_mem
  have substituted :=
    Derives.subst base (instantiateFourWords u v v v)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesFinalSquareInsertion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ v) (((v ++ u) ++ v) ++ v) := by
  have base :
      Derives basis (word 0 [1, 1]) (word 1 [0, 1, 1]) :=
    Derives.fromBasis finalSquareInsertionLaw_mem
  have substituted :=
    Derives.subst base (instantiateFourWords u v v v)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesFinalSquareContraction (u v : Word Nat) :
    Derives basis (((v ++ u) ++ v) ++ v) ((u ++ v) ++ v) :=
  (derivesFinalSquareInsertion u v).symm

/-- Swap arbitrary nonempty prefix blocks before two fixed nonempty suffix
blocks. -/
theorem derivesPrefixSwap (u v q r : Word Nat) :
    Derives basis (((u ++ v) ++ q) ++ r)
      (((v ++ u) ++ q) ++ r) := by
  have base : Derives basis prefixSwapLaw.lhs prefixSwapLaw.rhs :=
    Derives.fromBasis prefixSwapLaw_mem
  have substituted :=
    Derives.subst base (instantiateFourWords u v q r)
  simpa [prefixSwapLaw, word, w, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Two square blocks commute. -/
theorem derivesSquareCommutation (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      ((v ++ v) ++ (u ++ u)) := by
  have first := derivesSquareFinal u v
  have second := derivesPrefixSwap u v v u
  have third := (derivesSquareInterleave v u).symm
  exact first.trans <| second.trans third

def wordOfTerminalPair
    (stem : List Nat) (penultimate final : Nat) : Word Nat :=
  SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair
    stem penultimate final

@[simp]
theorem toList_wordOfTerminalPair
    (stem : List Nat) (penultimate final : Nat) :
    (wordOfTerminalPair stem penultimate final).toList =
      stem ++ [penultimate, final] := by
  simp [wordOfTerminalPair,
    SemigroupBasis.CoRoots.S5_240.toList_wordOfTerminalPair]

@[simp]
private theorem wordOfPrefixFinal_append_singleton
    (stem : List Nat) (penultimate final : Nat) :
    SemigroupBasis.Examples.wordOfPrefixFinal stem penultimate ++
        Word.singleton final =
      SemigroupBasis.Examples.wordOfPrefixFinal
        (stem ++ [penultimate]) final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    SemigroupBasis.Examples.toList_wordOfPrefixFinal,
    SemigroupBasis.Examples.toList_wordOfPrefixFinal]

/-- Every permutation before two fixed endpoint variables follows from the
new square-free law. -/
theorem derivesPrefixPermutation
    {prefix1 prefix2 : List Nat}
    (permutation : prefix1.Perm prefix2)
    (penultimate final : Nat) :
    Derives basis
      (wordOfTerminalPair prefix1 penultimate final)
      (wordOfTerminalPair prefix2 penultimate final) := by
  induction permutation with
  | nil => exact Derives.refl _
  | cons x _ induction =>
      simpa [wordOfTerminalPair,
        SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair,
        SemigroupBasis.Examples.wordOfPrefixFinal,
        List.append_assoc] using
        Derives.prepend (Word.singleton x) induction
  | swap x y suffix =>
      apply retargetDerives <|
        derivesPrefixSwap
          (Word.singleton y) (Word.singleton x)
          (SemigroupBasis.Examples.wordOfPrefixFinal suffix penultimate)
          (Word.singleton final)
      · rw [toList_wordOfTerminalPair]
        simp only [Word.toList_append, Word.toList_singleton,
          SemigroupBasis.Examples.toList_wordOfPrefixFinal]
        simp [List.append_assoc]
      · rw [toList_wordOfTerminalPair]
        simp only [Word.toList_append, Word.toList_singleton,
          SemigroupBasis.Examples.toList_wordOfPrefixFinal]
        simp [List.append_assoc]
  | trans _ _ first second => exact first.trans second

/-- Retain only the prefix occurrences needed to make the total multiplicity,
including the two endpoint positions, at most two. -/
def capPrefix : List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | x :: xs, penultimate, final =>
      let reduced := capPrefix xs penultimate final
      if (reduced ++ [penultimate, final]).count x < 2 then
        x :: reduced
      else
        reduced

theorem count_capPrefix_total
    (tested : Nat) : ∀ stem penultimate final,
    (capPrefix stem penultimate final ++
        [penultimate, final]).count tested =
      min ((stem ++ [penultimate, final]).count tested) 2
  | [], penultimate, final => by
      have bound :=
        List.count_le_length
          (a := tested) (l := [penultimate, final])
      have boundTwo : [penultimate, final].count tested ≤ 2 := by
        simpa using bound
      simp only [capPrefix, List.nil_append]
      exact (Nat.min_eq_left boundTwo).symm
  | x :: xs, penultimate, final => by
      simp only [capPrefix]
      split <;> rename_i retained
      · simp only [List.cons_append]
        by_cases equal : tested = x
        · subst tested
          rw [List.count_cons_self, List.count_cons_self,
            count_capPrefix_total]
          rw [count_capPrefix_total] at retained
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal),
            List.count_cons_of_ne (Ne.symm equal),
            count_capPrefix_total]
      · simp only [List.cons_append]
        by_cases equal : tested = x
        · subst tested
          rw [List.count_cons_self, count_capPrefix_total]
          rw [count_capPrefix_total] at retained
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal),
            count_capPrefix_total]

private theorem perm_cons_to_end (a : Nat) :
    ∀ stem : List Nat, (a :: stem).Perm (stem ++ [a])
  | [] => List.Perm.refl _
  | x :: xs =>
      (List.Perm.swap x a xs).trans <|
        List.Perm.cons x (perm_cons_to_end a xs)

private theorem perm_two_to_end (a b : Nat) :
    ∀ stem : List Nat, (a :: b :: stem).Perm (stem ++ [a, b])
  | [] => List.Perm.refl _
  | x :: xs =>
      (List.Perm.cons a (List.Perm.swap x b xs)).trans <|
        (List.Perm.swap x a (b :: xs)).trans <|
          List.Perm.cons x (perm_two_to_end a b xs)

private theorem perm_three_to_end (a b c : Nat) :
    ∀ stem : List Nat,
      (a :: b :: c :: stem).Perm (stem ++ [a, b, c])
  | [] => List.Perm.refl _
  | x :: xs => by
      have move :
          (a :: b :: c :: x :: xs).Perm
            (x :: a :: b :: c :: xs) := by
        exact
          (List.Perm.cons a <| List.Perm.cons b <|
            List.Perm.swap x c xs).trans <|
          (List.Perm.cons a <| List.Perm.swap x b (c :: xs)).trans <|
          List.Perm.swap x a (b :: c :: xs)
      exact move.trans <|
        List.Perm.cons x (perm_three_to_end a b c xs)

private theorem prepend_optional
    {left right : Word Nat}
    (pref : List Nat) (derivation : Derives basis left right) :
    Derives basis
      (match pref with
        | [] => left
        | x :: xs => word x xs ++ left)
      (match pref with
        | [] => right
        | x :: xs => word x xs ++ right) := by
  cases pref with
  | nil => exact derivation
  | cons x xs => exact Derives.prepend (word x xs) derivation

@[simp]
private theorem toList_prepend_optional
    (pref : List Nat) (suffix : Word Nat) :
    (match pref with
      | [] => suffix
      | x :: xs => word x xs ++ suffix).toList =
      pref ++ suffix.toList := by
  cases pref <;> simp [word, Word.toList, List.append_assoc]

private theorem derivesDeleteLeadingPrefix
    (x : Nat) (stem : List Nat) (penultimate final : Nat)
    (repeated : 2 ≤ (stem ++ [penultimate, final]).count x) :
    Derives basis
      (wordOfTerminalPair (x :: stem) penultimate final)
      (wordOfTerminalPair stem penultimate final) := by
  by_cases penultimateEq : penultimate = x
  · subst penultimate
    by_cases finalEq : final = x
    · subst final
      cases stem with
      | nil =>
          simpa [wordOfTerminalPair,
            SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair,
            SemigroupBasis.Examples.wordOfPrefixFinal,
            word, Word.singleton, Word.append,
            Word.append_assoc] using
            derivesPowerContraction (Word.singleton x)
      | cons head tail =>
          apply retargetDerives
            (derivesFinalSquareContraction
              (word head tail) (Word.singleton x))
          · rw [toList_wordOfTerminalPair]
            simp [word, Word.toList, List.append_assoc]
          · rw [toList_wordOfTerminalPair]
            simp [word, Word.toList, List.append_assoc]
    · have member : x ∈ stem := by
        have suffixCount : [x, final].count x = 1 := by
          simp [finalEq]
        rw [List.count_append, suffixCount] at repeated
        exact List.count_pos_iff.mp (by omega)
      have arrange : stem.Perm (x :: stem.erase x) :=
        List.perm_cons_erase member
      have enter :=
        Derives.prepend (Word.singleton x)
          (derivesPrefixPermutation arrange x final)
      have contract :
          Derives basis
            (wordOfTerminalPair (x :: x :: stem.erase x) x final)
            (wordOfTerminalPair (x :: stem.erase x) x final) := by
        cases erased : stem.erase x with
        | nil =>
            have raw := Derives.appendRight
              (derivesPowerContraction (Word.singleton x))
              (Word.singleton final)
            simpa [wordOfTerminalPair,
              SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair,
              SemigroupBasis.Examples.wordOfPrefixFinal,
              word, Word.singleton, Word.append,
              Word.append_assoc, erased] using raw
        | cons head tail =>
            have raw := Derives.appendRight
              (derivesEraseLeadingFinal
                (Word.singleton x) (word head tail))
              (Word.singleton final)
            apply retargetDerives raw
            · rw [toList_wordOfTerminalPair]
              simp [erased, word, Word.toList, List.append_assoc]
            · rw [toList_wordOfTerminalPair]
              simp [erased, word, Word.toList, List.append_assoc]
      exact enter.trans <| contract.trans <|
        derivesPrefixPermutation arrange.symm x final
  · by_cases finalEq : final = x
    · subst final
      have member : x ∈ stem := by
        have suffixCount : [penultimate, x].count x = 1 := by
          simp [penultimateEq]
        rw [List.count_append, suffixCount] at repeated
        exact List.count_pos_iff.mp (by omega)
      have arrange : stem.Perm (x :: stem.erase x) :=
        List.perm_cons_erase member
      have enter :=
        Derives.prepend (Word.singleton x)
          (derivesPrefixPermutation arrange penultimate x)
      have raw :=
        derivesEraseLeadingFinal
          (Word.singleton x)
          (SemigroupBasis.Examples.wordOfPrefixFinal
            (stem.erase x) penultimate)
      have contract :
          Derives basis
            (wordOfTerminalPair
              (x :: x :: stem.erase x) penultimate x)
            (wordOfTerminalPair
              (x :: stem.erase x) penultimate x) := by
        apply retargetDerives raw
        · rw [toList_wordOfTerminalPair]
          simp only [Word.toList_append, Word.toList_singleton,
            SemigroupBasis.Examples.toList_wordOfPrefixFinal]
          simp [List.append_assoc]
        · rw [toList_wordOfTerminalPair]
          simp only [Word.toList_append, Word.toList_singleton,
            SemigroupBasis.Examples.toList_wordOfPrefixFinal]
          simp [List.append_assoc]
      exact enter.trans <| contract.trans <|
        derivesPrefixPermutation arrange.symm penultimate x
    · have countStem : 2 ≤ stem.count x := by
        rw [List.count_append] at repeated
        simp [penultimateEq, finalEq] at repeated
        omega
      have firstMember : x ∈ stem :=
        List.count_pos_iff.mp (by omega)
      have erasedCount : (stem.erase x).count x = stem.count x - 1 := by
        rw [List.count_erase_self]
      have secondMember : x ∈ stem.erase x :=
        List.count_pos_iff.mp (by omega)
      let remainder := (stem.erase x).erase x
      have arrangeFront : stem.Perm (x :: x :: remainder) :=
        (List.perm_cons_erase firstMember).trans <|
          List.Perm.cons x <| by
            simpa [remainder] using
              List.perm_cons_erase secondMember
      have enter :=
        Derives.prepend (Word.singleton x)
          (derivesPrefixPermutation arrangeFront penultimate final)
      let suffix := wordOfTerminalPair remainder penultimate final
      have raw := Derives.appendRight
        (derivesPowerContraction (Word.singleton x)) suffix
      have contract :
          Derives basis
            (wordOfTerminalPair
              (x :: x :: x :: remainder) penultimate final)
            (wordOfTerminalPair
              (x :: x :: remainder) penultimate final) := by
        simpa [suffix, wordOfTerminalPair,
          SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair,
          SemigroupBasis.Examples.wordOfPrefixFinal,
          word, Word.singleton, Word.append,
          Word.append_assoc, List.append_assoc] using raw
      exact enter.trans <| contract.trans <|
        derivesPrefixPermutation arrangeFront.symm penultimate final

theorem derivesCapPrefix :
    ∀ stem penultimate final,
      Derives basis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair
          (capPrefix stem penultimate final) penultimate final)
  | [], penultimate, final => Derives.refl _
  | x :: xs, penultimate, final => by
      have tailNormal := derivesCapPrefix xs penultimate final
      have prefixed :
          Derives basis
            (wordOfTerminalPair (x :: xs) penultimate final)
            (wordOfTerminalPair
              (x :: capPrefix xs penultimate final)
              penultimate final) := by
        simpa [wordOfTerminalPair,
          SemigroupBasis.CoRoots.S5_240.wordOfTerminalPair,
          SemigroupBasis.Examples.wordOfPrefixFinal,
          List.append_assoc] using
          Derives.prepend (Word.singleton x) tailNormal
      simp only [capPrefix]
      split <;> rename_i retained
      · exact prefixed
      · exact prefixed.trans <|
          derivesDeleteLeadingPrefix x
            (capPrefix xs penultimate final) penultimate final
            (by omega)

private theorem derivesSameTailOfCapped
    (leftPrefix rightPrefix : List Nat)
    (penultimate final : Nat)
    (capped : ∀ tested,
      min ((leftPrefix ++ [penultimate, final]).count tested) 2 =
        min ((rightPrefix ++ [penultimate, final]).count tested) 2) :
    Derives basis
      (wordOfTerminalPair leftPrefix penultimate final)
      (wordOfTerminalPair rightPrefix penultimate final) := by
  let leftNormal := capPrefix leftPrefix penultimate final
  let rightNormal := capPrefix rightPrefix penultimate final
  have prefixCounts : ∀ tested,
      leftNormal.count tested = rightNormal.count tested := by
    intro tested
    have total :
        (leftNormal ++ [penultimate, final]).count tested =
          (rightNormal ++ [penultimate, final]).count tested := by
      calc
        (leftNormal ++ [penultimate, final]).count tested =
            min ((leftPrefix ++ [penultimate, final]).count tested) 2 := by
          simpa only [leftNormal] using
            count_capPrefix_total tested leftPrefix penultimate final
        _ = min
            ((rightPrefix ++ [penultimate, final]).count tested) 2 :=
          capped tested
        _ = (rightNormal ++ [penultimate, final]).count tested := by
          simpa only [rightNormal] using
            (count_capPrefix_total tested rightPrefix
              penultimate final).symm
    simp only [List.count_append] at total
    omega
  have permutation : leftNormal.Perm rightNormal :=
    List.perm_iff_count.mpr prefixCounts
  have leftDerivation := derivesCapPrefix leftPrefix penultimate final
  have rightDerivation := derivesCapPrefix rightPrefix penultimate final
  exact leftDerivation.trans <|
    (derivesPrefixPermutation permutation penultimate final).trans
      rightDerivation.symm

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem s3_8_models :
    Models SemigroupBasis.Generated.S3_8.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_8.table basis toFinFour (by decide)

theorem s5_240_models :
    Models SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_240.table basis toFinFour (by decide)

private theorem capped_of_derives
    {left right : Word Nat} (derivation : Derives basis left right) :
    ∀ tested,
      min (left.toList.count tested) 2 =
        min (right.toList.count tested) 2 := by
  let identity : Identity Nat := Identity.mk left right
  exact exponentValid_capped_count_eq identity <| by
    simpa [SemigroupBasis.Generated.S3_8.table,
      SemigroupBasis.Examples.commutativeExponentThree] using
      (fun valuation => derivation.sound s3_8_models valuation)

private theorem derivesRepeatedPenultimateSwitch
    (stem : List Nat) (oldMarker newMarker final : Nat)
    (oldMember : oldMarker ∈ stem)
    (newRepeated : 2 ≤ stem.count newMarker) :
    ∃ switchedPrefix,
      Derives basis
        (wordOfTerminalPair stem oldMarker final)
        (wordOfTerminalPair switchedPrefix newMarker final) := by
  by_cases equal : oldMarker = newMarker
  · subst newMarker
    exact ⟨stem, Derives.refl _⟩
  · have firstMember : newMarker ∈ stem :=
      List.count_pos_iff.mp (by omega)
    have erasedCount :
        (stem.erase newMarker).count newMarker =
          stem.count newMarker - 1 := by
      rw [List.count_erase_self]
    have secondMember : newMarker ∈ stem.erase newMarker :=
      List.count_pos_iff.mp (by omega)
    have oldInTwiceErased :
        oldMarker ∈ (stem.erase newMarker).erase newMarker := by
      rw [List.mem_erase_of_ne equal]
      rw [List.mem_erase_of_ne equal]
      exact oldMember
    let remainder :=
      ((stem.erase newMarker).erase newMarker).erase oldMarker
    have arrangeFront :
        stem.Perm (newMarker :: newMarker :: oldMarker :: remainder) :=
      (List.perm_cons_erase firstMember).trans <|
        List.Perm.cons newMarker <|
          (List.perm_cons_erase secondMember).trans <|
            List.Perm.cons newMarker <| by
              simpa [remainder] using
                List.perm_cons_erase oldInTwiceErased
    have arrange :
        stem.Perm (remainder ++ [newMarker, newMarker, oldMarker]) :=
      arrangeFront.trans <|
        perm_three_to_end newMarker newMarker oldMarker remainder
    have enter := derivesPrefixPermutation arrange oldMarker final
    have square := derivesSquareCommutation
      (Word.singleton newMarker) (Word.singleton oldMarker)
    have moved := Derives.appendRight
      (prepend_optional remainder square) (Word.singleton final)
    let switchedPrefix := remainder ++ [oldMarker, oldMarker, newMarker]
    have move :
        Derives basis
          (wordOfTerminalPair
            (remainder ++ [newMarker, newMarker, oldMarker])
            oldMarker final)
          (wordOfTerminalPair switchedPrefix newMarker final) := by
      apply retargetDerives moved
      · rw [Word.toList_append, Word.toList_singleton,
          toList_prepend_optional, toList_wordOfTerminalPair]
        simp [Word.toList, List.append_assoc]
      · rw [Word.toList_append, Word.toList_singleton,
          toList_prepend_optional, toList_wordOfTerminalPair]
        simp [switchedPrefix, Word.toList, List.append_assoc]
    exact ⟨switchedPrefix, enter.trans move⟩

private theorem derivesMakeTerminalSquare
    (stem : List Nat) (penultimate final : Nat)
    (penultimateRepeated :
      penultimate ∈ stem ∨ final = penultimate)
    (finalRepeated : final = penultimate ∨ final ∈ stem) :
    ∃ squarePrefix,
      Derives basis
        (wordOfTerminalPair stem penultimate final)
        (wordOfTerminalPair squarePrefix penultimate penultimate) := by
  by_cases equal : final = penultimate
  · subst final
    exact ⟨stem, Derives.refl _⟩
  · have penultimateMember : penultimate ∈ stem :=
      penultimateRepeated.resolve_right equal
    have finalMember : final ∈ stem :=
      finalRepeated.resolve_left equal
    have finalInErase : final ∈ stem.erase penultimate :=
      (List.mem_erase_of_ne equal).mpr finalMember
    let remainder := (stem.erase penultimate).erase final
    have arrangeFront :
        stem.Perm (penultimate :: final :: remainder) :=
      (List.perm_cons_erase penultimateMember).trans <|
        List.Perm.cons penultimate <| by
          simpa [remainder] using List.perm_cons_erase finalInErase
    have arrange :
        stem.Perm (remainder ++ [penultimate, final]) :=
      arrangeFront.trans <| perm_two_to_end penultimate final remainder
    have enter := derivesPrefixPermutation arrange penultimate final
    have interleave :=
      (derivesSquareInterleave
        (Word.singleton penultimate) (Word.singleton final)).symm
    have commute :=
      derivesSquareCommutation
        (Word.singleton penultimate) (Word.singleton final)
    have base := interleave.trans commute
    have moved := prepend_optional remainder base
    let squarePrefix := remainder ++ [final, final]
    have move :
        Derives basis
          (wordOfTerminalPair
            (remainder ++ [penultimate, final]) penultimate final)
          (wordOfTerminalPair
            squarePrefix penultimate penultimate) := by
      apply retargetDerives moved
      · rw [toList_prepend_optional, toList_wordOfTerminalPair]
        simp [Word.toList, List.append_assoc]
      · rw [toList_prepend_optional, toList_wordOfTerminalPair]
        simp [squarePrefix, Word.toList, List.append_assoc]
    exact ⟨squarePrefix, enter.trans move⟩

private theorem derivesSwitchTerminalSquare
    (stem : List Nat) (oldMarker newMarker : Nat)
    (newRepeated : 2 ≤ stem.count newMarker) :
    ∃ switchedPrefix,
      Derives basis
        (wordOfTerminalPair stem oldMarker oldMarker)
        (wordOfTerminalPair switchedPrefix newMarker newMarker) := by
  by_cases equal : oldMarker = newMarker
  · subst newMarker
    exact ⟨stem, Derives.refl _⟩
  · have firstMember : newMarker ∈ stem :=
      List.count_pos_iff.mp (by omega)
    have erasedCount :
        (stem.erase newMarker).count newMarker =
          stem.count newMarker - 1 := by
      rw [List.count_erase_self]
    have secondMember : newMarker ∈ stem.erase newMarker :=
      List.count_pos_iff.mp (by omega)
    let remainder := (stem.erase newMarker).erase newMarker
    have arrangeFront : stem.Perm (newMarker :: newMarker :: remainder) :=
      (List.perm_cons_erase firstMember).trans <|
        List.Perm.cons newMarker <| by
          simpa [remainder] using List.perm_cons_erase secondMember
    have arrange : stem.Perm (remainder ++ [newMarker, newMarker]) :=
      arrangeFront.trans <| perm_two_to_end newMarker newMarker remainder
    have enter := derivesPrefixPermutation arrange oldMarker oldMarker
    have square := derivesSquareCommutation
      (Word.singleton newMarker) (Word.singleton oldMarker)
    have moved := prepend_optional remainder square
    let switchedPrefix := remainder ++ [oldMarker, oldMarker]
    have move :
        Derives basis
          (wordOfTerminalPair
            (remainder ++ [newMarker, newMarker]) oldMarker oldMarker)
          (wordOfTerminalPair switchedPrefix newMarker newMarker) := by
      apply retargetDerives moved
      · rw [toList_prepend_optional, toList_wordOfTerminalPair]
        simp [Word.toList, List.append_assoc]
      · rw [toList_prepend_optional, toList_wordOfTerminalPair]
        simp [switchedPrefix, Word.toList, List.append_assoc]
    exact ⟨switchedPrefix, enter.trans move⟩

/-- Capped multiplicities together with the exact `S5_240` endpoint signature
are a complete invariant of the corrected nine-law basis. -/
theorem derives_of_capped_and_endpoint
    (left right : Word Nat)
    (capped : ∀ tested,
      min (left.toList.count tested) 2 =
        min (right.toList.count tested) 2)
    (endpoint :
      SemigroupBasis.CoRoots.S5_240.SameEndpointSuffixSignature left right) :
    Derives basis left right := by
  classical
  have leftReconstruct :=
    SemigroupBasis.CoRoots.S5_83.terminalSplit_renderWord left
  have rightReconstruct :=
    SemigroupBasis.CoRoots.S5_83.terminalSplit_renderWord right
  cases leftSplitEq : SemigroupBasis.CoRoots.S5_83.terminalSplit left with
  | singleton leftFinal =>
      cases rightSplitEq :
          SemigroupBasis.CoRoots.S5_83.terminalSplit right with
      | singleton rightFinal =>
          have rightUnique := (endpoint.uniqueFinal leftFinal).mp <| by
            simp [SemigroupBasis.CoRoots.S5_83.UniqueFinal, leftSplitEq]
          have finals : rightFinal = leftFinal := by
            simpa [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
              rightSplitEq] using rightUnique
          subst rightFinal
          rw [leftSplitEq] at leftReconstruct
          rw [rightSplitEq] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct]
          exact Derives.refl _
      | pair rightStem rightPenultimate rightFinal =>
          have leftSingleton :
              SemigroupBasis.CoRoots.S5_83.IsSingletonWord left := by
            simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
              leftSplitEq]
          have rightSingleton := endpoint.singleton.mp leftSingleton
          simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
            rightSplitEq] at rightSingleton
  | pair leftStem leftPenultimate leftFinal =>
      cases rightSplitEq :
          SemigroupBasis.CoRoots.S5_83.terminalSplit right with
      | singleton rightFinal =>
          have rightSingleton :
              SemigroupBasis.CoRoots.S5_83.IsSingletonWord right := by
            simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
              rightSplitEq]
          have leftSingleton := endpoint.singleton.mpr rightSingleton
          simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
            leftSplitEq] at leftSingleton
      | pair rightStem rightPenultimate rightFinal =>
          rw [leftSplitEq] at leftReconstruct
          rw [rightSplitEq] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct]
          have cappedLists : ∀ tested,
              min ((leftStem ++
                [leftPenultimate, leftFinal]).count tested) 2 =
              min ((rightStem ++
                [rightPenultimate, rightFinal]).count tested) 2 := by
            intro tested
            have cappedLists := capped tested
            rw [← SemigroupBasis.CoRoots.S5_83.terminalSplit_renderList left,
              ← SemigroupBasis.CoRoots.S5_83.terminalSplit_renderList right,
              leftSplitEq, rightSplitEq] at cappedLists
            simpa [
              SemigroupBasis.CoRoots.S5_83.TerminalSplit.renderList
            ] using cappedLists
          by_cases leftSimple :
              leftPenultimate ∉ leftStem ∧
                leftFinal ≠ leftPenultimate
          · have leftPair :
                SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
                  left leftPenultimate leftFinal := by
              simp [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
                leftSplitEq, leftSimple]
            have rightPair :=
              (endpoint.simplePenultimatePair
                leftPenultimate leftFinal).mp leftPair
            have rightParts :
                rightPenultimate = leftPenultimate ∧
                  rightFinal = leftFinal ∧
                  leftPenultimate ∉ rightStem ∧
                  leftFinal ≠ leftPenultimate := by
              simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
                rightSplitEq] using rightPair
            have rightPenultimateEq := rightParts.1
            have rightFinalEq := rightParts.2.1
            subst rightPenultimate
            subst rightFinal
            exact derivesSameTailOfCapped
              leftStem rightStem leftPenultimate leftFinal cappedLists
          · have leftPenultimateRepeated :
                leftPenultimate ∈ leftStem ∨
                  leftFinal = leftPenultimate := by
              by_cases member : leftPenultimate ∈ leftStem
              · exact Or.inl member
              · exact Or.inr <| by
                  apply Decidable.byContradiction
                  intro different
                  exact leftSimple ⟨member, different⟩
            by_cases leftFinalRepeated :
                leftFinal = leftPenultimate ∨ leftFinal ∈ leftStem
            · have rightFinalRepeated :
                  rightFinal = rightPenultimate ∨
                    rightFinal ∈ rightStem := by
                apply Decidable.byContradiction
                intro notRepeated
                have parts := not_or.mp notRepeated
                have rightUnique :
                    SemigroupBasis.CoRoots.S5_83.UniqueFinal
                      right rightFinal := by
                  simp [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
                    rightSplitEq, parts]
                have leftUnique :=
                  (endpoint.uniqueFinal rightFinal).mpr rightUnique
                have leftParts :
                    leftFinal = rightFinal ∧
                      leftFinal ≠ leftPenultimate ∧
                      leftFinal ∉ leftStem := by
                  simpa [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
                    leftSplitEq] using leftUnique
                rcases leftFinalRepeated with equal | member
                · exact leftParts.2.1 equal
                · exact leftParts.2.2 member
              have rightPenultimateRepeated :
                  rightPenultimate ∈ rightStem ∨
                    rightFinal = rightPenultimate := by
                apply Decidable.byContradiction
                intro notRepeated
                have parts := not_or.mp notRepeated
                have rightPair :
                    SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
                      right rightPenultimate rightFinal := by
                  simp [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
                    rightSplitEq, parts]
                have leftPair :=
                  (endpoint.simplePenultimatePair
                    rightPenultimate rightFinal).mpr rightPair
                have leftParts :
                    leftPenultimate = rightPenultimate ∧
                      leftFinal = rightFinal ∧
                      rightPenultimate ∉ leftStem ∧
                      rightFinal ≠ rightPenultimate := by
                  simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
                    leftSplitEq] using leftPair
                rcases leftPenultimateRepeated with member | equal
                · exact leftParts.2.2.1 <| by
                    simpa [leftParts.1] using member
                · exact leftParts.2.2.2 <| by
                    simpa [leftParts.1, leftParts.2.1] using equal
              obtain ⟨leftSquarePrefix, leftSquare⟩ :=
                derivesMakeTerminalSquare
                  leftStem leftPenultimate leftFinal
                  leftPenultimateRepeated leftFinalRepeated
              obtain ⟨rightSquarePrefix, rightSquare⟩ :=
                derivesMakeTerminalSquare
                  rightStem rightPenultimate rightFinal
                  rightPenultimateRepeated rightFinalRepeated
              by_cases markersEqual :
                  rightPenultimate = leftPenultimate
              · subst rightPenultimate
                have middleCapped : ∀ tested,
                    min ((leftSquarePrefix ++
                      [leftPenultimate, leftPenultimate]).count tested) 2 =
                    min ((rightSquarePrefix ++
                      [leftPenultimate, leftPenultimate]).count tested) 2 := by
                  intro tested
                  have rightSquareCapped :
                      min ((rightStem ++
                        [leftPenultimate, rightFinal]).count tested) 2 =
                      min ((rightSquarePrefix ++
                        [leftPenultimate, leftPenultimate]).count tested) 2 := by
                    simpa using capped_of_derives rightSquare tested
                  have leftSquareCapped :
                      min ((leftStem ++
                        [leftPenultimate, leftFinal]).count tested) 2 =
                      min ((leftSquarePrefix ++
                        [leftPenultimate, leftPenultimate]).count tested) 2 := by
                    simpa using capped_of_derives leftSquare tested
                  exact leftSquareCapped.symm.trans <|
                    (cappedLists tested).trans <|
                      rightSquareCapped
                exact leftSquare.trans <|
                  (derivesSameTailOfCapped leftSquarePrefix
                    rightSquarePrefix leftPenultimate leftPenultimate
                    middleCapped).trans rightSquare.symm
              · have leftMarkerRepeated :
                    2 ≤ (leftStem ++
                      [leftPenultimate, leftFinal]).count
                        leftPenultimate := by
                  rcases leftPenultimateRepeated with member | equal
                  · rw [List.count_append]
                    have positive := List.count_pos_iff.mpr member
                    simp
                    omega
                  · subst leftFinal
                    simp
                have rightMarkerOriginal :
                    2 ≤ (rightStem ++
                      [rightPenultimate, rightFinal]).count
                        leftPenultimate := by
                  have equality := cappedLists leftPenultimate
                  omega
                have rightMarkerRepeated :
                    2 ≤ (rightSquarePrefix.count leftPenultimate) := by
                  have squareCaps :
                      min ((rightStem ++
                        [rightPenultimate, rightFinal]).count
                          leftPenultimate) 2 =
                      min ((rightSquarePrefix ++
                        [rightPenultimate, rightPenultimate]).count
                          leftPenultimate) 2 := by
                    simpa using
                      capped_of_derives rightSquare leftPenultimate
                  rw [Nat.min_eq_right rightMarkerOriginal] at squareCaps
                  simp [markersEqual] at squareCaps
                  omega
                obtain ⟨switchedPrefix, switched⟩ :=
                  derivesSwitchTerminalSquare
                    rightSquarePrefix rightPenultimate
                    leftPenultimate rightMarkerRepeated
                have middleCapped : ∀ tested,
                    min ((leftSquarePrefix ++
                      [leftPenultimate, leftPenultimate]).count tested) 2 =
                    min ((switchedPrefix ++
                      [leftPenultimate, leftPenultimate]).count tested) 2 := by
                  intro tested
                  have rightSwitchedCapped :
                      min ((rightStem ++
                        [rightPenultimate, rightFinal]).count tested) 2 =
                      min ((switchedPrefix ++
                        [leftPenultimate, leftPenultimate]).count tested) 2 := by
                    have rightSquareCapped :
                        min ((rightStem ++
                          [rightPenultimate, rightFinal]).count tested) 2 =
                        min ((rightSquarePrefix ++
                          [rightPenultimate, rightPenultimate]).count tested) 2 := by
                      simpa using capped_of_derives rightSquare tested
                    have switchedCapped :
                        min ((rightSquarePrefix ++
                          [rightPenultimate, rightPenultimate]).count tested) 2 =
                        min ((switchedPrefix ++
                          [leftPenultimate, leftPenultimate]).count tested) 2 := by
                      simpa using capped_of_derives switched tested
                    exact rightSquareCapped.trans switchedCapped
                  have leftSquareCapped :
                      min ((leftStem ++
                        [leftPenultimate, leftFinal]).count tested) 2 =
                      min ((leftSquarePrefix ++
                        [leftPenultimate, leftPenultimate]).count tested) 2 := by
                    simpa using capped_of_derives leftSquare tested
                  exact leftSquareCapped.symm.trans <|
                    (cappedLists tested).trans <|
                      rightSwitchedCapped
                exact leftSquare.trans <|
                  (derivesSameTailOfCapped leftSquarePrefix
                    switchedPrefix leftPenultimate leftPenultimate
                    middleCapped).trans <|
                      switched.symm.trans rightSquare.symm
            · have leftFinalParts := not_or.mp leftFinalRepeated
              have leftUnique :
                  SemigroupBasis.CoRoots.S5_83.UniqueFinal
                    left leftFinal := by
                simp [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
                  leftSplitEq, leftFinalParts]
              have rightUnique :=
                (endpoint.uniqueFinal leftFinal).mp leftUnique
              have rightParts :
                  rightFinal = leftFinal ∧
                    rightFinal ≠ rightPenultimate ∧
                    rightFinal ∉ rightStem := by
                simpa [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
                  rightSplitEq] using rightUnique
              have rightFinalEq := rightParts.1
              subst rightFinal
              have leftPenultimateMember :
                  leftPenultimate ∈ leftStem :=
                leftPenultimateRepeated.resolve_right leftFinalParts.1
              have rightPenultimateMember :
                  rightPenultimate ∈ rightStem := by
                apply Decidable.byContradiction
                intro absent
                have rightPair :
                    SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair
                      right rightPenultimate leftFinal := by
                  simp [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
                    rightSplitEq, absent, rightParts.2.1]
                have leftPair :=
                  (endpoint.simplePenultimatePair
                    rightPenultimate leftFinal).mpr rightPair
                have leftParts :
                    leftPenultimate = rightPenultimate ∧
                      leftFinal = leftFinal ∧
                      rightPenultimate ∉ leftStem ∧
                      leftFinal ≠ rightPenultimate := by
                  simpa [SemigroupBasis.CoRoots.S5_240.SimplePenultimatePair,
                    leftSplitEq] using leftPair
                exact leftParts.2.2.1 <| by
                  simpa [leftParts.1] using leftPenultimateMember
              by_cases markersEqual :
                  rightPenultimate = leftPenultimate
              · subst rightPenultimate
                exact derivesSameTailOfCapped
                  leftStem rightStem leftPenultimate leftFinal cappedLists
              · have leftRepeatedTotal :
                    2 ≤ (rightStem.count leftPenultimate) := by
                  have leftTotal :
                      2 ≤ (leftStem ++
                        [leftPenultimate, leftFinal]).count
                          leftPenultimate := by
                    rw [List.count_append]
                    have positive :=
                      List.count_pos_iff.mpr leftPenultimateMember
                    simp [leftFinalParts.1]
                    omega
                  have equalCaps := cappedLists leftPenultimate
                  rw [Nat.min_eq_right leftTotal] at equalCaps
                  simp [markersEqual, leftFinalParts.1] at equalCaps
                  omega
                obtain ⟨switchedPrefix, switched⟩ :=
                  derivesRepeatedPenultimateSwitch
                    rightStem rightPenultimate leftPenultimate leftFinal
                    rightPenultimateMember leftRepeatedTotal
                have middleCapped : ∀ tested,
                    min ((leftStem ++
                      [leftPenultimate, leftFinal]).count tested) 2 =
                    min ((switchedPrefix ++
                      [leftPenultimate, leftFinal]).count tested) 2 := by
                  intro tested
                  have switchedCapped :
                      min ((rightStem ++
                        [rightPenultimate, leftFinal]).count tested) 2 =
                      min ((switchedPrefix ++
                        [leftPenultimate, leftFinal]).count tested) 2 := by
                    simpa using capped_of_derives switched tested
                  exact (cappedLists tested).trans switchedCapped
                exact (derivesSameTailOfCapped
                  leftStem switchedPrefix leftPenultimate leftFinal
                  middleCapped).trans switched.symm

/-- Unrestricted completeness of the corrected basis for the exact factor
intersection. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy SemigroupBasis.Generated.S3_8.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have capped := exponentValid_capped_count_eq identity <| by
    simpa [SemigroupBasis.Generated.S3_8.table,
      SemigroupBasis.Examples.commutativeExponentThree] using
      s3Valid
  exact derives_of_capped_and_endpoint identity.lhs identity.rhs capped
    (SemigroupBasis.CoRoots.S5_240.valid_signature identity s5Valid)

/-- The corrected nine laws are exactly a basis of the intersection. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup basis where
  leftModels := s3_8_models
  rightModels := s5_240_models
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6FactorPairS3_8S5_240
