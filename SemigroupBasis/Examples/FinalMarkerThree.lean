import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Multiplication for the zero-based form of
`[[1,1,1],[1,1,1],[1,2,3]]`. -/
def finalMarkerThreeMul (a b : Fin 3) : Fin 3 :=
  if a = 2 then b else 0

/-- The Smallsemi representative `S3_6`. -/
def finalMarkerThree : FiniteTable where
  order := 3
  mul := finalMarkerThreeMul
  assoc := by decide

def finalMarkerXX : Word Nat := ⟨0, [0]⟩
def finalMarkerXXX : Word Nat := ⟨0, [0, 0]⟩
def finalMarkerXY : Word Nat := ⟨0, [1]⟩
def finalMarkerXXY : Word Nat := ⟨0, [0, 1]⟩
def finalMarkerXYX : Word Nat := ⟨0, [1, 0]⟩
def finalMarkerXYY : Word Nat := ⟨0, [1, 1]⟩
def finalMarkerYXX : Word Nat := ⟨1, [0, 0]⟩

def finalMarkerPowerLaw : Identity Nat :=
  ⟨finalMarkerXX, finalMarkerXXX⟩

def finalMarkerPrefixDuplicationLaw : Identity Nat :=
  ⟨finalMarkerXY, finalMarkerXXY⟩

def finalMarkerCopyLaw : Identity Nat :=
  ⟨finalMarkerXYX, finalMarkerXYY⟩

def finalMarkerRotateLaw : Identity Nat :=
  ⟨finalMarkerXYX, finalMarkerYXX⟩

/-- The exact basis `xx = xxx`, `xy = xxy`, `xyx = xyy`,
`xyx = yxx`. -/
def finalMarkerThreeBasis : List (Identity Nat) :=
  [finalMarkerPowerLaw, finalMarkerPrefixDuplicationLaw,
    finalMarkerCopyLaw, finalMarkerRotateLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem finalMarkerDerivesPowerContraction (u : Word Nat) :
    Derives finalMarkerThreeBasis ((u ++ u) ++ u) (u ++ u) := by
  have hbase :
      Derives finalMarkerThreeBasis finalMarkerXXX finalMarkerXX :=
    Derives.symm <|
      Derives.fromBasis (e := finalMarkerPowerLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [finalMarkerThreeBasis, finalMarkerPowerLaw, finalMarkerXXX,
    finalMarkerXX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem finalMarkerDerivesPrefixDuplication (u v : Word Nat) :
    Derives finalMarkerThreeBasis (u ++ v) ((u ++ u) ++ v) := by
  have hbase :
      Derives finalMarkerThreeBasis finalMarkerXY finalMarkerXXY :=
    Derives.fromBasis (e := finalMarkerPrefixDuplicationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [finalMarkerThreeBasis, finalMarkerPrefixDuplicationLaw,
    finalMarkerXY, finalMarkerXXY, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

theorem finalMarkerDerivesCopy (u v : Word Nat) :
    Derives finalMarkerThreeBasis ((u ++ v) ++ u) ((u ++ v) ++ v) := by
  have hbase :
      Derives finalMarkerThreeBasis finalMarkerXYX finalMarkerXYY :=
    Derives.fromBasis (e := finalMarkerCopyLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [finalMarkerThreeBasis, finalMarkerCopyLaw, finalMarkerXYX,
    finalMarkerXYY, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem finalMarkerDerivesRotate (u v : Word Nat) :
    Derives finalMarkerThreeBasis ((u ++ v) ++ u) ((v ++ u) ++ u) := by
  have hbase :
      Derives finalMarkerThreeBasis finalMarkerXYX finalMarkerYXX :=
    Derives.fromBasis (e := finalMarkerRotateLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [finalMarkerThreeBasis, finalMarkerRotateLaw, finalMarkerXYX,
    finalMarkerYXX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

/-- A repeated terminal block may be switched from `v` to `u`. -/
theorem finalMarkerDerivesTerminalSwitch (u v : Word Nat) :
    Derives finalMarkerThreeBasis ((u ++ v) ++ v) ((v ++ u) ++ u) :=
  Derives.trans
    (Derives.symm (finalMarkerDerivesCopy u v))
    (finalMarkerDerivesRotate u v)

/-- Arbitrary nonempty blocks in the prefix before a fixed nonempty suffix
may be swapped. -/
theorem finalMarkerDerivesPrefixSwap (u v q : Word Nat) :
    Derives finalMarkerThreeBasis ((u ++ v) ++ q) ((v ++ u) ++ q) := by
  have expand :=
    finalMarkerDerivesPrefixDuplication (u ++ v) q
  have copyFirst :=
    Derives.appendRight (finalMarkerDerivesCopy u v) (v ++ q)
  have contractMiddle :=
    Derives.appendRight
      (Derives.prepend u (finalMarkerDerivesPowerContraction v)) q
  have switch :=
    Derives.appendRight (finalMarkerDerivesTerminalSwitch u v) q
  have contractLast :=
    Derives.prepend v <|
      Derives.symm (finalMarkerDerivesPrefixDuplication u q)
  exact Derives.trans expand <|
    Derives.trans
      (by simpa [Word.append_assoc] using copyFirst) <|
    Derives.trans
      (by simpa [Word.append_assoc] using contractMiddle) <|
    Derives.trans switch <|
      (by simpa [Word.append_assoc] using contractLast)

/-- A word with the listed prefix and final letter. -/
def wordOfPrefixFinal : List Nat → Nat → Word Nat
  | [], final => Word.singleton final
  | x :: xs, final => Word.singleton x ++ wordOfPrefixFinal xs final

@[simp]
theorem wordOfPrefixFinal_nil (final : Nat) :
    wordOfPrefixFinal [] final = Word.singleton final := rfl

@[simp]
theorem wordOfPrefixFinal_cons (x : Nat) (xs : List Nat) (final : Nat) :
    wordOfPrefixFinal (x :: xs) final =
      Word.singleton x ++ wordOfPrefixFinal xs final := rfl

theorem toList_wordOfPrefixFinal (pref : List Nat) (final : Nat) :
    (wordOfPrefixFinal pref final).toList = pref ++ [final] := by
  induction pref with
  | nil => rfl
  | cons x xs ih =>
      change x :: (wordOfPrefixFinal xs final).toList =
        x :: (xs ++ [final])
      rw [ih]

private def splitPrefixFinalAux (head : Nat) :
    List Nat → List Nat × Nat
  | [] => ([], head)
  | next :: rest =>
      let split := splitPrefixFinalAux next rest
      (head :: split.1, split.2)

def splitPrefixFinal (w : Word Nat) : List Nat × Nat :=
  splitPrefixFinalAux w.head w.tail

private theorem wordOfPrefixFinal_splitAux (head : Nat) (tail : List Nat) :
    wordOfPrefixFinal (splitPrefixFinalAux head tail).1
        (splitPrefixFinalAux head tail).2 =
      ⟨head, tail⟩ := by
  induction tail generalizing head with
  | nil => rfl
  | cons next rest ih =>
      simp only [splitPrefixFinalAux, wordOfPrefixFinal]
      rw [ih]
      rfl

theorem wordOfPrefixFinal_split (w : Word Nat) :
    wordOfPrefixFinal (splitPrefixFinal w).1
        (splitPrefixFinal w).2 = w := by
  cases w with
  | mk head tail =>
      exact wordOfPrefixFinal_splitAux head tail

private theorem finalMarkerDerivesPrefixPermutation
    {prefix₁ prefix₂ : List Nat} (hperm : prefix₁.Perm prefix₂)
    (final : Nat) :
    Derives finalMarkerThreeBasis
      (wordOfPrefixFinal prefix₁ final)
      (wordOfPrefixFinal prefix₂ final) := by
  induction hperm with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa using Derives.prepend (Word.singleton x) ih
  | swap x y xs =>
      simpa [Word.append_assoc] using
        finalMarkerDerivesPrefixSwap
          (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs final)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans ih₁ ih₂

private theorem perm_two_to_end (a b : Nat) :
    ∀ xs : List Nat, (a :: b :: xs).Perm (xs ++ [a, b])
  | [] => List.Perm.refl _
  | x :: xs =>
      (List.Perm.cons a (List.Perm.swap x b xs)).trans <|
        (List.Perm.swap x a (b :: xs)).trans <|
          List.Perm.cons x (perm_two_to_end a b xs)

private theorem perm_swap_at_end (a b : Nat) :
    ∀ xs : List Nat, (xs ++ [a, b]).Perm (xs ++ [b, a])
  | [] => List.Perm.swap b a []
  | x :: xs => List.Perm.cons x (perm_swap_at_end a b xs)

/-- If the final letter already occurs in the prefix, it may be replaced by
any other prefix letter. -/
private theorem finalMarkerDerivesRepeatedFinalSwitch
    (pref : List Nat) (oldFinal newFinal : Nat)
    (hold : oldFinal ∈ pref) (hnew : newFinal ∈ pref) :
    Derives finalMarkerThreeBasis
      (wordOfPrefixFinal pref oldFinal)
      (wordOfPrefixFinal pref newFinal) := by
  by_cases finals : oldFinal = newFinal
  · subst newFinal
    exact Derives.refl _
  · have oldInErase :
        oldFinal ∈ pref.erase newFinal := by
      simpa [finals] using hold
    let remainder := (pref.erase newFinal).erase oldFinal
    have arrangeFront :
        pref.Perm (newFinal :: oldFinal :: remainder) := by
      exact (List.perm_cons_erase hnew).trans <|
        List.Perm.cons newFinal <| by
          simpa [remainder] using List.perm_cons_erase oldInErase
    have arrange :
        pref.Perm (remainder ++ [newFinal, oldFinal]) :=
      arrangeFront.trans (perm_two_to_end newFinal oldFinal remainder)
    have restore :
        (remainder ++ [oldFinal, newFinal]).Perm pref :=
      (perm_swap_at_end oldFinal newFinal remainder).trans arrange.symm
    have switchAtEnd :
        Derives finalMarkerThreeBasis
          (wordOfPrefixFinal
            (remainder ++ [newFinal, oldFinal]) oldFinal)
          (wordOfPrefixFinal
            (remainder ++ [oldFinal, newFinal]) newFinal) := by
      induction remainder with
      | nil =>
          simpa [wordOfPrefixFinal, Word.append_assoc] using
            finalMarkerDerivesTerminalSwitch
              (Word.singleton newFinal) (Word.singleton oldFinal)
      | cons x xs ih =>
          simpa [wordOfPrefixFinal] using
            Derives.prepend (Word.singleton x) ih
    exact Derives.trans
      (finalMarkerDerivesPrefixPermutation arrange oldFinal) <|
      Derives.trans switchAtEnd <|
        finalMarkerDerivesPrefixPermutation restore newFinal

/-- Retain one copy of each prefix letter. The final letter is handled
separately, so a repeated final keeps one prefix witness. -/
def finalMarkerPrefixReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := finalMarkerPrefixReduce xs
      if x ∈ reduced then reduced else x :: reduced

theorem finalMarkerPrefixReduce_mem (z : Nat) (xs : List Nat) :
    z ∈ finalMarkerPrefixReduce xs ↔ z ∈ xs := by
  induction xs with
  | nil => simp [finalMarkerPrefixReduce]
  | cons x xs ih =>
      simp only [finalMarkerPrefixReduce]
      split <;> rename_i hx
      · constructor
        · intro hz
          exact List.Mem.tail x (ih.mp hz)
        · intro hz
          simp only [List.mem_cons] at hz
          rcases hz with hzx | hzTail
          · simpa [hzx] using hx
          · exact ih.mpr hzTail
      · simp [ih]

theorem finalMarkerPrefixReduce_nodup (xs : List Nat) :
    (finalMarkerPrefixReduce xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
      simp only [finalMarkerPrefixReduce]
      split <;> rename_i hx
      · exact ih
      · exact List.nodup_cons.2 ⟨hx, ih⟩

private theorem finalMarkerDerivesDeleteLeading
    (x : Nat) (pref : List Nat) (final : Nat)
    (hx : x ∈ pref) :
    Derives finalMarkerThreeBasis
      (wordOfPrefixFinal (x :: pref) final)
      (wordOfPrefixFinal pref final) := by
  have expose : pref.Perm (x :: pref.erase x) :=
    List.perm_cons_erase hx
  have arrange :
      (x :: pref).Perm (x :: x :: pref.erase x) :=
    List.Perm.cons x expose
  have contract :
      Derives finalMarkerThreeBasis
        (wordOfPrefixFinal (x :: x :: pref.erase x) final)
        (wordOfPrefixFinal (x :: pref.erase x) final) := by
    simpa [wordOfPrefixFinal, Word.append_assoc] using
      Derives.symm
        (finalMarkerDerivesPrefixDuplication
          (Word.singleton x)
          (wordOfPrefixFinal (pref.erase x) final))
  exact Derives.trans
    (finalMarkerDerivesPrefixPermutation arrange final) <|
    Derives.trans contract <|
      finalMarkerDerivesPrefixPermutation expose.symm final

theorem finalMarkerDerivesNormalPrefix :
    ∀ (pref : List Nat) (final : Nat),
      Derives finalMarkerThreeBasis
        (wordOfPrefixFinal pref final)
        (wordOfPrefixFinal (finalMarkerPrefixReduce pref) final)
  | [], final => Derives.refl _
  | x :: xs, final => by
      have suffixNormal := finalMarkerDerivesNormalPrefix xs final
      have prefixed :=
        Derives.prepend (Word.singleton x) suffixNormal
      by_cases hx : x ∈ finalMarkerPrefixReduce xs
      · have reduced :
            finalMarkerPrefixReduce (x :: xs) =
              finalMarkerPrefixReduce xs := by
          simp [finalMarkerPrefixReduce, hx]
        rw [reduced]
        exact Derives.trans
          (by simpa [wordOfPrefixFinal] using prefixed)
          (finalMarkerDerivesDeleteLeading
            x (finalMarkerPrefixReduce xs) final hx)
      · have reduced :
            finalMarkerPrefixReduce (x :: xs) =
              x :: finalMarkerPrefixReduce xs := by
          simp [finalMarkerPrefixReduce, hx]
        rw [reduced]
        simpa [wordOfPrefixFinal] using prefixed

private theorem perm_of_nodup_mem_iff :
    ∀ {xs ys : List Nat},
      xs.Nodup →
      ys.Nodup →
      (∀ z, z ∈ xs ↔ z ∈ ys) →
      xs.Perm ys
  | [], [], _, _, _ => List.Perm.refl []
  | [], y :: ys, _, _, hmem => by
      exact False.elim <| by
        have := (hmem y).2 (List.Mem.head ys)
        exact List.not_mem_nil this
  | x :: xs, [], _, _, hmem => by
      exact False.elim <| by
        have := (hmem x).1 (List.Mem.head xs)
        exact List.not_mem_nil this
  | x :: xs, y :: ys, hxs, hys, hmem => by
      have hxIn : x ∈ y :: ys :=
        (hmem x).1 (List.Mem.head xs)
      have targetPerm : (y :: ys).Perm (x :: (y :: ys).erase x) :=
        List.perm_cons_erase hxIn
      have tailNodup : xs.Nodup :=
        (List.nodup_cons.mp hxs).2
      have erasedNodup : ((y :: ys).erase x).Nodup :=
        hys.erase _
      have arrangedNodup :
          (x :: (y :: ys).erase x).Nodup :=
        targetPerm.nodup_iff.mp hys
      have xNotInErase : x ∉ (y :: ys).erase x :=
        (List.nodup_cons.mp arrangedNodup).1
      have tailMem :
          ∀ z, z ∈ xs ↔ z ∈ (y :: ys).erase x := by
        intro z
        have xNotInXs : x ∉ xs :=
          (List.nodup_cons.mp hxs).1
        by_cases hzx : z = x
        · subst z
          exact iff_of_false xNotInXs xNotInErase
        · constructor
          · intro hz
            have targetMem :=
              (targetPerm.mem_iff).mp <|
                (hmem z).1 (List.Mem.tail x hz)
            simp only [List.mem_cons] at targetMem
            rcases targetMem with targetHead | targetTail
            · exact False.elim (hzx targetHead)
            · exact targetTail
          · intro hz
            have targetMem : z ∈ x :: (y :: ys).erase x :=
              List.Mem.tail x hz
            have sourceMem :=
              (hmem z).2 ((targetPerm.mem_iff).mpr targetMem)
            simp only [List.mem_cons] at sourceMem
            rcases sourceMem with sourceHead | sourceTail
            · exact False.elim (hzx sourceHead)
            · exact sourceTail
      exact
        (List.Perm.cons x
          (perm_of_nodup_mem_iff tailNodup erasedNodup tailMem)).trans
          targetPerm.symm

private def finalMarkerSeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 1 else 2

/-- The separator output is `0` for a prefix occurrence, `1` for a simple
final occurrence, and `2` for absence. -/
theorem finalMarkerEval_separator (z : Nat) (pref : List Nat)
    (final : Nat) :
    finalMarkerThree.semigroup.eval (finalMarkerSeparator z)
        (wordOfPrefixFinal pref final) =
      if z ∈ pref then (0 : Fin 3)
      else if final = z then (1 : Fin 3) else (2 : Fin 3) := by
  induction pref with
  | nil =>
      simp [wordOfPrefixFinal, finalMarkerSeparator]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append, ih]
      by_cases hx : x = z
      · subst x
        simp [finalMarkerSeparator, finalMarkerThree,
          FiniteTable.semigroup, finalMarkerThreeMul]
      · simp [finalMarkerSeparator, finalMarkerThree,
          FiniteTable.semigroup, finalMarkerThreeMul, hx, Ne.symm hx]

private def finalMarkerSemanticValue
    (z : Nat) (pref : List Nat) (final : Nat) : Fin 3 :=
  if z ∈ pref then 0 else if final = z then 1 else 2

private theorem finalMarkerSemanticValue_eq_one_iff
    (z : Nat) (pref : List Nat) (final : Nat) :
    finalMarkerSemanticValue z pref final = (1 : Fin 3) ↔
      final = z ∧ z ∉ pref := by
  by_cases prefixMember : z ∈ pref
  · simp [finalMarkerSemanticValue, prefixMember]
  · by_cases finalEq : final = z
    · simp [finalMarkerSemanticValue, prefixMember, finalEq]
    · simp [finalMarkerSemanticValue, prefixMember, finalEq]

/-- A valid identity of the final-marker semigroup preserves the globally
simple final letter, expressed through the canonical prefix/final split. -/
theorem finalMarkerValid_splitSimpleFinal_iff
    (e : Identity Nat)
    (valid : e.SatisfiedBy finalMarkerThree.semigroup)
    (z : Nat) :
    ((splitPrefixFinal e.lhs).2 = z ∧
        z ∉ (splitPrefixFinal e.lhs).1) ↔
      ((splitPrefixFinal e.rhs).2 = z ∧
        z ∉ (splitPrefixFinal e.rhs).1) := by
  let lhsSplit := splitPrefixFinal e.lhs
  let rhsSplit := splitPrefixFinal e.rhs
  have lhsReconstruct :
      wordOfPrefixFinal lhsSplit.1 lhsSplit.2 = e.lhs :=
    wordOfPrefixFinal_split e.lhs
  have rhsReconstruct :
      wordOfPrefixFinal rhsSplit.1 rhsSplit.2 = e.rhs :=
    wordOfPrefixFinal_split e.rhs
  have evaluated := valid (finalMarkerSeparator z)
  rw [← lhsReconstruct, ← rhsReconstruct,
    finalMarkerEval_separator,
    finalMarkerEval_separator] at evaluated
  change
    finalMarkerSemanticValue z lhsSplit.1 lhsSplit.2 =
      finalMarkerSemanticValue z rhsSplit.1 rhsSplit.2
    at evaluated
  change
    (lhsSplit.2 = z ∧ z ∉ lhsSplit.1) ↔
      (rhsSplit.2 = z ∧ z ∉ rhsSplit.1)
  constructor
  · intro lhsSimple
    have lhsOne :
        finalMarkerSemanticValue
            z lhsSplit.1 lhsSplit.2 = (1 : Fin 3) := by
      exact
        (finalMarkerSemanticValue_eq_one_iff
          z lhsSplit.1 lhsSplit.2).2 lhsSimple
    have rhsOne :
        finalMarkerSemanticValue
            z rhsSplit.1 rhsSplit.2 = (1 : Fin 3) := by
      exact evaluated.symm.trans lhsOne
    exact
      (finalMarkerSemanticValue_eq_one_iff
        z rhsSplit.1 rhsSplit.2).1 rhsOne
  · intro rhsSimple
    have rhsOne :
        finalMarkerSemanticValue
            z rhsSplit.1 rhsSplit.2 = (1 : Fin 3) := by
      exact
        (finalMarkerSemanticValue_eq_one_iff
          z rhsSplit.1 rhsSplit.2).2 rhsSimple
    have lhsOne :
        finalMarkerSemanticValue
            z lhsSplit.1 lhsSplit.2 = (1 : Fin 3) := by
      exact evaluated.trans rhsOne
    exact
      (finalMarkerSemanticValue_eq_one_iff
        z lhsSplit.1 lhsSplit.2).1 lhsOne

private theorem finalMarkerMul_power (a : Fin 3) :
    finalMarkerThreeMul a a =
      finalMarkerThreeMul (finalMarkerThreeMul a a) a := by
  decide +revert

private theorem finalMarkerMul_prefixDuplication (a b : Fin 3) :
    finalMarkerThreeMul a b =
      finalMarkerThreeMul (finalMarkerThreeMul a a) b := by
  decide +revert

private theorem finalMarkerMul_copy (a b : Fin 3) :
    finalMarkerThreeMul (finalMarkerThreeMul a b) a =
      finalMarkerThreeMul (finalMarkerThreeMul a b) b := by
  decide +revert

private theorem finalMarkerMul_rotate (a b : Fin 3) :
    finalMarkerThreeMul (finalMarkerThreeMul a b) a =
      finalMarkerThreeMul (finalMarkerThreeMul b a) a := by
  decide +revert

theorem finalMarkerThreeBasis_models :
    Models finalMarkerThree.semigroup finalMarkerThreeBasis := by
  intro e he
  simp only [finalMarkerThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · intro valuation
    change
      finalMarkerThreeMul (valuation 0) (valuation 0) =
        finalMarkerThreeMul
          (finalMarkerThreeMul (valuation 0) (valuation 0))
          (valuation 0)
    exact finalMarkerMul_power (valuation 0)
  · intro valuation
    change
      finalMarkerThreeMul (valuation 0) (valuation 1) =
        finalMarkerThreeMul
          (finalMarkerThreeMul (valuation 0) (valuation 0))
          (valuation 1)
    exact finalMarkerMul_prefixDuplication
      (valuation 0) (valuation 1)
  · intro valuation
    change
      finalMarkerThreeMul
          (finalMarkerThreeMul (valuation 0) (valuation 1))
          (valuation 0) =
        finalMarkerThreeMul
          (finalMarkerThreeMul (valuation 0) (valuation 1))
          (valuation 1)
    exact finalMarkerMul_copy (valuation 0) (valuation 1)
  · intro valuation
    change
      finalMarkerThreeMul
          (finalMarkerThreeMul (valuation 0) (valuation 1))
          (valuation 0) =
        finalMarkerThreeMul
          (finalMarkerThreeMul (valuation 1) (valuation 0))
          (valuation 0)
    exact finalMarkerMul_rotate (valuation 0) (valuation 1)

private theorem finalMarkerNormalizedDerives
    (prefix₁ prefix₂ : List Nat) (final₁ final₂ : Nat)
    (nodup₁ : prefix₁.Nodup) (nodup₂ : prefix₂.Nodup)
    (equalEval :
      ∀ valuation : Nat → Fin 3,
        finalMarkerThree.semigroup.eval valuation
            (wordOfPrefixFinal prefix₁ final₁) =
          finalMarkerThree.semigroup.eval valuation
            (wordOfPrefixFinal prefix₂ final₂)) :
    Derives finalMarkerThreeBasis
      (wordOfPrefixFinal prefix₁ final₁)
      (wordOfPrefixFinal prefix₂ final₂) := by
  cases prefix₁ with
  | nil =>
      cases prefix₂ with
      | nil =>
          have finals : final₁ = final₂ := by
            apply Decidable.byContradiction
            intro hne
            have h := equalEval (finalMarkerSeparator final₁)
            rw [finalMarkerEval_separator,
              finalMarkerEval_separator] at h
            simp [Ne.symm hne] at h
          subst final₂
          exact Derives.refl _
      | cons y ys =>
          have h := equalEval (finalMarkerSeparator y)
          rw [finalMarkerEval_separator,
            finalMarkerEval_separator] at h
          simp only [List.not_mem_nil, if_false, List.mem_cons,
            true_or, if_true] at h
          split at h
          · exact False.elim ((by decide : (1 : Fin 3) ≠ 0) h)
          · exact False.elim ((by decide : (2 : Fin 3) ≠ 0) h)
  | cons x xs =>
      cases prefix₂ with
      | nil =>
          have h := equalEval (finalMarkerSeparator x)
          rw [finalMarkerEval_separator,
            finalMarkerEval_separator] at h
          simp only [List.not_mem_nil, if_false, List.mem_cons,
            true_or, if_true] at h
          split at h
          · exact False.elim ((by decide : (0 : Fin 3) ≠ 1) h)
          · exact False.elim ((by decide : (0 : Fin 3) ≠ 2) h)
      | cons y ys =>
          let leftPrefix := x :: xs
          let rightPrefix := y :: ys
          have prefixMem :
              ∀ z, z ∈ leftPrefix ↔ z ∈ rightPrefix := by
            intro z
            have h := equalEval (finalMarkerSeparator z)
            rw [finalMarkerEval_separator,
              finalMarkerEval_separator] at h
            constructor
            · intro hz
              apply Decidable.byContradiction
              intro hnz
              rw [if_pos hz, if_neg hnz] at h
              split at h <;> contradiction
            · intro hz
              apply Decidable.byContradiction
              intro hnz
              rw [if_neg hnz, if_pos hz] at h
              split at h <;> contradiction
          have prefixPerm : leftPrefix.Perm rightPrefix :=
            perm_of_nodup_mem_iff nodup₁ nodup₂ prefixMem
          by_cases repeated₁ : final₁ ∈ leftPrefix
          · have repeated₂ : final₂ ∈ rightPrefix := by
              apply Decidable.byContradiction
              intro simple₂
              have final₂NotLeft : final₂ ∉ leftPrefix := by
                intro hmem
                exact simple₂ ((prefixMem final₂).1 hmem)
              have finalsNe : final₁ ≠ final₂ := by
                intro finals
                subst final₂
                exact final₂NotLeft repeated₁
              have h := equalEval (finalMarkerSeparator final₂)
              rw [finalMarkerEval_separator,
                finalMarkerEval_separator] at h
              change final₂ ∉ x :: xs at final₂NotLeft
              change final₂ ∉ y :: ys at simple₂
              rw [if_neg final₂NotLeft, if_neg simple₂] at h
              simp [finalsNe] at h
            have final₂InLeft : final₂ ∈ leftPrefix :=
              (prefixMem final₂).2 repeated₂
            exact Derives.trans
              (finalMarkerDerivesRepeatedFinalSwitch
                leftPrefix final₁ final₂ repeated₁ final₂InLeft)
              (finalMarkerDerivesPrefixPermutation
                prefixPerm final₂)
          · have final₁NotRight : final₁ ∉ rightPrefix := by
              intro hmem
              exact repeated₁ ((prefixMem final₁).2 hmem)
            have finals : final₁ = final₂ := by
              apply Decidable.byContradiction
              intro hne
              have h := equalEval (finalMarkerSeparator final₁)
              rw [finalMarkerEval_separator,
                finalMarkerEval_separator] at h
              change final₁ ∉ x :: xs at repeated₁
              change final₁ ∉ y :: ys at final₁NotRight
              rw [if_neg repeated₁, if_neg final₁NotRight] at h
              simp [Ne.symm hne] at h
            subst final₂
            exact finalMarkerDerivesPrefixPermutation
              prefixPerm final₁

/-- Unrestricted completeness over `Nat` variables. A word is reduced by
deduplicating its prefix. Separator valuations recover the prefix content and
distinguish a simple final letter from the repeated-final state. -/
theorem finalMarkerThreeBasis_complete :
    BasisFor finalMarkerThree.semigroup finalMarkerThreeBasis := by
  refine ⟨finalMarkerThreeBasis_models, ?_⟩
  intro e valid
  let lhsSplit := splitPrefixFinal e.lhs
  let rhsSplit := splitPrefixFinal e.rhs
  have lhsReconstruct :
      wordOfPrefixFinal lhsSplit.1 lhsSplit.2 = e.lhs := by
    exact wordOfPrefixFinal_split e.lhs
  have rhsReconstruct :
      wordOfPrefixFinal rhsSplit.1 rhsSplit.2 = e.rhs := by
    exact wordOfPrefixFinal_split e.rhs
  have lhsNormal :=
    finalMarkerDerivesNormalPrefix lhsSplit.1 lhsSplit.2
  have rhsNormal :=
    finalMarkerDerivesNormalPrefix rhsSplit.1 rhsSplit.2
  rw [lhsReconstruct] at lhsNormal
  rw [rhsReconstruct] at rhsNormal
  have normalizedEval :
      ∀ valuation : Nat → Fin 3,
        finalMarkerThree.semigroup.eval valuation
            (wordOfPrefixFinal
              (finalMarkerPrefixReduce lhsSplit.1) lhsSplit.2) =
          finalMarkerThree.semigroup.eval valuation
            (wordOfPrefixFinal
              (finalMarkerPrefixReduce rhsSplit.1) rhsSplit.2) := by
    intro valuation
    have lhsSound :=
      lhsNormal.sound finalMarkerThreeBasis_models valuation
    have rhsSound :=
      rhsNormal.sound finalMarkerThreeBasis_models valuation
    exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
  have normalizedDerivation :=
    finalMarkerNormalizedDerives
      (finalMarkerPrefixReduce lhsSplit.1)
      (finalMarkerPrefixReduce rhsSplit.1)
      lhsSplit.2 rhsSplit.2
      (finalMarkerPrefixReduce_nodup lhsSplit.1)
      (finalMarkerPrefixReduce_nodup rhsSplit.1)
      normalizedEval
  exact Derives.trans lhsNormal <|
    Derives.trans normalizedDerivation (Derives.symm rhsNormal)

def finalMarkerThreeOppositeBasis : List (Identity Nat) :=
  reversedBasis finalMarkerThreeBasis

theorem finalMarkerThreeOppositeBasis_complete :
    BasisFor finalMarkerThree.semigroup.opposite
      finalMarkerThreeOppositeBasis := by
  simpa [finalMarkerThreeOppositeBasis] using
    finalMarkerThreeBasis_complete.oppositeReversed

end SemigroupBasis.Examples
