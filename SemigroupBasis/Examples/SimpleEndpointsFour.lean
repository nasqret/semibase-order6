import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for the catalogue representative `S4_20`. -/
def simpleEndpointsFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 1 then 0 else
      if a = 2 then (if b = 3 then 2 else 0) else
        if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else 3

/-- The order-four semigroup whose identities remember support and the
globally simple initial and final variables. -/
def simpleEndpointsFour : FiniteTable where
  order := 4
  mul := simpleEndpointsFourMul
  assoc := by decide

def simpleEndpointsXYYZ : Word Nat := ⟨0, [1, 1, 2]⟩
def simpleEndpointsXYZ : Word Nat := ⟨0, [1, 2]⟩
def simpleEndpointsXYX : Word Nat := ⟨0, [1, 0]⟩
def simpleEndpointsYXY : Word Nat := ⟨1, [0, 1]⟩
def simpleEndpointsXX : Word Nat := ⟨0, [0]⟩
def simpleEndpointsXXX : Word Nat := ⟨0, [0, 0]⟩

def simpleEndpointsContractionLaw : Identity Nat :=
  ⟨simpleEndpointsXYYZ, simpleEndpointsXYZ⟩

def simpleEndpointsRotationLaw : Identity Nat :=
  ⟨simpleEndpointsXYX, simpleEndpointsYXY⟩

def simpleEndpointsPowerLaw : Identity Nat :=
  ⟨simpleEndpointsXX, simpleEndpointsXXX⟩

/-- The basis `xyyz = xyz`, `xyx = yxy`, `xx = xxx`. -/
def simpleEndpointsBasis : List (Identity Nat) :=
  [simpleEndpointsContractionLaw, simpleEndpointsRotationLaw,
    simpleEndpointsPowerLaw]

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- Contract a doubled nonempty block between nonempty contexts. -/
theorem simpleEndpointsDerivesContraction
    (u v w : Word Nat) :
    Derives simpleEndpointsBasis
      (((u ++ v) ++ v) ++ w) ((u ++ v) ++ w) := by
  have hbase :
      Derives simpleEndpointsBasis
        simpleEndpointsXYYZ simpleEndpointsXYZ :=
    Derives.fromBasis (e := simpleEndpointsContractionLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [simpleEndpointsBasis, simpleEndpointsContractionLaw,
    simpleEndpointsXYYZ, simpleEndpointsXYZ, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

/-- The power law, oriented as `uu = uuu`. -/
theorem simpleEndpointsDerivesPowerExpansion (u : Word Nat) :
    Derives simpleEndpointsBasis
      (u ++ u) ((u ++ u) ++ u) := by
  have hbase :
      Derives simpleEndpointsBasis simpleEndpointsXX simpleEndpointsXXX :=
    Derives.fromBasis (e := simpleEndpointsPowerLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [simpleEndpointsBasis, simpleEndpointsPowerLaw,
    simpleEndpointsXX, simpleEndpointsXXX, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

/-- The block form of `xyx = yxy`. -/
theorem simpleEndpointsDerivesRotation (u v : Word Nat) :
    Derives simpleEndpointsBasis
      ((u ++ v) ++ u) ((v ++ u) ++ v) := by
  have hbase :
      Derives simpleEndpointsBasis simpleEndpointsXYX simpleEndpointsYXY :=
    Derives.fromBasis (e := simpleEndpointsRotationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [simpleEndpointsBasis, simpleEndpointsRotationLaw,
    simpleEndpointsXYX, simpleEndpointsYXY, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

/-- The six-step derivation from the tactic seed. Arbitrary adjacent nonempty
blocks may be transposed while a nonempty prefix and suffix remain fixed. -/
theorem simpleEndpointsDerivesInteriorSwap
    (a b c d : Word Nat) :
    Derives simpleEndpointsBasis
      (((a ++ b) ++ c) ++ d) (((a ++ c) ++ b) ++ d) := by
  let bc := b ++ c
  let cb := c ++ b
  have step1 :=
    Derives.symm (simpleEndpointsDerivesContraction a bc d)
  have step2 :=
    Derives.appendRight
      (Derives.prepend a (simpleEndpointsDerivesPowerExpansion bc)) d
  have step3 :=
    Derives.appendRight
      (Derives.prepend a (simpleEndpointsDerivesRotation b c))
      ((c ++ b) ++ (c ++ d))
  have step4 :=
    Derives.appendRight
      (Derives.prepend (((a ++ c) ++ b) ++ c)
        (simpleEndpointsDerivesRotation c b)) d
  have step5 :=
    Derives.appendRight
      (Derives.prepend a
        (Derives.symm (simpleEndpointsDerivesPowerExpansion cb))) d
  have step6 := simpleEndpointsDerivesContraction a cb d
  exact Derives.trans
    (by simpa [bc, Word.append_assoc] using step1) <|
    Derives.trans
      (by simpa [bc, Word.append_assoc] using step2) <|
    Derives.trans
      (by simpa [bc, Word.append_assoc] using step3) <|
    Derives.trans
      (by simpa [bc, cb, Word.append_assoc] using step4) <|
    Derives.trans
      (by simpa [bc, cb, Word.append_assoc] using step5)
      (by simpa [cb, Word.append_assoc] using step6)

/-- A word with fixed initial and final variables and an explicit interior. -/
def wordOfEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) : Word Nat :=
  ⟨initial, middle ++ [final]⟩

theorem wordOfEndpoints_eq
    (initial : Nat) (middle : List Nat) (final : Nat) :
    wordOfEndpoints initial middle final =
      Word.singleton initial ++ wordOfPrefixFinal middle final := by
  induction middle with
  | nil => rfl
  | cons x xs ih =>
      apply Word.toList_injective
      rw [Word.toList_append, Word.toList_singleton,
        toList_wordOfPrefixFinal]
      rfl

@[simp]
theorem wordOfEndpoints_cons
    (initial x : Nat) (middle : List Nat) (final : Nat) :
    wordOfEndpoints initial (x :: middle) final =
      Word.singleton initial ++ wordOfEndpoints x middle final := rfl

@[simp]
theorem wordOfEndpoints_nil (initial final : Nat) :
    wordOfEndpoints initial [] final =
      Word.singleton initial ++ Word.singleton final := rfl

@[simp]
theorem toList_wordOfEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) :
    (wordOfEndpoints initial middle final).toList =
      initial :: middle ++ [final] := by
  rfl

private theorem simpleEndpointsDerivesInteriorPermutation
    (initial final : Nat) {middle₁ middle₂ : List Nat}
    (hperm : middle₁.Perm middle₂) :
    Derives simpleEndpointsBasis
      (wordOfEndpoints initial middle₁ final)
      (wordOfEndpoints initial middle₂ final) := by
  induction hperm generalizing initial with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa [wordOfEndpoints_eq, Word.append_assoc] using
        Derives.prepend (Word.singleton initial) (ih x)
  | swap x y xs =>
      simpa [wordOfEndpoints_eq, Word.append_assoc] using
        simpleEndpointsDerivesInteriorSwap
          (Word.singleton initial)
          (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs final)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ initial) (ih₂ initial)

/-- Retain one representative of every interior variable. -/
def simpleEndpointsMiddleReduce (middle : List Nat) : List Nat :=
  finalMarkerPrefixReduce middle

theorem simpleEndpointsMiddleReduce_mem (z : Nat) (middle : List Nat) :
    z ∈ simpleEndpointsMiddleReduce middle ↔ z ∈ middle :=
  finalMarkerPrefixReduce_mem z middle

theorem simpleEndpointsMiddleReduce_nodup (middle : List Nat) :
    (simpleEndpointsMiddleReduce middle).Nodup :=
  finalMarkerPrefixReduce_nodup middle

private theorem simpleEndpointsDerivesDeleteLeadingInterior
    (initial x final : Nat) (middle : List Nat)
    (hx : x ∈ middle) :
    Derives simpleEndpointsBasis
      (wordOfEndpoints initial (x :: middle) final)
      (wordOfEndpoints initial middle final) := by
  have expose : middle.Perm (x :: middle.erase x) :=
    List.perm_cons_erase hx
  have sourcePerm :
      (x :: middle).Perm (x :: x :: middle.erase x) :=
    List.Perm.cons x expose
  have contract :
      Derives simpleEndpointsBasis
        (wordOfEndpoints initial (x :: x :: middle.erase x) final)
        (wordOfEndpoints initial (x :: middle.erase x) final) := by
    simpa [wordOfEndpoints_eq, Word.append_assoc] using
      simpleEndpointsDerivesContraction
        (Word.singleton initial) (Word.singleton x)
        (wordOfPrefixFinal (middle.erase x) final)
  exact Derives.trans
    (simpleEndpointsDerivesInteriorPermutation
      initial final sourcePerm) <|
    Derives.trans contract <|
      simpleEndpointsDerivesInteriorPermutation
        initial final expose.symm

theorem simpleEndpointsDerivesNormalizeMiddle :
    ∀ (initial : Nat) (middle : List Nat) (final : Nat),
      Derives simpleEndpointsBasis
        (wordOfEndpoints initial middle final)
        (wordOfEndpoints initial
          (simpleEndpointsMiddleReduce middle) final)
  | initial, [], final => Derives.refl _
  | initial, x :: xs, final => by
      have tailNormal :=
        simpleEndpointsDerivesNormalizeMiddle x xs final
      have prefixed :
          Derives simpleEndpointsBasis
            (wordOfEndpoints initial (x :: xs) final)
            (wordOfEndpoints initial
              (x :: simpleEndpointsMiddleReduce xs) final) := by
        simpa [wordOfEndpoints_eq, Word.append_assoc] using
          Derives.prepend (Word.singleton initial) tailNormal
      by_cases hx : x ∈ simpleEndpointsMiddleReduce xs
      · have reduceEq :
            simpleEndpointsMiddleReduce (x :: xs) =
              simpleEndpointsMiddleReduce xs := by
          change
            finalMarkerPrefixReduce (x :: xs) =
              finalMarkerPrefixReduce xs
          change x ∈ finalMarkerPrefixReduce xs at hx
          simp [finalMarkerPrefixReduce, hx]
        rw [reduceEq]
        exact Derives.trans prefixed <|
          simpleEndpointsDerivesDeleteLeadingInterior
            initial x final (simpleEndpointsMiddleReduce xs) hx
      · have reduceEq :
            simpleEndpointsMiddleReduce (x :: xs) =
              x :: simpleEndpointsMiddleReduce xs := by
          change
            finalMarkerPrefixReduce (x :: xs) =
              x :: finalMarkerPrefixReduce xs
          change x ∉ finalMarkerPrefixReduce xs at hx
          simp [finalMarkerPrefixReduce, hx]
        rw [reduceEq]
        exact prefixed

private theorem simpleEndpointsPerm_two_to_end (a b : Nat) :
    ∀ middle : List Nat,
      (a :: b :: middle).Perm (middle ++ [a, b])
  | [] => List.Perm.refl _
  | x :: xs =>
      (List.Perm.cons a (List.Perm.swap x b xs)).trans <|
        (List.Perm.swap x a (b :: xs)).trans <|
          List.Perm.cons x (simpleEndpointsPerm_two_to_end a b xs)

private theorem simpleEndpointsPerm_swap_at_end (a b : Nat) :
    ∀ middle : List Nat,
      (middle ++ [a, b]).Perm (middle ++ [b, a])
  | [] => List.Perm.swap b a []
  | x :: xs =>
      List.Perm.cons x (simpleEndpointsPerm_swap_at_end a b xs)

/-- Change a nonsimple final variable while preserving the fixed initial
variable and the interior support. -/
theorem simpleEndpointsDerivesFinalSwitch
    (initial : Nat) (middle : List Nat) (oldFinal newFinal : Nat)
    (hold : oldFinal ∈ middle) (hnew : newFinal ∈ middle) :
    Derives simpleEndpointsBasis
      (wordOfEndpoints initial middle oldFinal)
      (wordOfEndpoints initial middle newFinal) := by
  by_cases finals : oldFinal = newFinal
  · subst newFinal
    exact Derives.refl _
  · have newInErase :
        newFinal ∈ middle.erase oldFinal := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_of_ne (Ne.symm finals)]
      exact List.count_pos_iff.mpr hnew
    let remainder := (middle.erase oldFinal).erase newFinal
    have arrangeFront :
        middle.Perm (oldFinal :: newFinal :: remainder) := by
      exact (List.perm_cons_erase hold).trans <|
        List.Perm.cons oldFinal <| by
          simpa [remainder] using
            List.perm_cons_erase newInErase
    have arrange :
        middle.Perm (remainder ++ [oldFinal, newFinal]) :=
      arrangeFront.trans <|
        simpleEndpointsPerm_two_to_end oldFinal newFinal remainder
    have switchAtEnd :
        Derives simpleEndpointsBasis
          (wordOfEndpoints initial
            (remainder ++ [oldFinal, newFinal]) oldFinal)
          (wordOfEndpoints initial
            (remainder ++ [newFinal, oldFinal]) newFinal) := by
      induction remainder generalizing initial with
      | nil =>
          simpa [wordOfEndpoints_eq, Word.append_assoc] using
            Derives.prepend (Word.singleton initial) <|
              simpleEndpointsDerivesRotation
                (Word.singleton oldFinal)
                (Word.singleton newFinal)
      | cons x xs ih =>
          simpa [wordOfEndpoints_cons] using
            Derives.prepend (Word.singleton initial) (ih x)
    have restore :
        (remainder ++ [newFinal, oldFinal]).Perm middle :=
      (simpleEndpointsPerm_swap_at_end
        oldFinal newFinal remainder).symm.trans arrange.symm
    exact Derives.trans
      (simpleEndpointsDerivesInteriorPermutation
        initial oldFinal arrange) <|
      Derives.trans switchAtEnd <|
        simpleEndpointsDerivesInteriorPermutation
          initial newFinal restore

/-- Change a nonsimple initial variable while preserving the fixed final
variable and the interior support. -/
theorem simpleEndpointsDerivesInitialSwitch
    (oldInitial newInitial : Nat) (middle : List Nat) (final : Nat)
    (hold : oldInitial ∈ middle) (hnew : newInitial ∈ middle) :
    Derives simpleEndpointsBasis
      (wordOfEndpoints oldInitial middle final)
      (wordOfEndpoints newInitial middle final) := by
  by_cases initials : oldInitial = newInitial
  · subst newInitial
    exact Derives.refl _
  · have oldInErase :
        oldInitial ∈ middle.erase newInitial := by
      apply List.count_pos_iff.mp
      rw [List.count_erase_of_ne initials]
      exact List.count_pos_iff.mpr hold
    let remainder := (middle.erase newInitial).erase oldInitial
    have arrange :
        middle.Perm (newInitial :: oldInitial :: remainder) := by
      exact (List.perm_cons_erase hnew).trans <|
        List.Perm.cons newInitial <| by
          simpa [remainder] using
            List.perm_cons_erase oldInErase
    have switchAtFront :
        Derives simpleEndpointsBasis
          (wordOfEndpoints oldInitial
            (newInitial :: oldInitial :: remainder) final)
          (wordOfEndpoints newInitial
            (oldInitial :: newInitial :: remainder) final) := by
      have rotated :=
        Derives.appendRight
          (simpleEndpointsDerivesRotation
            (Word.singleton oldInitial)
            (Word.singleton newInitial))
          (wordOfPrefixFinal remainder final)
      simpa [wordOfEndpoints_eq, Word.append_assoc] using rotated
    have restore :
        (oldInitial :: newInitial :: remainder).Perm middle :=
      (List.Perm.swap newInitial oldInitial remainder).trans
        arrange.symm
    exact Derives.trans
      (simpleEndpointsDerivesInteriorPermutation
        oldInitial final arrange) <|
      Derives.trans switchAtFront <|
        simpleEndpointsDerivesInteriorPermutation
          newInitial final restore

private theorem simpleEndpointsPerm_one_to_end (x : Nat) :
    ∀ middle : List Nat, (x :: middle).Perm (middle ++ [x])
  | [] => List.Perm.refl _
  | y :: ys =>
      (List.Perm.swap y x ys).trans <|
        List.Perm.cons y (simpleEndpointsPerm_one_to_end x ys)

private theorem simpleEndpointsPerm_of_nodup_mem_iff :
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
          (simpleEndpointsPerm_of_nodup_mem_iff
            tailNodup erasedNodup tailMem)).trans targetPerm.symm

/-- Canonical interior produced when a closed endpoint is changed. It records
the old endpoint once and otherwise retains exactly the old interior support. -/
def simpleEndpointsClosedSwitchMiddle
    (oldEndpoint : Nat) (middle : List Nat) : List Nat :=
  simpleEndpointsMiddleReduce (oldEndpoint :: middle)

theorem simpleEndpointsClosedSwitchMiddle_nodup
    (oldEndpoint : Nat) (middle : List Nat) :
    (simpleEndpointsClosedSwitchMiddle oldEndpoint middle).Nodup :=
  simpleEndpointsMiddleReduce_nodup _

theorem simpleEndpointsClosedSwitchMiddle_mem
    (oldEndpoint z : Nat) (middle : List Nat) :
    z ∈ simpleEndpointsClosedSwitchMiddle oldEndpoint middle ↔
      z = oldEndpoint ∨ z ∈ middle := by
  rw [simpleEndpointsClosedSwitchMiddle,
    simpleEndpointsMiddleReduce_mem]
  simp [eq_comm]

/-- Change both equal nonsimple endpoints. The old endpoint is inserted into
the canonical interior, so support is preserved even when its only two
occurrences were the endpoints. -/
theorem simpleEndpointsDerivesClosedSwitch
    (oldEndpoint newEndpoint : Nat) (middle : List Nat)
    (middleNodup : middle.Nodup) (hnew : newEndpoint ∈ middle) :
    Derives simpleEndpointsBasis
      (wordOfEndpoints oldEndpoint middle oldEndpoint)
      (wordOfEndpoints newEndpoint
        (simpleEndpointsClosedSwitchMiddle oldEndpoint middle)
        newEndpoint) := by
  by_cases endpoints : oldEndpoint = newEndpoint
  · subst newEndpoint
    have reducedPerm :
        middle.Perm
          (simpleEndpointsClosedSwitchMiddle oldEndpoint middle) := by
      apply simpleEndpointsPerm_of_nodup_mem_iff
        middleNodup
        (simpleEndpointsClosedSwitchMiddle_nodup oldEndpoint middle)
      intro z
      rw [simpleEndpointsClosedSwitchMiddle_mem]
      constructor
      · intro hz
        exact Or.inr hz
      · intro hz
        rcases hz with rfl | hz
        · exact hnew
        · exact hz
    exact simpleEndpointsDerivesInteriorPermutation
      oldEndpoint oldEndpoint reducedPerm
  · let remainder := middle.erase newEndpoint
    have arrange :
        middle.Perm (newEndpoint :: remainder) := by
      simpa [remainder] using List.perm_cons_erase hnew
    have duplicate :
        Derives simpleEndpointsBasis
          (wordOfEndpoints oldEndpoint
            (newEndpoint :: remainder) oldEndpoint)
          (wordOfEndpoints oldEndpoint
            (newEndpoint :: newEndpoint :: remainder) oldEndpoint) := by
      simpa [wordOfEndpoints_eq, Word.append_assoc] using
        Derives.symm <|
          simpleEndpointsDerivesContraction
            (Word.singleton oldEndpoint)
            (Word.singleton newEndpoint)
            (wordOfPrefixFinal remainder oldEndpoint)
    have spread :
        (newEndpoint :: newEndpoint :: remainder).Perm
          (newEndpoint :: remainder ++ [newEndpoint]) :=
      List.Perm.cons newEndpoint <|
        simpleEndpointsPerm_one_to_end newEndpoint remainder
    let largeMiddle :=
      remainder ++ [newEndpoint, oldEndpoint, newEndpoint] ++ remainder
    have rotate :
        Derives simpleEndpointsBasis
          (wordOfEndpoints oldEndpoint
            (newEndpoint :: remainder ++ [newEndpoint]) oldEndpoint)
          (wordOfEndpoints newEndpoint largeMiddle newEndpoint) := by
      let block :=
        wordOfPrefixFinal (newEndpoint :: remainder) newEndpoint
      have h :=
        simpleEndpointsDerivesRotation
          (Word.singleton oldEndpoint)
          block
      have sourceEq :
          ((Word.singleton oldEndpoint ++ block) ++
              Word.singleton oldEndpoint) =
            wordOfEndpoints oldEndpoint
              (newEndpoint :: remainder ++ [newEndpoint])
              oldEndpoint := by
        apply Word.toList_injective
        rw [Word.toList_append, Word.toList_append]
        rw [show block.toList =
            (newEndpoint :: remainder) ++ [newEndpoint] by
          exact toList_wordOfPrefixFinal _ _]
        rw [toList_wordOfEndpoints]
        simp [List.append_assoc]
      have targetEq :
          ((block ++ Word.singleton oldEndpoint) ++ block) =
            wordOfEndpoints newEndpoint largeMiddle newEndpoint := by
        apply Word.toList_injective
        rw [Word.toList_append, Word.toList_append]
        rw [show block.toList =
            (newEndpoint :: remainder) ++ [newEndpoint] by
          exact toList_wordOfPrefixFinal _ _]
        rw [toList_wordOfEndpoints]
        simp [largeMiddle, List.append_assoc]
      rw [← sourceEq, ← targetEq]
      exact h
    have normalized :=
      simpleEndpointsDerivesNormalizeMiddle
        newEndpoint largeMiddle newEndpoint
    have middleMem :
        ∀ z, z ∈ middle ↔ z = newEndpoint ∨ z ∈ remainder := by
      intro z
      simpa [remainder, eq_comm] using arrange.mem_iff
    have reducedPerm :
        (simpleEndpointsMiddleReduce largeMiddle).Perm
          (simpleEndpointsClosedSwitchMiddle oldEndpoint middle) := by
      apply simpleEndpointsPerm_of_nodup_mem_iff
        (simpleEndpointsMiddleReduce_nodup largeMiddle)
        (simpleEndpointsClosedSwitchMiddle_nodup oldEndpoint middle)
      intro z
      rw [simpleEndpointsMiddleReduce_mem,
        simpleEndpointsClosedSwitchMiddle_mem]
      rw [middleMem]
      simp [largeMiddle, or_assoc, or_left_comm, or_comm]
    exact Derives.trans
      (simpleEndpointsDerivesInteriorPermutation
        oldEndpoint oldEndpoint arrange) <|
      Derives.trans duplicate <|
      Derives.trans
        (simpleEndpointsDerivesInteriorPermutation
          oldEndpoint oldEndpoint spread) <|
      Derives.trans rotate <|
      Derives.trans normalized <|
        simpleEndpointsDerivesInteriorPermutation
          newEndpoint newEndpoint reducedPerm

private theorem simpleEndpointsMul_contraction
    (a b c : Fin 4) :
    simpleEndpointsFourMul
        (simpleEndpointsFourMul
          (simpleEndpointsFourMul a b) b) c =
      simpleEndpointsFourMul
        (simpleEndpointsFourMul a b) c := by
  decide +revert

private theorem simpleEndpointsMul_rotation
    (a b : Fin 4) :
    simpleEndpointsFourMul
        (simpleEndpointsFourMul a b) a =
      simpleEndpointsFourMul
        (simpleEndpointsFourMul b a) b := by
  decide +revert

private theorem simpleEndpointsMul_power
    (a : Fin 4) :
    simpleEndpointsFourMul a a =
      simpleEndpointsFourMul
        (simpleEndpointsFourMul a a) a := by
  decide +revert

theorem simpleEndpointsFourBasis_models :
    Models simpleEndpointsFour.semigroup simpleEndpointsBasis := by
  intro e he
  simp only [simpleEndpointsBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    exact simpleEndpointsMul_contraction
      (valuation 0) (valuation 1) (valuation 2)
  · intro valuation
    exact simpleEndpointsMul_rotation
      (valuation 0) (valuation 1)
  · intro valuation
    exact simpleEndpointsMul_power (valuation 0)

private def simpleEndpointsSupportSeparator
    (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 0 else 3

theorem simpleEndpointsEval_supportSeparator
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    simpleEndpointsFour.semigroup.eval
        (simpleEndpointsSupportSeparator z)
        (wordOfEndpoints initial middle final) =
      if z ∈ initial :: middle ∨ final = z
      then (0 : Fin 4) else (3 : Fin 4) := by
  induction middle generalizing initial with
  | nil =>
      rw [wordOfEndpoints_nil, Semigroup.eval_append,
        Semigroup.eval_singleton, Semigroup.eval_singleton]
      by_cases hi : initial = z <;>
        by_cases hf : final = z <;>
          simp_all [simpleEndpointsSupportSeparator,
            simpleEndpointsFour, FiniteTable.semigroup,
            simpleEndpointsFourMul, eq_comm]
  | cons x xs ih =>
      rw [wordOfEndpoints_cons, Semigroup.eval_append,
        Semigroup.eval_singleton, ih]
      change
        simpleEndpointsFourMul
            (simpleEndpointsSupportSeparator z initial)
            (if z ∈ x :: xs ∨ final = z
              then (0 : Fin 4) else (3 : Fin 4)) =
          if z ∈ initial :: x :: xs ∨ final = z
          then (0 : Fin 4) else (3 : Fin 4)
      by_cases hi : initial = z <;>
        by_cases ht : z ∈ x :: xs ∨ final = z <;>
          simp_all [simpleEndpointsSupportSeparator,
            simpleEndpointsFourMul, eq_comm]

theorem simpleEndpointsEval_supportSeparator_eq_three_iff
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    simpleEndpointsFour.semigroup.eval
        (simpleEndpointsSupportSeparator z)
        (wordOfEndpoints initial middle final) = (3 : Fin 4) ↔
      z ∉ initial :: middle ∧ final ≠ z := by
  rw [simpleEndpointsEval_supportSeparator]
  by_cases hp : z ∈ initial :: middle <;>
    by_cases hf : final = z <;> simp [hp, hf]

private def simpleEndpointsInitialSeparator
    (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 3

theorem simpleEndpointsEval_initialSeparator
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    simpleEndpointsFour.semigroup.eval
        (simpleEndpointsInitialSeparator z)
        (wordOfEndpoints initial middle final) =
      if initial = z then
        if z ∈ middle ∨ final = z then (0 : Fin 4) else (2 : Fin 4)
      else
        if z ∈ middle ∨ final = z then (0 : Fin 4) else (3 : Fin 4) := by
  induction middle generalizing initial with
  | nil =>
      rw [wordOfEndpoints_nil, Semigroup.eval_append,
        Semigroup.eval_singleton, Semigroup.eval_singleton]
      by_cases hi : initial = z <;>
        by_cases hf : final = z <;>
          simp_all [simpleEndpointsInitialSeparator,
            simpleEndpointsFour, FiniteTable.semigroup,
            simpleEndpointsFourMul, eq_comm]
  | cons x xs ih =>
      rw [wordOfEndpoints_cons, Semigroup.eval_append,
        Semigroup.eval_singleton, ih]
      change
        simpleEndpointsFourMul
            (simpleEndpointsInitialSeparator z initial)
            (if x = z then
              if z ∈ xs ∨ final = z then (0 : Fin 4) else (2 : Fin 4)
            else
              if z ∈ xs ∨ final = z then (0 : Fin 4) else (3 : Fin 4)) =
          if initial = z then
            if z ∈ x :: xs ∨ final = z
            then (0 : Fin 4) else (2 : Fin 4)
          else
            if z ∈ x :: xs ∨ final = z
            then (0 : Fin 4) else (3 : Fin 4)
      by_cases hi : initial = z <;>
        by_cases hx : x = z <;>
          by_cases ht : z ∈ xs ∨ final = z <;>
            simp_all [simpleEndpointsInitialSeparator,
              simpleEndpointsFourMul, eq_comm]

theorem simpleEndpointsEval_initialSeparator_eq_two_iff
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    simpleEndpointsFour.semigroup.eval
        (simpleEndpointsInitialSeparator z)
        (wordOfEndpoints initial middle final) = (2 : Fin 4) ↔
      initial = z ∧ z ∉ middle ∧ final ≠ z := by
  rw [simpleEndpointsEval_initialSeparator]
  by_cases hi : initial = z <;>
    by_cases hm : z ∈ middle <;>
      by_cases hf : final = z <;> simp [hi, hm, hf]

private def simpleEndpointsFinalSeparator
    (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 3

theorem simpleEndpointsEval_finalSeparator
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    simpleEndpointsFour.semigroup.eval
        (simpleEndpointsFinalSeparator z)
        (wordOfEndpoints initial middle final) =
      if z ∈ initial :: middle then (0 : Fin 4) else
        if final = z then (1 : Fin 4) else (3 : Fin 4) := by
  induction middle generalizing initial with
  | nil =>
      rw [wordOfEndpoints_nil, Semigroup.eval_append,
        Semigroup.eval_singleton, Semigroup.eval_singleton]
      by_cases hi : initial = z <;>
        by_cases hf : final = z <;>
          simp_all [simpleEndpointsFinalSeparator,
            simpleEndpointsFour, FiniteTable.semigroup,
            simpleEndpointsFourMul, eq_comm]
  | cons x xs ih =>
      rw [wordOfEndpoints_cons, Semigroup.eval_append,
        Semigroup.eval_singleton, ih]
      change
        simpleEndpointsFourMul
            (simpleEndpointsFinalSeparator z initial)
            (if z ∈ x :: xs then (0 : Fin 4) else
              if final = z then (1 : Fin 4) else (3 : Fin 4)) =
          if z ∈ initial :: x :: xs then (0 : Fin 4) else
            if final = z then (1 : Fin 4) else (3 : Fin 4)
      by_cases hi : initial = z <;>
        by_cases hx : x = z <;>
          by_cases hm : z ∈ xs <;>
            by_cases hf : final = z <;>
              simp_all [simpleEndpointsFinalSeparator,
                simpleEndpointsFourMul, eq_comm]

theorem simpleEndpointsEval_finalSeparator_eq_one_iff
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    simpleEndpointsFour.semigroup.eval
        (simpleEndpointsFinalSeparator z)
        (wordOfEndpoints initial middle final) = (1 : Fin 4) ↔
      final = z ∧ z ∉ initial :: middle := by
  rw [simpleEndpointsEval_finalSeparator]
  by_cases hp : z ∈ initial :: middle <;>
    by_cases hf : final = z <;> simp [hp, hf]

/-- Add the common endpoint to the interior support when the endpoints agree.
After this saturation, an endpoint is globally simple exactly when it is
absent from the saturated middle. -/
def simpleEndpointsSaturatedMiddle
    (initial : Nat) (middle : List Nat) (final : Nat) : List Nat :=
  if initial = final then
    simpleEndpointsMiddleReduce (initial :: middle)
  else middle

theorem simpleEndpointsSaturatedMiddle_nodup
    (initial final : Nat) {middle : List Nat}
    (middleNodup : middle.Nodup) :
    (simpleEndpointsSaturatedMiddle initial middle final).Nodup := by
  by_cases endpoints : initial = final
  · simp [simpleEndpointsSaturatedMiddle, endpoints,
      simpleEndpointsMiddleReduce_nodup]
  · simp [simpleEndpointsSaturatedMiddle, endpoints, middleNodup]

theorem simpleEndpointsSaturatedMiddle_mem
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    z ∈ simpleEndpointsSaturatedMiddle initial middle final ↔
      z ∈ middle ∨ initial = final ∧ z = initial := by
  by_cases endpoints : initial = final
  · subst final
    simp [simpleEndpointsSaturatedMiddle,
      simpleEndpointsMiddleReduce_mem, eq_comm, or_comm]
  · simp [simpleEndpointsSaturatedMiddle, endpoints]

/-- Every endpoint word derives its saturated form once the interior has no
duplicates. The nontrivial branch is a closed word whose endpoint is missing
from the interior. -/
theorem simpleEndpointsDerivesSaturate
    (initial : Nat) (middle : List Nat) (final : Nat)
    (middleNodup : middle.Nodup) :
    Derives simpleEndpointsBasis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (simpleEndpointsSaturatedMiddle initial middle final) final) := by
  by_cases endpoints : initial = final
  · subst final
    by_cases present : initial ∈ middle
    · have targetPerm :
          middle.Perm
            (simpleEndpointsSaturatedMiddle initial middle initial) := by
        apply simpleEndpointsPerm_of_nodup_mem_iff
          middleNodup
          (simpleEndpointsSaturatedMiddle_nodup
            initial initial middleNodup)
        intro z
        rw [simpleEndpointsSaturatedMiddle_mem]
        constructor
        · exact Or.inl
        · rintro (hz | ⟨_, rfl⟩)
          · exact hz
          · exact present
      exact simpleEndpointsDerivesInteriorPermutation
        initial initial targetPerm
    · cases middle with
      | nil =>
          simpa [simpleEndpointsSaturatedMiddle,
            simpleEndpointsMiddleReduce, finalMarkerPrefixReduce,
            wordOfEndpoints_eq, Word.append_assoc] using
            simpleEndpointsDerivesPowerExpansion
              (Word.singleton initial)
      | cons x xs =>
          let firstMiddle :=
            simpleEndpointsClosedSwitchMiddle initial (x :: xs)
          have first :
              Derives simpleEndpointsBasis
                (wordOfEndpoints initial (x :: xs) initial)
                (wordOfEndpoints x firstMiddle x) := by
            simpa [firstMiddle] using
              simpleEndpointsDerivesClosedSwitch
                initial x (x :: xs) middleNodup
                (List.Mem.head xs)
          have firstNodup : firstMiddle.Nodup := by
            simpa [firstMiddle] using
              simpleEndpointsClosedSwitchMiddle_nodup
                initial (x :: xs)
          have initialInFirst : initial ∈ firstMiddle := by
            change initial ∈
              simpleEndpointsClosedSwitchMiddle initial (x :: xs)
            rw [simpleEndpointsClosedSwitchMiddle_mem]
            exact Or.inl rfl
          let secondMiddle :=
            simpleEndpointsClosedSwitchMiddle x firstMiddle
          have second :
              Derives simpleEndpointsBasis
                (wordOfEndpoints x firstMiddle x)
                (wordOfEndpoints initial secondMiddle initial) := by
            simpa [secondMiddle] using
              simpleEndpointsDerivesClosedSwitch
                x initial firstMiddle firstNodup initialInFirst
          have secondNodup : secondMiddle.Nodup := by
            simpa [secondMiddle] using
              simpleEndpointsClosedSwitchMiddle_nodup x firstMiddle
          have restore :
              secondMiddle.Perm
                (simpleEndpointsSaturatedMiddle
                  initial (x :: xs) initial) := by
            apply simpleEndpointsPerm_of_nodup_mem_iff
              secondNodup
              (simpleEndpointsSaturatedMiddle_nodup
                initial initial middleNodup)
            intro z
            simp only [secondMiddle, firstMiddle]
            rw [simpleEndpointsClosedSwitchMiddle_mem,
              simpleEndpointsSaturatedMiddle_mem]
            rw [simpleEndpointsClosedSwitchMiddle_mem]
            constructor
            · rintro (rfl | hz)
              · exact Or.inl (List.Mem.head xs)
              · rcases hz with rfl | hz
                · exact Or.inr ⟨rfl, rfl⟩
                · exact Or.inl hz
            · rintro (hz | ⟨_, rfl⟩)
              · exact Or.inr <| Or.inr hz
              · exact Or.inr <| Or.inl rfl
          exact Derives.trans first <|
            Derives.trans second <|
              simpleEndpointsDerivesInteriorPermutation
                initial initial restore
  · simp [simpleEndpointsSaturatedMiddle, endpoints]
    exact Derives.refl _

private theorem simpleEndpointsMiddle_mem_iff_semantic
    (z initial : Nat) (middle : List Nat) (final : Nat)
    (closed : initial = final → initial ∈ middle) :
    z ∈ middle ↔
      (z ∈ initial :: middle ∨ final = z) ∧
      ¬(initial = z ∧ z ∉ middle ∧ final ≠ z) ∧
      ¬(final = z ∧ z ∉ initial :: middle) := by
  constructor
  · intro hz
    exact ⟨Or.inl (List.Mem.tail initial hz),
      fun h => h.2.1 hz,
      fun h => h.2 (List.Mem.tail initial hz)⟩
  · rintro ⟨support, notInitial, notFinal⟩
    apply Decidable.byContradiction
    intro hz
    by_cases hi : initial = z
    · by_cases hf : final = z
      · apply hz
        simpa [hi] using closed (hi.trans hf.symm)
      · exact notInitial ⟨hi, hz, hf⟩
    · by_cases hf : final = z
      · apply notFinal
        refine ⟨hf, ?_⟩
        simpa [Ne.symm hi, hz]
      · exact False.elim <| by
          rcases support with support | support
          · exact hi <| (by simpa [hz] using support : z = initial).symm
          · exact hf support

private theorem simpleEndpointsNormalizedDerives
    (initial₁ initial₂ : Nat)
    (middle₁ middle₂ : List Nat)
    (final₁ final₂ : Nat)
    (nodup₁ : middle₁.Nodup) (nodup₂ : middle₂.Nodup)
    (closed₁ : initial₁ = final₁ → initial₁ ∈ middle₁)
    (closed₂ : initial₂ = final₂ → initial₂ ∈ middle₂)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial₁ middle₁ final₁) =
          simpleEndpointsFour.semigroup.eval valuation
            (wordOfEndpoints initial₂ middle₂ final₂)) :
    Derives simpleEndpointsBasis
      (wordOfEndpoints initial₁ middle₁ final₁)
      (wordOfEndpoints initial₂ middle₂ final₂) := by
  have supportIff :
      ∀ z,
        (z ∈ initial₁ :: middle₁ ∨ final₁ = z) ↔
          (z ∈ initial₂ :: middle₂ ∨ final₂ = z) := by
    intro z
    have absentIff :
        (z ∉ initial₁ :: middle₁ ∧ final₁ ≠ z) ↔
          (z ∉ initial₂ :: middle₂ ∧ final₂ ≠ z) := by
      constructor
      · intro h
        apply
          (simpleEndpointsEval_supportSeparator_eq_three_iff
            z initial₂ middle₂ final₂).1
        exact (equalEval (simpleEndpointsSupportSeparator z)).symm.trans <|
          (simpleEndpointsEval_supportSeparator_eq_three_iff
            z initial₁ middle₁ final₁).2 h
      · intro h
        apply
          (simpleEndpointsEval_supportSeparator_eq_three_iff
            z initial₁ middle₁ final₁).1
        exact (equalEval (simpleEndpointsSupportSeparator z)).trans <|
          (simpleEndpointsEval_supportSeparator_eq_three_iff
            z initial₂ middle₂ final₂).2 h
    constructor
    · intro h
      apply Decidable.byContradiction
      intro hn
      have absent₂ :
          z ∉ initial₂ :: middle₂ ∧ final₂ ≠ z := by
        simpa [not_or] using hn
      have absent₁ := absentIff.mpr absent₂
      exact (by simpa [not_or] using absent₁ : ¬
        (z ∈ initial₁ :: middle₁ ∨ final₁ = z)) h
    · intro h
      apply Decidable.byContradiction
      intro hn
      have absent₁ :
          z ∉ initial₁ :: middle₁ ∧ final₁ ≠ z := by
        simpa [not_or] using hn
      have absent₂ := absentIff.mp absent₁
      exact (by simpa [not_or] using absent₂ : ¬
        (z ∈ initial₂ :: middle₂ ∨ final₂ = z)) h
  have initialIff :
      ∀ z,
        (initial₁ = z ∧ z ∉ middle₁ ∧ final₁ ≠ z) ↔
          (initial₂ = z ∧ z ∉ middle₂ ∧ final₂ ≠ z) := by
    intro z
    constructor
    · intro h
      apply
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          z initial₂ middle₂ final₂).1
      exact (equalEval (simpleEndpointsInitialSeparator z)).symm.trans <|
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          z initial₁ middle₁ final₁).2 h
    · intro h
      apply
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          z initial₁ middle₁ final₁).1
      exact (equalEval (simpleEndpointsInitialSeparator z)).trans <|
        (simpleEndpointsEval_initialSeparator_eq_two_iff
          z initial₂ middle₂ final₂).2 h
  have finalIff :
      ∀ z,
        (final₁ = z ∧ z ∉ initial₁ :: middle₁) ↔
          (final₂ = z ∧ z ∉ initial₂ :: middle₂) := by
    intro z
    constructor
    · intro h
      apply
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          z initial₂ middle₂ final₂).1
      exact (equalEval (simpleEndpointsFinalSeparator z)).symm.trans <|
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          z initial₁ middle₁ final₁).2 h
    · intro h
      apply
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          z initial₁ middle₁ final₁).1
      exact (equalEval (simpleEndpointsFinalSeparator z)).trans <|
        (simpleEndpointsEval_finalSeparator_eq_one_iff
          z initial₂ middle₂ final₂).2 h
  have middleMem : ∀ z, z ∈ middle₁ ↔ z ∈ middle₂ := by
    intro z
    rw [simpleEndpointsMiddle_mem_iff_semantic
      z initial₁ middle₁ final₁ closed₁]
    rw [simpleEndpointsMiddle_mem_iff_semantic
      z initial₂ middle₂ final₂ closed₂]
    exact and_congr (supportIff z) <|
      and_congr (not_congr (initialIff z))
        (not_congr (finalIff z))
  have initialDerivation :
      Derives simpleEndpointsBasis
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₁ final₁) := by
    by_cases simple₁ : initial₁ ∉ middle₁
    · have finalNe : final₁ ≠ initial₁ := by
        intro h
        exact simple₁ (closed₁ h.symm)
      have matched :=
        (initialIff initial₁).mp ⟨rfl, simple₁, finalNe⟩
      simpa [matched.1] using
        (Derives.refl
          (wordOfEndpoints initial₁ middle₁ final₁) :
            Derives simpleEndpointsBasis
              (wordOfEndpoints initial₁ middle₁ final₁)
              (wordOfEndpoints initial₁ middle₁ final₁))
    · have repeated₁ : initial₁ ∈ middle₁ :=
        Decidable.byContradiction simple₁
      have repeated₂ : initial₂ ∈ middle₂ := by
        apply Decidable.byContradiction
        intro absent₂
        have finalNe₂ : final₂ ≠ initial₂ := by
          intro h
          exact absent₂ (closed₂ h.symm)
        have simpleOnLeft :=
          (initialIff initial₂).mpr ⟨rfl, absent₂, finalNe₂⟩
        exact simpleOnLeft.2.1 <| by
          simpa [simpleOnLeft.1] using repeated₁
      exact simpleEndpointsDerivesInitialSwitch
        initial₁ initial₂ middle₁ final₁ repeated₁
        ((middleMem initial₂).2 repeated₂)
  have finalDerivation :
      Derives simpleEndpointsBasis
        (wordOfEndpoints initial₂ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₁ final₂) := by
    by_cases simple₁ : final₁ ∉ middle₁
    · have initialNe : initial₁ ≠ final₁ := by
        intro h
        exact simple₁ <| by simpa [h] using closed₁ h
      have matched :=
        (finalIff final₁).mp
          ⟨rfl, by simpa [Ne.symm initialNe, simple₁]⟩
      simpa [matched.1] using
        (Derives.refl
          (wordOfEndpoints initial₂ middle₁ final₁) :
            Derives simpleEndpointsBasis
              (wordOfEndpoints initial₂ middle₁ final₁)
              (wordOfEndpoints initial₂ middle₁ final₁))
    · have repeated₁ : final₁ ∈ middle₁ :=
        Decidable.byContradiction simple₁
      have repeated₂ : final₂ ∈ middle₂ := by
        apply Decidable.byContradiction
        intro absent₂
        have initialNe₂ : initial₂ ≠ final₂ := by
          intro h
          exact absent₂ <| by simpa [h] using closed₂ h
        have simpleOnLeft :=
          (finalIff final₂).mpr
            ⟨rfl, by
              simpa [Ne.symm initialNe₂, absent₂]⟩
        apply simpleOnLeft.2
        exact List.Mem.tail initial₁ <| by
          simpa [simpleOnLeft.1] using repeated₁
      exact simpleEndpointsDerivesFinalSwitch
        initial₂ middle₁ final₁ final₂ repeated₁
        ((middleMem final₂).2 repeated₂)
  have middlePerm : middle₁.Perm middle₂ :=
    simpleEndpointsPerm_of_nodup_mem_iff nodup₁ nodup₂ middleMem
  exact Derives.trans initialDerivation <|
    Derives.trans finalDerivation <|
      simpleEndpointsDerivesInteriorPermutation
        initial₂ final₂ middlePerm

def simpleEndpointsNormalMiddle
    (initial : Nat) (middle : List Nat) (final : Nat) : List Nat :=
  simpleEndpointsSaturatedMiddle initial
    (simpleEndpointsMiddleReduce middle) final

theorem simpleEndpointsNormalMiddle_nodup
    (initial : Nat) (middle : List Nat) (final : Nat) :
    (simpleEndpointsNormalMiddle initial middle final).Nodup :=
  simpleEndpointsSaturatedMiddle_nodup initial final
    (simpleEndpointsMiddleReduce_nodup middle)

theorem simpleEndpointsNormalMiddle_closed
    (initial : Nat) (middle : List Nat) (final : Nat) :
    initial = final →
      initial ∈ simpleEndpointsNormalMiddle initial middle final := by
  intro endpoints
  apply
    (simpleEndpointsSaturatedMiddle_mem
      initial initial (simpleEndpointsMiddleReduce middle) final).2
  exact Or.inr ⟨endpoints, rfl⟩

theorem simpleEndpointsDerivesNormalEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives simpleEndpointsBasis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (simpleEndpointsNormalMiddle initial middle final) final) := by
  exact Derives.trans
    (simpleEndpointsDerivesNormalizeMiddle initial middle final) <|
      simpleEndpointsDerivesSaturate initial
        (simpleEndpointsMiddleReduce middle) final
        (simpleEndpointsMiddleReduce_nodup middle)

private theorem simpleEndpointsFold_zero
    (xs : List Nat) :
    xs.foldl
        (fun current _ =>
          simpleEndpointsFourMul current (1 : Fin 4))
        (0 : Fin 4) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      change
        xs.foldl
          (fun current _ =>
            simpleEndpointsFourMul current (1 : Fin 4))
          (simpleEndpointsFourMul 0 1) = 0
      rw [show simpleEndpointsFourMul 0 1 = (0 : Fin 4) by decide]
      exact ih

/-- The constant valuation `1` separates singleton words from all longer
words. -/
theorem simpleEndpointsSingletonSeparator (w : Word Nat) :
    simpleEndpointsFour.semigroup.eval
        (fun _ => (1 : Fin 4)) w = (1 : Fin 4) ↔
      w.tail = [] := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              simpleEndpointsFourMul current (1 : Fin 4))
            (1 : Fin 4) = 1 ↔
          tail = []
      cases tail with
      | nil => simp
      | cons x xs =>
          simp only [List.foldl_cons, List.cons_ne_nil, iff_false]
          rw [show simpleEndpointsFourMul 1 1 = (0 : Fin 4) by decide]
          rw [simpleEndpointsFold_zero]
          decide

/-- Unrestricted completeness over `Nat` variables. Normal forms retain the
support and precisely those initial and final variables that occur globally
once. -/
theorem simpleEndpointsFourBasis_complete :
    BasisFor simpleEndpointsFour.semigroup simpleEndpointsBasis := by
  refine ⟨simpleEndpointsFourBasis_models, ?_⟩
  intro e valid
  cases e with
  | mk lhs rhs =>
      cases lhs with
      | mk lhsInitial lhsTail =>
          cases rhs with
          | mk rhsInitial rhsTail =>
              cases lhsTail with
              | nil =>
                  cases rhsTail with
                  | nil =>
                      have evaluated :=
                        valid
                          (simpleEndpointsSupportSeparator lhsInitial)
                      change
                        simpleEndpointsSupportSeparator
                            lhsInitial lhsInitial =
                          simpleEndpointsSupportSeparator
                            lhsInitial rhsInitial at evaluated
                      have initials : lhsInitial = rhsInitial := by
                        apply Decidable.byContradiction
                        intro hne
                        simp [simpleEndpointsSupportSeparator,
                          hne, Ne.symm hne] at evaluated
                      subst rhsInitial
                      exact Derives.refl _
                  | cons rhsNext rhsRest =>
                      have evaluated := valid (fun _ => (1 : Fin 4))
                      have lhsOne :=
                        (simpleEndpointsSingletonSeparator
                          (Word.mk lhsInitial [])).2 rfl
                      have rhsOne := evaluated.symm.trans lhsOne
                      have tailNil :=
                        (simpleEndpointsSingletonSeparator
                          (Word.mk rhsInitial
                            (rhsNext :: rhsRest))).1 rhsOne
                      simp at tailNil
              | cons lhsNext lhsRest =>
                      cases rhsTail with
                      | nil =>
                          have evaluated := valid (fun _ => (1 : Fin 4))
                          have rhsOne :=
                            (simpleEndpointsSingletonSeparator
                              (Word.mk rhsInitial [])).2 rfl
                          have lhsOne := evaluated.trans rhsOne
                          have tailNil :=
                            (simpleEndpointsSingletonSeparator
                              (Word.mk lhsInitial
                                (lhsNext :: lhsRest))).1 lhsOne
                          simp at tailNil
                      | cons rhsNext rhsRest =>
                          let lhsSuffix : Word Nat :=
                            Word.mk lhsNext lhsRest
                          let rhsSuffix : Word Nat :=
                            Word.mk rhsNext rhsRest
                          let lhsSplit := splitPrefixFinal lhsSuffix
                          let rhsSplit := splitPrefixFinal rhsSuffix
                          let lhsMiddle :=
                            simpleEndpointsNormalMiddle
                              lhsInitial lhsSplit.1 lhsSplit.2
                          let rhsMiddle :=
                            simpleEndpointsNormalMiddle
                              rhsInitial rhsSplit.1 rhsSplit.2
                          have lhsReconstruct :
                              wordOfEndpoints lhsInitial
                                  lhsSplit.1 lhsSplit.2 =
                                Word.mk lhsInitial
                                  (lhsNext :: lhsRest) := by
                            rw [wordOfEndpoints_eq]
                            simp only [lhsSplit]
                            rw [wordOfPrefixFinal_split lhsSuffix]
                            rfl
                          have rhsReconstruct :
                              wordOfEndpoints rhsInitial
                                  rhsSplit.1 rhsSplit.2 =
                                Word.mk rhsInitial
                                  (rhsNext :: rhsRest) := by
                            rw [wordOfEndpoints_eq]
                            simp only [rhsSplit]
                            rw [wordOfPrefixFinal_split rhsSuffix]
                            rfl
                          have lhsNormal :
                              Derives simpleEndpointsBasis
                                (Word.mk lhsInitial
                                  (lhsNext :: lhsRest))
                                (wordOfEndpoints lhsInitial
                                  lhsMiddle lhsSplit.2) := by
                            rw [← lhsReconstruct]
                            simpa [lhsMiddle] using
                              simpleEndpointsDerivesNormalEndpoints
                                lhsInitial lhsSplit.1 lhsSplit.2
                          have rhsNormal :
                              Derives simpleEndpointsBasis
                                (Word.mk rhsInitial
                                  (rhsNext :: rhsRest))
                                (wordOfEndpoints rhsInitial
                                  rhsMiddle rhsSplit.2) := by
                            rw [← rhsReconstruct]
                            simpa [rhsMiddle] using
                              simpleEndpointsDerivesNormalEndpoints
                                rhsInitial rhsSplit.1 rhsSplit.2
                          have normalizedEval :
                              ∀ valuation : Nat → Fin 4,
                                simpleEndpointsFour.semigroup.eval valuation
                                    (wordOfEndpoints lhsInitial
                                      lhsMiddle lhsSplit.2) =
                                  simpleEndpointsFour.semigroup.eval valuation
                                    (wordOfEndpoints rhsInitial
                                      rhsMiddle rhsSplit.2) := by
                            intro valuation
                            have lhsSound :=
                              lhsNormal.sound
                                simpleEndpointsFourBasis_models valuation
                            have rhsSound :=
                              rhsNormal.sound
                                simpleEndpointsFourBasis_models valuation
                            exact lhsSound.symm.trans <|
                              (valid valuation).trans rhsSound
                          have normalizedDerivation :=
                            simpleEndpointsNormalizedDerives
                              lhsInitial rhsInitial
                              lhsMiddle rhsMiddle
                              lhsSplit.2 rhsSplit.2
                              (by
                                simpa [lhsMiddle] using
                                  simpleEndpointsNormalMiddle_nodup
                                    lhsInitial lhsSplit.1 lhsSplit.2)
                              (by
                                simpa [rhsMiddle] using
                                  simpleEndpointsNormalMiddle_nodup
                                    rhsInitial rhsSplit.1 rhsSplit.2)
                              (by
                                simpa [lhsMiddle] using
                                  simpleEndpointsNormalMiddle_closed
                                    lhsInitial lhsSplit.1 lhsSplit.2)
                              (by
                                simpa [rhsMiddle] using
                                  simpleEndpointsNormalMiddle_closed
                                    rhsInitial rhsSplit.1 rhsSplit.2)
                              normalizedEval
                          exact Derives.trans lhsNormal <|
                            Derives.trans normalizedDerivation
                              (Derives.symm rhsNormal)

def simpleEndpointsFourOppositeBasis : List (Identity Nat) :=
  reversedBasis simpleEndpointsBasis

theorem simpleEndpointsFourOppositeBasis_complete :
    BasisFor simpleEndpointsFour.semigroup.opposite
      simpleEndpointsFourOppositeBasis := by
  simpa [simpleEndpointsFourOppositeBasis] using
    simpleEndpointsFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples
