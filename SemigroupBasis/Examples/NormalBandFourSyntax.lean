import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

def normalBandX : Word Nat := Word.singleton 0
def normalBandXX : Word Nat := ⟨0, [0]⟩
def normalBandXYZX : Word Nat := ⟨0, [1, 2, 0]⟩
def normalBandXZYX : Word Nat := ⟨0, [2, 1, 0]⟩

def normalBandIdempotenceLaw : Identity Nat :=
  ⟨normalBandX, normalBandXX⟩

def normalBandInteriorSwapLaw : Identity Nat :=
  ⟨normalBandXYZX, normalBandXZYX⟩

/-- The normal-band basis `x = xx`, `xyzx = xzyx`. -/
def normalBandBasis : List (Identity Nat) :=
  [normalBandIdempotenceLaw, normalBandInteriorSwapLaw]

private def normalBandInstantiateThree
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem normalBandDerivesIdempotenceExpansion (u : Word Nat) :
    Derives normalBandBasis u (u ++ u) := by
  have hbase :
      Derives normalBandBasis normalBandX normalBandXX :=
    Derives.fromBasis (e := normalBandIdempotenceLaw) <|
      List.Mem.head _
  have h :=
    Derives.subst hbase (normalBandInstantiateThree u u u)
  simpa [normalBandBasis, normalBandIdempotenceLaw, normalBandX,
    normalBandXX, normalBandInstantiateThree, Word.bind, Word.append,
    Word.singleton] using h

theorem normalBandDerivesIdempotenceContraction (u : Word Nat) :
    Derives normalBandBasis (u ++ u) u :=
  Derives.symm (normalBandDerivesIdempotenceExpansion u)

theorem normalBandDerivesSandwichSwap (u v w : Word Nat) :
    Derives normalBandBasis
      (((u ++ v) ++ w) ++ u)
      (((u ++ w) ++ v) ++ u) := by
  have hbase :
      Derives normalBandBasis normalBandXYZX normalBandXZYX :=
    Derives.fromBasis (e := normalBandInteriorSwapLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase (normalBandInstantiateThree u v w)
  simpa [normalBandBasis, normalBandInteriorSwapLaw,
    normalBandXYZX, normalBandXZYX, normalBandInstantiateThree,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

/-- Adjacent nonempty blocks may be interchanged between arbitrary nonempty
prefix and suffix blocks. The proof duplicates the whole word, applies the
normal-band law three times, and contracts the resulting square. -/
theorem normalBandDerivesInteriorSwap
    (a b c d : Word Nat) :
    Derives normalBandBasis
      (((a ++ b) ++ c) ++ d)
      (((a ++ c) ++ b) ++ d) := by
  let source := ((a ++ b) ++ c) ++ d
  let target := ((a ++ c) ++ b) ++ d
  have first := normalBandDerivesIdempotenceExpansion source
  have second :=
    Derives.appendRight
      (normalBandDerivesSandwichSwap a b (c ++ d))
      ((b ++ c) ++ d)
  have third :=
    Derives.appendRight
      (Derives.prepend a
        (normalBandDerivesSandwichSwap c ((d ++ b) ++ a) b))
      d
  have fourth :=
    Derives.prepend ((a ++ c) ++ b)
      (normalBandDerivesSandwichSwap d b (a ++ c))
  have fifth := normalBandDerivesIdempotenceContraction target
  exact Derives.trans
    (by simpa [source, Word.append_assoc] using first) <|
    Derives.trans
      (by simpa [source, Word.append_assoc] using second) <|
    Derives.trans
      (by simpa [Word.append_assoc] using third) <|
    Derives.trans
      (by simpa [target, Word.append_assoc] using fourth)
      (by simpa [target, Word.append_assoc] using fifth)

/-- A word with fixed initial and final variables and an explicit middle. -/
def normalBandWordOfEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) : Word Nat :=
  ⟨initial, middle ++ [final]⟩

/-- A nonempty word with the listed prefix and final variable. -/
def normalBandWordOfPrefixFinal : List Nat → Nat → Word Nat
  | [], final => Word.singleton final
  | x :: xs, final =>
      Word.singleton x ++ normalBandWordOfPrefixFinal xs final

@[simp]
theorem normalBandToList_wordOfPrefixFinal
    (pref : List Nat) (final : Nat) :
    (normalBandWordOfPrefixFinal pref final).toList =
      pref ++ [final] := by
  induction pref with
  | nil => rfl
  | cons x xs ih =>
      change
        x :: (normalBandWordOfPrefixFinal xs final).toList =
          x :: (xs ++ [final])
      rw [ih]

theorem normalBandWordOfEndpoints_eq
    (initial : Nat) (middle : List Nat) (final : Nat) :
    normalBandWordOfEndpoints initial middle final =
      Word.singleton initial ++
        normalBandWordOfPrefixFinal middle final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    normalBandToList_wordOfPrefixFinal]
  rfl

@[simp]
theorem normalBandWordOfEndpoints_cons
    (initial x : Nat) (middle : List Nat) (final : Nat) :
    normalBandWordOfEndpoints initial (x :: middle) final =
      Word.singleton initial ++
        normalBandWordOfEndpoints x middle final := rfl

@[simp]
theorem normalBandWordOfEndpoints_nil
    (initial final : Nat) :
    normalBandWordOfEndpoints initial [] final =
      Word.singleton initial ++ Word.singleton final := rfl

@[simp]
theorem normalBandToList_wordOfEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) :
    (normalBandWordOfEndpoints initial middle final).toList =
      initial :: middle ++ [final] := by
  rfl

private theorem normalBandDerivesInteriorPermutation
    (initial final : Nat) {middle₁ middle₂ : List Nat}
    (hperm : middle₁.Perm middle₂) :
    Derives normalBandBasis
      (normalBandWordOfEndpoints initial middle₁ final)
      (normalBandWordOfEndpoints initial middle₂ final) := by
  induction hperm generalizing initial with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa using Derives.prepend (Word.singleton initial) (ih x)
  | swap x y xs =>
      simpa [normalBandWordOfEndpoints_eq, Word.append_assoc] using
        normalBandDerivesInteriorSwap
          (Word.singleton initial)
          (Word.singleton y) (Word.singleton x)
          (normalBandWordOfPrefixFinal xs final)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ initial) (ih₂ initial)

private theorem normalBandPerm_one_to_end (x : Nat) :
    ∀ middle : List Nat, (x :: middle).Perm (middle ++ [x])
  | [] => List.Perm.refl _
  | y :: ys =>
      (List.Perm.swap y x ys).trans <|
        List.Perm.cons y (normalBandPerm_one_to_end x ys)

private theorem normalBandDerivesInsertMember
    (initial : Nat) (middle : List Nat) (final x : Nat)
    (hx : x ∈ initial :: middle ++ [final]) :
    Derives normalBandBasis
      (normalBandWordOfEndpoints initial middle final)
      (normalBandWordOfEndpoints initial (middle ++ [x]) final) := by
  have hx' : x = initial ∨ x ∈ middle ∨ x = final := by
    simpa [List.mem_append] using hx
  rcases hx' with hxHead | hx | hxFinal
  · subst x
    have duplicate :=
      Derives.appendRight
        (normalBandDerivesIdempotenceExpansion
          (Word.singleton initial))
        (normalBandWordOfPrefixFinal middle final)
    have move :
        (initial :: middle).Perm (middle ++ [initial]) :=
      normalBandPerm_one_to_end initial middle
    exact Derives.trans
      (by
        simpa [normalBandWordOfEndpoints_eq, Word.append_assoc] using
          duplicate) <|
      normalBandDerivesInteriorPermutation initial final move
  · have expose :
        middle.Perm (x :: middle.erase x) :=
      List.perm_cons_erase hx
    have arrange :=
      normalBandDerivesInteriorPermutation initial final expose
    have duplicate :=
      Derives.appendRight
        (Derives.prepend (Word.singleton initial)
          (normalBandDerivesIdempotenceExpansion
            (Word.singleton x)))
        (normalBandWordOfPrefixFinal (middle.erase x) final)
    have restore :
        (x :: x :: middle.erase x).Perm (middle ++ [x]) :=
      (List.Perm.cons x expose.symm).trans
        (normalBandPerm_one_to_end x middle)
    exact Derives.trans arrange <|
      Derives.trans
        (by
          simpa [normalBandWordOfEndpoints_eq, Word.append_assoc] using
            duplicate)
        (normalBandDerivesInteriorPermutation initial final restore)
  · subst x
    have duplicate :=
      Derives.prepend (Word.mk initial middle)
        (normalBandDerivesIdempotenceExpansion
          (Word.singleton final))
    simpa [normalBandWordOfEndpoints, Word.append, Word.singleton,
      List.append_assoc] using duplicate

private theorem normalBandDerivesInsertList
    (initial : Nat) (middle : List Nat) (final : Nat) :
    ∀ xs : List Nat,
      (∀ x, x ∈ xs → x ∈ initial :: middle ++ [final]) →
      Derives normalBandBasis
        (normalBandWordOfEndpoints initial middle final)
        (normalBandWordOfEndpoints initial (middle ++ xs) final)
  | [], _ => by
      simpa using
        (Derives.refl
          (normalBandWordOfEndpoints initial middle final))
  | x :: xs, hcontent => by
      have first :=
        normalBandDerivesInsertMember initial middle final x
          (hcontent x (List.Mem.head xs))
      have remainingContent :
          ∀ y, y ∈ xs →
            y ∈ initial :: (middle ++ [x]) ++ [final] := by
        intro y hy
        have original :=
          hcontent y (List.Mem.tail x hy)
        have original' :
            y = initial ∨ y ∈ middle ∨ y = final := by
          simpa [List.mem_append] using original
        rcases original' with h | h | h
        · simp [h]
        · simp [List.mem_append, h]
        · simp [h]
      have rest :=
        normalBandDerivesInsertList initial (middle ++ [x]) final
          xs remainingContent
      exact Derives.trans first <| by
        simpa [List.append_assoc] using rest

private theorem normalBandMiddle_perm_of_same_counts
    (initial final : Nat) {middle₁ middle₂ : List Nat}
    (hcount :
      ∀ z,
        (initial :: middle₁ ++ [final]).count z =
          (initial :: middle₂ ++ [final]).count z) :
    middle₁.Perm middle₂ := by
  rw [List.perm_iff_count]
  intro z
  have hz := hcount z
  simp only [List.count_cons, List.count_append,
    List.count_nil] at hz
  omega

private theorem normalBandDerivesConstantWord
    (x : Nat) :
    ∀ tail : List Nat,
      (∀ y, y ∈ tail → y = x) →
      Derives normalBandBasis
        (Word.singleton x) (Word.mk x tail)
  | [], _ => Derives.refl _
  | y :: ys, hall => by
      have hy : y = x := hall y (List.Mem.head ys)
      subst y
      have first :=
        normalBandDerivesIdempotenceExpansion (Word.singleton x)
      have rest :=
        normalBandDerivesConstantWord x ys
          (fun z hz => hall z (List.Mem.tail x hz))
      exact Derives.trans first <| by
        simpa [Word.append, Word.singleton] using
          Derives.prepend (Word.singleton x) rest

private theorem normalBandDropLast_append_final
    (x : Nat) (xs : List Nat) :
    (x :: xs).dropLast ++ [xs.getLastD x] = x :: xs := by
  have h :=
    List.dropLast_concat_getLast
      (l := x :: xs) (by simp)
  rw [List.getLast_eq_getLastD] at h
  exact h

/-- Words with the same support, initial variable, and final variable are
equationally equivalent under the normal-band basis. -/
theorem normalBandDerivesSameSignature
    (u v : Word Nat)
    (heads : u.head = v.head)
    (finals :
      u.tail.getLastD u.head = v.tail.getLastD v.head)
    (support :
      ∀ z, z ∈ u.toList ↔ z ∈ v.toList) :
    Derives normalBandBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          simp only at heads finals support
          subst vHead
          cases uTail with
          | nil =>
              have allV :
                  ∀ y, y ∈ vTail → y = uHead := by
                intro y hy
                have inU :
                    y ∈ [uHead] := by
                  exact (support y).2 <|
                    List.Mem.tail uHead hy
                simpa using inU
              exact normalBandDerivesConstantWord uHead vTail allV
          | cons uNext uRest =>
              cases vTail with
              | nil =>
                  have allU :
                      ∀ y, y ∈ uNext :: uRest → y = uHead := by
                    intro y hy
                    have inV :
                        y ∈ [uHead] := by
                      exact (support y).1 <|
                        List.Mem.tail uHead hy
                    simpa using inV
                  exact Derives.symm <|
                    normalBandDerivesConstantWord
                      uHead (uNext :: uRest) allU
              | cons vNext vRest =>
                  let uFinal := uRest.getLastD uNext
                  let vFinal := vRest.getLastD vNext
                  let uMiddle := (uNext :: uRest).dropLast
                  let vMiddle := (vNext :: vRest).dropLast
                  have finalEq : uFinal = vFinal := by
                    rw [List.getLastD_cons, List.getLastD_cons] at finals
                    exact finals
                  have uReconstruct :
                      normalBandWordOfEndpoints
                          uHead uMiddle uFinal =
                        Word.mk uHead (uNext :: uRest) := by
                    apply Word.toList_injective
                    change
                      uHead :: uMiddle ++ [uFinal] =
                        uHead :: uNext :: uRest
                    congr 1
                    simpa [uMiddle, uFinal] using
                      normalBandDropLast_append_final uNext uRest
                  have vReconstruct :
                      normalBandWordOfEndpoints
                          uHead vMiddle uFinal =
                        Word.mk uHead (vNext :: vRest) := by
                    rw [finalEq]
                    apply Word.toList_injective
                    change
                      uHead :: vMiddle ++ [vFinal] =
                        uHead :: vNext :: vRest
                    congr 1
                    simpa [vMiddle, vFinal] using
                      normalBandDropLast_append_final vNext vRest
                  have uEndpointList :
                      uHead :: uMiddle ++ [uFinal] =
                        (Word.mk uHead (uNext :: uRest)).toList :=
                    congrArg Word.toList uReconstruct
                  have vEndpointList :
                      uHead :: vMiddle ++ [uFinal] =
                        (Word.mk uHead (vNext :: vRest)).toList :=
                    congrArg Word.toList vReconstruct
                  let commonMiddle :=
                    (Word.mk uHead (uNext :: uRest)).toList ++
                      (Word.mk uHead (vNext :: vRest)).toList
                  let uInsert :=
                    [uHead, uFinal] ++
                      (Word.mk uHead (vNext :: vRest)).toList
                  let vInsert :=
                    [uHead, uFinal] ++
                      (Word.mk uHead (uNext :: uRest)).toList
                  have uInsertContent :
                      ∀ x, x ∈ uInsert →
                        x ∈ uHead :: uMiddle ++ [uFinal] := by
                    intro x hx
                    simp only [uInsert, List.mem_append,
                      List.mem_cons, List.not_mem_nil, or_false] at hx
                    rcases hx with hx | hx
                    · rcases hx with rfl | rfl
                      · exact List.Mem.head _
                      · exact List.mem_append_right _ <|
                          List.Mem.head []
                    · have inU :=
                        (support x).2 hx
                      rw [uEndpointList]
                      exact inU
                  have vInsertContent :
                      ∀ x, x ∈ vInsert →
                        x ∈ uHead :: vMiddle ++ [uFinal] := by
                    intro x hx
                    simp only [vInsert, List.mem_append,
                      List.mem_cons, List.not_mem_nil, or_false] at hx
                    rcases hx with hx | hx
                    · rcases hx with rfl | rfl
                      · exact List.Mem.head _
                      · exact List.mem_append_right _ <|
                          List.Mem.head []
                    · have inV :=
                        (support x).1 hx
                      rw [vEndpointList]
                      exact inV
                  have uExpanded :=
                    normalBandDerivesInsertList
                      uHead uMiddle uFinal uInsert uInsertContent
                  have vExpanded :=
                    normalBandDerivesInsertList
                      uHead vMiddle uFinal vInsert vInsertContent
                  have uPerm :
                      (uMiddle ++ uInsert).Perm commonMiddle := by
                    rw [List.perm_iff_count]
                    intro z
                    have endpointCount :=
                      congrArg (List.count z) uEndpointList
                    simp only [commonMiddle, uInsert, Word.toList,
                      List.count_append, List.count_cons,
                      List.count_nil] at endpointCount ⊢
                    omega
                  have vPerm :
                      (vMiddle ++ vInsert).Perm commonMiddle := by
                    rw [List.perm_iff_count]
                    intro z
                    have endpointCount :=
                      congrArg (List.count z) vEndpointList
                    simp only [commonMiddle, vInsert, Word.toList,
                      List.count_append, List.count_cons,
                      List.count_nil] at endpointCount ⊢
                    omega
                  rw [← uReconstruct, ← vReconstruct]
                  exact Derives.trans uExpanded <|
                    Derives.trans
                      (normalBandDerivesInteriorPermutation
                        uHead uFinal uPerm)
                      (Derives.symm <|
                        Derives.trans vExpanded <|
                          normalBandDerivesInteriorPermutation
                            uHead uFinal vPerm)

end SemigroupBasis.Examples
