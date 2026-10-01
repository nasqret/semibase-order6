import SemigroupBasis.Examples.CyclicTwo

namespace SemigroupBasis.Examples

open SemigroupBasis

def affineParityX : Word Nat := Word.singleton 0
def affineParityXXX : Word Nat := ⟨0, [0, 0]⟩
def affineParityXXYX : Word Nat := ⟨0, [0, 1, 0]⟩
def affineParityYX : Word Nat := ⟨1, [0]⟩
def affineParityXYYX : Word Nat := ⟨0, [1, 1, 0]⟩
def affineParityYXYX : Word Nat := ⟨1, [0, 1, 0]⟩

def affineParityPowerLaw : Identity Nat :=
  ⟨affineParityX, affineParityXXX⟩

def affineParitySquareReturnLaw : Identity Nat :=
  ⟨affineParityXXYX, affineParityYX⟩

def affineParityMiddleSquareLaw : Identity Nat :=
  ⟨affineParityXYYX, affineParityYXYX⟩

/-- Edmunds' basis for the four-element affine transformation semigroup:
`x = xxx`, `xxyx = yx`, and `xyyx = yxyx`. -/
def affineParityFourBasis : List (Identity Nat) :=
  [affineParityPowerLaw, affineParitySquareReturnLaw,
    affineParityMiddleSquareLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem affineParityDerivesTripleContraction (u : Word Nat) :
    Derives affineParityFourBasis ((u ++ u) ++ u) u := by
  have hbase :
      Derives affineParityFourBasis affineParityXXX affineParityX :=
    Derives.symm <|
      Derives.fromBasis (e := affineParityPowerLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [affineParityFourBasis, affineParityPowerLaw,
    affineParityXXX, affineParityX, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

/-- The second basis law with arbitrary nonempty blocks:
`u u v u = v u`. -/
theorem affineParityDerivesSquareReturn (u v : Word Nat) :
    Derives affineParityFourBasis
      (((u ++ u) ++ v) ++ u) (v ++ u) := by
  have hbase :
      Derives affineParityFourBasis affineParityXXYX affineParityYX :=
    Derives.fromBasis (e := affineParitySquareReturnLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [affineParityFourBasis, affineParitySquareReturnLaw,
    affineParityXXYX, affineParityYX, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

/-- The third basis law with arbitrary nonempty blocks:
`u v v u = v u v u`. -/
theorem affineParityDerivesMiddleSquare (u v : Word Nat) :
    Derives affineParityFourBasis
      (((u ++ v) ++ v) ++ u) (((v ++ u) ++ v) ++ u) := by
  have hbase :
      Derives affineParityFourBasis affineParityXYYX affineParityYXYX :=
    Derives.fromBasis (e := affineParityMiddleSquareLaw) <|
      List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [affineParityFourBasis, affineParityMiddleSquareLaw,
    affineParityXYYX, affineParityYXYX, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

def affineParityWordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- Prefix a possibly empty list of letters to a nonempty word. -/
def affineParityPrependLetters : List Nat → Word Nat → Word Nat
  | [], suffix => suffix
  | x :: xs, suffix =>
      Word.singleton x ++ affineParityPrependLetters xs suffix

@[simp]
theorem affineParityPrependLetters_toList
    (xs : List Nat) (suffix : Word Nat) :
    (affineParityPrependLetters xs suffix).toList =
      xs ++ suffix.toList := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [affineParityPrependLetters, Word.toList_append, ih]
      rfl

/-- A square immediately before a suffix containing the same letter can be
deleted. This combines `x = x³` at the head of the suffix with
`x² y x = y x` when a nonempty block precedes the guarded occurrence. -/
theorem affineParityDerivesDeleteSquare
    (x : Nat) (suffix : Word Nat) (hx : x ∈ suffix.toList) :
    Derives affineParityFourBasis
      (affineParityPrependLetters [x, x] suffix) suffix := by
  cases suffix with
  | mk head tail =>
      change x ∈ head :: tail at hx
      simp only [List.mem_cons] at hx
      rcases hx with hhead | hx
      · subst head
        cases tail with
        | nil =>
            simpa [affineParityPrependLetters,
              Word.singleton, Word.append, Word.append_assoc] using
                affineParityDerivesTripleContraction
                  (Word.singleton x)
        | cons y ys =>
            have h :=
              Derives.appendRight
                (affineParityDerivesTripleContraction
                  (Word.singleton x))
                (affineParityWordOfCons y ys)
            simpa [affineParityPrependLetters,
              affineParityWordOfCons, Word.singleton, Word.append,
              Word.append_assoc] using h
      · cases tail with
        | nil => contradiction
        | cons first rest =>
            obtain ⟨before, after, htail⟩ :=
              List.mem_iff_append.mp hx
            let middle := affineParityWordOfCons head before
            cases after with
            | nil =>
                simpa [affineParityPrependLetters,
                  affineParityWordOfCons, middle, htail,
                  Word.singleton, Word.append, Word.append_assoc] using
                    affineParityDerivesSquareReturn
                      (Word.singleton x) middle
            | cons y ys =>
                have h :=
                  Derives.appendRight
                    (affineParityDerivesSquareReturn
                      (Word.singleton x) middle)
                    (affineParityWordOfCons y ys)
                simpa [affineParityPrependLetters,
                  affineParityWordOfCons, middle, htail,
                  Word.singleton, Word.append, Word.append_assoc,
                  List.append_assoc] using h

/-- Adjacent guarded letters commute. Both letters must occur in the suffix,
which supplies the square expansions and contractions used in Edmunds'
four-step derivation. -/
theorem affineParityDerivesGuardedSwap
    (x y : Nat) (suffix : Word Nat)
    (hx : x ∈ suffix.toList) (hy : y ∈ suffix.toList) :
    Derives affineParityFourBasis
      (affineParityPrependLetters [x, y] suffix)
      (affineParityPrependLetters [y, x] suffix) := by
  let yySuffix := affineParityPrependLetters [y, y] suffix
  have expandY :
      Derives affineParityFourBasis suffix yySuffix :=
    Derives.symm (affineParityDerivesDeleteSquare y suffix hy)
  have hxYY : x ∈ yySuffix.toList := by
    simp [yySuffix, hx]
  have expandX :
      Derives affineParityFourBasis yySuffix
        (affineParityPrependLetters [x, x] yySuffix) :=
    Derives.symm (affineParityDerivesDeleteSquare x yySuffix hxYY)
  have expandSuffix :
      Derives affineParityFourBasis suffix
        (affineParityPrependLetters [x, x, y, y] suffix) := by
    exact Derives.trans expandY <| by
      simpa [yySuffix, affineParityPrependLetters,
        Word.append_assoc] using expandX
  have first :=
    Derives.prepend
      (affineParityWordOfCons x [y]) expandSuffix
  have secondCore :=
    affineParityDerivesMiddleSquare
      (Word.singleton y) (Word.singleton x)
  have second :=
    Derives.appendRight
      (Derives.prepend (Word.singleton x) secondCore)
      (affineParityPrependLetters [y] suffix)
  have third :=
    Derives.appendRight
      (affineParityDerivesSquareReturn
        (Word.singleton x) (Word.singleton y))
      (affineParityPrependLetters [y, y] suffix)
  have fourth :=
    Derives.prepend
      (affineParityWordOfCons y [x])
      (affineParityDerivesDeleteSquare y suffix hy)
  exact Derives.trans
    (by
      simpa [affineParityPrependLetters,
        affineParityWordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using first) <|
    Derives.trans
      (by
        simpa [affineParityPrependLetters,
          affineParityWordOfCons, Word.singleton, Word.append,
          Word.append_assoc] using second) <|
      Derives.trans
        (by
          simpa [affineParityPrependLetters,
            affineParityWordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using third)
        (by
          simpa [affineParityPrependLetters,
            affineParityWordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using fourth)

/-- A guarded block may be permuted arbitrarily. -/
theorem affineParityDerivesGuardedPermutation
    (suffix : Word Nat) {xs ys : List Nat}
    (permutation : xs.Perm ys)
    (guard : ∀ z, z ∈ xs → z ∈ suffix.toList) :
    Derives affineParityFourBasis
      (affineParityPrependLetters xs suffix)
      (affineParityPrependLetters ys suffix) := by
  induction permutation generalizing suffix with
  | nil =>
      exact Derives.refl suffix
  | cons x permutation ih =>
      have h := ih suffix (fun z hz =>
        guard z (List.Mem.tail x hz))
      simpa [affineParityPrependLetters] using
        Derives.prepend (Word.singleton x) h
  | swap x y rest =>
      let guardedSuffix :=
        affineParityPrependLetters rest suffix
      have xGuarded : x ∈ suffix.toList :=
        guard x (by simp)
      have yGuarded : y ∈ suffix.toList :=
        guard y (by simp)
      have hx : x ∈ guardedSuffix.toList := by
        simp [guardedSuffix, xGuarded]
      have hy : y ∈ guardedSuffix.toList := by
        simp [guardedSuffix, yGuarded]
      simpa [guardedSuffix, affineParityPrependLetters] using
        affineParityDerivesGuardedSwap y x guardedSuffix hy hx
  | trans first second ih₁ ih₂ =>
      have firstDerivation := ih₁ suffix guard
      have secondDerivation := ih₂ suffix (fun z hz =>
        guard z ((first.mem_iff).mpr hz))
      exact Derives.trans
        firstDerivation secondDerivation

theorem affineParityPrependLetters_derivation
    (letters : List Nat) {left right : Word Nat}
    (derivation :
      Derives affineParityFourBasis left right) :
    Derives affineParityFourBasis
      (affineParityPrependLetters letters left)
      (affineParityPrependLetters letters right) := by
  induction letters with
  | nil => exact derivation
  | cons letter rest ih =>
      simpa [affineParityPrependLetters] using
        Derives.prepend (Word.singleton letter) ih

/-- Toggle one letter in a duplicate-free parity block. -/
def affineParityToggle (x : Nat) (xs : List Nat) : List Nat :=
  if x ∈ xs then xs.erase x else x :: xs

theorem affineParityToggle_nodup
    (x : Nat) {xs : List Nat} (nodup : xs.Nodup) :
    (affineParityToggle x xs).Nodup := by
  by_cases hx : x ∈ xs
  · simp [affineParityToggle, hx, nodup.erase]
  · simp [affineParityToggle, hx, nodup]

theorem affineParityToggle_mem
    (x z : Nat) (xs : List Nat)
    (hz : z ∈ affineParityToggle x xs) :
    z = x ∨ z ∈ xs := by
  by_cases hx : x ∈ xs
  · right
    rw [affineParityToggle, if_pos hx] at hz
    exact List.mem_of_mem_erase hz
  · simpa [affineParityToggle, hx] using hz

/-- Prefixing one more occurrence toggles a guarded parity block. -/
theorem affineParityDerivesToggle
    (x : Nat) (block : List Nat) (suffix : Word Nat)
    (blockGuard : ∀ z, z ∈ block → z ∈ suffix.toList)
    (xGuard : x ∈ suffix.toList) :
    Derives affineParityFourBasis
      (affineParityPrependLetters (x :: block) suffix)
      (affineParityPrependLetters
        (affineParityToggle x block) suffix) := by
  by_cases hx : x ∈ block
  · have expose : block.Perm (x :: block.erase x) :=
      List.perm_cons_erase hx
    have reordered :=
      affineParityDerivesGuardedPermutation
        suffix expose blockGuard
    have prefixed :=
      Derives.prepend (Word.singleton x) reordered
    let reducedSuffix :=
      affineParityPrependLetters (block.erase x) suffix
    have xInReduced : x ∈ reducedSuffix.toList := by
      simp [reducedSuffix, xGuard]
    have deleted :=
      affineParityDerivesDeleteSquare
        x reducedSuffix xInReduced
    exact Derives.trans
      (by
        simpa [affineParityPrependLetters, reducedSuffix,
          Word.append_assoc] using prefixed)
      (by
        simpa [affineParityToggle, hx, reducedSuffix,
          affineParityPrependLetters, Word.append_assoc] using deleted)
  · simp [affineParityToggle, hx]
    exact Derives.refl _

structure AffineParitySegment where
  parity : List Nat
  marker : Nat
deriving Repr, DecidableEq

def affineParityMarkers :
    List AffineParitySegment → List Nat
  | [] => []
  | segment :: rest =>
      segment.marker :: affineParityMarkers rest

def affineParityRender :
    List AffineParitySegment → List Nat
  | [] => []
  | segment :: rest =>
      segment.parity ++
        segment.marker :: affineParityRender rest

/-- Render a nonempty segment list as a semigroup word. -/
def affineParityRenderWord
    (segment : AffineParitySegment)
    (rest : List AffineParitySegment) : Word Nat :=
  affineParityPrependLetters segment.parity <|
    affineParityWordOfCons segment.marker
      (affineParityRender rest)

@[simp]
theorem affineParityRenderWord_toList
    (segment : AffineParitySegment)
    (rest : List AffineParitySegment) :
    (affineParityRenderWord segment rest).toList =
      affineParityRender (segment :: rest) := by
  rw [affineParityRenderWord,
    affineParityPrependLetters_toList]
  rfl

theorem affineParityMarker_mem_render :
    ∀ {segments : List AffineParitySegment} {z : Nat},
      z ∈ affineParityMarkers segments →
      z ∈ affineParityRender segments
  | [], _, hz => by
      simp [affineParityMarkers] at hz
  | segment :: rest, z, hz => by
      simp only [affineParityMarkers, List.mem_cons] at hz
      simp only [affineParityRender, List.mem_append,
        List.mem_cons]
      rcases hz with rfl | hz
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr <|
          affineParityMarker_mem_render hz)

/-- Canonical segment invariants. Markers are distinct, each parity block is
duplicate-free, and every block letter occurs in its guarded suffix. -/
inductive AffineParitySegmentsNormal :
    List AffineParitySegment → Prop
  | nil : AffineParitySegmentsNormal []
  | cons {parity : List Nat} {marker : Nat}
      {rest : List AffineParitySegment} :
      parity.Nodup →
      marker ∉ affineParityMarkers rest →
      (∀ z, z ∈ parity →
        z = marker ∨ z ∈ affineParityMarkers rest) →
      AffineParitySegmentsNormal rest →
      AffineParitySegmentsNormal
        (⟨parity, marker⟩ :: rest)

/-- Scan from right to left. A new variable creates a marker; an old variable
toggles the parity block immediately before the first marker. -/
def affineParityNormalSegments :
    List Nat → List AffineParitySegment
  | [] => []
  | x :: xs =>
      match affineParityNormalSegments xs with
      | [] => [⟨[], x⟩]
      | segment :: rest =>
          if x ∈ affineParityMarkers (segment :: rest) then
            ⟨affineParityToggle x segment.parity,
              segment.marker⟩ :: rest
          else
            ⟨[], x⟩ :: segment :: rest

theorem affineParityNormalSegments_normal :
    ∀ xs : List Nat,
      AffineParitySegmentsNormal
        (affineParityNormalSegments xs)
  | [] => AffineParitySegmentsNormal.nil
  | x :: xs => by
      have restNormal :=
        affineParityNormalSegments_normal xs
      cases hs : affineParityNormalSegments xs with
      | nil =>
          rw [affineParityNormalSegments, hs]
          exact AffineParitySegmentsNormal.cons
            List.nodup_nil
            List.not_mem_nil
            (fun _ hz => False.elim <| List.not_mem_nil hz)
            AffineParitySegmentsNormal.nil
      | cons segment rest =>
          cases segment with
          | mk parity marker =>
              rw [hs] at restNormal
              cases restNormal with
              | cons parityNodup markerFresh parityGuard tailNormal =>
                  by_cases hx :
                      x ∈ affineParityMarkers
                        (⟨parity, marker⟩ :: rest)
                  · have whole :
                        affineParityNormalSegments (x :: xs) =
                          ⟨affineParityToggle x parity,
                            marker⟩ :: rest := by
                        rw [affineParityNormalSegments, hs]
                        exact if_pos hx
                    rw [whole]
                    apply AffineParitySegmentsNormal.cons
                      (affineParityToggle_nodup
                        x parityNodup)
                      markerFresh
                      ?_
                      tailNormal
                    intro z hz
                    rcases
                        affineParityToggle_mem
                          x z parity hz with
                      rfl | hz
                    · simpa [affineParityMarkers] using hx
                    · exact parityGuard z hz
                  · have whole :
                        affineParityNormalSegments (x :: xs) =
                          ⟨[], x⟩ ::
                            ⟨parity, marker⟩ :: rest := by
                        rw [affineParityNormalSegments, hs]
                        exact if_neg hx
                    rw [whole]
                    exact AffineParitySegmentsNormal.cons
                      List.nodup_nil
                      (by
                        simpa [affineParityMarkers] using hx)
                      (fun _ hz =>
                        False.elim <| List.not_mem_nil hz)
                      (AffineParitySegmentsNormal.cons
                        parityNodup markerFresh parityGuard
                        tailNormal)

theorem affineParityNormalSegments_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    affineParityNormalSegments (x :: xs) ≠ [] := by
  cases hs : affineParityNormalSegments xs with
  | nil =>
      have whole :
          affineParityNormalSegments (x :: xs) =
            [⟨[], x⟩] := by
        rw [affineParityNormalSegments, hs]
      rw [whole]
      simp
  | cons segment rest =>
      by_cases hx :
          x ∈ affineParityMarkers (segment :: rest)
      · have whole :
            affineParityNormalSegments (x :: xs) =
              ⟨affineParityToggle x segment.parity,
                segment.marker⟩ :: rest := by
            rw [affineParityNormalSegments, hs]
            exact if_pos hx
        rw [whole]
        simp
      · have whole :
            affineParityNormalSegments (x :: xs) =
              ⟨[], x⟩ :: segment :: rest := by
            rw [affineParityNormalSegments, hs]
            exact if_neg hx
        rw [whole]
        simp

private theorem affineParityDerivesNormalizeList :
    ∀ (x : Nat) (xs : List Nat),
      match affineParityNormalSegments (x :: xs) with
      | [] => False
      | segment :: rest =>
          Derives affineParityFourBasis
            (affineParityWordOfCons x xs)
            (affineParityRenderWord segment rest)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal :=
        affineParityDerivesNormalizeList y ys
      have suffixSegmentsNormal :=
        affineParityNormalSegments_normal (y :: ys)
      cases hs :
          affineParityNormalSegments (y :: ys) with
      | nil =>
          exact False.elim <|
            affineParityNormalSegments_cons_ne_nil y ys hs
      | cons segment rest =>
          cases segment with
          | mk parity marker =>
              rw [hs] at suffixNormal suffixSegmentsNormal
              have prefixed :=
                Derives.prepend (Word.singleton x) suffixNormal
              by_cases hx :
                  x ∈ affineParityMarkers
                    (⟨parity, marker⟩ :: rest)
              · cases suffixSegmentsNormal with
                | cons parityNodup markerFresh parityGuard tailNormal =>
                    let guardedSuffix :=
                      affineParityWordOfCons marker
                        (affineParityRender rest)
                    have xGuard :
                        x ∈ guardedSuffix.toList := by
                      change
                        x ∈ marker ::
                          affineParityRender rest
                      have hx' :
                          x = marker ∨
                            x ∈ affineParityMarkers rest := by
                        simpa [affineParityMarkers] using hx
                      rcases hx' with rfl | hx'
                      · exact List.Mem.head _
                      · exact List.Mem.tail _ <|
                          affineParityMarker_mem_render hx'
                    have blockGuard :
                        ∀ z, z ∈ parity →
                          z ∈ guardedSuffix.toList := by
                      intro z hz
                      change
                        z ∈ marker ::
                          affineParityRender rest
                      rcases parityGuard z hz with rfl | hz
                      · exact List.Mem.head _
                      · exact List.Mem.tail _ <|
                          affineParityMarker_mem_render hz
                    have toggled :=
                      affineParityDerivesToggle
                        x parity guardedSuffix
                        blockGuard xGuard
                    have whole :
                        affineParityNormalSegments
                            (x :: y :: ys) =
                          ⟨affineParityToggle x parity,
                            marker⟩ :: rest := by
                      rw [affineParityNormalSegments, hs]
                      exact if_pos hx
                    rw [whole]
                    exact Derives.trans
                      (by
                        simpa [affineParityWordOfCons,
                          affineParityRenderWord,
                          affineParityPrependLetters,
                          guardedSuffix, Word.singleton,
                          Word.append, Word.append_assoc,
                          affineParityRender] using prefixed)
                      (by
                        simpa [affineParityRenderWord,
                          guardedSuffix, affineParityRender]
                          using toggled)
              · have whole :
                    affineParityNormalSegments
                        (x :: y :: ys) =
                      ⟨[], x⟩ ::
                        ⟨parity, marker⟩ :: rest := by
                  rw [affineParityNormalSegments, hs]
                  exact if_neg hx
                rw [whole]
                have sourceEq :
                    Word.singleton x ++
                        affineParityWordOfCons y ys =
                      affineParityWordOfCons x (y :: ys) :=
                  rfl
                have targetEq :
                    Word.singleton x ++
                        affineParityRenderWord
                          ⟨parity, marker⟩ rest =
                      affineParityRenderWord
                        ⟨[], x⟩
                        (⟨parity, marker⟩ :: rest) := by
                  apply Word.toList_injective
                  rw [Word.toList_append,
                    Word.toList_singleton,
                    affineParityRenderWord_toList,
                    affineParityRenderWord_toList]
                  rfl
                change
                  Derives affineParityFourBasis
                    (affineParityWordOfCons x (y :: ys))
                    (affineParityRenderWord
                      ⟨[], x⟩
                      (⟨parity, marker⟩ :: rest))
                rw [← sourceEq, ← targetEq]
                exact prefixed

/-- Every nonempty word derives to its right-to-left marker/parity normal
form. -/
theorem affineParityDerivesNormal (word : Word Nat) :
    match affineParityNormalSegments word.toList with
    | [] => False
    | segment :: rest =>
        Derives affineParityFourBasis word
          (affineParityRenderWord segment rest) := by
  cases word with
  | mk head tail =>
      exact affineParityDerivesNormalizeList head tail

end SemigroupBasis.Examples
