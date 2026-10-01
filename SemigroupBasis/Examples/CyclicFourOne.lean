import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The zero-based table of the cyclic semigroup `C_{4,1}`:
`[[1,1,1,1],[1,1,1,3],[1,1,1,1],[1,3,1,2]]`. -/
def cyclicFourOneMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0
  else if a = 1 then
    if b = 3 then 2 else 0
  else if a = 2 then 0
  else
    if b = 1 then 2 else if b = 3 then 1 else 0

/-- The four-element cyclic semigroup with index four and period one. -/
def cyclicFourOne : FiniteTable where
  order := 4
  mul := cyclicFourOneMul
  assoc := by decide

def cyclicFourOneXY : Word Nat := ⟨0, [1]⟩
def cyclicFourOneYX : Word Nat := ⟨1, [0]⟩
def cyclicFourOneXYZTU : Word Nat := ⟨0, [1, 2, 3, 4]⟩
def cyclicFourOneYZTU : Word Nat := ⟨1, [2, 3, 4]⟩
def cyclicFourOneXYY : Word Nat := ⟨0, [1, 1]⟩
def cyclicFourOneXXY : Word Nat := ⟨0, [0, 1]⟩

def cyclicFourOneCommutativityLaw : Identity Nat :=
  ⟨cyclicFourOneXY, cyclicFourOneYX⟩

def cyclicFourOneLongCancellationLaw : Identity Nat :=
  ⟨cyclicFourOneXYZTU, cyclicFourOneYZTU⟩

def cyclicFourOneMultiplicityLaw : Identity Nat :=
  ⟨cyclicFourOneXYY, cyclicFourOneXXY⟩

/-- The basis `xy = yx`, `xyztu = yztu`, `xyy = xxy` for `C_{4,1}`. -/
def cyclicFourOneBasis : List (Identity Nat) :=
  [cyclicFourOneCommutativityLaw, cyclicFourOneLongCancellationLaw,
    cyclicFourOneMultiplicityLaw]

private def instantiateFiveWords
    (u v w t r : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | 3 => t
  | 4 => r
  | n + 5 => Word.singleton (n + 5)

theorem cyclicFourOneDerivesCommutativity (u v : Word Nat) :
    Derives cyclicFourOneBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives cyclicFourOneBasis cyclicFourOneXY cyclicFourOneYX :=
    Derives.fromBasis (e := cyclicFourOneCommutativityLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateFiveWords u v v v v)
  simpa [cyclicFourOneBasis, cyclicFourOneCommutativityLaw,
    cyclicFourOneXY, cyclicFourOneYX, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton] using h

theorem cyclicFourOneDerivesDropPrefix
    (u v w t r : Word Nat) :
    Derives cyclicFourOneBasis
      (((((u ++ v) ++ w) ++ t) ++ r))
      ((((v ++ w) ++ t) ++ r)) := by
  have hbase :
      Derives cyclicFourOneBasis
        cyclicFourOneXYZTU cyclicFourOneYZTU :=
    Derives.fromBasis (e := cyclicFourOneLongCancellationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateFiveWords u v w t r)
  simpa [cyclicFourOneBasis, cyclicFourOneLongCancellationLaw,
    cyclicFourOneXYZTU, cyclicFourOneYZTU, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

theorem cyclicFourOneDerivesMultiplicityTransfer
    (u v : Word Nat) :
    Derives cyclicFourOneBasis
      ((u ++ v) ++ v) ((u ++ u) ++ v) := by
  have hbase :
      Derives cyclicFourOneBasis
        cyclicFourOneXYY cyclicFourOneXXY :=
    Derives.fromBasis (e := cyclicFourOneMultiplicityLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateFiveWords u v v v v)
  simpa [cyclicFourOneBasis, cyclicFourOneMultiplicityLaw,
    cyclicFourOneXYY, cyclicFourOneXXY, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives cyclicFourOneBasis
        (wordOfCons x xs) (wordOfCons y ys) →
      ListDerives (x :: xs) (y :: ys)

private theorem listDerives_of_perm {xs ys : List Nat}
    (h : xs.Perm ys) : ListDerives xs ys := by
  induction h with
  | nil =>
      exact ListDerives.empty
  | cons x _ ih =>
      cases ih with
      | empty =>
          exact ListDerives.words (Derives.refl _)
      | words derivation =>
          exact ListDerives.words <| by
            simpa [wordOfCons, Word.singleton, Word.append] using
              Derives.prepend (Word.singleton x) derivation
  | swap x y xs =>
      exact ListDerives.words <| by
        cases xs with
        | nil =>
            simpa [wordOfCons, Word.append, Word.singleton] using
              cyclicFourOneDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (cyclicFourOneDerivesCommutativity
                  (Word.singleton y) (Word.singleton x))
                (wordOfCons z zs)
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using swapped
  | trans _ _ ih₁ ih₂ =>
      cases ih₁ with
      | empty =>
          cases ih₂
          exact ListDerives.empty
      | words first =>
          cases ih₂ with
          | words second =>
              exact ListDerives.words (Derives.trans first second)

theorem cyclicFourOneDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives cyclicFourOneBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

private def longMarker : Word Nat :=
  wordOfCons 0 [0, 0, 0]

private theorem cyclicFourOneDerivesReplaceFirst
    (a b c d marker : Nat) :
    Derives cyclicFourOneBasis
      (wordOfCons a [b, c, d])
      (wordOfCons marker [b, c, d]) := by
  have insert :=
    Derives.symm <|
      cyclicFourOneDerivesDropPrefix
        (Word.singleton marker) (Word.singleton a)
        (Word.singleton b) (Word.singleton c) (Word.singleton d)
  have commute :=
    Derives.appendRight
      (cyclicFourOneDerivesCommutativity
        (Word.singleton marker) (Word.singleton a))
      ((Word.singleton b ++ Word.singleton c) ++ Word.singleton d)
  have remove :=
    cyclicFourOneDerivesDropPrefix
      (Word.singleton a) (Word.singleton marker)
      (Word.singleton b) (Word.singleton c) (Word.singleton d)
  exact Derives.trans
    (by
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using insert)
    (Derives.trans
      (by
        simpa [wordOfCons, Word.singleton, Word.append,
          Word.append_assoc] using commute)
      (by
        simpa [wordOfCons, Word.singleton, Word.append,
          Word.append_assoc] using remove))

private theorem cyclicFourOneDerivesFourToMarker
    (a b c d : Nat) :
    Derives cyclicFourOneBasis
      (wordOfCons a [b, c, d]) longMarker := by
  have replaceA := cyclicFourOneDerivesReplaceFirst a b c d 0
  have arrangeB :
      Derives cyclicFourOneBasis
        (wordOfCons 0 [b, c, d])
        (wordOfCons b [0, c, d]) :=
    cyclicFourOneDerivesPermutation _ _ (by
      rw [List.perm_iff_count]
      intro z
      simp only [wordOfCons, Word.toList, List.count_cons,
        List.count_nil]
      omega)
  have replaceB := cyclicFourOneDerivesReplaceFirst b 0 c d 0
  have arrangeC :
      Derives cyclicFourOneBasis
        (wordOfCons 0 [0, c, d])
        (wordOfCons c [0, 0, d]) :=
    cyclicFourOneDerivesPermutation _ _ (by
      rw [List.perm_iff_count]
      intro z
      simp only [wordOfCons, Word.toList, List.count_cons,
        List.count_nil]
      omega)
  have replaceC := cyclicFourOneDerivesReplaceFirst c 0 0 d 0
  have arrangeD :
      Derives cyclicFourOneBasis
        (wordOfCons 0 [0, 0, d])
        (wordOfCons d [0, 0, 0]) :=
    cyclicFourOneDerivesPermutation _ _ (by
      rw [List.perm_iff_count]
      intro z
      simp only [wordOfCons, Word.toList, List.count_cons,
        List.count_nil]
      omega)
  have replaceD := cyclicFourOneDerivesReplaceFirst d 0 0 0 0
  exact Derives.trans replaceA <|
    Derives.trans arrangeB <|
    Derives.trans replaceB <|
    Derives.trans arrangeC <|
    Derives.trans replaceC <|
    Derives.trans arrangeD replaceD

private theorem cyclicFourOneDerivesToMarker :
    ∀ (x : Nat) (xs : List Nat),
      4 ≤ (wordOfCons x xs).toList.length →
      Derives cyclicFourOneBasis (wordOfCons x xs) longMarker
  | x, [], h => by
      simp [wordOfCons, Word.toList] at h
  | x, [y], h => by
      simp [wordOfCons, Word.toList] at h
  | x, [y, z], h => by
      simp [wordOfCons, Word.toList] at h
  | x, [y, z, t], _ =>
      cyclicFourOneDerivesFourToMarker x y z t
  | x, y :: z :: t :: u :: us, h => by
      have drop :=
        cyclicFourOneDerivesDropPrefix
          (Word.singleton x) (Word.singleton y)
          (Word.singleton z) (Word.singleton t) (wordOfCons u us)
      have rest :=
        cyclicFourOneDerivesToMarker y (z :: t :: u :: us) (by
          simp [wordOfCons, Word.toList])
      exact Derives.trans
        (by
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using drop)
        rest
termination_by
  _ xs _ => xs.length

/-- Every two words of length at least four are derivably equal. -/
theorem cyclicFourOneDerivesLongWords (u v : Word Nat)
    (hu : 4 ≤ u.toList.length) (hv : 4 ≤ v.toList.length) :
    Derives cyclicFourOneBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          exact Derives.trans
            (cyclicFourOneDerivesToMarker uHead uTail hu)
            (Derives.symm
              (cyclicFourOneDerivesToMarker vHead vTail hv))

private theorem pairTripleDerivesCanonical
    (a d p q r : Nat) (hne : a ≠ d)
    (hp : p = a ∨ p = d) (hq : q = a ∨ q = d)
    (hr : r = a ∨ r = d)
    (ha : a = p ∨ a = q ∨ a = r)
    (hd : d = p ∨ d = q ∨ d = r) :
    Derives cyclicFourOneBasis
      (wordOfCons p [q, r]) (wordOfCons a [a, d]) := by
  rcases hp with hp | hp
  · subst p
    rcases hq with hq | hq
    · subst q
      rcases hr with hr | hr
      · subst r
        exfalso
        simpa [hne, Ne.symm hne] using hd
      · subst r
        exact Derives.refl _
    · subst q
      rcases hr with hr | hr
      · subst r
        exact cyclicFourOneDerivesPermutation _ _ (by
          rw [List.perm_iff_count]
          intro z
          simp only [wordOfCons, Word.toList, List.count_cons,
            List.count_nil]
          omega)
      · subst r
        simpa [wordOfCons, Word.singleton, Word.append,
          Word.append_assoc] using
            cyclicFourOneDerivesMultiplicityTransfer
              (Word.singleton a) (Word.singleton d)
  · subst p
    rcases hq with hq | hq
    · subst q
      rcases hr with hr | hr
      · subst r
        exact cyclicFourOneDerivesPermutation _ _ (by
          rw [List.perm_iff_count]
          intro z
          simp only [wordOfCons, Word.toList, List.count_cons,
            List.count_nil]
          omega)
      · subst r
        exact Derives.trans
          (cyclicFourOneDerivesPermutation
            (wordOfCons d [a, d]) (wordOfCons a [d, d]) (by
            rw [List.perm_iff_count]
            intro z
            simp only [wordOfCons, Word.toList, List.count_cons,
              List.count_nil]
            omega))
          (by
            simpa [wordOfCons, Word.singleton, Word.append,
              Word.append_assoc] using
                cyclicFourOneDerivesMultiplicityTransfer
                  (Word.singleton a) (Word.singleton d))
    · subst q
      rcases hr with hr | hr
      · subst r
        exact Derives.trans
          (cyclicFourOneDerivesPermutation
            (wordOfCons d [d, a]) (wordOfCons a [d, d]) (by
            rw [List.perm_iff_count]
            intro z
            simp only [wordOfCons, Word.toList, List.count_cons,
              List.count_nil]
            omega))
          (by
            simpa [wordOfCons, Word.singleton, Word.append,
              Word.append_assoc] using
                cyclicFourOneDerivesMultiplicityTransfer
                  (Word.singleton a) (Word.singleton d))
      · subst r
        exfalso
        simpa [hne, Ne.symm hne] using ha

private theorem perm_of_distinct_triple_support_eq
    {a b c p q r : Nat}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsupport :
      ∀ z, z ∈ [a, b, c] ↔ z ∈ [p, q, r]) :
    [a, b, c].Perm [p, q, r] := by
  have hp : p = a ∨ p = b ∨ p = c := by
    simpa using (hsupport p).mpr (by simp)
  have hq : q = a ∨ q = b ∨ q = c := by
    simpa using (hsupport q).mpr (by simp)
  have hr : r = a ∨ r = b ∨ r = c := by
    simpa using (hsupport r).mpr (by simp)
  have ha : a = p ∨ a = q ∨ a = r := by
    simpa using (hsupport a).mp (by simp)
  have hb : b = p ∨ b = q ∨ b = r := by
    simpa using (hsupport b).mp (by simp)
  have hc : c = p ∨ c = q ∨ c = r := by
    simpa using (hsupport c).mp (by simp)
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  have hcb : c ≠ b := Ne.symm hbc
  rcases hp with rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl <;>
    simp_all
  all_goals
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_cons, List.count_nil]
    omega

private theorem cyclicFourOneDerivesLengthThreeSupport
    (a b c p q r : Nat)
    (hsupport :
      ∀ z, z ∈ [a, b, c] ↔ z ∈ [p, q, r]) :
    Derives cyclicFourOneBasis
      (wordOfCons a [b, c]) (wordOfCons p [q, r]) := by
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      have hp : p = a := by
        simpa using (hsupport p).mpr (by simp)
      have hq : q = a := by
        simpa using (hsupport q).mpr (by simp)
      have hr : r = a := by
        simpa using (hsupport r).mpr (by simp)
      subst p
      subst q
      subst r
      exact Derives.refl _
    · have hp : p = a ∨ p = c := by
        simpa using (hsupport p).mpr (by simp)
      have hq : q = a ∨ q = c := by
        simpa using (hsupport q).mpr (by simp)
      have hr : r = a ∨ r = c := by
        simpa using (hsupport r).mpr (by simp)
      have ha : a = p ∨ a = q ∨ a = r := by
        simpa using (hsupport a).mp (by simp)
      have hc : c = p ∨ c = q ∨ c = r := by
        simpa using (hsupport c).mp (by simp)
      exact Derives.symm <|
          pairTripleDerivesCanonical a c p q r hac hp hq hr ha hc
  · by_cases hac : a = c
    ·
      have hp : p = a ∨ p = b := by
        have h : p = a ∨ p = b ∨ p = c := by
          simpa using (hsupport p).mpr (by simp)
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inl (h.trans hac.symm)
      have hq : q = a ∨ q = b := by
        have h : q = a ∨ q = b ∨ q = c := by
          simpa using (hsupport q).mpr (by simp)
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inl (h.trans hac.symm)
      have hr : r = a ∨ r = b := by
        have h : r = a ∨ r = b ∨ r = c := by
          simpa using (hsupport r).mpr (by simp)
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact Or.inl (h.trans hac.symm)
      have ha : a = p ∨ a = q ∨ a = r := by
        simpa using (hsupport a).mp (by simp)
      have hb : b = p ∨ b = q ∨ b = r := by
        simpa using (hsupport b).mp (by simp)
      subst c
      have sourceCanonical :
          Derives cyclicFourOneBasis
            (wordOfCons a [b, a]) (wordOfCons a [a, b]) :=
        cyclicFourOneDerivesPermutation _ _ (by
          rw [List.perm_iff_count]
          intro z
          simp only [wordOfCons, Word.toList, List.count_cons,
            List.count_nil]
          omega)
      exact Derives.trans sourceCanonical <|
        Derives.symm <|
          pairTripleDerivesCanonical a b p q r hab hp hq hr ha hb
    · by_cases hbc : b = c
      · subst c
        have hp : p = a ∨ p = b := by
          simpa using (hsupport p).mpr (by simp)
        have hq : q = a ∨ q = b := by
          simpa using (hsupport q).mpr (by simp)
        have hr : r = a ∨ r = b := by
          simpa using (hsupport r).mpr (by simp)
        have ha : a = p ∨ a = q ∨ a = r := by
          simpa using (hsupport a).mp (by simp)
        have hb : b = p ∨ b = q ∨ b = r := by
          simpa using (hsupport b).mp (by simp)
        have sourceCanonical :
            Derives cyclicFourOneBasis
              (wordOfCons a [b, b]) (wordOfCons a [a, b]) := by
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using
              cyclicFourOneDerivesMultiplicityTransfer
                (Word.singleton a) (Word.singleton b)
        exact Derives.trans sourceCanonical <|
          Derives.symm <|
            pairTripleDerivesCanonical a b p q r hab hp hq hr ha hb
      · exact cyclicFourOneDerivesPermutation _ _ <|
          perm_of_distinct_triple_support_eq hab hac hbc hsupport

/-- The state of the power `gⁿ`, where element `3` is the generator:
`g, g², g³, g⁴, ... = 3,1,2,0,0,...`. -/
private def cyclicFourOneState (n : Nat) : Fin 4 :=
  if n = 1 then 3
  else if n = 2 then 1
  else if n = 3 then 2
  else 0

private theorem cyclicFourOneMul_state_one
    (n : Nat) (nPos : 0 < n) :
    cyclicFourOneMul (cyclicFourOneState n)
        (cyclicFourOneState 1) =
      cyclicFourOneState (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · by_cases hn3 : n = 3
      · subst n
        rfl
      · have hn4 : 4 ≤ n := by omega
        have hn0 : n ≠ 0 := by omega
        have hnext1 : n + 1 ≠ 1 := by omega
        have hnext2 : n + 1 ≠ 2 := by omega
        have hnext3 : n + 1 ≠ 3 := by omega
        apply Fin.ext
        simp [cyclicFourOneState, cyclicFourOneMul, hn0, hn1, hn2,
          hn3, hnext1, hnext2, hnext3]

private theorem cyclicFourOneMul_state_two
    (n : Nat) (nPos : 0 < n) :
    cyclicFourOneMul (cyclicFourOneState n)
        (cyclicFourOneState 2) =
      cyclicFourOneState (n + 2) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · by_cases hn3 : n = 3
      · subst n
        rfl
      · have hn4 : 4 ≤ n := by omega
        have hn0 : n ≠ 0 := by omega
        have hnext1 : n + 2 ≠ 1 := by omega
        have hnext2 : n + 2 ≠ 2 := by omega
        have hnext3 : n + 2 ≠ 3 := by omega
        apply Fin.ext
        simp [cyclicFourOneState, cyclicFourOneMul, hn0, hn1, hn2,
          hn3, hnext1, hnext2, hnext3]

private def weightedValuation (weight : Nat → Nat) : Nat → Fin 4 :=
  fun x => cyclicFourOneState (weight x)

private def weightSum (weight : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => weight x + weightSum weight xs

private theorem cyclicFourOneFold_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (xs : List Nat) (acc : Nat) (accPos : 0 < acc) :
    xs.foldl
        (fun current x =>
          cyclicFourOneMul current (weightedValuation weight x))
        (cyclicFourOneState acc) =
      cyclicFourOneState (acc + weightSum weight xs) := by
  induction xs generalizing acc with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases oneOrTwo x with hx | hx
      · rw [show weightedValuation weight x =
          cyclicFourOneState 1 by simp [weightedValuation, hx]]
        rw [cyclicFourOneMul_state_one acc accPos]
        rw [ih (acc + 1) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega
      · rw [show weightedValuation weight x =
          cyclicFourOneState 2 by simp [weightedValuation, hx]]
        rw [cyclicFourOneMul_state_two acc accPos]
        rw [ih (acc + 2) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega

private theorem cyclicFourOneEval_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (w : Word Nat) :
    cyclicFourOne.semigroup.eval (weightedValuation weight) w =
      cyclicFourOneState (weightSum weight w.toList) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              cyclicFourOneMul current (weightedValuation weight x))
            (weightedValuation weight head) =
          cyclicFourOneState
            (weightSum weight (head :: tail))
      rw [show weightedValuation weight head =
          cyclicFourOneState (weight head) by rfl]
      have headPos : 0 < weight head := by
        rcases oneOrTwo head with h | h <;> omega
      rw [cyclicFourOneFold_weighted weight oneOrTwo tail
        (weight head) headPos]
      simp [weightSum]

private def unitWeight : Nat → Nat := fun _ => 1

private def doubledWeight (z : Nat) : Nat → Nat :=
  fun x => if x = z then 2 else 1

private theorem weightSum_unit (xs : List Nat) :
    weightSum unitWeight xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [weightSum, unitWeight, ih]
      omega

private theorem weightSum_doubled (z : Nat) (xs : List Nat) :
    weightSum (doubledWeight z) xs = xs.length + xs.count z := by
  induction xs with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      by_cases hx : x = z
      · subst x
        simp [weightSum, doubledWeight, ih]
        omega
      · simp [weightSum, doubledWeight, hx, ih]
        omega

private theorem cyclicFourOneEval_unit (w : Word Nat) :
    cyclicFourOne.semigroup.eval (weightedValuation unitWeight) w =
      cyclicFourOneState w.toList.length := by
  rw [cyclicFourOneEval_weighted unitWeight (by
    intro x
    exact Or.inl rfl)]
  rw [weightSum_unit]

private theorem cyclicFourOneEval_doubled (z : Nat) (w : Word Nat) :
    cyclicFourOne.semigroup.eval (weightedValuation (doubledWeight z)) w =
      cyclicFourOneState (w.toList.length + w.toList.count z) := by
  rw [cyclicFourOneEval_weighted (doubledWeight z) (by
    intro x
    by_cases hx : x = z
    · exact Or.inr (by simp [doubledWeight, hx])
    · exact Or.inl (by simp [doubledWeight, hx]))]
  rw [weightSum_doubled]

private theorem cyclicFourOneState_eq_one
    {n : Nat} (nPos : 0 < n) :
    cyclicFourOneState n = cyclicFourOneState 1 ↔ n = 1 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · exact hn1
    · by_cases hn2 : n = 2
      · subst n
        simp [cyclicFourOneState] at h
      · by_cases hn3 : n = 3
        · subst n
          simp [cyclicFourOneState] at h
        · simp [cyclicFourOneState, hn1, hn2, hn3] at h
  · intro h
    rw [h]

private theorem cyclicFourOneState_eq_two
    {n : Nat} (nPos : 0 < n) :
    cyclicFourOneState n = cyclicFourOneState 2 ↔ n = 2 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · subst n
      simp [cyclicFourOneState] at h
    · by_cases hn2 : n = 2
      · exact hn2
      · by_cases hn3 : n = 3
        · subst n
          simp [cyclicFourOneState] at h
        · simp [cyclicFourOneState, hn1, hn2, hn3] at h
  · intro h
    rw [h]

private theorem cyclicFourOneState_eq_three
    {n : Nat} (nPos : 0 < n) :
    cyclicFourOneState n = cyclicFourOneState 3 ↔ n = 3 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · subst n
      simp [cyclicFourOneState] at h
    · by_cases hn2 : n = 2
      · subst n
        simp [cyclicFourOneState] at h
      · by_cases hn3 : n = 3
        · exact hn3
        · simp [cyclicFourOneState, hn1, hn2, hn3] at h
  · intro h
    rw [h]

private theorem cyclicFourOneState_one_add_injective
    {m n : Nat} (mLe : m ≤ 1) (nLe : n ≤ 1)
    (h :
      cyclicFourOneState (1 + m) =
        cyclicFourOneState (1 + n)) :
    m = n := by
  have hm : m = 0 ∨ m = 1 := by omega
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hm with rfl | rfl <;>
    rcases hn with rfl | rfl <;>
    simp [cyclicFourOneState] at h ⊢

private theorem cyclicFourOneState_two_add_injective
    {m n : Nat} (mLe : m ≤ 2) (nLe : n ≤ 2)
    (h :
      cyclicFourOneState (2 + m) =
        cyclicFourOneState (2 + n)) :
    m = n := by
  have hm : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hm with rfl | rfl | rfl <;>
    rcases hn with rfl | rfl | rfl <;>
    simp [cyclicFourOneState] at h ⊢

private theorem cyclicFourOneState_three_add_zero_iff (n : Nat) :
    cyclicFourOneState (3 + n) = cyclicFourOneState 3 ↔ n = 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hne1 : 3 + n ≠ 1 := by omega
    have hne2 : 3 + n ≠ 2 := by omega
    have hne3 : 3 + n ≠ 3 := by omega
    simp [cyclicFourOneState, hne1, hne2, hne3, hn]

private theorem word_eq_of_length_three
    (w : Word Nat) (hlength : w.toList.length = 3) :
    ∃ a b c, w = wordOfCons a [b, c] := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at hlength
      | cons second rest =>
          cases rest with
          | nil =>
              simp [Word.toList] at hlength
          | cons third more =>
              cases more with
              | nil =>
                  exact ⟨head, second, third, rfl⟩
              | cons fourth remaining =>
                  simp [Word.toList] at hlength

def cyclicFourOneFiniteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def cyclicFourOneFiniteLongCancellationLaw : Identity (Fin 5) :=
  ⟨⟨0, [1, 2, 3, 4]⟩, ⟨1, [2, 3, 4]⟩⟩

def cyclicFourOneFiniteMultiplicityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 1]⟩, ⟨0, [0, 1]⟩⟩

theorem cyclicFourOneFiniteCommutativityLaw_map :
    cyclicFourOneFiniteCommutativityLaw.map Fin.val =
      cyclicFourOneCommutativityLaw := rfl

theorem cyclicFourOneFiniteLongCancellationLaw_map :
    cyclicFourOneFiniteLongCancellationLaw.map Fin.val =
      cyclicFourOneLongCancellationLaw := rfl

theorem cyclicFourOneFiniteMultiplicityLaw_map :
    cyclicFourOneFiniteMultiplicityLaw.map Fin.val =
      cyclicFourOneMultiplicityLaw := rfl

set_option maxRecDepth 100000 in
theorem cyclicFourOneBasis_models :
    Models cyclicFourOne.semigroup cyclicFourOneBasis := by
  intro e he
  simp only [cyclicFourOneBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · rw [← cyclicFourOneFiniteCommutativityLaw_map]
    exact cyclicFourOne.checkIdentityNat_sound
      cyclicFourOneFiniteCommutativityLaw (by decide)
  · rw [← cyclicFourOneFiniteLongCancellationLaw_map]
    exact cyclicFourOne.checkIdentityNat_sound
      cyclicFourOneFiniteLongCancellationLaw (by decide)
  · rw [← cyclicFourOneFiniteMultiplicityLaw_map]
    exact cyclicFourOne.checkIdentityNat_sound
      cyclicFourOneFiniteMultiplicityLaw (by decide)

/-- Unrestricted completeness over `Nat` variables. Lengths one and two
retain exact multiplicities, length three retains only support, and every
word of length at least four belongs to one derivability class. -/
theorem cyclicFourOneBasis_complete :
    BasisFor cyclicFourOne.semigroup cyclicFourOneBasis := by
  refine ⟨cyclicFourOneBasis_models, ?_⟩
  intro e valid
  have lengthState :
      cyclicFourOneState e.lhs.toList.length =
        cyclicFourOneState e.rhs.toList.length := by
    have evaluated := valid (weightedValuation unitWeight)
    rw [cyclicFourOneEval_unit, cyclicFourOneEval_unit] at evaluated
    exact evaluated
  have weightedState :
      ∀ z,
        cyclicFourOneState
            (e.lhs.toList.length + e.lhs.toList.count z) =
          cyclicFourOneState
            (e.rhs.toList.length + e.rhs.toList.count z) := by
    intro z
    have evaluated := valid (weightedValuation (doubledWeight z))
    rw [cyclicFourOneEval_doubled,
      cyclicFourOneEval_doubled] at evaluated
    exact evaluated
  have lhsPos : 0 < e.lhs.toList.length := by
    cases e.lhs
    simp [Word.toList]
  have rhsPos : 0 < e.rhs.toList.length := by
    cases e.rhs
    simp [Word.toList]
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne : e.rhs.toList.length = 1 := by
      apply (cyclicFourOneState_eq_one rhsPos).mp
      rw [← lengthState, lhsOne]
    have countEq : ∀ z,
        e.lhs.toList.count z = e.rhs.toList.count z := by
      intro z
      apply cyclicFourOneState_one_add_injective
      · simpa [lhsOne] using
          (List.count_le_length (a := z) (l := e.lhs.toList))
      · simpa [rhsOne] using
          (List.count_le_length (a := z) (l := e.rhs.toList))
      · simpa [lhsOne, rhsOne] using weightedState z
    exact cyclicFourOneDerivesPermutation e.lhs e.rhs <|
      List.perm_iff_count.mpr countEq
  · by_cases lhsTwo : e.lhs.toList.length = 2
    · have rhsTwo : e.rhs.toList.length = 2 := by
        apply (cyclicFourOneState_eq_two rhsPos).mp
        rw [← lengthState, lhsTwo]
      have countEq : ∀ z,
          e.lhs.toList.count z = e.rhs.toList.count z := by
        intro z
        apply cyclicFourOneState_two_add_injective
        · simpa [lhsTwo] using
            (List.count_le_length (a := z) (l := e.lhs.toList))
        · simpa [rhsTwo] using
            (List.count_le_length (a := z) (l := e.rhs.toList))
        · simpa [lhsTwo, rhsTwo] using weightedState z
      exact cyclicFourOneDerivesPermutation e.lhs e.rhs <|
        List.perm_iff_count.mpr countEq
    · by_cases lhsThree : e.lhs.toList.length = 3
      · have rhsThree : e.rhs.toList.length = 3 := by
          apply (cyclicFourOneState_eq_three rhsPos).mp
          rw [← lengthState, lhsThree]
        have countZeroEq :
            ∀ z,
              e.lhs.toList.count z = 0 ↔
                e.rhs.toList.count z = 0 := by
          intro z
          constructor
          · intro hl
            apply (cyclicFourOneState_three_add_zero_iff
              (e.rhs.toList.count z)).mp
            simpa [lhsThree, rhsThree, hl] using
              (weightedState z).symm
          · intro hr
            apply (cyclicFourOneState_three_add_zero_iff
              (e.lhs.toList.count z)).mp
            simpa [lhsThree, rhsThree, hr] using weightedState z
        have supportEq :
            ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
          intro z
          constructor
          · intro hl
            have hlPos : 0 < e.lhs.toList.count z :=
              List.count_pos_iff.mpr hl
            have hrNe : e.rhs.toList.count z ≠ 0 := by
              intro hrZero
              have hlZero := (countZeroEq z).mpr hrZero
              omega
            exact List.count_pos_iff.mp (Nat.pos_of_ne_zero hrNe)
          · intro hr
            have hrPos : 0 < e.rhs.toList.count z :=
              List.count_pos_iff.mpr hr
            have hlNe : e.lhs.toList.count z ≠ 0 := by
              intro hlZero
              have hrZero := (countZeroEq z).mp hlZero
              omega
            exact List.count_pos_iff.mp (Nat.pos_of_ne_zero hlNe)
        obtain ⟨lx, ly, lz, lhsShape⟩ :=
          word_eq_of_length_three e.lhs lhsThree
        obtain ⟨rx, ry, rz, rhsShape⟩ :=
          word_eq_of_length_three e.rhs rhsThree
        rw [lhsShape, rhsShape] at supportEq ⊢
        exact cyclicFourOneDerivesLengthThreeSupport
          lx ly lz rx ry rz (by
            intro z
            simpa [wordOfCons, Word.toList] using supportEq z)
      · have lhsLong : 4 ≤ e.lhs.toList.length := by omega
        have rhsNotOne : e.rhs.toList.length ≠ 1 := by
          intro rhsOne
          have lhsStateOne :
              cyclicFourOneState e.lhs.toList.length =
                cyclicFourOneState 1 := by
            rw [lengthState, rhsOne]
          exact lhsOne <|
            (cyclicFourOneState_eq_one lhsPos).mp lhsStateOne
        have rhsNotTwo : e.rhs.toList.length ≠ 2 := by
          intro rhsTwo
          have lhsStateTwo :
              cyclicFourOneState e.lhs.toList.length =
                cyclicFourOneState 2 := by
            rw [lengthState, rhsTwo]
          exact lhsTwo <|
            (cyclicFourOneState_eq_two lhsPos).mp lhsStateTwo
        have rhsNotThree : e.rhs.toList.length ≠ 3 := by
          intro rhsThree
          have lhsStateThree :
              cyclicFourOneState e.lhs.toList.length =
                cyclicFourOneState 3 := by
            rw [lengthState, rhsThree]
          exact lhsThree <|
            (cyclicFourOneState_eq_three lhsPos).mp lhsStateThree
        have rhsLong : 4 ≤ e.rhs.toList.length := by omega
        exact cyclicFourOneDerivesLongWords
          e.lhs e.rhs lhsLong rhsLong

theorem cyclicFourOneOppositeBasis_complete :
    BasisFor cyclicFourOne.semigroup.opposite
      (reversedBasis cyclicFourOneBasis) :=
  cyclicFourOneBasis_complete.oppositeReversed

end SemigroupBasis.Examples
