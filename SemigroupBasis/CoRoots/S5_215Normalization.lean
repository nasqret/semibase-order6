import SemigroupBasis.CoRoots.S5_215

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_215Normalization

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_215

private def instantiateFourWords
    (u v w q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | 3 => q
  | n + 4 => Word.singleton (n + 4)

/-- Commutativity is available after arbitrary nonempty-word
substitution. -/
theorem correctedDerivesCommutativity (u v : Word Nat) :
    Derives correctedBasis (u ++ v) (v ++ u) := by
  have base :
      Derives correctedBasis xy yx :=
    Derives.fromBasis (e := commutativityLaw) <| by
      exact List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateFourWords u v v v)
  simpa [correctedBasis, commutativityLaw, xy, yx,
    SemigroupBasis.CoRoots.S5_215.w,
    instantiateFourWords, Word.bind, Word.append,
    Word.singleton] using substituted

/-- The multiplicity-transfer law after arbitrary nonempty-word
substitution. -/
theorem correctedDerivesTransfer (u v : Word Nat) :
    Derives correctedBasis
      ((u ++ u) ++ v) ((u ++ v) ++ v) := by
  have base :
      Derives correctedBasis xxy xyy :=
    Derives.fromBasis (e := transferLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have substituted :=
    Derives.subst base (instantiateFourWords u v v v)
  simpa [correctedBasis, transferLaw, xxy, xyy,
    SemigroupBasis.CoRoots.S5_215.w,
    instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Every product of four nonempty blocks permits duplication of its first
block. -/
theorem correctedDerivesLongDuplication
    (u v w q : Word Nat) :
    Derives correctedBasis
      (((u ++ v) ++ w) ++ q)
      ((((u ++ u) ++ v) ++ w) ++ q) := by
  have base :
      Derives correctedBasis xyzt xxyzt :=
    Derives.fromBasis (e := squarefreeInsertionLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateFourWords u v w q)
  simpa [correctedBasis, squarefreeInsertionLaw, xyzt, xxyzt,
    SemigroupBasis.CoRoots.S5_215.w,
    instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Five copies of a nonempty block contract to four copies. -/
theorem correctedDerivesFiveContraction (u : Word Nat) :
    Derives correctedBasis
      ((((u ++ u) ++ u) ++ u) ++ u)
      (((u ++ u) ++ u) ++ u) :=
  Derives.symm (correctedDerivesLongDuplication u u u u)

def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives correctedBasis
        (wordOfCons x xs) (wordOfCons y ys) →
      ListDerives (x :: xs) (y :: ys)

private theorem listDerives_of_perm {xs ys : List Nat}
    (permutation : xs.Perm ys) : ListDerives xs ys := by
  induction permutation with
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
              correctedDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (correctedDerivesCommutativity
                  (Word.singleton y) (Word.singleton x))
                (wordOfCons z zs)
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using swapped
  | trans _ _ ihFirst ihSecond =>
      cases ihFirst with
      | empty =>
          cases ihSecond
          exact ListDerives.empty
      | words first =>
          cases ihSecond with
          | words second =>
              exact ListDerives.words (Derives.trans first second)

/-- Every permutation of a word follows from commutativity. -/
theorem correctedDerivesPermutation (u v : Word Nat)
    (permutation : u.toList.Perm v.toList) :
    Derives correctedBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm permutation with
          | words derivation =>
              exact derivation

/-- In a word of length at least four, any already-supported letter can be
appended by exposing four nonempty blocks and applying the insertion law. -/
theorem correctedDerivesAppendMember
    (w : Word Nat) (x : Nat)
    (hlong : 4 ≤ w.toList.length)
    (hx : x ∈ w.toList) :
    Derives correctedBasis w (w ++ Word.singleton x) := by
  let remaining := w.toList.erase x
  have sourcePerm : w.toList.Perm (x :: remaining) := by
    simpa [remaining] using List.perm_cons_erase hx
  have remainingLong : 3 ≤ remaining.length := by
    have lengths := sourcePerm.length_eq
    simp only [List.length_cons] at lengths
    omega
  cases hremaining : remaining with
  | nil =>
      rw [hremaining] at remainingLong
      simp at remainingLong
  | cons a rest =>
      cases hrest : rest with
      | nil =>
          rw [hremaining, hrest] at remainingLong
          simp at remainingLong
      | cons b more =>
          cases hmore : more with
          | nil =>
              rw [hremaining, hrest, hmore] at remainingLong
              simp at remainingLong
          | cons c cs =>
              have remainingEq :
                  remaining = a :: b :: c :: cs := by
                rw [hremaining, hrest, hmore]
              rw [remainingEq] at sourcePerm
              have arrange :
                  Derives correctedBasis w
                    (wordOfCons x (a :: b :: c :: cs)) :=
                correctedDerivesPermutation _ _ <| by
                  simpa [wordOfCons, Word.toList] using sourcePerm
              have duplicate :
                  Derives correctedBasis
                    (wordOfCons x (a :: b :: c :: cs))
                    (wordOfCons x (x :: a :: b :: c :: cs)) := by
                simpa [wordOfCons, Word.singleton, Word.append,
                  Word.append_assoc] using
                    correctedDerivesLongDuplication
                      (Word.singleton x) (Word.singleton a)
                      (Word.singleton b) (wordOfCons c cs)
              have finishPerm :
                  (x :: x :: a :: b :: c :: cs).Perm
                    (w ++ Word.singleton x).toList := by
                rw [List.perm_iff_count]
                intro z
                have sourceCounts :=
                  (List.perm_iff_count.mp sourcePerm) z
                simp only [Word.toList_append, Word.toList_singleton,
                  List.count_append, List.count_cons,
                  List.count_nil] at sourceCounts ⊢
                omega
              have finish :
                  Derives correctedBasis
                    (wordOfCons x (x :: a :: b :: c :: cs))
                    (w ++ Word.singleton x) :=
                correctedDerivesPermutation _ _ <| by
                  simpa [wordOfCons, Word.toList] using finishPerm
              exact arrange.trans (duplicate.trans finish)

/-- Append an entire list whose letters already occur in a long word. -/
theorem correctedDerivesAppendList
    (w : Word Nat) (xs : List Nat)
    (hlong : 4 ≤ w.toList.length)
    (hcontent : ∀ x, x ∈ xs → x ∈ w.toList) :
    Derives correctedBasis w ⟨w.head, w.tail ++ xs⟩ := by
  induction xs generalizing w with
  | nil =>
      simpa using Derives.refl w
  | cons x xs ih =>
      have hx : x ∈ w.toList :=
        hcontent x (List.Mem.head xs)
      have firstStep :=
        correctedDerivesAppendMember w x hlong hx
      have currentLong :
          4 ≤ (w ++ Word.singleton x).toList.length := by
        rw [Word.toList_append]
        simp only [Word.toList_singleton, List.length_append,
          List.length_singleton]
        omega
      have remainingContent :
          ∀ y, y ∈ xs →
            y ∈ (w ++ Word.singleton x).toList := by
        intro y hy
        rw [Word.toList_append]
        exact List.mem_append_left _ <|
          hcontent y (List.Mem.tail x hy)
      have restStep :=
        ih (w ++ Word.singleton x) currentLong remainingContent
      exact firstStep.trans <| by
        simpa [Word.append, Word.singleton,
          List.append_assoc] using restStep

/-- Every word of length at least four derives to its square. -/
theorem correctedDerivesSquare (w : Word Nat)
    (hlong : 4 ≤ w.toList.length) :
    Derives correctedBasis w (w ++ w) := by
  have expanded :=
    correctedDerivesAppendList w w.toList hlong
      (fun _ member => member)
  simpa [Word.toList, Word.append] using expanded

/-- Every word of length at least four derives to its fourth power. -/
theorem correctedDerivesFourthPower (w : Word Nat)
    (hlong : 4 ≤ w.toList.length) :
    Derives correctedBasis w ((w ++ w) ++ (w ++ w)) := by
  have square := correctedDerivesSquare w hlong
  have squareLong : 4 ≤ (w ++ w).toList.length := by
    rw [Word.toList_append, List.length_append]
    omega
  exact square.trans
    (correctedDerivesSquare (w ++ w) squareLong)

/-- Retain at most four copies of every variable. -/
def capFourReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := capFourReduce xs
      if reduced.count x < 4 then x :: reduced else reduced

theorem count_capFourReduce (z : Nat) (xs : List Nat) :
    (capFourReduce xs).count z = min (xs.count z) 4 := by
  induction xs with
  | nil =>
      simp [capFourReduce]
  | cons x xs ih =>
      simp only [capFourReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, ih]
          rw [ih] at hcount
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx), ih]

private theorem capFourReduce_cons_ne_nil (x : Nat) (xs : List Nat) :
    capFourReduce (x :: xs) ≠ [] := by
  intro empty
  have count := count_capFourReduce x (x :: xs)
  rw [empty] at count
  simp at count
  omega

private theorem four_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 4) :
    xs.Perm
      (x :: x :: x :: x ::
        ((((xs.erase x).erase x).erase x).erase x)) := by
  have hx : x ∈ xs := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase hx
  have count₁ : (xs.erase x).count x = 3 := by
    rw [List.count_erase_self]
    omega
  have hx₁ : x ∈ xs.erase x :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase hx₁
  have count₂ : ((xs.erase x).erase x).count x = 2 := by
    rw [List.count_erase_self]
    omega
  have hx₂ : x ∈ (xs.erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  have third := List.perm_cons_erase hx₂
  have count₃ : (((xs.erase x).erase x).erase x).count x = 1 := by
    rw [List.count_erase_self]
    omega
  have hx₃ : x ∈ ((xs.erase x).erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <| List.Perm.cons x <|
    second.trans <| List.Perm.cons x <|
      third.trans <| List.Perm.cons x
        (List.perm_cons_erase hx₃)

private theorem contractLeadingFive :
    ∀ x xs,
      Derives correctedBasis
        (wordOfCons x (x :: x :: x :: x :: xs))
        (wordOfCons x (x :: x :: x :: xs))
  | x, [] => by
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
          correctedDerivesFiveContraction (Word.singleton x)
  | x, y :: ys => by
      have base :
          Derives correctedBasis
            (wordOfCons x [x, x, x, x])
            (wordOfCons x [x, x, x]) := by
        simpa [wordOfCons, Word.singleton, Word.append,
          Word.append_assoc] using
            correctedDerivesFiveContraction (Word.singleton x)
      have appended :=
        Derives.appendRight base (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using appended

private theorem correctedDerivesNormalizeList :
    ∀ x xs,
      match capFourReduce (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives correctedBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := correctedDerivesNormalizeList y ys
      cases reducedEq : capFourReduce (y :: ys) with
      | nil =>
          exact False.elim
            (capFourReduce_cons_ne_nil y ys reducedEq)
      | cons z zs =>
          rw [reducedEq] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          by_cases hcount : (z :: zs).count x < 4
          · have reduced :
                capFourReduce (x :: y :: ys) = x :: z :: zs := by
              change
                (if (capFourReduce (y :: ys)).count x < 4 then
                  x :: capFourReduce (y :: ys)
                else capFourReduce (y :: ys)) = x :: z :: zs
              rw [reducedEq, if_pos hcount]
            rw [reduced]
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have countLe : (z :: zs).count x ≤ 4 := by
              rw [← reducedEq, count_capFourReduce]
              exact Nat.min_le_right _ _
            have countEq : (z :: zs).count x = 4 := by omega
            let remainder :=
              ((((z :: zs).erase x).erase x).erase x).erase x
            have suffixPerm :
                (z :: zs).Perm
                  (x :: x :: x :: x :: remainder) := by
              simpa [remainder] using
                four_copies_perm x (z :: zs) countEq
            have expandedPerm :
                (x :: z :: zs).Perm
                  (x :: x :: x :: x :: x :: remainder) :=
              List.Perm.cons x suffixPerm
            have arrangedToReduced :
                (x :: x :: x :: x :: remainder).Perm
                  (z :: zs) :=
              suffixPerm.symm
            have arrange :
                Derives correctedBasis
                  (wordOfCons x (z :: zs))
                  (wordOfCons x
                    (x :: x :: x :: x :: remainder)) :=
              correctedDerivesPermutation _ _ expandedPerm
            have contract := contractLeadingFive x remainder
            have restore :
                Derives correctedBasis
                  (wordOfCons x (x :: x :: x :: remainder))
                  (wordOfCons z zs) :=
              correctedDerivesPermutation _ _ arrangedToReduced
            have reduced :
                capFourReduce (x :: y :: ys) = z :: zs := by
              change
                (if (capFourReduce (y :: ys)).count x < 4 then
                  x :: capFourReduce (y :: ys)
                else capFourReduce (y :: ys)) = z :: zs
              rw [reducedEq, if_neg hcount]
            rw [reduced]
            exact Derives.trans
              (by
                simpa [wordOfCons, Word.append, Word.singleton,
                  Word.append_assoc] using prefixed)
              (arrange.trans (contract.trans restore))
termination_by
  _ xs => xs.length

theorem correctedDerivesCapFourNormal (w : Word Nat) :
    match capFourReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives correctedBasis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact correctedDerivesNormalizeList head tail

/-- The canonical long-word list contains four copies of every supported
variable. -/
def quadrupleSupportReduce (xs : List Nat) : List Nat :=
  capFourReduce ((xs ++ xs) ++ (xs ++ xs))

theorem count_quadrupleSupportReduce (z : Nat) (xs : List Nat) :
    (quadrupleSupportReduce xs).count z =
      if z ∈ xs then 4 else 0 := by
  rw [quadrupleSupportReduce, count_capFourReduce,
    List.count_append, List.count_append]
  by_cases hz : z ∈ xs
  · rw [if_pos hz]
    have positive : 0 < xs.count z := List.count_pos_iff.mpr hz
    omega
  · rw [if_neg hz]
    have zero : xs.count z = 0 := List.count_eq_zero.mpr hz
    omega

theorem quadrupleSupportReduce_perm_of_support_eq
    {xs ys : List Nat}
    (support : ∀ z, z ∈ xs ↔ z ∈ ys) :
    (quadrupleSupportReduce xs).Perm
      (quadrupleSupportReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_quadrupleSupportReduce,
    count_quadrupleSupportReduce]
  simp only [support z]

/-- Every long word reaches the four-copies-per-support canonical
normal form. -/
theorem correctedDerivesLongNormal (w : Word Nat)
    (hlong : 4 ≤ w.toList.length) :
    match quadrupleSupportReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives correctedBasis w (wordOfCons x xs) := by
  have fourth := correctedDerivesFourthPower w hlong
  have normalized :=
    correctedDerivesCapFourNormal ((w ++ w) ++ (w ++ w))
  have sameReduction :
      quadrupleSupportReduce w.toList =
        capFourReduce (((w ++ w) ++ (w ++ w)).toList) := by
    simp [quadrupleSupportReduce, Word.toList_append,
      List.append_assoc]
  cases reduction :
      capFourReduce (((w ++ w) ++ (w ++ w)).toList) with
  | nil =>
      rw [reduction] at normalized
      exact False.elim normalized
  | cons x xs =>
      rw [reduction] at normalized
      rw [sameReduction, reduction]
      exact fourth.trans normalized

private theorem perm_xyx_xxy (x y : Nat) :
    [x, y, x].Perm [x, x, y] := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_nil]
  omega

private theorem perm_yxx_xxy (x y : Nat) :
    [y, x, x].Perm [x, x, y] := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_nil]
  omega

private theorem perm_yxy_xyy (x y : Nat) :
    [y, x, y].Perm [x, y, y] := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_nil]
  omega

private theorem perm_yyx_xyy (x y : Nat) :
    [y, y, x].Perm [x, y, y] := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_cons, List.count_nil]
  omega

private theorem derivesXYYToXXY (x y : Nat) :
    Derives correctedBasis
      (wordOfCons x [y, y]) (wordOfCons x [x, y]) := by
  simpa [wordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
      Derives.symm
        (correctedDerivesTransfer
          (Word.singleton x) (Word.singleton y))

private theorem derivesTripleTwoSupport
    (x y a b c : Nat) (xyNe : x ≠ y)
    (support :
      ∀ z, z ∈ [a, b, c] ↔ z = x ∨ z = y) :
    Derives correctedBasis
      (wordOfCons a [b, c]) (wordOfCons x [x, y]) := by
  have xMember : x ∈ [a, b, c] :=
    (support x).mpr (Or.inl rfl)
  have yMember : y ∈ [a, b, c] :=
    (support y).mpr (Or.inr rfl)
  have ha : a = x ∨ a = y :=
    (support a).mp (by simp)
  have hb : b = x ∨ b = y :=
    (support b).mp (by simp)
  have hc : c = x ∨ c = y :=
    (support c).mp (by simp)
  rcases ha with hax | hay
  · subst a
    rcases hb with hbx | hby
    · subst b
      rcases hc with hcx | hcy
      · subst c
        have yx : y = x := by
          simpa using yMember
        exact False.elim (xyNe yx.symm)
      · subst c
        exact Derives.refl _
    · subst b
      rcases hc with hcx | hcy
      · subst c
        exact correctedDerivesPermutation _ _ <| by
          simpa [wordOfCons, Word.toList] using perm_xyx_xxy x y
      · subst c
        exact derivesXYYToXXY x y
  · subst a
    rcases hb with hbx | hby
    · subst b
      rcases hc with hcx | hcy
      · subst c
        exact correctedDerivesPermutation _ _ <| by
          simpa [wordOfCons, Word.toList] using perm_yxx_xxy x y
      · subst c
        exact Derives.trans
          (correctedDerivesPermutation _ _ <| by
            simpa [wordOfCons, Word.toList] using perm_yxy_xyy x y)
          (derivesXYYToXXY x y)
    · subst b
      rcases hc with hcx | hcy
      · subst c
        exact Derives.trans
          (correctedDerivesPermutation _ _ <| by
            simpa [wordOfCons, Word.toList] using perm_yyx_xyy x y)
          (derivesXYYToXXY x y)
      · subst c
        have xyEq : x = y := by
          simpa using xMember
        exact False.elim (xyNe xyEq)

private theorem nodupPerm
    {xs ys : List Nat} (xsNodup : xs.Nodup)
    (ysNodup : ys.Nodup)
    (support : ∀ z, z ∈ xs ↔ z ∈ ys) :
    xs.Perm ys := by
  rw [List.perm_iff_count]
  intro z
  rw [xsNodup.count, ysNodup.count]
  simp only [support z]

private theorem tripleNodup_of_support
    {a b c d e f : Nat}
    (sourceNodup : [a, b, c].Nodup)
    (support :
      ∀ z, z ∈ [a, b, c] ↔ z ∈ [d, e, f]) :
    [d, e, f].Nodup := by
  have ha : a = d ∨ a = e ∨ a = f := by
    simpa using (support a).mp (by simp)
  have hb : b = d ∨ b = e ∨ b = f := by
    simpa using (support b).mp (by simp)
  have hc : c = d ∨ c = e ∨ c = f := by
    simpa using (support c).mp (by simp)
  rcases ha with ha | ha | ha <;>
    rcases hb with hb | hb | hb <;>
    rcases hc with hc | hc | hc <;>
    simp_all [eq_comm]

/-- Length-three words are classified exactly by support. -/
theorem correctedDerivesTripleOfSupportEq
    (a b c d e f : Nat)
    (support :
      ∀ z, z ∈ [a, b, c] ↔ z ∈ [d, e, f]) :
    Derives correctedBasis
      (wordOfCons a [b, c]) (wordOfCons d [e, f]) := by
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      have hd : d = a := by
        have member := (support d).mpr (by simp)
        simpa using member
      have he : e = a := by
        have member := (support e).mpr (by simp)
        simpa using member
      have hf : f = a := by
        have member := (support f).mpr (by simp)
        simpa using member
      subst d
      subst e
      subst f
      exact Derives.refl _
    · have sourceSupport :
          ∀ z, z ∈ [a, a, c] ↔ z = a ∨ z = c := by
        intro z
        simp
      have targetSupport :
          ∀ z, z ∈ [d, e, f] ↔ z = a ∨ z = c := by
        intro z
        exact (support z).symm.trans (sourceSupport z)
      have left :=
        derivesTripleTwoSupport a c a a c hac sourceSupport
      have right :=
        derivesTripleTwoSupport a c d e f hac targetSupport
      exact left.trans right.symm
  · by_cases hac : a = c
    · subst c
      have sourceSupport :
          ∀ z, z ∈ [a, b, a] ↔ z = a ∨ z = b := by
        intro z
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · intro member
          rcases member with member | member | member
          · exact Or.inl member
          · exact Or.inr member
          · exact Or.inl member
        · intro member
          rcases member with member | member
          · exact Or.inl member
          · exact Or.inr (Or.inl member)
      have targetSupport :
          ∀ z, z ∈ [d, e, f] ↔ z = a ∨ z = b := by
        intro z
        exact (support z).symm.trans (sourceSupport z)
      have left :=
        derivesTripleTwoSupport a b a b a hab sourceSupport
      have right :=
        derivesTripleTwoSupport a b d e f hab targetSupport
      exact left.trans right.symm
    · by_cases hbc : b = c
      · subst c
        have sourceSupport :
            ∀ z, z ∈ [a, b, b] ↔ z = a ∨ z = b := by
          intro z
          simp
        have targetSupport :
            ∀ z, z ∈ [d, e, f] ↔ z = a ∨ z = b := by
          intro z
          exact (support z).symm.trans (sourceSupport z)
        have left :=
          derivesTripleTwoSupport a b a b b hab sourceSupport
        have right :=
          derivesTripleTwoSupport a b d e f hab targetSupport
        exact left.trans right.symm
      · have sourceNodup : [a, b, c].Nodup := by
          simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac,
            Ne.symm hbc]
        have targetNodup :=
          tripleNodup_of_support sourceNodup support
        exact correctedDerivesPermutation _ _ <| by
          simpa [wordOfCons, Word.toList] using
            nodupPerm sourceNodup targetNodup support

/-- Word-level length-three support completeness. -/
theorem correctedDerivesLengthThreeOfSupportEq
    (u v : Word Nat)
    (uThree : u.toList.length = 3)
    (vThree : v.toList.length = 3)
    (support :
      ∀ z, z ∈ u.toList ↔ z ∈ v.toList) :
    Derives correctedBasis u v := by
  cases u with
  | mk a uTail =>
      cases uTail with
      | nil =>
          simp [Word.toList] at uThree
      | cons b uRest =>
          cases uRest with
          | nil =>
              simp [Word.toList] at uThree
          | cons c uMore =>
              have uMoreNil : uMore = [] := by
                simp [Word.toList] at uThree
                omega
              subst uMore
              cases v with
              | mk d vTail =>
                  cases vTail with
                  | nil =>
                      simp [Word.toList] at vThree
                  | cons e vRest =>
                      cases vRest with
                      | nil =>
                          simp [Word.toList] at vThree
                      | cons f vMore =>
                          have vMoreNil : vMore = [] := by
                            simp [Word.toList] at vThree
                            omega
                          subst vMore
                          simpa [wordOfCons, Word.toList] using
                            correctedDerivesTripleOfSupportEq
                              a b c d e f <| by
                                simpa [Word.toList] using support

private theorem perm_of_length_two_support_eq
    {xs ys : List Nat}
    (leftLength : xs.length = 2)
    (rightLength : ys.length = 2)
    (support : ∀ z, z ∈ xs ↔ z ∈ ys) :
    xs.Perm ys := by
  rcases xs with _ | ⟨a, xs⟩
  · simp at leftLength
  rcases xs with _ | ⟨b, xs⟩
  · simp at leftLength
  rcases xs with _ | ⟨c, xs⟩
  · rcases ys with _ | ⟨p, ys⟩
    · simp at rightLength
    rcases ys with _ | ⟨q, ys⟩
    · simp at rightLength
    rcases ys with _ | ⟨r, ys⟩
    · by_cases hab : a = b
      · subst b
        have hp : p = a := by
          have member := (support p).mpr (by simp)
          simpa using member
        have hq : q = a := by
          have member := (support q).mpr (by simp)
          simpa using member
        subst p
        subst q
        exact List.Perm.refl _
      · have hp : p = a ∨ p = b := by
          simpa using (support p).mpr (by simp)
        have hq : q = a ∨ q = b := by
          simpa using (support q).mpr (by simp)
        rcases hp with hp | hp
        · have hqb : q = b := by
            rcases hq with hqa | hqb
            · have hb := (support b).mp (by simp)
              have hba : b = a := by
                simpa [hp, hqa] using hb
              exact False.elim (hab hba.symm)
            · exact hqb
          simp [hp, hqb]
        · rcases hq with hqa | hqb
          · simpa [hp, hqa] using
              (List.Perm.swap a b []).symm
          · have ha := (support a).mp (by simp)
            have habEq : a = b := by
              simpa [hp, hqb] using ha
            exact False.elim (hab habEq)
    · simp at rightLength
  · simp at leftLength

/-- Two words have the same variable support. -/
def SameSupport (u v : Word Nat) : Prop :=
  ∀ z, z ∈ u.toList ↔ z ∈ v.toList

/-- The proposed exact congruence for the repaired three-law basis. -/
def CorrectedClass (u v : Word Nat) : Prop :=
  SameSupport u v ∧
    min u.toList.length 4 = min v.toList.length 4

/-- Support and total length capped at four are sufficient for
derivability from the repaired basis. -/
theorem correctedDerivesOfClass
    {u v : Word Nat} (sameClass : CorrectedClass u v) :
    Derives correctedBasis u v := by
  rcases sameClass with ⟨support, cappedLength⟩
  have leftPositive : 0 < u.toList.length := by
    simp [Word.toList]
  have rightPositive : 0 < v.toList.length := by
    simp [Word.toList]
  by_cases leftOne : u.toList.length = 1
  · have rightOne : v.toList.length = 1 := by
      omega
    have leftTail : u.tail = [] := by
      cases tailEq : u.tail with
      | nil => rfl
      | cons x xs =>
          have lower : 2 ≤ u.toList.length := by
            simp [Word.toList, tailEq]
          omega
    have rightTail : v.tail = [] := by
      cases tailEq : v.tail with
      | nil => rfl
      | cons x xs =>
          have lower : 2 ≤ v.toList.length := by
            simp [Word.toList, tailEq]
          omega
    have headMember : u.head ∈ v.toList :=
      (support u.head).mp (List.Mem.head _)
    have heads : u.head = v.head := by
      simpa [Word.toList, rightTail] using headMember
    have words : u = v := by
      apply Word.toList_injective
      simp [Word.toList, leftTail, rightTail, heads]
    rw [words]
    exact Derives.refl _
  · by_cases leftTwo : u.toList.length = 2
    · have rightTwo : v.toList.length = 2 := by
        omega
      exact correctedDerivesPermutation u v <|
        perm_of_length_two_support_eq
          leftTwo rightTwo support
    · by_cases leftThree : u.toList.length = 3
      · have rightThree : v.toList.length = 3 := by
          omega
        exact correctedDerivesLengthThreeOfSupportEq
          u v leftThree rightThree support
      · have leftLong : 4 ≤ u.toList.length := by omega
        have rightLong : 4 ≤ v.toList.length := by omega
        have reducedPerm :
            (quadrupleSupportReduce u.toList).Perm
              (quadrupleSupportReduce v.toList) :=
          quadrupleSupportReduce_perm_of_support_eq support
        have leftNormal := correctedDerivesLongNormal u leftLong
        have rightNormal := correctedDerivesLongNormal v rightLong
        cases leftReduction : quadrupleSupportReduce u.toList with
        | nil =>
            have count :=
              count_quadrupleSupportReduce u.head u.toList
            have member : u.head ∈ u.toList := by
              simp [Word.toList]
            rw [if_pos member] at count
            rw [leftReduction] at count
            simp at count
        | cons x xs =>
            cases rightReduction :
                quadrupleSupportReduce v.toList with
            | nil =>
                rw [leftReduction, rightReduction] at reducedPerm
                exact False.elim
                  (List.not_perm_cons_nil reducedPerm)
            | cons y ys =>
                rw [leftReduction] at leftNormal
                rw [rightReduction] at rightNormal
                rw [leftReduction, rightReduction] at reducedPerm
                exact leftNormal.trans <|
                  (correctedDerivesPermutation
                    (wordOfCons x xs) (wordOfCons y ys)
                    reducedPerm).trans rightNormal.symm

/-- Any semigroup whose valid identities preserve support and capped length
has the repaired list as a complete basis. -/
theorem correctedBasis_complete_of_separates
    {S : Type u} (G : Semigroup S)
    (models : Models G correctedBasis)
    (validSupport :
      ∀ e : Identity Nat, e.SatisfiedBy G →
        SameSupport e.lhs e.rhs)
    (validCappedLength :
      ∀ e : Identity Nat, e.SatisfiedBy G →
        min e.lhs.toList.length 4 =
          min e.rhs.toList.length 4) :
    BasisFor G correctedBasis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact correctedDerivesOfClass
    ⟨validSupport identity valid,
      validCappedLength identity valid⟩

end SemigroupBasis.CoRoots.S5_215Normalization
