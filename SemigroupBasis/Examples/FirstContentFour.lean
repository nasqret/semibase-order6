import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Multiplication for the zero-based form of the stored table
`[[1,1,1,1],[1,1,1,1],[1,1,3,1],[4,4,4,4]]`. -/
def firstContentFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 1 then 0 else
      if a = 2 then (if b = 2 then 2 else 0) else 3

/-- The Smallsemi representative `S4_55`. -/
def firstContentFour : FiniteTable where
  order := 4
  mul := firstContentFourMul
  assoc := by decide

def firstContentXX : Word Nat := ⟨0, [0]⟩
def firstContentXXX : Word Nat := ⟨0, [0, 0]⟩
def firstContentXY : Word Nat := ⟨0, [1]⟩
def firstContentXXY : Word Nat := ⟨0, [0, 1]⟩
def firstContentXYX : Word Nat := ⟨0, [1, 0]⟩
def firstContentXYZ : Word Nat := ⟨0, [1, 2]⟩
def firstContentXZY : Word Nat := ⟨0, [2, 1]⟩

def firstContentPowerLaw : Identity Nat :=
  ⟨firstContentXX, firstContentXXX⟩

def firstContentLeftDuplicationLaw : Identity Nat :=
  ⟨firstContentXY, firstContentXXY⟩

def firstContentReturnDuplicationLaw : Identity Nat :=
  ⟨firstContentXY, firstContentXYX⟩

def firstContentSuffixCommutationLaw : Identity Nat :=
  ⟨firstContentXYZ, firstContentXZY⟩

/-- The exact basis `xx = xxx`, `xy = xxy`, `xy = xyx`,
`xyz = xzy`. -/
def firstContentFourBasis : List (Identity Nat) :=
  [firstContentPowerLaw, firstContentLeftDuplicationLaw,
    firstContentReturnDuplicationLaw, firstContentSuffixCommutationLaw]

private def instantiateThreeWords (p u v : Word Nat) : Nat → Word Nat
  | 0 => p
  | 1 => u
  | 2 => v
  | n + 3 => Word.singleton (n + 3)

theorem firstContentDerivesLeftDuplication (u v : Word Nat) :
    Derives firstContentFourBasis (u ++ v) ((u ++ u) ++ v) := by
  have hbase :
      Derives firstContentFourBasis firstContentXY firstContentXXY :=
    Derives.fromBasis (e := firstContentLeftDuplicationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [firstContentFourBasis, firstContentLeftDuplicationLaw,
    firstContentXY, firstContentXXY, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

theorem firstContentDerivesReturnDuplication (u v : Word Nat) :
    Derives firstContentFourBasis (u ++ v) ((u ++ v) ++ u) := by
  have hbase :
      Derives firstContentFourBasis firstContentXY firstContentXYX :=
    Derives.fromBasis (e := firstContentReturnDuplicationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [firstContentFourBasis, firstContentReturnDuplicationLaw,
    firstContentXY, firstContentXYX, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- The two duplication identities imply duplication of the right block:
`uv = uvu = uvvu = uvv`. -/
theorem firstContentDerivesRightDuplication (u v : Word Nat) :
    Derives firstContentFourBasis (u ++ v) (u ++ (v ++ v)) := by
  have first := firstContentDerivesReturnDuplication u v
  have second :=
    Derives.prepend u (firstContentDerivesLeftDuplication v u)
  have third :=
    Derives.symm (firstContentDerivesReturnDuplication u (v ++ v))
  exact Derives.trans first <|
    Derives.trans
      (by simpa [Word.append_assoc] using second)
      (by simpa [Word.append_assoc] using third)

/-- Arbitrary nonempty blocks after a fixed nonempty prefix may be swapped. -/
theorem firstContentDerivesSuffixSwap (p u v : Word Nat) :
    Derives firstContentFourBasis
      ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have hbase :
      Derives firstContentFourBasis firstContentXYZ firstContentXZY :=
    Derives.fromBasis (e := firstContentSuffixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords p u v)
  simpa [firstContentFourBasis, firstContentSuffixCommutationLaw,
    firstContentXYZ, firstContentXZY, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfHeadTail (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- Any permutation of the suffix is derivable while the first letter stays
fixed. -/
theorem firstContentDerivesSuffixPermutation
    {xs ys : List Nat} (hperm : xs.Perm ys) (head : Nat) :
    Derives firstContentFourBasis
      (wordOfHeadTail head xs) (wordOfHeadTail head ys) := by
  induction hperm generalizing head with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa [wordOfHeadTail, Word.append, Word.singleton] using
        Derives.prepend (Word.singleton head) (ih x)
  | swap x y xs =>
      cases xs with
      | nil =>
          simpa [wordOfHeadTail, Word.append, Word.singleton,
            Word.append_assoc] using
            firstContentDerivesSuffixSwap
              (Word.singleton head) (Word.singleton y)
              (Word.singleton x)
      | cons z zs =>
          have swapped :=
            Derives.appendRight
              (firstContentDerivesSuffixSwap
                (Word.singleton head) (Word.singleton y)
                (Word.singleton x))
              (wordOfHeadTail z zs)
          simpa [wordOfHeadTail, Word.append, Word.singleton,
            Word.append_assoc] using swapped
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ head) (ih₂ head)

private theorem perm_cons_to_end (x : Nat) :
    ∀ xs : List Nat, (x :: xs).Perm (xs ++ [x])
  | [] => List.Perm.refl _
  | y :: ys =>
      (List.Perm.swap y x ys).trans <|
        List.Perm.cons y (perm_cons_to_end x ys)

/-- In a non-singleton word, any already occurring letter may be appended.
If it is the first letter, use `xy = xyx`. Otherwise permute a suffix
occurrence to the end, duplicate that final block, and restore the suffix
order. -/
theorem firstContentDerivesAppendMember (w : Word Nat) (x : Nat)
    (hlong : w.tail ≠ []) (hx : x ∈ w.toList) :
    Derives firstContentFourBasis w (w ++ Word.singleton x) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          exact False.elim (hlong rfl)
      | cons next rest =>
          simp only [Word.toList, List.mem_cons] at hx
          rcases hx with hxHead | hxTail
          · subst x
            simpa [wordOfHeadTail, Word.append, Word.singleton,
              Word.append_assoc] using
              firstContentDerivesReturnDuplication
                (Word.singleton head) (wordOfHeadTail next rest)
          · have arrange :
                (next :: rest).Perm
                  ((next :: rest).erase x ++ [x]) := by
              have hxTail' : x ∈ next :: rest := by
                simpa only [List.mem_cons] using hxTail
              exact (List.perm_cons_erase hxTail').trans <|
                perm_cons_to_end x ((next :: rest).erase x)
            have arranged :=
              firstContentDerivesSuffixPermutation arrange head
            let prefWord : Word Nat :=
              wordOfHeadTail head ((next :: rest).erase x)
            have duplicate :=
              firstContentDerivesRightDuplication
                prefWord (Word.singleton x)
            have restore :
                (((next :: rest).erase x ++ [x]) ++ [x]).Perm
                  ((next :: rest) ++ [x]) := by
              exact arrange.symm.append_right [x]
            have restored :=
              firstContentDerivesSuffixPermutation restore head
            exact Derives.trans arranged <|
              Derives.trans
                (by
                  simpa [prefWord, wordOfHeadTail, Word.append,
                    Word.singleton, List.append_assoc] using duplicate)
                (by
                  simpa [wordOfHeadTail, Word.append, Word.singleton,
                    List.append_assoc] using restored)

theorem firstContentDerivesAppendList (w : Word Nat) (xs : List Nat)
    (hlong : w.tail ≠ [])
    (hcontent : ∀ x, x ∈ xs → x ∈ w.toList) :
    Derives firstContentFourBasis w ⟨w.head, w.tail ++ xs⟩ := by
  induction xs generalizing w with
  | nil =>
      simpa using Derives.refl w
  | cons x xs ih =>
      have hx : x ∈ w.toList :=
        hcontent x (List.Mem.head xs)
      have firstStep :=
        firstContentDerivesAppendMember w x hlong hx
      have appendedLong :
          (w ++ Word.singleton x).tail ≠ [] := by
        simp
      have remainingContent :
          ∀ y, y ∈ xs →
            y ∈ (w ++ Word.singleton x).toList := by
        intro y hy
        rw [Word.toList_append]
        exact List.mem_append_left _ <|
          hcontent y (List.Mem.tail x hy)
      have restStep :=
        ih (w ++ Word.singleton x) appendedLong remainingContent
      exact Derives.trans firstStep <| by
        simpa [Word.singleton, List.append_assoc] using restStep

/-- A non-singleton word may be expanded by any word whose content is already
present. -/
theorem firstContentDerivesContentExpansion (u v : Word Nat)
    (hlong : u.tail ≠ [])
    (hcontent : ∀ x, x ∈ v.toList → x ∈ u.toList) :
    Derives firstContentFourBasis u (u ++ v) := by
  have h :=
    firstContentDerivesAppendList u v.toList hlong hcontent
  simpa [Word.toList, Word.append] using h

/-- Words with the same first letter commute as whole blocks. -/
theorem firstContentDerivesConcatSwap (u v : Word Nat)
    (heads : u.head = v.head) :
    Derives firstContentFourBasis (u ++ v) (v ++ u) := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          simp only at heads
          subst vHead
          cases uTail with
          | nil =>
              cases vTail with
              | nil =>
                  exact Derives.refl _
              | cons vNext vRest =>
                  let vSuffix : Word Nat := ⟨vNext, vRest⟩
                  simpa [vSuffix, Word.append_assoc] using
                    firstContentDerivesSuffixSwap
                      (Word.singleton uHead) (Word.singleton uHead) vSuffix
          | cons uNext uRest =>
              let uSuffix : Word Nat := ⟨uNext, uRest⟩
              cases vTail with
              | nil =>
                  exact Derives.symm <| by
                    simpa [uSuffix, Word.append_assoc] using
                      firstContentDerivesSuffixSwap
                        (Word.singleton uHead) (Word.singleton uHead) uSuffix
              | cons vNext vRest =>
                  let vSuffix : Word Nat := ⟨vNext, vRest⟩
                  have firstSwap :=
                    firstContentDerivesSuffixSwap
                      (Word.singleton uHead) uSuffix
                      (Word.singleton uHead ++ vSuffix)
                  have secondSwap :=
                    Derives.appendRight
                      (firstContentDerivesSuffixSwap
                        (Word.singleton uHead) (Word.singleton uHead) vSuffix)
                      uSuffix
                  exact Derives.trans
                    (by
                      simpa [uSuffix, vSuffix, Word.append_assoc] using
                        firstSwap)
                    (by
                      simpa [uSuffix, vSuffix, Word.append_assoc] using
                        secondSwap)

private theorem firstContentMul_zero_left (a : Fin 4) :
    firstContentFourMul 0 a = 0 := by
  decide +revert

private theorem firstContentFold_zero
    (valuation : Nat → Fin 4) (xs : List Nat) :
    xs.foldl
        (fun current x => firstContentFourMul current (valuation x))
        (0 : Fin 4) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, firstContentMul_zero_left]
      exact ih

/-- Assigning every variable `1` separates singleton words from all longer
words. -/
theorem firstContentFourSingletonSeparator (w : Word Nat) :
    firstContentFour.semigroup.eval (fun _ => (1 : Fin 4)) w =
        (1 : Fin 4) ↔
      w.tail = [] := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ => firstContentFourMul current (1 : Fin 4))
            (1 : Fin 4) = 1 ↔
          tail = []
      cases tail with
      | nil =>
          simp
      | cons x xs =>
          simp only [List.foldl_cons, List.cons_ne_nil, iff_false]
          rw [show firstContentFourMul 1 1 = (0 : Fin 4) by decide]
          rw [firstContentFold_zero]
          decide

private theorem firstContentMul_eq_two_iff (a b : Fin 4) :
    firstContentFourMul a b = (2 : Fin 4) ↔
      a = (2 : Fin 4) ∧ b = (2 : Fin 4) := by
  decide +revert

private theorem firstContentFold_eq_two_iff
    (valuation : Nat → Fin 4) (xs : List Nat) (acc : Fin 4) :
    xs.foldl
        (fun current x => firstContentFourMul current (valuation x)) acc =
          (2 : Fin 4) ↔
      acc = (2 : Fin 4) ∧
        ∀ x, x ∈ xs → valuation x = (2 : Fin 4) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, firstContentMul_eq_two_iff]
      constructor
      · rintro ⟨⟨hacc, hx⟩, hxs⟩
        exact ⟨hacc, fun y hy => by
          simp only [List.mem_cons] at hy
          rcases hy with hy | hy
          · simpa [hy] using hx
          · exact hxs y hy⟩
      · rintro ⟨hacc, hall⟩
        exact ⟨⟨hacc, hall x (List.Mem.head xs)⟩,
          fun y hy => hall y (List.Mem.tail x hy)⟩

theorem firstContentFourEval_eq_two_iff
    (valuation : Nat → Fin 4) (w : Word Nat) :
    firstContentFour.semigroup.eval valuation w = (2 : Fin 4) ↔
      ∀ x, x ∈ w.toList → valuation x = (2 : Fin 4) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              firstContentFourMul current (valuation x))
            (valuation head) = (2 : Fin 4) ↔
          ∀ x, x ∈ head :: tail → valuation x = (2 : Fin 4)
      rw [firstContentFold_eq_two_iff]
      constructor
      · rintro ⟨hhead, htail⟩ x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx
        · simpa [hx] using hhead
        · exact htail x hx
      · intro hall
        exact ⟨hall head (List.Mem.head tail),
          fun x hx => hall x (List.Mem.tail head hx)⟩

def firstContentSupportSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 0 else 2

/-- The support separator returns `2` exactly when the tested variable is
absent. -/
theorem firstContentFourSupportSeparator (z : Nat) (w : Word Nat) :
    firstContentFour.semigroup.eval (firstContentSupportSeparator z) w =
        (2 : Fin 4) ↔
      z ∉ w.toList := by
  rw [firstContentFourEval_eq_two_iff]
  constructor
  · intro hall hz
    have := hall z hz
    simp [firstContentSupportSeparator] at this
  · intro hz x hx
    have hne : x ≠ z := by
      intro h
      apply hz
      simpa [h] using hx
    simp [firstContentSupportSeparator, hne]

private theorem firstContentFold_three
    (valuation : Nat → Fin 4) (xs : List Nat) :
    xs.foldl
        (fun current x => firstContentFourMul current (valuation x))
        (3 : Fin 4) = 3 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [List.foldl_cons, firstContentFourMul] using ih

def firstContentHeadSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 3 else 0

/-- The head separator returns `3` exactly when the tested variable is the
first letter. -/
theorem firstContentFourHeadSeparator (z : Nat) (w : Word Nat) :
    firstContentFour.semigroup.eval (firstContentHeadSeparator z) w =
        (3 : Fin 4) ↔
      w.head = z := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              firstContentFourMul current
                (firstContentHeadSeparator z x))
            (firstContentHeadSeparator z head) = 3 ↔
          head = z
      by_cases hhead : head = z
      · subst head
        rw [show firstContentHeadSeparator z z = (3 : Fin 4) by
          simp [firstContentHeadSeparator]]
        rw [firstContentFold_three]
        simp
      · change
          tail.foldl
                (fun current x =>
                  firstContentFourMul current
                    (firstContentHeadSeparator z x))
                (firstContentHeadSeparator z head) = 3 ↔
            head = z
        rw [show firstContentHeadSeparator z head = (0 : Fin 4) by
          simp [firstContentHeadSeparator, hhead]]
        rw [firstContentFold_zero]
        simp [hhead]

theorem firstContentFourValid_support_eq (e : Identity Nat)
    (valid : e.SatisfiedBy firstContentFour.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (firstContentSupportSeparator z)
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    have rhsTwo :=
      (firstContentFourSupportSeparator z e.rhs).2 hr
    have lhsNotTwo :
        firstContentFour.semigroup.eval
            (firstContentSupportSeparator z) e.lhs ≠ (2 : Fin 4) := by
      intro lhsTwo
      exact
        (firstContentFourSupportSeparator z e.lhs).1 lhsTwo hl
    exact lhsNotTwo (evaluated.trans rhsTwo)
  · intro hr
    apply Decidable.byContradiction
    intro hl
    have lhsTwo :=
      (firstContentFourSupportSeparator z e.lhs).2 hl
    have rhsNotTwo :
        firstContentFour.semigroup.eval
            (firstContentSupportSeparator z) e.rhs ≠ (2 : Fin 4) := by
      intro rhsTwo
      exact
        (firstContentFourSupportSeparator z e.rhs).1 rhsTwo hr
    exact rhsNotTwo (evaluated.symm.trans lhsTwo)

theorem firstContentFourValid_head_eq (e : Identity Nat)
    (valid : e.SatisfiedBy firstContentFour.semigroup) :
    e.lhs.head = e.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  have evaluated := valid (firstContentHeadSeparator e.lhs.head)
  have lhsThree :
      firstContentFour.semigroup.eval
          (firstContentHeadSeparator e.lhs.head) e.lhs = (3 : Fin 4) :=
    (firstContentFourHeadSeparator e.lhs.head e.lhs).2 rfl
  have rhsNotThree :
      firstContentFour.semigroup.eval
          (firstContentHeadSeparator e.lhs.head) e.rhs ≠ (3 : Fin 4) := by
    intro rhsThree
    exact headsNe <|
      (firstContentFourHeadSeparator e.lhs.head e.rhs).1 rhsThree |>.symm
  exact rhsNotThree (evaluated.symm.trans lhsThree)

theorem firstContentFourValid_singleton_iff (e : Identity Nat)
    (valid : e.SatisfiedBy firstContentFour.semigroup) :
    e.lhs.tail = [] ↔ e.rhs.tail = [] := by
  have evaluated := valid (fun _ => (1 : Fin 4))
  constructor
  · intro hl
    apply (firstContentFourSingletonSeparator e.rhs).1
    exact evaluated.symm.trans <|
      (firstContentFourSingletonSeparator e.lhs).2 hl
  · intro hr
    apply (firstContentFourSingletonSeparator e.lhs).1
    exact evaluated.trans <|
      (firstContentFourSingletonSeparator e.rhs).2 hr

private theorem firstContentMul_power (a : Fin 4) :
    firstContentFourMul a a =
      firstContentFourMul (firstContentFourMul a a) a := by
  decide +revert

private theorem firstContentMul_left_duplication (a b : Fin 4) :
    firstContentFourMul a b =
      firstContentFourMul (firstContentFourMul a a) b := by
  decide +revert

private theorem firstContentMul_return_duplication (a b : Fin 4) :
    firstContentFourMul a b =
      firstContentFourMul (firstContentFourMul a b) a := by
  decide +revert

private theorem firstContentMul_suffix_commutation
    (a b c : Fin 4) :
    firstContentFourMul (firstContentFourMul a b) c =
      firstContentFourMul (firstContentFourMul a c) b := by
  decide +revert

theorem firstContentFourBasis_models :
    Models firstContentFour.semigroup firstContentFourBasis := by
  intro e he
  simp only [firstContentFourBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · intro valuation
    change
      firstContentFourMul (valuation 0) (valuation 0) =
        firstContentFourMul
          (firstContentFourMul (valuation 0) (valuation 0))
          (valuation 0)
    exact firstContentMul_power (valuation 0)
  · intro valuation
    change
      firstContentFourMul (valuation 0) (valuation 1) =
        firstContentFourMul
          (firstContentFourMul (valuation 0) (valuation 0))
          (valuation 1)
    exact firstContentMul_left_duplication (valuation 0) (valuation 1)
  · intro valuation
    change
      firstContentFourMul (valuation 0) (valuation 1) =
        firstContentFourMul
          (firstContentFourMul (valuation 0) (valuation 1))
          (valuation 0)
    exact firstContentMul_return_duplication (valuation 0) (valuation 1)
  · intro valuation
    change
      firstContentFourMul
          (firstContentFourMul (valuation 0) (valuation 1))
          (valuation 2) =
        firstContentFourMul
          (firstContentFourMul (valuation 0) (valuation 2))
          (valuation 1)
    exact firstContentMul_suffix_commutation
      (valuation 0) (valuation 1) (valuation 2)

/-- Unrestricted completeness over `Nat` variables. Singleton projections stay
separate. Every longer word is determined by its first variable and content:
repetitions can be inserted or removed, and the suffix can be permuted
arbitrarily. -/
theorem firstContentFourBasis_complete :
    BasisFor firstContentFour.semigroup firstContentFourBasis := by
  refine ⟨firstContentFourBasis_models, ?_⟩
  intro e valid
  have heads := firstContentFourValid_head_eq e valid
  have supportEq := firstContentFourValid_support_eq e valid
  have singletonEq := firstContentFourValid_singleton_iff e valid
  by_cases lhsSingleton : e.lhs.tail = []
  · have rhsSingleton := singletonEq.mp lhsSingleton
    have wordsEq : e.lhs = e.rhs := by
      cases e with
      | mk lhs rhs =>
          cases lhs with
          | mk lhsHead lhsTail =>
              cases rhs with
              | mk rhsHead rhsTail =>
                  simp only at heads lhsSingleton rhsSingleton
                  subst rhsHead
                  subst lhsTail
                  subst rhsTail
                  rfl
    rw [wordsEq]
    exact Derives.refl _
  · have rhsLong : e.rhs.tail ≠ [] := by
      intro rhsSingleton
      exact lhsSingleton (singletonEq.mpr rhsSingleton)
    have lhsExpansion :
        Derives firstContentFourBasis e.lhs (e.lhs ++ e.rhs) :=
      firstContentDerivesContentExpansion e.lhs e.rhs lhsSingleton
        (fun x hx => (supportEq x).2 hx)
    have rhsExpansion :
        Derives firstContentFourBasis e.rhs (e.rhs ++ e.lhs) :=
      firstContentDerivesContentExpansion e.rhs e.lhs rhsLong
        (fun x hx => (supportEq x).1 hx)
    exact Derives.trans lhsExpansion <|
      Derives.trans
        (firstContentDerivesConcatSwap e.lhs e.rhs heads)
        (Derives.symm rhsExpansion)

def firstContentFourOppositeBasis : List (Identity Nat) :=
  reversedBasis firstContentFourBasis

theorem firstContentFourOppositeBasis_complete :
    BasisFor firstContentFour.semigroup.opposite
      firstContentFourOppositeBasis := by
  simpa [firstContentFourOppositeBasis] using
    firstContentFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples
