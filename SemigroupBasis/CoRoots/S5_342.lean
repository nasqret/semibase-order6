import SemigroupBasis.Examples.FirstRepeatedMarkerFour
import SemigroupBasis.Examples.SimpleEndpointsFour
import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.CoRoots.S5_342

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyz : Word Nat := w 0 [1, 2]
def xyyz : Word Nat := w 0 [1, 1, 2]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyy : Word Nat := w 0 [2, 1, 1]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftEndpointDuplicationLaw : Identity Nat := ⟨xyx, xxyx⟩
def squareLaw : Identity Nat := ⟨xyx, xxyy⟩
def middleDuplicationLaw : Identity Nat := ⟨xyz, xyyz⟩
def closedInteriorSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩
def repeatedFinalSwapLaw : Identity Nat := ⟨xyzy, xzyy⟩

/-- The exact common basis of `S5_342`, `S5_353`, and `S5_591`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftEndpointDuplicationLaw, squareLaw,
    middleDuplicationLaw, closedInteriorSwapLaw, repeatedFinalSwapLaw]

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun e => e.map toFinThree

private theorem basis_roundTrip_checked :
    basis.all (fun e =>
      decide ((e.map toFinThree).map Fin.val = e)) = true := by
  decide

private theorem basis_roundTrip
    (e : Identity Nat) (member : e ∈ basis) :
    (e.map toFinThree).map Fin.val = e := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) e member

theorem models_of_finite_checks
    (T : FiniteTable)
    (checked : finiteBasis.all T.checkIdentity = true) :
    Models T.semigroup basis := by
  intro e member
  have finiteMember : e.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨e, member, rfl⟩
  have finiteValid :=
    T.checkIdentityNat_sound (e.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip e member] at finiteValid
  exact finiteValid

set_option maxRecDepth 100000 in
theorem basis_models_firstRepeatedMarkerFour :
    Models firstRepeatedMarkerFour.semigroup basis :=
  models_of_finite_checks firstRepeatedMarkerFour (by decide)

set_option maxRecDepth 100000 in
theorem basis_models_finalMarkerThree :
    Models finalMarkerThree.semigroup basis :=
  models_of_finite_checks finalMarkerThree (by decide)

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis xx xxx :=
    Derives.fromBasis (e := powerLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesLeftEndpointExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have base : Derives basis xyx xxyx :=
    Derives.fromBasis (e := leftEndpointDuplicationLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [leftEndpointDuplicationLaw, xyx, xxyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesSquareExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ u) ++ (v ++ v)) := by
  have base : Derives basis xyx xxyy :=
    Derives.fromBasis (e := squareLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [squareLaw, xyx, xxyy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesMiddleDuplication (u v z : Word Nat) :
    Derives basis ((u ++ v) ++ z) (((u ++ v) ++ v) ++ z) := by
  have base : Derives basis xyz xyyz :=
    Derives.fromBasis (e := middleDuplicationLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [middleDuplicationLaw, xyz, xyyz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesClosedInteriorSwap (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u) (((u ++ z) ++ v) ++ u) := by
  have base : Derives basis xyzx xzyx :=
    Derives.fromBasis (e := closedInteriorSwapLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [closedInteriorSwapLaw, xyzx, xzyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesRepeatedFinalSwap (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ v) (((u ++ z) ++ v) ++ v) := by
  have base : Derives basis xyzy xzyy :=
    Derives.fromBasis (e := repeatedFinalSwapLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [repeatedFinalSwapLaw, xyzy, xzyy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Arbitrary adjacent nonempty blocks commute between fixed nonempty
prefix and suffix contexts. -/
theorem derivesInteriorSwap (a b c d : Word Nat) :
    Derives basis (((a ++ b) ++ c) ++ d) (((a ++ c) ++ b) ++ d) := by
  have step₁ :=
    derivesMiddleDuplication a (b ++ c) d
  have step₂ :=
    Derives.appendRight
      (Derives.prepend a (derivesRepeatedFinalSwap b c b)) d
  have step₃ :=
    Derives.appendRight
      (Derives.prepend a (Derives.symm (derivesSquareExpansion b c))) d
  have step₄ :=
    Derives.appendRight (derivesRepeatedFinalSwap a b c) d
  have step₅ :=
    Derives.symm (derivesMiddleDuplication (a ++ c) b d)
  exact Derives.trans
    (by simpa [Word.append_assoc] using step₁) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step₂) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step₃) <|
    Derives.trans
      (by simpa [Word.append_assoc] using step₄)
      (by simpa [Word.append_assoc] using step₅)

/-- If the terminal variable is repeated, switch the terminal marker while
keeping the first variable fixed. -/
theorem derivesTerminalSwitch (a oldFinal newFinal : Word Nat) :
    Derives basis
      (((a ++ oldFinal) ++ newFinal) ++ oldFinal)
      (((a ++ newFinal) ++ oldFinal) ++ newFinal) := by
  have step₁ := derivesRepeatedFinalSwap a oldFinal newFinal
  have step₂ :=
    derivesMiddleDuplication a newFinal (oldFinal ++ oldFinal)
  have step₃ :=
    Derives.prepend a <|
      Derives.symm (derivesSquareExpansion newFinal oldFinal)
  exact Derives.trans step₁ <|
    Derives.trans
      (by simpa [Word.append_assoc] using step₂)
      (by simpa [Word.append_assoc] using step₃)

private theorem derivesInteriorPermutation
    (initial final : Nat) {middle₁ middle₂ : List Nat}
    (hperm : middle₁.Perm middle₂) :
    Derives basis
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
        derivesInteriorSwap
          (Word.singleton initial)
          (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs final)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ initial) (ih₂ initial)

def middleReduce (middle : List Nat) : List Nat :=
  finalMarkerPrefixReduce middle

theorem middleReduce_mem (z : Nat) (middle : List Nat) :
    z ∈ middleReduce middle ↔ z ∈ middle :=
  finalMarkerPrefixReduce_mem z middle

theorem middleReduce_nodup (middle : List Nat) :
    (middleReduce middle).Nodup :=
  finalMarkerPrefixReduce_nodup middle

private theorem derivesDeleteLeadingInterior
    (initial x final : Nat) (middle : List Nat)
    (hx : x ∈ middle) :
    Derives basis
      (wordOfEndpoints initial (x :: middle) final)
      (wordOfEndpoints initial middle final) := by
  have expose : middle.Perm (x :: middle.erase x) :=
    List.perm_cons_erase hx
  have sourcePerm :
      (x :: middle).Perm (x :: x :: middle.erase x) :=
    List.Perm.cons x expose
  have contract :
      Derives basis
        (wordOfEndpoints initial (x :: x :: middle.erase x) final)
        (wordOfEndpoints initial (x :: middle.erase x) final) := by
    simpa [wordOfEndpoints_eq, Word.append_assoc] using
      Derives.symm <|
        derivesMiddleDuplication
          (Word.singleton initial) (Word.singleton x)
          (wordOfPrefixFinal (middle.erase x) final)
  exact Derives.trans
    (derivesInteriorPermutation initial final sourcePerm) <|
    Derives.trans contract <|
      derivesInteriorPermutation initial final expose.symm

theorem derivesNormalizeMiddle :
    ∀ (initial : Nat) (middle : List Nat) (final : Nat),
      Derives basis
        (wordOfEndpoints initial middle final)
        (wordOfEndpoints initial (middleReduce middle) final)
  | initial, [], final => Derives.refl _
  | initial, x :: xs, final => by
      have tailNormal := derivesNormalizeMiddle x xs final
      have prefixed :
          Derives basis
            (wordOfEndpoints initial (x :: xs) final)
            (wordOfEndpoints initial (x :: middleReduce xs) final) := by
        simpa [wordOfEndpoints_eq, Word.append_assoc] using
          Derives.prepend (Word.singleton initial) tailNormal
      by_cases hx : x ∈ middleReduce xs
      · have reduceEq :
            middleReduce (x :: xs) = middleReduce xs := by
          change
            finalMarkerPrefixReduce (x :: xs) =
              finalMarkerPrefixReduce xs
          change x ∈ finalMarkerPrefixReduce xs at hx
          simp [finalMarkerPrefixReduce, hx]
        rw [reduceEq]
        exact Derives.trans prefixed <|
          derivesDeleteLeadingInterior
            initial x final (middleReduce xs) hx
      · have reduceEq :
            middleReduce (x :: xs) = x :: middleReduce xs := by
          change
            finalMarkerPrefixReduce (x :: xs) =
              x :: finalMarkerPrefixReduce xs
          change x ∉ finalMarkerPrefixReduce xs at hx
          simp [finalMarkerPrefixReduce, hx]
        rw [reduceEq]
        exact prefixed

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
          (perm_of_nodup_mem_iff
            tailNodup erasedNodup tailMem)).trans targetPerm.symm

def saturatedMiddle
    (initial : Nat) (middle : List Nat) (final : Nat) : List Nat :=
  if initial = final then middleReduce (initial :: middle) else middle

theorem saturatedMiddle_nodup
    (initial final : Nat) {middle : List Nat}
    (middleNodup : middle.Nodup) :
    (saturatedMiddle initial middle final).Nodup := by
  by_cases endpoints : initial = final
  · simp [saturatedMiddle, endpoints, middleReduce_nodup]
  · simp [saturatedMiddle, endpoints, middleNodup]

theorem saturatedMiddle_mem
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    z ∈ saturatedMiddle initial middle final ↔
      z ∈ middle ∨ initial = final ∧ z = initial := by
  by_cases endpoints : initial = final
  · subst final
    simp [saturatedMiddle, middleReduce_mem, eq_comm, or_comm]
  · simp [saturatedMiddle, endpoints]

theorem derivesSaturate
    (initial : Nat) (middle : List Nat) (final : Nat)
    (middleNodup : middle.Nodup) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial
        (saturatedMiddle initial middle final) final) := by
  by_cases endpoints : initial = final
  · subst final
    by_cases present : initial ∈ middle
    · have targetPerm :
          middle.Perm (saturatedMiddle initial middle initial) := by
        apply perm_of_nodup_mem_iff
          middleNodup
          (saturatedMiddle_nodup initial initial middleNodup)
        intro z
        rw [saturatedMiddle_mem]
        constructor
        · exact Or.inl
        · rintro (hz | ⟨_, rfl⟩)
          · exact hz
          · exact present
      exact derivesInteriorPermutation initial initial targetPerm
    · cases middle with
      | nil =>
          simpa [saturatedMiddle, middleReduce,
            finalMarkerPrefixReduce, wordOfEndpoints_eq,
            Word.append_assoc] using
            derivesPowerExpansion (Word.singleton initial)
      | cons x xs =>
          let middleWord : Word Nat := ⟨x, xs⟩
          have expanded :
              Derives basis
                (wordOfEndpoints initial (x :: xs) initial)
                (wordOfEndpoints initial (initial :: x :: xs) initial) := by
            simpa [wordOfEndpoints, middleWord, Word.append,
              Word.singleton, Word.append_assoc] using
              derivesLeftEndpointExpansion
                (Word.singleton initial) middleWord
          have sourceNodup : (initial :: x :: xs).Nodup := by
            have tailNodup : (x :: xs).Nodup := middleNodup
            exact List.nodup_cons.mpr ⟨present, tailNodup⟩
          have targetPerm :
              (initial :: x :: xs).Perm
                (saturatedMiddle initial (x :: xs) initial) := by
            apply perm_of_nodup_mem_iff
              sourceNodup
              (saturatedMiddle_nodup
                initial initial middleNodup)
            intro z
            rw [saturatedMiddle_mem]
            simp [eq_comm, or_assoc, or_left_comm, or_comm]
          exact Derives.trans expanded <|
            derivesInteriorPermutation initial initial targetPerm
  · simp [saturatedMiddle, endpoints]
    exact Derives.refl _

def normalMiddle
    (initial : Nat) (middle : List Nat) (final : Nat) : List Nat :=
  saturatedMiddle initial (middleReduce middle) final

theorem normalMiddle_nodup
    (initial : Nat) (middle : List Nat) (final : Nat) :
    (normalMiddle initial middle final).Nodup :=
  saturatedMiddle_nodup initial final (middleReduce_nodup middle)

theorem normalMiddle_closed
    (initial : Nat) (middle : List Nat) (final : Nat) :
    initial = final → initial ∈ normalMiddle initial middle final := by
  intro endpoints
  apply
    (saturatedMiddle_mem
      initial initial (middleReduce middle) final).2
  exact Or.inr ⟨endpoints, rfl⟩

theorem derivesNormalEndpoints
    (initial : Nat) (middle : List Nat) (final : Nat) :
    Derives basis
      (wordOfEndpoints initial middle final)
      (wordOfEndpoints initial (normalMiddle initial middle final) final) :=
  Derives.trans
    (derivesNormalizeMiddle initial middle final)
    (derivesSaturate initial (middleReduce middle) final
      (middleReduce_nodup middle))

private theorem perm_two_to_end (a b : Nat) :
    ∀ middle : List Nat,
      (a :: b :: middle).Perm (middle ++ [a, b])
  | [] => List.Perm.refl _
  | x :: xs =>
      (List.Perm.cons a (List.Perm.swap x b xs)).trans <|
        (List.Perm.swap x a (b :: xs)).trans <|
          List.Perm.cons x (perm_two_to_end a b xs)

private theorem perm_swap_at_end (a b : Nat) :
    ∀ middle : List Nat,
      (middle ++ [a, b]).Perm (middle ++ [b, a])
  | [] => List.Perm.swap b a []
  | x :: xs => List.Perm.cons x (perm_swap_at_end a b xs)

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-- Change a repeated final variable while preserving the initial variable
and the interior support. -/
theorem derivesFinalSwitch
    (initial : Nat) (middle : List Nat) (oldFinal newFinal : Nat)
    (hold : oldFinal ∈ middle) (hnew : newFinal ∈ middle) :
    Derives basis
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
          simpa [remainder] using List.perm_cons_erase newInErase
    have arrange :
        middle.Perm (remainder ++ [oldFinal, newFinal]) :=
      arrangeFront.trans (perm_two_to_end oldFinal newFinal remainder)
    have switchAtEnd :
        Derives basis
          (wordOfEndpoints initial
            (remainder ++ [oldFinal, newFinal]) oldFinal)
          (wordOfEndpoints initial
            (remainder ++ [newFinal, oldFinal]) newFinal) := by
      simpa [wordOfEndpoints, wordOfCons, Word.append,
        Word.singleton, Word.append_assoc, List.append_assoc] using
        derivesTerminalSwitch
          (wordOfCons initial remainder)
          (Word.singleton oldFinal) (Word.singleton newFinal)
    have restore :
        (remainder ++ [newFinal, oldFinal]).Perm middle :=
      (perm_swap_at_end oldFinal newFinal remainder).symm.trans
        arrange.symm
    exact Derives.trans
      (derivesInteriorPermutation initial oldFinal arrange) <|
      Derives.trans switchAtEnd <|
        derivesInteriorPermutation initial newFinal restore

private def headSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 2

private theorem headFoldZero (z : Nat) :
    ∀ xs : List Nat,
      xs.foldl
        (fun current x =>
          firstRepeatedMarkerFourMul current (headSeparator z x))
        (0 : Fin 4) = 0
  | [] => rfl
  | x :: xs => by
      simp only [List.foldl_cons]
      rw [show firstRepeatedMarkerFourMul 0 (headSeparator z x) =
          (0 : Fin 4) by
        simp [firstRepeatedMarkerFourMul]]
      exact headFoldZero z xs

private theorem headFoldTwo (z : Nat) :
    ∀ xs : List Nat,
      xs.foldl
        (fun current x =>
          firstRepeatedMarkerFourMul current (headSeparator z x))
        (2 : Fin 4) = 2
  | [] => rfl
  | x :: xs => by
      simp only [List.foldl_cons]
      rw [show firstRepeatedMarkerFourMul 2 (headSeparator z x) =
          (2 : Fin 4) by
        simp [firstRepeatedMarkerFourMul]]
      exact headFoldTwo z xs

theorem eval_headSeparator (z : Nat) (word : Word Nat) :
    firstRepeatedMarkerFour.semigroup.eval (headSeparator z) word =
      if word.head = z then
        if word.tail = [] then (1 : Fin 4) else 0
      else 2 := by
  cases word with
  | mk head tail =>
      by_cases hz : head = z
      · subst head
        cases tail with
        | nil =>
            simp [Semigroup.eval, headSeparator]
        | cons x xs =>
            simp only [Word.head, Word.tail, if_pos,
              List.cons_ne_nil, if_false]
            change
              xs.foldl
                (fun current y =>
                  firstRepeatedMarkerFourMul current
                    (headSeparator z y))
                (firstRepeatedMarkerFourMul
                  (headSeparator z z) (headSeparator z x)) = 0
            rw [show headSeparator z z = (1 : Fin 4) by
              simp [headSeparator]]
            rw [show
                firstRepeatedMarkerFourMul 1 (headSeparator z x) =
                  (0 : Fin 4) by
              by_cases hx : x = z <;>
                simp [headSeparator, firstRepeatedMarkerFourMul, hx]]
            exact headFoldZero z xs
      · simp only [Word.head, Word.tail, if_neg hz]
        change
          tail.foldl
            (fun current x =>
              firstRepeatedMarkerFourMul current (headSeparator z x))
            (headSeparator z head) = 2
        rw [show headSeparator z head = (2 : Fin 4) by
          simp [headSeparator, hz]]
        exact headFoldTwo z tail

theorem valid_head_eq (e : Identity Nat)
    (valid : e.SatisfiedBy firstRepeatedMarkerFour.semigroup) :
    e.lhs.head = e.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  have evaluated := valid (headSeparator e.lhs.head)
  rw [eval_headSeparator, eval_headSeparator] at evaluated
  by_cases tailNil : e.lhs.tail = [] <;>
    simp [tailNil, Ne.symm headsNe] at evaluated

theorem valid_tail_nil_iff (e : Identity Nat)
    (valid : e.SatisfiedBy firstRepeatedMarkerFour.semigroup) :
    e.lhs.tail = [] ↔ e.rhs.tail = [] := by
  have heads := valid_head_eq e valid
  have evaluated := valid (headSeparator e.lhs.head)
  rw [eval_headSeparator, eval_headSeparator] at evaluated
  simp only [if_pos rfl, if_pos heads.symm] at evaluated
  by_cases lhsNil : e.lhs.tail = [] <;>
    by_cases rhsNil : e.rhs.tail = [] <;>
      simp [lhsNil, rhsNil] at evaluated ⊢

private def uniqueInitialSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 3

theorem eval_uniqueInitialSeparator
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    firstRepeatedMarkerFour.semigroup.eval
        (uniqueInitialSeparator z)
        (wordOfEndpoints initial middle final) =
      if initial = z then
        if z ∈ middle ∨ final = z then (0 : Fin 4) else 1
      else
        if z ∈ middle ∨ final = z then (0 : Fin 4) else 3 := by
  induction middle generalizing initial with
  | nil =>
      rw [wordOfEndpoints_nil, Semigroup.eval_append,
        Semigroup.eval_singleton, Semigroup.eval_singleton]
      by_cases hi : initial = z <;>
        by_cases hf : final = z <;>
          simp_all [uniqueInitialSeparator, firstRepeatedMarkerFour,
            FiniteTable.semigroup, firstRepeatedMarkerFourMul, eq_comm]
  | cons x xs ih =>
      rw [wordOfEndpoints_cons, Semigroup.eval_append,
        Semigroup.eval_singleton, ih]
      change
        firstRepeatedMarkerFourMul
            (uniqueInitialSeparator z initial)
            (if x = z then
              if z ∈ xs ∨ final = z then (0 : Fin 4) else 1
            else
              if z ∈ xs ∨ final = z then (0 : Fin 4) else 3) =
          if initial = z then
            if z ∈ x :: xs ∨ final = z
            then (0 : Fin 4) else 1
          else
            if z ∈ x :: xs ∨ final = z
            then (0 : Fin 4) else 3
      by_cases hi : initial = z <;>
        by_cases hx : x = z <;>
          by_cases ht : z ∈ xs ∨ final = z <;>
            simp_all [uniqueInitialSeparator,
              firstRepeatedMarkerFourMul, eq_comm]

theorem eval_uniqueInitialSeparator_eq_three_iff
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    firstRepeatedMarkerFour.semigroup.eval
        (uniqueInitialSeparator z)
        (wordOfEndpoints initial middle final) = (3 : Fin 4) ↔
      z ∉ initial :: middle ∧ final ≠ z := by
  rw [eval_uniqueInitialSeparator]
  by_cases hi : initial = z
  · subst initial
    by_cases hm : z ∈ middle <;>
      by_cases hf : final = z <;> simp [hm, hf]
  · have hzi : z ≠ initial := Ne.symm hi
    by_cases hm : z ∈ middle <;>
      by_cases hf : final = z <;>
        simp [hi, hzi, hm, hf]

theorem eval_uniqueInitialSeparator_eq_one_iff
    (z initial : Nat) (middle : List Nat) (final : Nat) :
    firstRepeatedMarkerFour.semigroup.eval
        (uniqueInitialSeparator z)
        (wordOfEndpoints initial middle final) = (1 : Fin 4) ↔
      initial = z ∧ z ∉ middle ∧ final ≠ z := by
  rw [eval_uniqueInitialSeparator]
  by_cases hi : initial = z <;>
    by_cases hm : z ∈ middle <;>
      by_cases hf : final = z <;> simp [hi, hm, hf]

private def finalSeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 1 else 2

private theorem eval_finalSeparator
    (z : Nat) (pref : List Nat) (final : Nat) :
    finalMarkerThree.semigroup.eval (finalSeparator z)
        (wordOfPrefixFinal pref final) =
      if z ∈ pref then (0 : Fin 3)
      else if final = z then (1 : Fin 3) else 2 := by
  induction pref with
  | nil =>
      simp [wordOfPrefixFinal, finalSeparator]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append, ih]
      by_cases hx : x = z
      · subst x
        simp [finalSeparator, finalMarkerThree,
          FiniteTable.semigroup, finalMarkerThreeMul]
      · simp [finalSeparator, finalMarkerThree,
          FiniteTable.semigroup, finalMarkerThreeMul, hx, Ne.symm hx]

private theorem simpleFinal_iff_of_valid
    (initial₁ : Nat) (middle₁ : List Nat) (final₁ : Nat)
    (initial₂ : Nat) (middle₂ : List Nat) (final₂ : Nat)
    (valid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          finalMarkerThree.semigroup) :
    ∀ z,
      (final₁ = z ∧ z ∉ initial₁ :: middle₁) ↔
        (final₂ = z ∧ z ∉ initial₂ :: middle₂) := by
  intro z
  have evaluated := valid (finalSeparator z)
  rw [wordOfEndpoints_eq, wordOfEndpoints_eq,
    ← wordOfPrefixFinal_cons, ← wordOfPrefixFinal_cons,
    eval_finalSeparator, eval_finalSeparator] at evaluated
  constructor
  · intro simple₁
    apply Decidable.byContradiction
    intro notSimple₂
    rw [if_neg simple₁.2, if_pos simple₁.1] at evaluated
    by_cases present₂ : z ∈ initial₂ :: middle₂
    · rw [if_pos present₂] at evaluated
      exact (by decide : (1 : Fin 3) ≠ 0) evaluated
    · have finalNe₂ : final₂ ≠ z := by
        intro finalEq
        exact notSimple₂ ⟨finalEq, present₂⟩
      rw [if_neg present₂, if_neg finalNe₂] at evaluated
      exact (by decide : (1 : Fin 3) ≠ 2) evaluated
  · intro simple₂
    apply Decidable.byContradiction
    intro notSimple₁
    rw [if_neg simple₂.2, if_pos simple₂.1] at evaluated
    by_cases present₁ : z ∈ initial₁ :: middle₁
    · rw [if_pos present₁] at evaluated
      exact (by decide : (0 : Fin 3) ≠ 1) evaluated
    · have finalNe₁ : final₁ ≠ z := by
        intro finalEq
        exact notSimple₁ ⟨finalEq, present₁⟩
      rw [if_neg present₁, if_neg finalNe₁] at evaluated
      exact (by decide : (2 : Fin 3) ≠ 1) evaluated

private theorem middle_mem_iff_semantic
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

private theorem normalizedDerives
    (initial₁ initial₂ : Nat)
    (middle₁ middle₂ : List Nat)
    (final₁ final₂ : Nat)
    (nodup₁ : middle₁.Nodup) (nodup₂ : middle₂.Nodup)
    (closed₁ : initial₁ = final₁ → initial₁ ∈ middle₁)
    (closed₂ : initial₂ = final₂ → initial₂ ∈ middle₂)
    (firstValid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          firstRepeatedMarkerFour.semigroup)
    (finalValid :
      (Identity.mk
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₂ middle₂ final₂)).SatisfiedBy
          finalMarkerThree.semigroup) :
    Derives basis
      (wordOfEndpoints initial₁ middle₁ final₁)
      (wordOfEndpoints initial₂ middle₂ final₂) := by
  let normalIdentity : Identity Nat :=
    ⟨wordOfEndpoints initial₁ middle₁ final₁,
      wordOfEndpoints initial₂ middle₂ final₂⟩
  have initials :
      initial₁ = initial₂ := by
    exact valid_head_eq normalIdentity firstValid
  subst initial₂
  have supportIff :
      ∀ z,
        (z ∈ initial₁ :: middle₁ ∨ final₁ = z) ↔
          (z ∈ initial₁ :: middle₂ ∨ final₂ = z) := by
    intro z
    have absentIff :
        (z ∉ initial₁ :: middle₁ ∧ final₁ ≠ z) ↔
          (z ∉ initial₁ :: middle₂ ∧ final₂ ≠ z) := by
      constructor
      · intro h
        apply
          (eval_uniqueInitialSeparator_eq_three_iff
            z initial₁ middle₂ final₂).1
        exact
          (firstValid (uniqueInitialSeparator z)).symm.trans <|
            (eval_uniqueInitialSeparator_eq_three_iff
              z initial₁ middle₁ final₁).2 h
      · intro h
        apply
          (eval_uniqueInitialSeparator_eq_three_iff
            z initial₁ middle₁ final₁).1
        exact
          (firstValid (uniqueInitialSeparator z)).trans <|
            (eval_uniqueInitialSeparator_eq_three_iff
              z initial₁ middle₂ final₂).2 h
    constructor
    · intro h
      apply Decidable.byContradiction
      intro hn
      have absent₂ :
          z ∉ initial₁ :: middle₂ ∧ final₂ ≠ z := by
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
        (z ∈ initial₁ :: middle₂ ∨ final₂ = z)) h
  have initialIff :
      ∀ z,
        (initial₁ = z ∧ z ∉ middle₁ ∧ final₁ ≠ z) ↔
          (initial₁ = z ∧ z ∉ middle₂ ∧ final₂ ≠ z) := by
    intro z
    constructor
    · intro h
      apply
        (eval_uniqueInitialSeparator_eq_one_iff
          z initial₁ middle₂ final₂).1
      exact
        (firstValid (uniqueInitialSeparator z)).symm.trans <|
          (eval_uniqueInitialSeparator_eq_one_iff
            z initial₁ middle₁ final₁).2 h
    · intro h
      apply
        (eval_uniqueInitialSeparator_eq_one_iff
          z initial₁ middle₁ final₁).1
      exact
        (firstValid (uniqueInitialSeparator z)).trans <|
          (eval_uniqueInitialSeparator_eq_one_iff
            z initial₁ middle₂ final₂).2 h
  have finalIff :=
    simpleFinal_iff_of_valid
      initial₁ middle₁ final₁ initial₁ middle₂ final₂ finalValid
  have middleMem : ∀ z, z ∈ middle₁ ↔ z ∈ middle₂ := by
    intro z
    rw [middle_mem_iff_semantic
      z initial₁ middle₁ final₁ closed₁]
    rw [middle_mem_iff_semantic
      z initial₁ middle₂ final₂ closed₂]
    exact and_congr (supportIff z) <|
      and_congr (not_congr (initialIff z))
        (not_congr (finalIff z))
  have finalDerivation :
      Derives basis
        (wordOfEndpoints initial₁ middle₁ final₁)
        (wordOfEndpoints initial₁ middle₁ final₂) := by
    by_cases simple₁ : final₁ ∉ middle₁
    · have initialNe : initial₁ ≠ final₁ := by
        intro h
        exact simple₁ <| by simpa [h] using closed₁ h
      have matched :=
        (finalIff final₁).mp
          ⟨rfl, by simpa [Ne.symm initialNe, simple₁]⟩
      simpa [matched.1] using
        (Derives.refl
          (wordOfEndpoints initial₁ middle₁ final₁) :
            Derives basis
              (wordOfEndpoints initial₁ middle₁ final₁)
              (wordOfEndpoints initial₁ middle₁ final₁))
    · have repeated₁ : final₁ ∈ middle₁ :=
        Decidable.byContradiction simple₁
      have repeated₂ : final₂ ∈ middle₂ := by
        apply Decidable.byContradiction
        intro absent₂
        have initialNe₂ : initial₁ ≠ final₂ := by
          intro h
          exact absent₂ <| by simpa [h] using closed₂ h
        have simpleOnLeft :=
          (finalIff final₂).mpr
            ⟨rfl, by simpa [Ne.symm initialNe₂, absent₂]⟩
        apply simpleOnLeft.2
        exact List.Mem.tail initial₁ <| by
          simpa [simpleOnLeft.1] using repeated₁
      exact derivesFinalSwitch
        initial₁ middle₁ final₁ final₂ repeated₁
        ((middleMem final₂).2 repeated₂)
  have middlePerm : middle₁.Perm middle₂ :=
    perm_of_nodup_mem_iff nodup₁ nodup₂ middleMem
  exact Derives.trans finalDerivation <|
    derivesInteriorPermutation initial₁ final₂ middlePerm

/-- Unrestricted completeness for every finite table whose identities factor
through the first/repeated-initial and unique-final marker semantics. -/
theorem basis_complete_of_factors
    (T : FiniteTable)
    (models : Models T.semigroup basis)
    (toFirstRepeated :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.SatisfiedBy firstRepeatedMarkerFour.semigroup)
    (toFinalMarker :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.SatisfiedBy finalMarkerThree.semigroup) :
    BasisFor T.semigroup basis := by
  refine ⟨models, ?_⟩
  intro e valid
  have firstValid := toFirstRepeated e valid
  have finalValid := toFinalMarker e valid
  have heads := valid_head_eq e firstValid
  have singletonIff := valid_tail_nil_iff e firstValid
  rcases e with
    ⟨⟨lhsHead, lhsTail⟩, ⟨rhsHead, rhsTail⟩⟩
  change lhsHead = rhsHead at heads
  change lhsTail = [] ↔ rhsTail = [] at singletonIff
  subst rhsHead
  cases lhsTail with
  | nil =>
      have rhsNil : rhsTail = [] := singletonIff.mp rfl
      subst rhsTail
      exact Derives.refl _
  | cons lhsNext lhsRest =>
      cases rhsTail with
      | nil =>
          have lhsNil : lhsNext :: lhsRest = [] :=
            singletonIff.mpr rfl
          simp at lhsNil
      | cons rhsNext rhsRest =>
          let lhsSuffix : Word Nat := ⟨lhsNext, lhsRest⟩
          let rhsSuffix : Word Nat := ⟨rhsNext, rhsRest⟩
          let lhsSplit := splitPrefixFinal lhsSuffix
          let rhsSplit := splitPrefixFinal rhsSuffix
          let lhsMiddle :=
            normalMiddle lhsHead lhsSplit.1 lhsSplit.2
          let rhsMiddle :=
            normalMiddle lhsHead rhsSplit.1 rhsSplit.2
          have lhsReconstruct :
              wordOfEndpoints lhsHead lhsSplit.1 lhsSplit.2 =
                Word.mk lhsHead (lhsNext :: lhsRest) := by
            rw [wordOfEndpoints_eq]
            simp only [lhsSplit]
            rw [wordOfPrefixFinal_split lhsSuffix]
            rfl
          have rhsReconstruct :
              wordOfEndpoints lhsHead rhsSplit.1 rhsSplit.2 =
                Word.mk lhsHead (rhsNext :: rhsRest) := by
            rw [wordOfEndpoints_eq]
            simp only [rhsSplit]
            rw [wordOfPrefixFinal_split rhsSuffix]
            rfl
          have lhsNormal :
              Derives basis
                (Word.mk lhsHead (lhsNext :: lhsRest))
                (wordOfEndpoints lhsHead lhsMiddle lhsSplit.2) := by
            rw [← lhsReconstruct]
            simpa [lhsMiddle] using
              derivesNormalEndpoints
                lhsHead lhsSplit.1 lhsSplit.2
          have rhsNormal :
              Derives basis
                (Word.mk lhsHead (rhsNext :: rhsRest))
                (wordOfEndpoints lhsHead rhsMiddle rhsSplit.2) := by
            rw [← rhsReconstruct]
            simpa [rhsMiddle] using
              derivesNormalEndpoints
                lhsHead rhsSplit.1 rhsSplit.2
          let normalIdentity : Identity Nat :=
            ⟨wordOfEndpoints lhsHead lhsMiddle lhsSplit.2,
              wordOfEndpoints lhsHead rhsMiddle rhsSplit.2⟩
          have normalFirstValid :
              normalIdentity.SatisfiedBy
                firstRepeatedMarkerFour.semigroup := by
            intro valuation
            have lhsSound :=
              lhsNormal.sound
                basis_models_firstRepeatedMarkerFour valuation
            have rhsSound :=
              rhsNormal.sound
                basis_models_firstRepeatedMarkerFour valuation
            exact lhsSound.symm.trans <|
              (firstValid valuation).trans rhsSound
          have normalFinalValid :
              normalIdentity.SatisfiedBy finalMarkerThree.semigroup := by
            intro valuation
            have lhsSound :=
              lhsNormal.sound basis_models_finalMarkerThree valuation
            have rhsSound :=
              rhsNormal.sound basis_models_finalMarkerThree valuation
            exact lhsSound.symm.trans <|
              (finalValid valuation).trans rhsSound
          have normalizedDerivation :=
            normalizedDerives
              lhsHead lhsHead lhsMiddle rhsMiddle
              lhsSplit.2 rhsSplit.2
              (by
                simpa [lhsMiddle] using
                  normalMiddle_nodup
                    lhsHead lhsSplit.1 lhsSplit.2)
              (by
                simpa [rhsMiddle] using
                  normalMiddle_nodup
                    lhsHead rhsSplit.1 rhsSplit.2)
              (by
                simpa [lhsMiddle] using
                  normalMiddle_closed
                    lhsHead lhsSplit.1 lhsSplit.2)
              (by
                simpa [rhsMiddle] using
                  normalMiddle_closed
                    lhsHead rhsSplit.1 rhsSplit.2)
              normalFirstValid normalFinalValid
          exact Derives.trans lhsNormal <|
            Derives.trans normalizedDerivation (Derives.symm rhsNormal)

end SemigroupBasis.CoRoots.S5_342
