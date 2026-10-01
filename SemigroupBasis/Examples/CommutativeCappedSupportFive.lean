import SemigroupBasis.Examples.CommutativeExponentFour
import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The zero-based multiplication table of the stored representative
`S5_201`:
`[[1,1,1,1,1],[1,1,1,1,1],[1,1,1,1,3],
  [1,1,1,2,1],[1,1,3,1,5]]`. -/
def commutativeCappedSupportFiveMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then 0
  else if a = 1 then 0
  else if a = 2 then
    if b = 4 then 2 else 0
  else if a = 3 then
    if b = 3 then 1 else 0
  else
    if b = 2 then 2 else if b = 4 then 4 else 0

/-- The five-element commutative semigroup `S5_201`. -/
def commutativeCappedSupportFive : FiniteTable where
  order := 5
  mul := commutativeCappedSupportFiveMul
  assoc := by decide

def cappedSupportXY : Word Nat := ⟨0, [1]⟩
def cappedSupportYX : Word Nat := ⟨1, [0]⟩
def cappedSupportXXX : Word Nat := ⟨0, [0, 0]⟩
def cappedSupportXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def cappedSupportXXY : Word Nat := ⟨0, [0, 1]⟩
def cappedSupportXXXY : Word Nat := ⟨0, [0, 0, 1]⟩

def cappedSupportCommutativityLaw : Identity Nat :=
  ⟨cappedSupportXY, cappedSupportYX⟩

def cappedSupportUnaryLaw : Identity Nat :=
  ⟨cappedSupportXXX, cappedSupportXXXX⟩

def cappedSupportContextLaw : Identity Nat :=
  ⟨cappedSupportXXY, cappedSupportXXXY⟩

/-- The exact basis `xy = yx`, `xxx = xxxx`, `xxy = xxxy`. -/
def commutativeCappedSupportFiveBasis : List (Identity Nat) :=
  [cappedSupportCommutativityLaw, cappedSupportUnaryLaw,
    cappedSupportContextLaw]

private theorem exponentFourAxiomsDerive
    (e : Identity Nat) (he : e ∈ commutativeExponentFourBasis) :
    Derives commutativeCappedSupportFiveBasis e.lhs e.rhs := by
  simp only [commutativeExponentFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact Derives.fromBasis (e := cappedSupportCommutativityLaw) <| by
      exact List.Mem.head _
  · exact Derives.fromBasis (e := cappedSupportUnaryLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)

/-- Every derivation from the commutative exponent-three cap transports to
the first two laws of the `S5_201` basis. -/
theorem cappedSupportDerivesExponentFour {u v : Word Nat}
    (h : Derives commutativeExponentFourBasis u v) :
    Derives commutativeCappedSupportFiveBasis u v :=
  h.transport exponentFourAxiomsDerive

theorem cappedSupportDerivesCommutativity (u v : Word Nat) :
    Derives commutativeCappedSupportFiveBasis (u ++ v) (v ++ u) :=
  cappedSupportDerivesExponentFour
    (exponentFourDerivesCommutativity u v)

theorem cappedSupportDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativeCappedSupportFiveBasis u v :=
  cappedSupportDerivesExponentFour
    (exponentFourDerivesPermutation u v h)

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

/-- The contextual law contracts or expands a third copy of any nonempty
word while a fixed nonempty marker remains present. -/
theorem cappedSupportDerivesContextTriple
    (marker u : Word Nat) :
    Derives commutativeCappedSupportFiveBasis
      (marker ++ (u ++ u)) (marker ++ ((u ++ u) ++ u)) := by
  have hbase :
      Derives commutativeCappedSupportFiveBasis
        cappedSupportXXY cappedSupportXXXY :=
    Derives.fromBasis (e := cappedSupportContextLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have expanded :=
    Derives.subst hbase (instantiateTwoWords u marker)
  have enter :=
    cappedSupportDerivesCommutativity marker (u ++ u)
  have exit :=
    cappedSupportDerivesCommutativity ((u ++ u) ++ u) marker
  exact Derives.trans enter <|
    Derives.trans
      (by
        simpa [cappedSupportContextLaw, cappedSupportXXY,
          cappedSupportXXXY, instantiateTwoWords, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using expanded)
      (by simpa [Word.append_assoc] using exit)

private theorem bind_append
    (u v : Word Nat) (σ : Nat → Word Nat) :
    (u ++ v).bind σ = u.bind σ ++ v.bind σ := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (w : Word Nat) (τ σ : Nat → Word Nat) :
    (w.bind τ).bind σ =
      w.bind (fun x => (τ x).bind σ) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (w : Word Nat) :
    w.bind Word.singleton = w := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay a derivation from `xx = xxx`, `xy = yx` after one fixed
nonempty marker. The marker supplies the residual `y` in `xxy = xxxy`. -/
theorem cappedSupportLiftExponentThree
    {u v : Word Nat}
    (h : Derives commutativeExponentThreeBasis u v)
    (marker : Word Nat) (σ : Nat → Word Nat) :
    Derives commutativeCappedSupportFiveBasis
      (marker ++ u.bind σ) (marker ++ v.bind σ) := by
  induction h generalizing marker σ with
  | fromBasis hmem =>
      simp only [commutativeExponentThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · simpa [exponentThreeLaw, exponentXX, exponentXXX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          cappedSupportDerivesContextTriple marker (σ 0)
      · have commute :=
          cappedSupportDerivesCommutativity (σ 0) (σ 1)
        simpa [exponentCommutativityLaw, exponentXY, exponentYX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend marker commute
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih marker σ)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ marker σ) (ih₂ marker σ)
  | prepend p _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (marker ++ p.bind σ) σ
  | appendRight _ q ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (ih marker σ) (q.bind σ)
  | subst _ τ ih =>
      simpa [bind_bind] using
        ih marker (fun x => (τ x).bind σ)

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private def frontedWord (z : Nat) (w : Word Nat) : Word Nat :=
  wordOfCons z (w.toList.erase z)

private def markerReduce (z : Nat) (w : Word Nat) : Word Nat :=
  wordOfCons z (exponentReduce (w.toList.erase z))

private def doubleMarkerReduce
    (a b : Nat) (w : Word Nat) : Word Nat :=
  markerReduce b (markerReduce a w)

private theorem word_perm_frontedWord
    (z : Nat) (w : Word Nat) (present : z ∈ w.toList) :
    w.toList.Perm (frontedWord z w).toList := by
  simpa [frontedWord, wordOfCons, Word.toList] using
    List.perm_cons_erase present

private theorem exponentReduce_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    exponentReduce (x :: xs) ≠ [] := by
  intro hempty
  have hcount := count_exponentReduce x (x :: xs)
  rw [hempty] at hcount
  simp at hcount
  omega

/-- Move a supported marker to the front and cap every multiplicity in the
remaining word at two. -/
theorem cappedSupportDerivesMarkerReduce
    (z : Nat) (w : Word Nat)
    (present : z ∈ w.toList)
    (other : ∃ y, y ∈ w.toList ∧ y ≠ z) :
    Derives commutativeCappedSupportFiveBasis
      w (markerReduce z w) := by
  obtain ⟨y, hy, hyz⟩ := other
  have hyErase : y ∈ w.toList.erase z :=
    (List.mem_erase_of_ne hyz).mpr hy
  have arrange :=
    cappedSupportDerivesPermutation
      w (frontedWord z w)
      (word_perm_frontedWord z w present)
  cases he : w.toList.erase z with
  | nil =>
      rw [he] at hyErase
      simp at hyErase
  | cons r rs =>
      let rest : Word Nat := wordOfCons r rs
      have oldNormal := exponentDerivesNormal rest
      cases hn : exponentReduce rest.toList with
      | nil =>
          exact False.elim <| exponentReduce_cons_ne_nil r rs <| by
            simpa [rest, wordOfCons, Word.toList] using hn
      | cons q qs =>
          rw [hn] at oldNormal
          change
            Derives commutativeExponentThreeBasis
              rest (wordOfCons q qs) at oldNormal
          have lifted :=
            cappedSupportLiftExponentThree oldNormal
              (Word.singleton z) Word.singleton
          rw [bind_singleton, bind_singleton] at lifted
          change
            Derives commutativeCappedSupportFiveBasis
              (wordOfCons z (r :: rs))
              (wordOfCons z (q :: qs)) at lifted
          have hn' : exponentReduce (r :: rs) = q :: qs := by
            simpa [rest, wordOfCons, Word.toList] using hn
          exact Derives.trans arrange <| by
            change
              Derives commutativeCappedSupportFiveBasis
                (wordOfCons z (w.toList.erase z))
                (wordOfCons z
                  (exponentReduce (w.toList.erase z)))
            rw [he, hn']
            exact lifted

theorem count_markerReduce
    (t z : Nat) (w : Word Nat) (_present : z ∈ w.toList) :
    (markerReduce z w).toList.count t =
      if t = z then
        1 + min (w.toList.count t - 1) 2
      else
        min (w.toList.count t) 2 := by
  by_cases htz : t = z
  · subst t
    rw [show (markerReduce z w).toList =
        z :: exponentReduce (w.toList.erase z) by
      rfl]
    rw [List.count_cons_self, count_exponentReduce,
      List.count_erase_self]
    simp
    omega
  · rw [show (markerReduce z w).toList =
        z :: exponentReduce (w.toList.erase z) by
      rfl]
    rw [List.count_cons_of_ne (Ne.symm htz),
      count_exponentReduce, List.count_erase_of_ne htz]
    simp [htz]

private theorem markerReduce_mem_of_ne
    (a b : Nat) (w : Word Nat)
    (ha : a ∈ w.toList) (hb : b ∈ w.toList)
    (hba : b ≠ a) :
    b ∈ (markerReduce a w).toList := by
  rw [← List.count_pos_iff, count_markerReduce b a w ha]
  simp only [if_neg hba]
  have hpositive : 0 < w.toList.count b :=
    List.count_pos_iff.mpr hb
  omega

/-- After two distinct supported markers have taken turns as the fixed
context, every coordinate is capped at two. -/
theorem count_doubleMarkerReduce
    (t a b : Nat) (w : Word Nat)
    (ha : a ∈ w.toList) (hb : b ∈ w.toList)
    (hab : a ≠ b) :
    (doubleMarkerReduce a b w).toList.count t =
      min (w.toList.count t) 2 := by
  let first := markerReduce a w
  have hbFirst : b ∈ first.toList :=
    markerReduce_mem_of_ne a b w ha hb (Ne.symm hab)
  by_cases htb : t = b
  · subst t
    rw [doubleMarkerReduce, count_markerReduce b b first hbFirst,
      if_pos rfl, count_markerReduce b a w ha,
      if_neg (Ne.symm hab)]
    have hpositive : 0 < w.toList.count b :=
      List.count_pos_iff.mpr hb
    omega
  · rw [doubleMarkerReduce, count_markerReduce t b first hbFirst,
      if_neg htb]
    by_cases hta : t = a
    · subst t
      rw [count_markerReduce a a w ha, if_pos rfl]
      have hpositive : 0 < w.toList.count a :=
        List.count_pos_iff.mpr ha
      omega
    · rw [count_markerReduce t a w ha, if_neg hta]
      omega

theorem cappedSupportDerivesDoubleMarkerReduce
    (a b : Nat) (w : Word Nat)
    (ha : a ∈ w.toList) (hb : b ∈ w.toList)
    (hab : a ≠ b) :
    Derives commutativeCappedSupportFiveBasis
      w (doubleMarkerReduce a b w) := by
  have first :=
    cappedSupportDerivesMarkerReduce a w ha ⟨b, hb, Ne.symm hab⟩
  have hbFirst : b ∈ (markerReduce a w).toList :=
    markerReduce_mem_of_ne a b w ha hb (Ne.symm hab)
  have haFirst : a ∈ (markerReduce a w).toList := by
    simp [markerReduce, wordOfCons, Word.toList]
  have second :=
    cappedSupportDerivesMarkerReduce b (markerReduce a w)
      hbFirst ⟨a, haFirst, hab⟩
  exact Derives.trans first second

private theorem cappedSupportFiveMul_commutative (a b : Fin 5) :
    commutativeCappedSupportFiveMul a b =
      commutativeCappedSupportFiveMul b a := by
  decide +revert

private theorem cappedSupportFiveMul_unary (a : Fin 5) :
    commutativeCappedSupportFiveMul
        (commutativeCappedSupportFiveMul a a) a =
      commutativeCappedSupportFiveMul
        (commutativeCappedSupportFiveMul
          (commutativeCappedSupportFiveMul a a) a) a := by
  decide +revert

private theorem cappedSupportFiveMul_context (a b : Fin 5) :
    commutativeCappedSupportFiveMul
        (commutativeCappedSupportFiveMul a a) b =
      commutativeCappedSupportFiveMul
        (commutativeCappedSupportFiveMul
          (commutativeCappedSupportFiveMul a a) a) b := by
  decide +revert

theorem commutativeCappedSupportFiveBasis_models :
    Models commutativeCappedSupportFive.semigroup
      commutativeCappedSupportFiveBasis := by
  intro e he
  simp only [commutativeCappedSupportFiveBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    exact cappedSupportFiveMul_commutative
      (valuation 0) (valuation 1)
  · intro valuation
    exact cappedSupportFiveMul_unary (valuation 0)
  · intro valuation
    exact cappedSupportFiveMul_context
      (valuation 0) (valuation 1)

private def coordinateSeparator (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then 2 else 4

private def coordinateState (n : Nat) : Fin 5 :=
  ⟨2 * (2 - min n 2), by omega⟩

private theorem coordinateMul_target (n : Nat) :
    commutativeCappedSupportFiveMul (coordinateState n) 2 =
      coordinateState (n + 1) := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
          apply Fin.ext
          simp [coordinateState, commutativeCappedSupportFiveMul]

private theorem coordinateMul_other (n : Nat) :
    commutativeCappedSupportFiveMul (coordinateState n) 4 =
      coordinateState n := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
          apply Fin.ext
          simp [coordinateState, commutativeCappedSupportFiveMul]

private theorem coordinateFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          commutativeCappedSupportFiveMul current
            (coordinateSeparator z x))
        (coordinateState acc) =
      coordinateState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show coordinateSeparator z z = (2 : Fin 5) by
          simp [coordinateSeparator]]
        rw [coordinateMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show coordinateSeparator z x = (4 : Fin 5) by
          simp [coordinateSeparator, hx]]
        rw [coordinateMul_other, ih]

private theorem cappedSupportEval_coordinateSeparator
    (z : Nat) (w : Word Nat) :
    commutativeCappedSupportFive.semigroup.eval
        (coordinateSeparator z) w =
      coordinateState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              commutativeCappedSupportFiveMul current
                (coordinateSeparator z x))
            (coordinateSeparator z head) =
          coordinateState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show coordinateSeparator z z = coordinateState 1 by
          apply Fin.ext
          simp [coordinateSeparator, coordinateState]]
        rw [coordinateFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show coordinateSeparator z head = coordinateState 0 by
          apply Fin.ext
          simp [coordinateSeparator, coordinateState, hhead]]
        rw [coordinateFold]
        congr 1
        omega

theorem cappedSupportValid_cappedCountTwo
    (e : Identity Nat)
    (valid : e.SatisfiedBy commutativeCappedSupportFive.semigroup) :
    ∀ z, min (e.lhs.toList.count z) 2 =
      min (e.rhs.toList.count z) 2 := by
  intro z
  have evaluated := valid (coordinateSeparator z)
  rw [cappedSupportEval_coordinateSeparator,
    cappedSupportEval_coordinateSeparator] at evaluated
  have values := Fin.mk.inj evaluated
  change
    2 * (2 - min (e.lhs.toList.count z) 2) =
      2 * (2 - min (e.rhs.toList.count z) 2) at values
  have hl : min (e.lhs.toList.count z) 2 ≤ 2 :=
    Nat.min_le_right _ _
  have hr : min (e.rhs.toList.count z) 2 ≤ 2 :=
    Nat.min_le_right _ _
  omega

theorem cappedSupportValid_support
    (e : Identity Nat)
    (valid : e.SatisfiedBy commutativeCappedSupportFive.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  have capped := cappedSupportValid_cappedCountTwo e valid
  intro z
  constructor
  · intro hz
    have hpositive : 0 < e.lhs.toList.count z :=
      List.count_pos_iff.mpr hz
    have rhsPositive : 0 < e.rhs.toList.count z := by
      have := capped z
      omega
    exact List.count_pos_iff.mp rhsPositive
  · intro hz
    have hpositive : 0 < e.rhs.toList.count z :=
      List.count_pos_iff.mpr hz
    have lhsPositive : 0 < e.lhs.toList.count z := by
      have := capped z
      omega
    exact List.count_pos_iff.mp lhsPositive

private def constantThree : Nat → Fin 5 := fun _ => 3

private def unaryLengthState (n : Nat) : Fin 5 :=
  if n = 1 then 3 else if n = 2 then 1 else 0

private theorem unaryMul_three (n : Nat) (hn : 1 ≤ n) :
    commutativeCappedSupportFiveMul (unaryLengthState n) 3 =
      unaryLengthState (n + 1) := by
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
          cases n with
          | zero => rfl
          | succ n =>
              simp [unaryLengthState,
                commutativeCappedSupportFiveMul]

private theorem unaryFold
    (xs : List Nat) (acc : Nat) (hacc : 1 ≤ acc) :
    xs.foldl
        (fun current _ =>
          commutativeCappedSupportFiveMul current 3)
        (unaryLengthState acc) =
      unaryLengthState (acc + xs.length) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [unaryMul_three acc hacc, ih (acc + 1) (by omega)]
      congr 1
      omega

private theorem cappedSupportEval_constantThree (w : Word Nat) :
    commutativeCappedSupportFive.semigroup.eval constantThree w =
      unaryLengthState w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              commutativeCappedSupportFiveMul current 3) 3 =
          unaryLengthState (head :: tail).length
      simpa [unaryLengthState, Nat.add_comm] using
        unaryFold tail 1 (by omega)

private theorem unaryLengthState_injective
    {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (h : unaryLengthState m = unaryLengthState n) :
    min m 3 = min n 3 := by
  have values := congrArg Fin.val h
  by_cases hm1 : m = 1
  · subst m
    by_cases hn1 : n = 1
    · subst n
      rfl
    · by_cases hn2 : n = 2
      · subst n
        simp [unaryLengthState] at values
        omega
      · have hn3 : 3 ≤ n := by omega
        simp [unaryLengthState, hn1, hn2] at values
  · by_cases hm2 : m = 2
    · subst m
      by_cases hn1 : n = 1
      · subst n
        simp [unaryLengthState] at values
        omega
      · by_cases hn2 : n = 2
        · subst n
          rfl
        · have hn3 : 3 ≤ n := by omega
          simp [unaryLengthState, hn1, hn2] at values
    · have hm3 : 3 ≤ m := by omega
      by_cases hn1 : n = 1
      · subst n
        simp [unaryLengthState, hm1, hm2] at values
        omega
      · by_cases hn2 : n = 2
        · subst n
          simp [unaryLengthState, hm1, hm2] at values
        · have hn3 : 3 ≤ n := by omega
          simp [Nat.min_eq_right (by omega : 3 ≤ m),
            Nat.min_eq_right (by omega : 3 ≤ n)]

theorem cappedSupportValid_cappedLengthThree
    (e : Identity Nat)
    (valid : e.SatisfiedBy commutativeCappedSupportFive.semigroup) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 := by
  have evaluated := valid constantThree
  rw [cappedSupportEval_constantThree,
    cappedSupportEval_constantThree] at evaluated
  exact unaryLengthState_injective
    (by simp [Word.toList]) (by simp [Word.toList]) evaluated

private theorem count_eq_length_of_all_eq
    (a : Nat) (xs : List Nat)
    (h : ∀ z, z ∈ xs → z = a) :
    xs.count a = xs.length := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      have hxa : x = a := h x (by simp)
      subst x
      rw [List.count_cons_self, List.length_cons]
      congr 1
      exact ih (fun z hz => h z (by simp [hz]))

private theorem capThreeReduce_word_ne_nil (w : Word Nat) :
    capThreeReduce w.toList ≠ [] := by
  intro hempty
  have hcount := count_capThreeReduce w.head w.toList
  rw [hempty] at hcount
  simp [Word.toList] at hcount
  omega

/-- Unrestricted completeness over `Nat` variables. Unary words retain
exponents one, two, and three; words with at least two support variables
retain each coordinate only up to exponent two. -/
theorem commutativeCappedSupportFiveBasis_complete :
    BasisFor commutativeCappedSupportFive.semigroup
      commutativeCappedSupportFiveBasis := by
  refine ⟨commutativeCappedSupportFiveBasis_models, ?_⟩
  intro e valid
  have cappedTwo := cappedSupportValid_cappedCountTwo e valid
  have supportEq := cappedSupportValid_support e valid
  have cappedLength := cappedSupportValid_cappedLengthThree e valid
  let a := e.lhs.head
  by_cases hmulti :
      ∃ b, b ∈ e.lhs.toList ∧ b ≠ a
  · obtain ⟨b, hbLeft, hba⟩ := hmulti
    have haLeft : a ∈ e.lhs.toList := by
      simp [a, Word.toList]
    have haRight : a ∈ e.rhs.toList :=
      (supportEq a).mp haLeft
    have hbRight : b ∈ e.rhs.toList :=
      (supportEq b).mp hbLeft
    have lhsNormal :=
      cappedSupportDerivesDoubleMarkerReduce
        a b e.lhs haLeft hbLeft (Ne.symm hba)
    have rhsNormal :=
      cappedSupportDerivesDoubleMarkerReduce
        a b e.rhs haRight hbRight (Ne.symm hba)
    have reducedPerm :
        (doubleMarkerReduce a b e.lhs).toList.Perm
          (doubleMarkerReduce a b e.rhs).toList := by
      rw [List.perm_iff_count]
      intro z
      rw [count_doubleMarkerReduce z a b e.lhs
          haLeft hbLeft (Ne.symm hba),
        count_doubleMarkerReduce z a b e.rhs
          haRight hbRight (Ne.symm hba),
        cappedTwo z]
    exact Derives.trans lhsNormal <|
      Derives.trans
        (cappedSupportDerivesPermutation
          (doubleMarkerReduce a b e.lhs)
          (doubleMarkerReduce a b e.rhs) reducedPerm)
        (Derives.symm rhsNormal)
  · have lhsUnary :
        ∀ z, z ∈ e.lhs.toList → z = a := by
      intro z hz
      apply Decidable.byContradiction
      intro hza
      exact hmulti ⟨z, hz, hza⟩
    have rhsUnary :
        ∀ z, z ∈ e.rhs.toList → z = a := by
      intro z hz
      exact lhsUnary z ((supportEq z).mpr hz)
    have cappedThree :
        ∀ z, min (e.lhs.toList.count z) 3 =
          min (e.rhs.toList.count z) 3 := by
      intro z
      by_cases hza : z = a
      · subst z
        rw [count_eq_length_of_all_eq a e.lhs.toList lhsUnary,
          count_eq_length_of_all_eq a e.rhs.toList rhsUnary,
          cappedLength]
      · have hzLeft : z ∉ e.lhs.toList := by
          intro hz
          exact hza (lhsUnary z hz)
        have hzRight : z ∉ e.rhs.toList := by
          intro hz
          exact hza (rhsUnary z hz)
        rw [List.count_eq_zero.mpr hzLeft,
          List.count_eq_zero.mpr hzRight]
    have reducedPerm :
        (capThreeReduce e.lhs.toList).Perm
          (capThreeReduce e.rhs.toList) :=
      capThreeReduce_perm_of_capped_count_eq cappedThree
    have lhsOld := exponentFourDerivesNormal e.lhs
    have rhsOld := exponentFourDerivesNormal e.rhs
    cases hl : capThreeReduce e.lhs.toList with
    | nil =>
        exact False.elim (capThreeReduce_word_ne_nil e.lhs hl)
    | cons x xs =>
        cases hr : capThreeReduce e.rhs.toList with
        | nil =>
            exact False.elim (capThreeReduce_word_ne_nil e.rhs hr)
        | cons y ys =>
            rw [hl] at lhsOld
            rw [hr] at rhsOld
            rw [hl, hr] at reducedPerm
            change
              Derives commutativeExponentFourBasis
                e.lhs (wordOfCons x xs) at lhsOld
            change
              Derives commutativeExponentFourBasis
                e.rhs (wordOfCons y ys) at rhsOld
            have lhsNormal :=
              cappedSupportDerivesExponentFour lhsOld
            have rhsNormal :=
              cappedSupportDerivesExponentFour rhsOld
            exact Derives.trans lhsNormal <|
              Derives.trans
                (cappedSupportDerivesPermutation
                  (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
                (Derives.symm rhsNormal)

end SemigroupBasis.Examples
