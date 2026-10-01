import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_830

open SemigroupBasis

def xx : Word Nat := ⟨0, [0]⟩
def xxx : Word Nat := ⟨0, [0, 0]⟩
def xy : Word Nat := ⟨0, [1]⟩
def xyx : Word Nat := ⟨0, [1, 0]⟩
def xxyz : Word Nat := ⟨0, [0, 1, 2]⟩
def xxzy : Word Nat := ⟨0, [0, 2, 1]⟩

def squareLaw : Identity Nat := ⟨xx, xxx⟩
def returnLaw : Identity Nat := ⟨xy, xyx⟩
def doubledPrefixSwapLaw : Identity Nat := ⟨xxyz, xxzy⟩

/-- The common three-identity basis of the `S5_830` family. -/
def basis : List (Identity Nat) :=
  [squareLaw, returnLaw, doubledPrefixSwapLaw]

def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

def wordOfTwo (x y : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, y :: xs⟩

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Append a second copy of the first nonempty block. -/
theorem derivesAppendFirst (u v : Word Nat) :
    Derives basis (u ++ v) ((u ++ v) ++ u) := by
  have hbase : Derives basis xy xyx :=
    Derives.fromBasis (e := returnLaw) <| by
      exact List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [basis, returnLaw, xy, xyx, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

/-- Contract a repeated final block after a nonempty prefix. -/
theorem derivesRightContraction (p u : Word Nat) :
    Derives basis ((p ++ u) ++ u) (p ++ u) := by
  have expandPrefix :=
    Derives.appendRight (derivesAppendFirst p u) u
  have contractMiddle :=
    Derives.prepend p <| Derives.symm (derivesAppendFirst u p)
  have contractFinal :=
    Derives.symm (derivesAppendFirst p u)
  exact Derives.trans expandPrefix <|
    Derives.trans
      (by simpa [Word.append_assoc] using contractMiddle) <| by
    simpa [Word.append_assoc] using contractFinal

/-- Contract two consecutive copies of a product of two nonempty blocks. -/
theorem derivesBlockSquareContraction (p q : Word Nat) :
    Derives basis ((p ++ q) ++ (p ++ q)) (p ++ q) := by
  have first :=
    Derives.appendRight
      (Derives.symm (derivesAppendFirst p q)) q
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (derivesRightContraction p q)

/-- Swap two nonempty blocks after two fixed nonempty prefix blocks. -/
theorem derivesTailSwap (p q u v : Word Nat) :
    Derives basis (((p ++ q) ++ u) ++ v)
      (((p ++ q) ++ v) ++ u) := by
  have expand :=
    Derives.appendRight
      (Derives.symm (derivesBlockSquareContraction p q))
      (u ++ v)
  have hbase : Derives basis xxyz xxzy :=
    Derives.fromBasis (e := doubledPrefixSwapLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have swap :=
    Derives.subst hbase (instantiateThreeWords (p ++ q) u v)
  have contract :=
    Derives.appendRight
      (derivesBlockSquareContraction p q) (v ++ u)
  exact Derives.trans
    (by simpa [Word.append_assoc] using expand) <|
    Derives.trans
      (by
        simpa [basis, doubledPrefixSwapLaw, xxyz, xxzy,
          instantiateThreeWords, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using swap) <| by
    simpa [Word.append_assoc] using contract

/-- Every permutation of the suffix after the first two letters is
derivable. -/
theorem derivesTailPermutation (first second : Nat)
    {xs ys : List Nat} (permutation : xs.Perm ys) :
    Derives basis (wordOfTwo first second xs)
      (wordOfTwo first second ys) := by
  induction permutation generalizing first second with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      have suffix := ih (first := second) (second := x)
      simpa [wordOfTwo, Word.singleton, Word.append] using
        Derives.prepend (Word.singleton first) suffix
  | swap x y xs =>
      cases xs with
      | nil =>
          simpa [wordOfTwo, Word.singleton, Word.append,
            Word.append_assoc] using
              derivesTailSwap
                (Word.singleton first) (Word.singleton second)
                (Word.singleton y) (Word.singleton x)
      | cons z zs =>
          have swapped :=
            Derives.appendRight
              (derivesTailSwap
                (Word.singleton first) (Word.singleton second)
                (Word.singleton y) (Word.singleton x))
              (wordOfCons z zs)
          simpa [wordOfTwo, wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using swapped
  | trans _ _ ihFirst ihSecond =>
      exact Derives.trans
        (ihFirst (first := first) (second := second))
        (ihSecond (first := first) (second := second))

private theorem perm_cons_to_end (x : Nat) :
    ∀ xs : List Nat, (x :: xs).Perm (xs ++ [x])
  | [] => List.Perm.refl _
  | y :: ys =>
      (List.Perm.swap y x ys).trans <|
        List.Perm.cons y (perm_cons_to_end x ys)

/-- A word of length at least two may be expanded by one copy of any
variable already in its support. -/
theorem derivesAppendMember (w : Word Nat) (x : Nat)
    (hlong : 2 ≤ w.toList.length) (member : x ∈ w.toList) :
    Derives basis w (w ++ Word.singleton x) := by
  cases w with
  | mk first tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at hlong
      | cons second rest =>
          by_cases xFirst : x = first
          · subst x
            simpa [wordOfCons, Word.singleton, Word.append,
              Word.append_assoc] using
                derivesAppendFirst
                  (Word.singleton first) (wordOfCons second rest)
          · by_cases xSecond : x = second
            · subst x
              cases rest with
              | nil =>
                  simpa [Word.singleton, Word.append,
                    Word.append_assoc] using
                      Derives.symm
                        (derivesRightContraction
                          (Word.singleton first)
                          (Word.singleton second))
              | cons third more =>
                  have duplicate :=
                    derivesAppendFirst
                      (Word.singleton second) (wordOfCons third more)
                  simpa [wordOfCons, Word.singleton, Word.append,
                    Word.append_assoc] using
                      Derives.prepend (Word.singleton first) duplicate
            · have inRest : x ∈ rest := by
                simpa [Word.toList, xFirst, xSecond] using member
              let remaining := rest.erase x
              have arrange :
                  rest.Perm (remaining ++ [x]) := by
                exact
                  (List.perm_cons_erase inRest).trans <|
                    perm_cons_to_end x remaining
              have arranged :=
                derivesTailPermutation first second arrange
              have duplicate :=
                Derives.symm <|
                  derivesRightContraction
                    (wordOfTwo first second remaining)
                    (Word.singleton x)
              have restore :
                  ((remaining ++ [x]) ++ [x]).Perm
                    (rest ++ [x]) := by
                exact arrange.symm.append_right [x]
              have restored :=
                derivesTailPermutation first second restore
              exact Derives.trans arranged <|
                Derives.trans
                  (by
                    simpa [remaining, wordOfTwo, Word.singleton,
                      Word.append, Word.append_assoc,
                      List.append_assoc] using duplicate)
                  (by
                    simpa [wordOfTwo, Word.singleton, Word.append,
                      List.append_assoc] using restored)

theorem derivesAppendList (w : Word Nat) (xs : List Nat)
    (hlong : 2 ≤ w.toList.length)
    (supported : ∀ x, x ∈ xs → x ∈ w.toList) :
    Derives basis w ⟨w.head, w.tail ++ xs⟩ := by
  induction xs generalizing w with
  | nil =>
      simpa using Derives.refl w
  | cons x xs ih =>
      have xSupported : x ∈ w.toList :=
        supported x (List.Mem.head xs)
      have firstStep := derivesAppendMember w x hlong xSupported
      have appendedLong :
          2 ≤ (w ++ Word.singleton x).toList.length := by
        simp only [Word.toList_append, Word.toList_singleton,
          List.length_append, List.length_cons, List.length_nil]
        omega
      have restSupported :
          ∀ y, y ∈ xs →
            y ∈ (w ++ Word.singleton x).toList := by
        intro y hy
        rw [Word.toList_append]
        exact List.mem_append_left _ <|
          supported y (List.Mem.tail x hy)
      have restStep :=
        ih (w ++ Word.singleton x) appendedLong restSupported
      exact Derives.trans firstStep <| by
        simpa [Word.singleton, List.append_assoc] using restStep

/-- A word of length at least two may be expanded by any word whose support
it contains. -/
theorem derivesContentExpansion (u v : Word Nat)
    (uLong : 2 ≤ u.toList.length)
    (supported : ∀ x, x ∈ v.toList → x ∈ u.toList) :
    Derives basis u (u ++ v) := by
  have expanded :=
    derivesAppendList u v.toList uLong supported
  simpa [Word.toList, Word.append] using expanded

/-- The first two letters of a word. -/
def FirstTwo (w : Word Nat) : List Nat :=
  w.toList.take 2

/-- Two words have the same support when they contain the same variables,
without regard to multiplicity. -/
def SameSupport (u v : Word Nat) : Prop :=
  ∀ z, z ∈ u.toList ↔ z ∈ v.toList

/-- Concatenated words with equal first-two prefixes commute as whole
blocks. -/
theorem derivesConcatSwap (u v : Word Nat)
    (uLong : 2 ≤ u.toList.length)
    (vLong : 2 ≤ v.toList.length)
    (firstTwoEq : FirstTwo u = FirstTwo v) :
    Derives basis (u ++ v) (v ++ u) := by
  cases u with
  | mk uHead uTail =>
      cases uTail with
      | nil =>
          simp [Word.toList] at uLong
      | cons uSecond uRest =>
          cases v with
          | mk vHead vTail =>
              cases vTail with
              | nil =>
                  simp [Word.toList] at vLong
              | cons vSecond vRest =>
                  simp only [FirstTwo, Word.toList] at firstTwoEq
                  have heads : uHead = vHead := by
                    exact (List.cons.inj firstTwoEq).1
                  have tails :
                      uSecond :: [] = vSecond :: [] := by
                    exact (List.cons.inj firstTwoEq).2
                  have seconds : uSecond = vSecond := by
                    exact (List.cons.inj tails).1
                  subst vHead
                  subst vSecond
                  have permutation :
                      (uRest ++ uHead :: uSecond :: vRest).Perm
                        (vRest ++ uHead :: uSecond :: uRest) := by
                    rw [List.perm_iff_count]
                    intro z
                    simp only [List.count_append, List.count_cons]
                    omega
                  simpa [wordOfTwo, Word.append, List.append_assoc] using
                    derivesTailPermutation
                      uHead uSecond permutation

/-- Words of length at least two with equal first-two prefixes and support
are derivably equal. -/
theorem derivesOfFirstTwoSupportEq (u v : Word Nat)
    (uLong : 2 ≤ u.toList.length)
    (vLong : 2 ≤ v.toList.length)
    (firstTwoEq : FirstTwo u = FirstTwo v)
    (support : SameSupport u v) :
    Derives basis u v := by
  have uExpansion :
      Derives basis u (u ++ v) :=
    derivesContentExpansion u v uLong
      (fun x hx => (support x).mpr hx)
  have vExpansion :
      Derives basis v (v ++ u) :=
    derivesContentExpansion v u vLong
      (fun x hx => (support x).mp hx)
  exact Derives.trans uExpansion <|
    Derives.trans
      (derivesConcatSwap u v uLong vLong firstTwoEq)
      (Derives.symm vExpansion)

private def finiteSquareLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

private def finiteReturnLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

private def finiteDoubledPrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [0, 2, 1]⟩⟩

private theorem finiteSquareLaw_map :
    finiteSquareLaw.map Fin.val = squareLaw := rfl

private theorem finiteReturnLaw_map :
    finiteReturnLaw.map Fin.val = returnLaw := rfl

private theorem finiteDoubledPrefixSwapLaw_map :
    finiteDoubledPrefixSwapLaw.map Fin.val =
      doubledPrefixSwapLaw := rfl

private theorem models_of_checks
    (T : FiniteTable)
    (square : T.checkIdentity finiteSquareLaw = true)
    (returning : T.checkIdentity finiteReturnLaw = true)
    (swap : T.checkIdentity finiteDoubledPrefixSwapLaw = true) :
    Models T.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · rw [finiteSquareLaw_map.symm]
    exact T.checkIdentityNat_sound finiteSquareLaw square
  · rw [finiteReturnLaw_map.symm]
    exact T.checkIdentityNat_sound finiteReturnLaw returning
  · rw [finiteDoubledPrefixSwapLaw_map.symm]
    exact T.checkIdentityNat_sound finiteDoubledPrefixSwapLaw swap

private def marker
    (target other : Fin 5) (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then target else other

private theorem fold_absent_iff
    (mul : Fin 5 → Fin 5 → Fin 5)
    (target other output : Fin 5)
    (z : Nat)
    (step :
      ∀ current x,
        mul current (marker target other z x) = output ↔
          current = output ∧ x ≠ z)
    (xs : List Nat) (initial : Fin 5) :
    xs.foldl
        (fun current x =>
          mul current (marker target other z x))
        initial = output ↔
      initial = output ∧ z ∉ xs := by
  induction xs generalizing initial with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, step]
      simp only [List.mem_cons, not_or]
      constructor
      · rintro ⟨⟨currentOutput, xNe⟩, restAbsent⟩
        exact
          ⟨currentOutput, fun zx => xNe zx.symm, restAbsent⟩
      · rintro ⟨currentOutput, zNe, restAbsent⟩
        exact
          ⟨⟨currentOutput, fun xz => zNe xz.symm⟩, restAbsent⟩

private theorem fold_left_zero
    (valuation : Nat → Fin 5) (xs : List Nat)
    (initial : Fin 5) (absorbing : initial = 0 ∨ initial = 2) :
    xs.foldl
        (fun current x =>
          Generated.Catalogue.S5_830.mul current (valuation x))
        initial = initial := by
  induction xs generalizing initial with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.foldl_cons]
      rcases absorbing with rfl | rfl
      · simpa [Generated.Catalogue.S5_830.mul] using
          ih (0 : Fin 5) (Or.inl rfl)
      · simpa [Generated.Catalogue.S5_830.mul] using
          ih (2 : Fin 5) (Or.inr rfl)

private theorem eval_two_then_left_zero
    (valuation : Nat → Fin 5)
    (first second : Nat) (rest : List Nat)
    (output : Fin 5)
    (product :
      Generated.Catalogue.S5_830.mul
          (valuation first) (valuation second) = output)
    (absorbing : output = 0 ∨ output = 2) :
    Generated.Catalogue.S5_830.table.semigroup.eval valuation
        (wordOfTwo first second rest) = output := by
  change
    rest.foldl
        (fun current x =>
          Generated.Catalogue.S5_830.mul current (valuation x))
        (Generated.Catalogue.S5_830.mul
          (valuation first) (valuation second)) = output
  rw [product, fold_left_zero valuation rest output absorbing]

private theorem supportStep
    (z : Nat) (current : Fin 5) (x : Nat) :
    Generated.Catalogue.S5_830.mul current
        (marker 0 3 z x) = 3 ↔
      current = 3 ∧ x ≠ z := by
  by_cases hx : x = z
  · subst x
    simp [marker, Generated.Catalogue.S5_830.mul]
    decide +revert
  · simp [marker, hx, Generated.Catalogue.S5_830.mul]
    decide +revert

private theorem evalSupport (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_830.table.semigroup.eval
        (marker 0 3 z) w = (3 : Fin 5) ↔
      z ∉ w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_830.mul current
                (marker 0 3 z x))
            (marker 0 3 z head) = 3 ↔
          z ∉ head :: tail
      rw [fold_absent_iff
        Generated.Catalogue.S5_830.mul 0 3 3 z (supportStep z)]
      simp [marker, eq_comm]

private theorem evalHead (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S5_830.table.semigroup.eval
        (marker 0 2 z) w = (0 : Fin 5) ↔
      w.head = z := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              Generated.Catalogue.S5_830.mul current
                (marker 0 2 z x))
            (marker 0 2 z head) = 0 ↔
          head = z
      rw [fold_left_zero (marker 0 2 z) tail
        (marker 0 2 z head)]
      · simp [marker]
      · by_cases h : head = z
        · exact Or.inl (by simp [marker, h])
        · exact Or.inr (by simp [marker, h])

private theorem evalSingleton (w : Word Nat) :
    Generated.Catalogue.S5_830.table.semigroup.eval
        (fun _ => (1 : Fin 5)) w = (1 : Fin 5) ↔
      w.tail = [] := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Semigroup.eval]
      | cons second rest =>
          simp only [Semigroup.eval, List.foldl_cons,
            List.cons_ne_nil, iff_false]
          rw [show
            Generated.Catalogue.S5_830.table.semigroup.mul
                (1 : Fin 5) (1 : Fin 5) = (0 : Fin 5) by rfl]
          have folded :=
            fold_left_zero (fun _ => (1 : Fin 5)) rest 0
              (Or.inl rfl)
          rw [show
            rest.foldl
                (fun current _ =>
                  Generated.Catalogue.S5_830.table.semigroup.mul
                    current (1 : Fin 5))
                (0 : Fin 5) = (0 : Fin 5) by
              simpa [FiniteTable.semigroup] using folded]
          decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_830.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_830.table
    (by decide) (by decide) (by decide)

theorem valid_support (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_830.table.semigroup) :
    SameSupport e.lhs e.rhs := by
  intro z
  have evaluated := valid (marker 0 3 z)
  have absent :
      z ∉ e.lhs.toList ↔ z ∉ e.rhs.toList := by
    calc
      z ∉ e.lhs.toList ↔
          Generated.Catalogue.S5_830.table.semigroup.eval
              (marker 0 3 z) e.lhs = (3 : Fin 5) :=
        (evalSupport z e.lhs).symm
      _ ↔ Generated.Catalogue.S5_830.table.semigroup.eval
              (marker 0 3 z) e.rhs = (3 : Fin 5) := by
        rw [evaluated]
      _ ↔ z ∉ e.rhs.toList := evalSupport z e.rhs
  constructor
  · intro lhsMember
    apply Decidable.byContradiction
    intro rhsAbsent
    exact (absent.mpr rhsAbsent) lhsMember
  · intro rhsMember
    apply Decidable.byContradiction
    intro lhsAbsent
    exact (absent.mp lhsAbsent) rhsMember

private theorem valid_head (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_830.table.semigroup) :
    e.lhs.head = e.rhs.head := by
  have evaluated := valid (marker 0 2 e.lhs.head)
  have rhsHead : e.rhs.head = e.lhs.head := by
    apply (evalHead e.lhs.head e.rhs).mp
    rw [← evaluated]
    exact (evalHead e.lhs.head e.lhs).mpr rfl
  exact rhsHead.symm

private theorem valid_singleton_iff (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_830.table.semigroup) :
    e.lhs.tail = [] ↔ e.rhs.tail = [] := by
  have evaluated := valid (fun _ => (1 : Fin 5))
  calc
    e.lhs.tail = [] ↔
        Generated.Catalogue.S5_830.table.semigroup.eval
            (fun _ => (1 : Fin 5)) e.lhs = (1 : Fin 5) :=
      (evalSingleton e.lhs).symm
    _ ↔ Generated.Catalogue.S5_830.table.semigroup.eval
            (fun _ => (1 : Fin 5)) e.rhs = (1 : Fin 5) := by
      rw [evaluated]
    _ ↔ e.rhs.tail = [] := evalSingleton e.rhs

private theorem second_eq_of_valid
    (first lhsSecond rhsSecond : Nat)
    (lhsRest rhsRest : List Nat)
    (valid :
      (Identity.mk
        (wordOfTwo first lhsSecond lhsRest)
        (wordOfTwo first rhsSecond rhsRest)).SatisfiedBy
          Generated.Catalogue.S5_830.table.semigroup) :
    lhsSecond = rhsSecond := by
  apply Decidable.byContradiction
  intro secondsNe
  by_cases lhsHead : lhsSecond = first
  · subst lhsSecond
    have rhsHead : rhsSecond ≠ first := by
      intro equal
      exact secondsNe equal.symm
    let valuation : Nat → Fin 5 :=
      fun x => if x = first then 1 else if x = rhsSecond then 4 else 0
    have lhsEval :
        Generated.Catalogue.S5_830.table.semigroup.eval valuation
            (wordOfTwo first first lhsRest) = (0 : Fin 5) := by
      apply eval_two_then_left_zero
        valuation first first lhsRest (0 : Fin 5)
      · simp [valuation, Generated.Catalogue.S5_830.mul]
      · exact Or.inl rfl
    have rhsEval :
        Generated.Catalogue.S5_830.table.semigroup.eval valuation
            (wordOfTwo first rhsSecond rhsRest) = (2 : Fin 5) := by
      apply eval_two_then_left_zero
        valuation first rhsSecond rhsRest (2 : Fin 5)
      · simp [valuation, rhsHead, Generated.Catalogue.S5_830.mul]
      · exact Or.inr rfl
    have evaluated := valid valuation
    rw [lhsEval, rhsEval] at evaluated
    exact (by decide : (0 : Fin 5) ≠ 2) evaluated
  · by_cases rhsHead : rhsSecond = first
    · subst rhsSecond
      let valuation : Nat → Fin 5 :=
        fun x => if x = first then 1
          else if x = lhsSecond then 4 else 0
      have lhsEval :
          Generated.Catalogue.S5_830.table.semigroup.eval valuation
              (wordOfTwo first lhsSecond lhsRest) = (2 : Fin 5) := by
        apply eval_two_then_left_zero
          valuation first lhsSecond lhsRest (2 : Fin 5)
        · simp [valuation, lhsHead,
            Generated.Catalogue.S5_830.mul]
        · exact Or.inr rfl
      have rhsEval :
          Generated.Catalogue.S5_830.table.semigroup.eval valuation
              (wordOfTwo first first rhsRest) = (0 : Fin 5) := by
        apply eval_two_then_left_zero
          valuation first first rhsRest (0 : Fin 5)
        · simp [valuation, Generated.Catalogue.S5_830.mul]
        · exact Or.inl rfl
      have evaluated := valid valuation
      rw [lhsEval, rhsEval] at evaluated
      exact (by decide : (2 : Fin 5) ≠ 0) evaluated
    · let valuation : Nat → Fin 5 :=
        fun x => if x = first then 1
          else if x = lhsSecond then 4 else 0
      have rhsLhs : rhsSecond ≠ lhsSecond := by
        exact fun equal => secondsNe equal.symm
      have lhsEval :
          Generated.Catalogue.S5_830.table.semigroup.eval valuation
              (wordOfTwo first lhsSecond lhsRest) = (2 : Fin 5) := by
        apply eval_two_then_left_zero
          valuation first lhsSecond lhsRest (2 : Fin 5)
        · simp [valuation, lhsHead,
            Generated.Catalogue.S5_830.mul]
        · exact Or.inr rfl
      have rhsEval :
          Generated.Catalogue.S5_830.table.semigroup.eval valuation
              (wordOfTwo first rhsSecond rhsRest) = (0 : Fin 5) := by
        apply eval_two_then_left_zero
          valuation first rhsSecond rhsRest (0 : Fin 5)
        · simp [valuation, rhsHead, rhsLhs,
            Generated.Catalogue.S5_830.mul]
        · exact Or.inl rfl
      have evaluated := valid valuation
      rw [lhsEval, rhsEval] at evaluated
      exact (by decide : (2 : Fin 5) ≠ 0) evaluated

theorem valid_firstTwo (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_830.table.semigroup) :
    FirstTwo e.lhs = FirstTwo e.rhs := by
  rcases e with
    ⟨⟨lhsHead, lhsTail⟩, ⟨rhsHead, rhsTail⟩⟩
  have heads :
      lhsHead = rhsHead :=
    valid_head
      ⟨⟨lhsHead, lhsTail⟩, ⟨rhsHead, rhsTail⟩⟩ valid
  have singletonIff :
      lhsTail = [] ↔ rhsTail = [] :=
    valid_singleton_iff
      ⟨⟨lhsHead, lhsTail⟩, ⟨rhsHead, rhsTail⟩⟩ valid
  cases lhsTail with
  | nil =>
      have rhsNil : rhsTail = [] := singletonIff.mp rfl
      subst rhsTail
      subst rhsHead
      rfl
  | cons lhsSecond lhsRest =>
      cases rhsTail with
      | nil =>
          simp at singletonIff
      | cons rhsSecond rhsRest =>
          subst rhsHead
          have specialized :
              (Identity.mk
                (wordOfTwo lhsHead lhsSecond lhsRest)
                (wordOfTwo lhsHead rhsSecond rhsRest)).SatisfiedBy
                  Generated.Catalogue.S5_830.table.semigroup := by
            simpa [wordOfTwo] using valid
          have seconds :=
            second_eq_of_valid lhsHead lhsSecond rhsSecond
              lhsRest rhsRest specialized
          subst rhsSecond
          rfl

/-- Generic completeness theorem for the `S5_830` basis. A finite table only
has to model the basis and recover the first two letters and support. -/
theorem basis_complete_of_separates
    (T : FiniteTable)
    (modelsT : Models T.semigroup basis)
    (firstTwoT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        FirstTwo e.lhs = FirstTwo e.rhs)
    (supportT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        SameSupport e.lhs e.rhs) :
    BasisFor T.semigroup basis := by
  refine ⟨modelsT, ?_⟩
  intro e valid
  have firstTwoEq := firstTwoT e valid
  have support := supportT e valid
  have firstTwoLengths := congrArg List.length firstTwoEq
  simp only [FirstTwo, List.length_take] at firstTwoLengths
  have lhsPositive : 0 < e.lhs.toList.length := by
    simp [Word.toList]
  have rhsPositive : 0 < e.rhs.toList.length := by
    simp [Word.toList]
  by_cases lhsLong : 2 ≤ e.lhs.toList.length
  · have rhsLong : 2 ≤ e.rhs.toList.length := by
      omega
    exact derivesOfFirstTwoSupportEq
      e.lhs e.rhs lhsLong rhsLong firstTwoEq support
  · have lhsOne : e.lhs.toList.length = 1 := by
      omega
    have rhsOne : e.rhs.toList.length = 1 := by
      omega
    have lhsTail : e.lhs.tail = [] := by
      cases tailShape : e.lhs.tail with
      | nil => rfl
      | cons x xs =>
          have atLeastTwo : 2 ≤ e.lhs.toList.length := by
            simp [Word.toList, tailShape]
          omega
    have rhsTail : e.rhs.tail = [] := by
      cases tailShape : e.rhs.tail with
      | nil => rfl
      | cons x xs =>
          have atLeastTwo : 2 ≤ e.rhs.toList.length := by
            simp [Word.toList, tailShape]
          omega
    have headMember : e.lhs.head ∈ e.rhs.toList :=
      (support e.lhs.head).mp (List.Mem.head _)
    have heads : e.lhs.head = e.rhs.head := by
      simpa [Word.toList, rhsTail] using headMember
    have words : e.lhs = e.rhs := by
      apply Word.toList_injective
      simp [Word.toList, lhsTail, rhsTail, heads]
    rw [words]
    exact Derives.refl _

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_830.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S5_830.table
    models valid_firstTwo valid_support

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_830.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

/-- The exact congruence generated by the `S5_830` basis: singleton words
are literal, while longer words are classified by their first two letters
and support. -/
def ExactBasisClass (u v : Word Nat) : Prop :=
  u = v ∨
    (2 ≤ u.toList.length ∧
      2 ≤ v.toList.length ∧
      FirstTwo u = FirstTwo v ∧
      SameSupport u v)

/-- Complete syntactic characterization of derivability from the published
three identities. -/
theorem derives_iff_exactBasisClass {u v : Word Nat} :
    Derives basis u v ↔ ExactBasisClass u v := by
  constructor
  · intro derivation
    have valid :
        (Identity.mk u v).SatisfiedBy
          Generated.Catalogue.S5_830.table.semigroup :=
      fun valuation => derivation.sound models valuation
    have firstTwoEq := valid_firstTwo (Identity.mk u v) valid
    have support := valid_support (Identity.mk u v) valid
    have firstTwoLengths := congrArg List.length firstTwoEq
    simp only [FirstTwo, List.length_take] at firstTwoLengths
    have uPositive : 0 < u.toList.length := by
      simp [Word.toList]
    have vPositive : 0 < v.toList.length := by
      simp [Word.toList]
    by_cases uLong : 2 ≤ u.toList.length
    · exact Or.inr ⟨uLong, by omega, firstTwoEq, support⟩
    · have uOne : u.toList.length = 1 := by omega
      have vOne : v.toList.length = 1 := by omega
      have uTail : u.tail = [] := by
        cases tailShape : u.tail with
        | nil => rfl
        | cons x xs =>
            have atLeastTwo : 2 ≤ u.toList.length := by
              simp [Word.toList, tailShape]
            omega
      have vTail : v.tail = [] := by
        cases tailShape : v.tail with
        | nil => rfl
        | cons x xs =>
            have atLeastTwo : 2 ≤ v.toList.length := by
              simp [Word.toList, tailShape]
            omega
      have headMember : u.head ∈ v.toList :=
        (support u.head).mp (List.Mem.head _)
      have heads : u.head = v.head := by
        simpa [Word.toList, vTail] using headMember
      have words : u = v := by
        apply Word.toList_injective
        simp [Word.toList, uTail, vTail, heads]
      exact Or.inl words
  · intro sameClass
    rcases sameClass with equal |
      ⟨uLong, vLong, firstTwoEq, support⟩
    · subst v
      exact Derives.refl _
    · exact derivesOfFirstTwoSupportEq
        u v uLong vLong firstTwoEq support

end SemigroupBasis.CoRoots.S5_830
