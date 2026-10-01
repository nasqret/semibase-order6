import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

def commonSquareX : Word Nat := Word.singleton 0
def commonSquareY : Word Nat := Word.singleton 1
def commonSquareXX : Word Nat := ⟨0, [0]⟩
def commonSquareYY : Word Nat := ⟨1, [1]⟩
def commonSquareXY : Word Nat := ⟨0, [1]⟩
def commonSquareYX : Word Nat := ⟨1, [0]⟩
def commonSquareXXXY : Word Nat := ⟨0, [0, 0, 1]⟩

def commonSquareLaw : Identity Nat :=
  ⟨commonSquareXX, commonSquareYY⟩

def commonSquareCommutativityLaw : Identity Nat :=
  ⟨commonSquareXY, commonSquareYX⟩

def commonSquareInsertionLaw : Identity Nat :=
  ⟨commonSquareXY, commonSquareXXXY⟩

/-- The common basis `xx = yy`, `xy = yx`, `xy = xxxy`. -/
def commonSquareParityBasis : List (Identity Nat) :=
  [commonSquareLaw, commonSquareCommutativityLaw,
    commonSquareInsertionLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem commonSquareDerivesSquares (u v : Word Nat) :
    Derives commonSquareParityBasis (u ++ u) (v ++ v) := by
  have hbase :
      Derives commonSquareParityBasis commonSquareXX commonSquareYY :=
    Derives.fromBasis (e := commonSquareLaw) <| by
      exact List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commonSquareParityBasis, commonSquareLaw, commonSquareXX,
    commonSquareYY, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton] using h

theorem commonSquareDerivesCommutativity (u v : Word Nat) :
    Derives commonSquareParityBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commonSquareParityBasis commonSquareXY commonSquareYX :=
    Derives.fromBasis (e := commonSquareCommutativityLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commonSquareParityBasis, commonSquareCommutativityLaw,
    commonSquareXY, commonSquareYX, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton] using h

theorem commonSquareDerivesInsertion (u v : Word Nat) :
    Derives commonSquareParityBasis
      (u ++ v) (((u ++ u) ++ u) ++ v) := by
  have hbase :
      Derives commonSquareParityBasis commonSquareXY commonSquareXXXY :=
    Derives.fromBasis (e := commonSquareInsertionLaw) <| by
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commonSquareParityBasis, commonSquareInsertionLaw,
    commonSquareXY, commonSquareXXXY, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

theorem commonSquareDerivesAbsorbSquare
    (marker u v : Word Nat) :
    Derives commonSquareParityBasis
      ((marker ++ marker) ++ ((u ++ u) ++ v))
      ((marker ++ marker) ++ v) := by
  have replaceSquare :=
    Derives.appendRight
      (Derives.prepend (marker ++ marker)
        (commonSquareDerivesSquares u marker)) v
  have contract :=
    Derives.symm
      (commonSquareDerivesInsertion marker (marker ++ v))
  exact Derives.trans
    (by
      simpa [Word.append_assoc] using replaceSquare)
    (by
      simpa [Word.append_assoc] using contract)

theorem commonSquareDerivesSquareIdempotent
    (marker u : Word Nat) :
    Derives commonSquareParityBasis
      ((marker ++ marker) ++ (u ++ u))
      (marker ++ marker) := by
  have replaceSquare :=
    Derives.prepend (marker ++ marker)
      (commonSquareDerivesSquares u marker)
  have contract :=
    Derives.symm (commonSquareDerivesInsertion marker marker)
  exact Derives.trans
    (by
      simpa [Word.append_assoc] using replaceSquare)
    (by
      simpa [Word.append_assoc] using contract)

private theorem bind_append (u v : Word Nat) (σ : Nat → Word Nat) :
    (u ++ v).bind σ = u.bind σ ++ v.bind σ := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem commonSquarePrependAfterMarker
    {u v : Word Nat} (marker p : Word Nat)
    (h :
      Derives commonSquareParityBasis
        ((marker ++ marker) ++ u)
        ((marker ++ marker) ++ v)) :
    Derives commonSquareParityBasis
      ((marker ++ marker) ++ (p ++ u))
      ((marker ++ marker) ++ (p ++ v)) := by
  have enter :=
    Derives.appendRight
      (commonSquareDerivesCommutativity (marker ++ marker) p) u
  have middle := Derives.prepend p h
  have exit :=
    Derives.appendRight
      (commonSquareDerivesCommutativity p (marker ++ marker)) v
  exact Derives.trans
    (by simpa [Word.append_assoc] using enter)
    (Derives.trans
      (by simpa [Word.append_assoc] using middle)
      (by simpa [Word.append_assoc] using exit))

private theorem commonSquareSubstituteAfterMarker
    {u v : Word Nat} (marker : Word Nat)
    (h :
      Derives commonSquareParityBasis
        ((marker ++ marker) ++ u)
        ((marker ++ marker) ++ v))
    (σ : Nat → Word Nat) :
    Derives commonSquareParityBasis
      ((marker ++ marker) ++ u.bind σ)
      ((marker ++ marker) ++ v.bind σ) := by
  let boundMarker := marker.bind σ
  have enter :=
    Derives.appendRight
      (commonSquareDerivesSquares marker boundMarker) (u.bind σ)
  have middle := Derives.subst h σ
  have exit :=
    Derives.appendRight
      (commonSquareDerivesSquares boundMarker marker) (v.bind σ)
  exact Derives.trans
    (by simpa [boundMarker, Word.append_assoc] using enter)
    (Derives.trans
      (by
        simpa [boundMarker, bind_append,
          Word.append_assoc] using middle)
      (by simpa [boundMarker, Word.append_assoc] using exit))

/-- Every cyclic-parity derivation remains valid after prefixing both sides
by a common square. This transports the unrestricted cyclic normalizer to the
present basis without imposing a variable or word-length bound. -/
theorem commonSquareLiftCyclic
    {u v : Word Nat}
    (h : Derives cyclicTwoBasis u v) (marker : Word Nat) :
    Derives commonSquareParityBasis
      ((marker ++ marker) ++ u)
      ((marker ++ marker) ++ v) := by
  induction h generalizing marker with
  | fromBasis hmem =>
      simp only [cyclicTwoBasis, List.mem_cons, List.not_mem_nil,
        or_false] at hmem
      rcases hmem with rfl | rfl
      · have commute :=
          Derives.prepend (marker ++ marker) <|
            commonSquareDerivesCommutativity
              (Word.singleton 0) (Word.singleton 1)
        simpa [cyclicCommutativityLaw, cyclicXY, cyclicYX,
          Word.append_assoc] using commute
      · simpa [cyclicCancellationLaw, cyclicXXY, cyclicY,
          Word.append_assoc] using
            commonSquareDerivesAbsorbSquare marker
              (Word.singleton 0) (Word.singleton 1)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih marker)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ marker) (ih₂ marker)
  | prepend p _ ih =>
      exact commonSquarePrependAfterMarker marker p (ih marker)
  | appendRight _ q ih =>
      simpa [Word.append_assoc] using
        Derives.appendRight (ih marker) q
  | subst h σ ih =>
      exact commonSquareSubstituteAfterMarker marker (ih marker) σ

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

def commonSquareMarker : Word Nat :=
  Word.singleton 0 ++ Word.singleton 0

def commonSquareParityNormal (w : Word Nat) : Word Nat :=
  match w.tail with
  | [] => w
  | _ :: _ =>
      match parityReduce w.toList with
      | [] => commonSquareMarker
      | x :: xs => commonSquareMarker ++ wordOfCons x xs

private theorem commonSquareDerivesInsertMarker
    (x y : Nat) (ys : List Nat) :
    Derives commonSquareParityBasis
      (wordOfCons x (y :: ys))
      (commonSquareMarker ++ wordOfCons x (y :: ys)) := by
  let first := Word.singleton x
  let suffix := wordOfCons y ys
  have insert := commonSquareDerivesInsertion first suffix
  have changeSquare :=
    Derives.appendRight
      (commonSquareDerivesSquares first (Word.singleton 0))
      (first ++ suffix)
  exact Derives.trans
    (by
      simpa [first, suffix, wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using insert)
    (by
      simpa [first, suffix, commonSquareMarker, wordOfCons, Word.append,
        Word.singleton, Word.append_assoc] using changeSquare)

theorem commonSquareParityDerivesNormal (w : Word Nat) :
    Derives commonSquareParityBasis w (commonSquareParityNormal w) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          exact Derives.refl _
      | cons next rest =>
          have insert :=
            commonSquareDerivesInsertMarker head next rest
          have cyclicNormal :=
            cyclicDerivesNormal (wordOfCons head (next :: rest))
          change
            match parityReduce (head :: next :: rest) with
            | [] =>
                Derives cyclicTwoBasis
                  (wordOfCons head (next :: rest))
                  (Word.singleton head ++ Word.singleton head)
            | x :: xs =>
                Derives cyclicTwoBasis
                  (wordOfCons head (next :: rest))
                  (wordOfCons x xs) at cyclicNormal
          cases hp : parityReduce (head :: next :: rest) with
          | nil =>
              rw [hp] at cyclicNormal
              change
                Derives commonSquareParityBasis
                  (wordOfCons head (next :: rest))
                  (match parityReduce (head :: next :: rest) with
                  | [] => commonSquareMarker
                  | x :: xs => commonSquareMarker ++ wordOfCons x xs)
              rw [hp]
              have lifted :=
                commonSquareLiftCyclic cyclicNormal (Word.singleton 0)
              have absorb :=
                commonSquareDerivesSquareIdempotent
                  (Word.singleton 0) (Word.singleton head)
              exact Derives.trans insert <|
                Derives.trans
                  (by
                    simpa [commonSquareMarker, wordOfCons, Word.append,
                      Word.singleton, Word.append_assoc] using lifted)
                  (by
                    simpa [commonSquareMarker, Word.append,
                      Word.singleton, Word.append_assoc] using absorb)
          | cons x xs =>
              rw [hp] at cyclicNormal
              change
                Derives commonSquareParityBasis
                  (wordOfCons head (next :: rest))
                  (match parityReduce (head :: next :: rest) with
                  | [] => commonSquareMarker
                  | x :: xs => commonSquareMarker ++ wordOfCons x xs)
              rw [hp]
              have lifted :=
                commonSquareLiftCyclic cyclicNormal (Word.singleton 0)
              exact Derives.trans insert <| by
                simpa [commonSquareParityNormal, commonSquareMarker,
                  wordOfCons, Word.append, Word.singleton,
                  Word.append_assoc, hp] using lifted

/-- Generic unrestricted completeness for the common-square parity basis.
The model must distinguish singleton words from products, separate singleton
variables, and recover the parity vector of every product identity. -/
theorem commonSquareParityBasis_complete_of_separates
    (T : FiniteTable)
    (models : Models T.semigroup commonSquareParityBasis)
    (lengthClass :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        (e.lhs.tail = [] ↔ e.rhs.tail = []))
    (singletonHead :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.lhs.tail = [] → e.rhs.tail = [] →
        e.lhs.head = e.rhs.head)
    (parity :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.lhs.tail ≠ [] → e.rhs.tail ≠ [] →
        ∀ z, e.lhs.toList.count z % 2 =
          e.rhs.toList.count z % 2) :
    BasisFor T.semigroup commonSquareParityBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  by_cases hl : e.lhs.tail = []
  · have hr := (lengthClass e valid).mp hl
    have heads := singletonHead e valid hl hr
    cases e with
    | mk lhs rhs =>
        cases lhs with
        | mk lx lxs =>
            cases rhs with
            | mk rx rxs =>
                simp only at hl hr heads
                subst lxs
                subst rxs
                subst rx
                exact Derives.refl _
  · have hr : e.rhs.tail ≠ [] := by
      intro rhsEmpty
      exact hl ((lengthClass e valid).mpr rhsEmpty)
    have lhsTail :
        ∃ x xs, e.lhs.tail = x :: xs := by
      cases htail : e.lhs.tail with
      | nil => exact False.elim (hl htail)
      | cons x xs => exact ⟨x, xs, rfl⟩
    have rhsTail :
        ∃ x xs, e.rhs.tail = x :: xs := by
      cases htail : e.rhs.tail with
      | nil => exact False.elim (hr htail)
      | cons x xs => exact ⟨x, xs, rfl⟩
    obtain ⟨lx, lxs, lhsTailEq⟩ := lhsTail
    obtain ⟨rx, rxs, rhsTailEq⟩ := rhsTail
    have parityEq := parity e valid hl hr
    have reducedPerm :
        (parityReduce e.lhs.toList).Perm
          (parityReduce e.rhs.toList) :=
      parityReduce_perm_of_parity_eq parityEq
    have lhsNormal := commonSquareParityDerivesNormal e.lhs
    have rhsNormal := commonSquareParityDerivesNormal e.rhs
    cases hlp : parityReduce e.lhs.toList with
    | nil =>
        rw [hlp] at reducedPerm
        have hrp : parityReduce e.rhs.toList = [] :=
          reducedPerm.nil_eq.symm
        rw [commonSquareParityNormal, lhsTailEq, hlp] at lhsNormal
        rw [commonSquareParityNormal, rhsTailEq, hrp] at rhsNormal
        exact Derives.trans lhsNormal (Derives.symm rhsNormal)
    | cons x xs =>
        cases hrp : parityReduce e.rhs.toList with
        | nil =>
            rw [hlp, hrp] at reducedPerm
            exact False.elim (List.not_perm_cons_nil reducedPerm)
        | cons y ys =>
            rw [commonSquareParityNormal, lhsTailEq, hlp] at lhsNormal
            rw [commonSquareParityNormal, rhsTailEq, hrp] at rhsNormal
            rw [hlp, hrp] at reducedPerm
            have cyclicPermutation :=
              cyclicDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm
            have commonPermutation :=
              commonSquareLiftCyclic cyclicPermutation (Word.singleton 0)
            exact Derives.trans lhsNormal <|
              Derives.trans
                (by
                  simpa [commonSquareMarker, wordOfCons,
                    Word.append_assoc] using commonPermutation)
                (Derives.symm rhsNormal)

/-- Exact zero-based multiplication table for `S3_2`,
`[[1,1,3],[1,1,3],[3,3,1]]` in one-based notation. -/
def commonSquareParityFirstMul (a b : Fin 3) : Fin 3 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 0 else 2
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 0 else 2
  else
    if b = 0 then 2 else if b = 1 then 2 else 0

def commonSquareParityFirst : FiniteTable where
  order := 3
  mul := commonSquareParityFirstMul
  assoc := by decide

private def firstParityValue (n : Nat) : Fin 3 :=
  if n % 2 = 0 then 0 else 2

private def firstParitySeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 2 else 0

private theorem firstParityMul_target (n : Nat) :
    commonSquareParityFirstMul (firstParityValue n) 2 =
      firstParityValue (n + 1) := by
  by_cases hn : n % 2 = 0
  · have hnext : (n + 1) % 2 = 1 := by omega
    simp [firstParityValue, commonSquareParityFirstMul, hn, hnext]
  · have hmod : n % 2 = 1 := by omega
    have hnext : (n + 1) % 2 = 0 := by omega
    simp [firstParityValue, commonSquareParityFirstMul, hmod, hnext]

private theorem firstParityMul_other (n : Nat) :
    commonSquareParityFirstMul (firstParityValue n) 0 =
      firstParityValue n := by
  by_cases hn : n % 2 = 0
  · simp [firstParityValue, commonSquareParityFirstMul, hn]
  · have hmod : n % 2 = 1 := by omega
    simp [firstParityValue, commonSquareParityFirstMul, hmod]

private theorem firstParityFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          commonSquareParityFirstMul current (firstParitySeparator z x))
        (firstParityValue acc) =
      firstParityValue (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show firstParitySeparator z z = (2 : Fin 3) by
          simp [firstParitySeparator]]
        rw [firstParityMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show firstParitySeparator z x = (0 : Fin 3) by
          simp [firstParitySeparator, hx]]
        rw [firstParityMul_other, ih]

theorem commonSquareParityFirstEval_separator
    (z : Nat) (w : Word Nat) :
    commonSquareParityFirst.semigroup.eval (firstParitySeparator z) w =
      firstParityValue (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              commonSquareParityFirstMul current
                (firstParitySeparator z x))
            (firstParitySeparator z head) =
          firstParityValue ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show firstParitySeparator z z = firstParityValue 1 by
          apply Fin.ext
          simp [firstParitySeparator, firstParityValue]]
        rw [firstParityFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show firstParitySeparator z head = firstParityValue 0 by
          apply Fin.ext
          simp [firstParitySeparator, firstParityValue, hhead]]
        rw [firstParityFold]
        congr 1
        omega

private theorem firstParityValue_mod_injective {m n : Nat}
    (h : firstParityValue m = firstParityValue n) :
    m % 2 = n % 2 := by
  by_cases hm : m % 2 = 0 <;> by_cases hn : n % 2 = 0
  · exact hm.trans hn.symm
  · have specialized := congrArg Fin.val h
    simp [firstParityValue, hm, hn] at specialized
  · have specialized := congrArg Fin.val h
    simp [firstParityValue, hm, hn] at specialized
  · omega

theorem commonSquareParityFirstValid_parity
    (e : Identity Nat)
    (valid : e.SatisfiedBy commonSquareParityFirst.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 := by
  intro z
  have evaluated := valid (firstParitySeparator z)
  rw [commonSquareParityFirstEval_separator,
    commonSquareParityFirstEval_separator] at evaluated
  exact firstParityValue_mod_injective evaluated

private theorem commonSquareParityFirstFold_one
    (xs : List Nat) :
    xs.foldl
        (fun current _ => commonSquareParityFirstMul current 1) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      change xs.foldl
        (fun current _ => commonSquareParityFirstMul current 1) 0 = 0
      exact ih

private theorem commonSquareParityFirstEval_long_one
    (x y : Nat) (ys : List Nat) :
    commonSquareParityFirst.semigroup.eval (fun _ => (1 : Fin 3))
      (wordOfCons x (y :: ys)) = (0 : Fin 3) := by
  change
    ys.foldl
      (fun current _ => commonSquareParityFirstMul current 1)
      (commonSquareParityFirstMul 1 1) = 0
  change
    ys.foldl
      (fun current _ => commonSquareParityFirstMul current 1) 0 = 0
  exact commonSquareParityFirstFold_one ys

theorem commonSquareParityFirstValid_lengthClass
    (e : Identity Nat)
    (valid : e.SatisfiedBy commonSquareParityFirst.semigroup) :
    e.lhs.tail = [] ↔ e.rhs.tail = [] := by
  constructor
  · intro hl
    by_cases hr : e.rhs.tail = []
    · exact hr
    · exfalso
      cases e with
      | mk lhs rhs =>
          cases lhs with
          | mk lx lxs =>
              cases rhs with
              | mk rx rxs =>
                  simp only at hl hr
                  subst lxs
                  cases rxs with
                  | nil => exact hr rfl
                  | cons ry rys =>
                      have evaluated := valid (fun _ => (1 : Fin 3))
                      change (1 : Fin 3) =
                        commonSquareParityFirst.semigroup.eval
                          (fun _ => (1 : Fin 3))
                          (wordOfCons rx (ry :: rys)) at evaluated
                      rw [commonSquareParityFirstEval_long_one] at evaluated
                      contradiction
  · intro hr
    by_cases hl : e.lhs.tail = []
    · exact hl
    · exfalso
      cases e with
      | mk lhs rhs =>
          cases lhs with
          | mk lx lxs =>
              cases rhs with
              | mk rx rxs =>
                  simp only at hl hr
                  subst rxs
                  cases lxs with
                  | nil => exact hl rfl
                  | cons ly lys =>
                      have evaluated := valid (fun _ => (1 : Fin 3))
                      change
                        commonSquareParityFirst.semigroup.eval
                          (fun _ => (1 : Fin 3))
                          (wordOfCons lx (ly :: lys)) =
                        (1 : Fin 3) at evaluated
                      rw [commonSquareParityFirstEval_long_one] at evaluated
                      contradiction

theorem commonSquareParityFirstValid_singletonHead
    (e : Identity Nat)
    (valid : e.SatisfiedBy commonSquareParityFirst.semigroup)
    (hl : e.lhs.tail = []) (hr : e.rhs.tail = []) :
    e.lhs.head = e.rhs.head := by
  by_cases heads : e.lhs.head = e.rhs.head
  · exact heads
  · exfalso
    let valuation : Nat → Fin 3 :=
      fun z => if z = e.lhs.head then 0 else 1
    have evaluated := valid valuation
    cases e with
    | mk lhs rhs =>
        cases lhs with
        | mk lx lxs =>
            cases rhs with
            | mk rx rxs =>
                simp only at hl hr heads
                subst lxs
                subst rxs
                change valuation lx = valuation rx at evaluated
                simp [valuation] at evaluated
                exact heads evaluated.symm

private theorem commonSquareParityFirstMul_square
    (a b : Fin 3) :
    commonSquareParityFirstMul a a =
      commonSquareParityFirstMul b b := by
  decide +revert

private theorem commonSquareParityFirstMul_commutative
    (a b : Fin 3) :
    commonSquareParityFirstMul a b =
      commonSquareParityFirstMul b a := by
  decide +revert

private theorem commonSquareParityFirstMul_insertion
    (a b : Fin 3) :
    commonSquareParityFirstMul a b =
      commonSquareParityFirstMul
        (commonSquareParityFirstMul
          (commonSquareParityFirstMul a a) a) b := by
  decide +revert

theorem commonSquareParityFirstBasis_models :
    Models commonSquareParityFirst.semigroup
      commonSquareParityBasis := by
  intro e he
  simp only [commonSquareParityBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    change
      commonSquareParityFirstMul (valuation 0) (valuation 0) =
        commonSquareParityFirstMul (valuation 1) (valuation 1)
    exact commonSquareParityFirstMul_square _ _
  · intro valuation
    change
      commonSquareParityFirstMul (valuation 0) (valuation 1) =
        commonSquareParityFirstMul (valuation 1) (valuation 0)
    exact commonSquareParityFirstMul_commutative _ _
  · intro valuation
    change
      commonSquareParityFirstMul (valuation 0) (valuation 1) =
        commonSquareParityFirstMul
          (commonSquareParityFirstMul
            (commonSquareParityFirstMul (valuation 0) (valuation 0))
            (valuation 0)) (valuation 1)
    exact commonSquareParityFirstMul_insertion _ _

theorem commonSquareParityFirstBasis_complete :
    BasisFor commonSquareParityFirst.semigroup
      commonSquareParityBasis :=
  commonSquareParityBasis_complete_of_separates
    commonSquareParityFirst
    commonSquareParityFirstBasis_models
    commonSquareParityFirstValid_lengthClass
    commonSquareParityFirstValid_singletonHead
    (fun e valid _ _ =>
      commonSquareParityFirstValid_parity e valid)

theorem commonSquareParityFirst_selfDual :
    commonSquareParityFirst.semigroup.opposite =
      commonSquareParityFirst.semigroup := by
  unfold commonSquareParityFirst FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  exact commonSquareParityFirstMul_commutative b a

theorem commonSquareParityFirstOppositeBasis_complete :
    BasisFor commonSquareParityFirst.semigroup.opposite
      commonSquareParityBasis := by
  rw [commonSquareParityFirst_selfDual]
  exact commonSquareParityFirstBasis_complete

/-- Exact zero-based multiplication table for `S3_3`,
`[[1,2,2],[2,1,1],[2,1,1]]` in one-based notation. -/
def commonSquareParitySecondMul (a b : Fin 3) : Fin 3 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 1 else 1
  else if a = 1 then
    if b = 0 then 1 else if b = 1 then 0 else 0
  else
    if b = 0 then 1 else if b = 1 then 0 else 0

def commonSquareParitySecond : FiniteTable where
  order := 3
  mul := commonSquareParitySecondMul
  assoc := by decide

private def secondParityValue (n : Nat) : Fin 3 :=
  ⟨n % 2, by omega⟩

private def secondParitySeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 1 else 0

private theorem secondParityMul_target (n : Nat) :
    commonSquareParitySecondMul (secondParityValue n) 1 =
      secondParityValue (n + 1) := by
  by_cases hn : n % 2 = 0
  · have hnext : (n + 1) % 2 = 1 := by omega
    simp [secondParityValue, commonSquareParitySecondMul, hn, hnext]
  · have hmod : n % 2 = 1 := by omega
    have hnext : (n + 1) % 2 = 0 := by omega
    simp [secondParityValue, commonSquareParitySecondMul, hmod, hnext]

private theorem secondParityMul_other (n : Nat) :
    commonSquareParitySecondMul (secondParityValue n) 0 =
      secondParityValue n := by
  by_cases hn : n % 2 = 0
  · simp [secondParityValue, commonSquareParitySecondMul, hn]
  · have hmod : n % 2 = 1 := by omega
    simp [secondParityValue, commonSquareParitySecondMul, hmod]

private theorem secondParityFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          commonSquareParitySecondMul current (secondParitySeparator z x))
        (secondParityValue acc) =
      secondParityValue (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show secondParitySeparator z z = (1 : Fin 3) by
          simp [secondParitySeparator]]
        rw [secondParityMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show secondParitySeparator z x = (0 : Fin 3) by
          simp [secondParitySeparator, hx]]
        rw [secondParityMul_other, ih]

theorem commonSquareParitySecondEval_separator
    (z : Nat) (w : Word Nat) :
    commonSquareParitySecond.semigroup.eval
        (secondParitySeparator z) w =
      secondParityValue (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              commonSquareParitySecondMul current
                (secondParitySeparator z x))
            (secondParitySeparator z head) =
          secondParityValue ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show secondParitySeparator z z = secondParityValue 1 by
          apply Fin.ext
          simp [secondParitySeparator, secondParityValue]]
        rw [secondParityFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show secondParitySeparator z head = secondParityValue 0 by
          apply Fin.ext
          simp [secondParitySeparator, secondParityValue, hhead]]
        rw [secondParityFold]
        congr 1
        omega

theorem commonSquareParitySecondValid_parity
    (e : Identity Nat)
    (valid : e.SatisfiedBy commonSquareParitySecond.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 := by
  intro z
  have evaluated := valid (secondParitySeparator z)
  rw [commonSquareParitySecondEval_separator,
    commonSquareParitySecondEval_separator] at evaluated
  exact Fin.mk.inj evaluated

private theorem commonSquareParitySecondMul_ne_two
    (a b : Fin 3) :
    commonSquareParitySecondMul a b ≠ 2 := by
  decide +revert

private theorem commonSquareParitySecondFold_ne_two
    (xs : List Nat) (acc : Fin 3) (hacc : acc ≠ 2) :
    xs.foldl
        (fun current _ => commonSquareParitySecondMul current 2) acc ≠ 2 := by
  induction xs generalizing acc with
  | nil =>
      exact hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih _ (commonSquareParitySecondMul_ne_two _ _)

private theorem commonSquareParitySecondEval_long_two
    (x y : Nat) (ys : List Nat) :
    commonSquareParitySecond.semigroup.eval (fun _ => (2 : Fin 3))
      (wordOfCons x (y :: ys)) ≠ (2 : Fin 3) := by
  change
    ys.foldl
      (fun current _ => commonSquareParitySecondMul current 2)
      (commonSquareParitySecondMul 2 2) ≠ 2
  exact commonSquareParitySecondFold_ne_two ys _
    (commonSquareParitySecondMul_ne_two _ _)

theorem commonSquareParitySecondValid_lengthClass
    (e : Identity Nat)
    (valid : e.SatisfiedBy commonSquareParitySecond.semigroup) :
    e.lhs.tail = [] ↔ e.rhs.tail = [] := by
  constructor
  · intro hl
    by_cases hr : e.rhs.tail = []
    · exact hr
    · exfalso
      cases e with
      | mk lhs rhs =>
          cases lhs with
          | mk lx lxs =>
              cases rhs with
              | mk rx rxs =>
                  simp only at hl hr
                  subst lxs
                  cases rxs with
                  | nil => exact hr rfl
                  | cons ry rys =>
                      have evaluated := valid (fun _ => (2 : Fin 3))
                      change (2 : Fin 3) =
                        commonSquareParitySecond.semigroup.eval
                          (fun _ => (2 : Fin 3))
                          (wordOfCons rx (ry :: rys)) at evaluated
                      exact
                        (commonSquareParitySecondEval_long_two rx ry rys)
                          evaluated.symm
  · intro hr
    by_cases hl : e.lhs.tail = []
    · exact hl
    · exfalso
      cases e with
      | mk lhs rhs =>
          cases lhs with
          | mk lx lxs =>
              cases rhs with
              | mk rx rxs =>
                  simp only at hl hr
                  subst rxs
                  cases lxs with
                  | nil => exact hl rfl
                  | cons ly lys =>
                      have evaluated := valid (fun _ => (2 : Fin 3))
                      change
                        commonSquareParitySecond.semigroup.eval
                          (fun _ => (2 : Fin 3))
                          (wordOfCons lx (ly :: lys)) =
                        (2 : Fin 3) at evaluated
                      exact
                        (commonSquareParitySecondEval_long_two lx ly lys)
                          evaluated

theorem commonSquareParitySecondValid_singletonHead
    (e : Identity Nat)
    (valid : e.SatisfiedBy commonSquareParitySecond.semigroup)
    (hl : e.lhs.tail = []) (hr : e.rhs.tail = []) :
    e.lhs.head = e.rhs.head := by
  by_cases heads : e.lhs.head = e.rhs.head
  · exact heads
  · exfalso
    let valuation : Nat → Fin 3 :=
      fun z => if z = e.lhs.head then 0 else 2
    have evaluated := valid valuation
    cases e with
    | mk lhs rhs =>
        cases lhs with
        | mk lx lxs =>
            cases rhs with
            | mk rx rxs =>
                simp only at hl hr heads
                subst lxs
                subst rxs
                change valuation lx = valuation rx at evaluated
                simp [valuation] at evaluated
                exact heads evaluated.symm

private theorem commonSquareParitySecondMul_square
    (a b : Fin 3) :
    commonSquareParitySecondMul a a =
      commonSquareParitySecondMul b b := by
  decide +revert

private theorem commonSquareParitySecondMul_commutative
    (a b : Fin 3) :
    commonSquareParitySecondMul a b =
      commonSquareParitySecondMul b a := by
  decide +revert

private theorem commonSquareParitySecondMul_insertion
    (a b : Fin 3) :
    commonSquareParitySecondMul a b =
      commonSquareParitySecondMul
        (commonSquareParitySecondMul
          (commonSquareParitySecondMul a a) a) b := by
  decide +revert

theorem commonSquareParitySecondBasis_models :
    Models commonSquareParitySecond.semigroup
      commonSquareParityBasis := by
  intro e he
  simp only [commonSquareParityBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl
  · intro valuation
    change
      commonSquareParitySecondMul (valuation 0) (valuation 0) =
        commonSquareParitySecondMul (valuation 1) (valuation 1)
    exact commonSquareParitySecondMul_square _ _
  · intro valuation
    change
      commonSquareParitySecondMul (valuation 0) (valuation 1) =
        commonSquareParitySecondMul (valuation 1) (valuation 0)
    exact commonSquareParitySecondMul_commutative _ _
  · intro valuation
    change
      commonSquareParitySecondMul (valuation 0) (valuation 1) =
        commonSquareParitySecondMul
          (commonSquareParitySecondMul
            (commonSquareParitySecondMul (valuation 0) (valuation 0))
            (valuation 0)) (valuation 1)
    exact commonSquareParitySecondMul_insertion _ _

theorem commonSquareParitySecondBasis_complete :
    BasisFor commonSquareParitySecond.semigroup
      commonSquareParityBasis :=
  commonSquareParityBasis_complete_of_separates
    commonSquareParitySecond
    commonSquareParitySecondBasis_models
    commonSquareParitySecondValid_lengthClass
    commonSquareParitySecondValid_singletonHead
    (fun e valid _ _ =>
      commonSquareParitySecondValid_parity e valid)

theorem commonSquareParitySecond_selfDual :
    commonSquareParitySecond.semigroup.opposite =
      commonSquareParitySecond.semigroup := by
  unfold commonSquareParitySecond FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  exact commonSquareParitySecondMul_commutative b a

theorem commonSquareParitySecondOppositeBasis_complete :
    BasisFor commonSquareParitySecond.semigroup.opposite
      commonSquareParityBasis := by
  rw [commonSquareParitySecond_selfDual]
  exact commonSquareParitySecondBasis_complete

end SemigroupBasis.Examples
