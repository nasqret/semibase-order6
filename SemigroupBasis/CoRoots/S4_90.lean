import SemigroupBasis.Examples.CommutativeParityThree
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S4_90

open SemigroupBasis
open SemigroupBasis.Examples

def suffixParityX : Word Nat := Word.singleton 0
def suffixParityXXX : Word Nat := ⟨0, [0, 0]⟩
def suffixParityXYZ : Word Nat := ⟨0, [1, 2]⟩
def suffixParityXZY : Word Nat := ⟨0, [2, 1]⟩

def suffixParityPowerLaw : Identity Nat :=
  ⟨suffixParityX, suffixParityXXX⟩

def suffixParityCommutationLaw : Identity Nat :=
  ⟨suffixParityXYZ, suffixParityXZY⟩

/-- Edmunds' basis `xyz = xzy`, `x = xxx` for `S4_90`. -/
def basis : List (Identity Nat) :=
  [suffixParityCommutationLaw, suffixParityPowerLaw]

private def instantiateThreeWords (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem derivesTripleContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) u := by
  have hbase :
      Derives basis suffixParityXXX suffixParityX :=
    Derives.symm <|
      Derives.fromBasis (e := suffixParityPowerLaw) <| by
        exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords u u u)
  simpa [basis, suffixParityPowerLaw, suffixParityXXX,
    suffixParityX, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

/-- Arbitrary nonempty blocks in the suffix of a word may be swapped. -/
theorem derivesSuffixSwap (p u v : Word Nat) :
    Derives basis ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have hbase :
      Derives basis suffixParityXYZ suffixParityXZY :=
    Derives.fromBasis (e := suffixParityCommutationLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords p u v)
  simpa [basis, suffixParityCommutationLaw, suffixParityXYZ,
    suffixParityXZY, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- The suffix is commutative while the first letter remains fixed. -/
theorem derivesTailPermutation (head : Nat) {xs ys : List Nat}
    (h : xs.Perm ys) :
    Derives basis (wordOfCons head xs) (wordOfCons head ys) := by
  induction h generalizing head with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      have suffix := ih (head := x)
      simpa [wordOfCons, Word.singleton, Word.append] using
        Derives.prepend (Word.singleton head) suffix
  | swap x y xs =>
      cases xs with
      | nil =>
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using
              derivesSuffixSwap
                (Word.singleton head) (Word.singleton y)
                (Word.singleton x)
      | cons z zs =>
          have swapped :=
            Derives.appendRight
              (derivesSuffixSwap
                (Word.singleton head) (Word.singleton y)
                (Word.singleton x))
              (wordOfCons z zs)
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using swapped
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ (head := head)) (ih₂ (head := head))

private def suffixLimit (head x : Nat) : Nat :=
  if x = head then 1 else 2

/-- Reduce the suffix modulo two. The first variable may occur zero or one
time in the suffix; every other supported variable occurs once or twice. -/
def reduceSuffix (head : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := reduceSuffix head xs
      if reduced.count x < suffixLimit head x then
        x :: reduced
      else
        reduced.erase x

theorem reduceSuffix_count_le (head z : Nat) (xs : List Nat) :
    (reduceSuffix head xs).count z ≤ suffixLimit head z := by
  induction xs with
  | nil =>
      simp [reduceSuffix, suffixLimit]
  | cons x xs ih =>
      simp only [reduceSuffix]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx)]
          exact ih
      · by_cases hzx : z = x
        · subst z
          rw [List.count_erase_self]
          omega
        · rw [List.count_erase_of_ne hzx]
          exact ih

theorem reduceSuffix_count_mod_two (head z : Nat) (xs : List Nat) :
    (reduceSuffix head xs).count z % 2 = xs.count z % 2 := by
  induction xs with
  | nil =>
      simp [reduceSuffix]
  | cons x xs ih =>
      simp only [reduceSuffix]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx)]
          exact ih
      · by_cases hzx : z = x
        · subst z
          have countLe :
              (reduceSuffix head xs).count x ≤ suffixLimit head x :=
            reduceSuffix_count_le head x xs
          have countEq :
              (reduceSuffix head xs).count x = suffixLimit head x := by
            omega
          have priorParity := ih
          rw [List.count_erase_self, List.count_cons_self, countEq]
          by_cases hx : x = head
          · subst x
            simp [suffixLimit] at countEq
            rw [countEq] at priorParity
            omega
          · simp [suffixLimit, hx] at countEq
            rw [countEq] at priorParity
            omega
        · rw [List.count_erase_of_ne hzx,
            List.count_cons_of_ne (Ne.symm hzx)]
          exact ih

theorem mem_reduceSuffix_iff_of_ne
    (head z : Nat) (hz : z ≠ head) (xs : List Nat) :
    z ∈ reduceSuffix head xs ↔ z ∈ xs := by
  induction xs with
  | nil =>
      simp [reduceSuffix]
  | cons x xs ih =>
      simp only [reduceSuffix]
      split <;> rename_i hcount
      · simp [ih]
      · by_cases hzx : z = x
        · subst x
          have countLe := reduceSuffix_count_le head z xs
          have countEq : (reduceSuffix head xs).count z = 2 := by
            simp [suffixLimit, hz] at hcount countLe
            omega
          have remains : z ∈ (reduceSuffix head xs).erase z := by
            rw [← List.count_pos_iff, List.count_erase_self, countEq]
            omega
          simp [remains]
        · rw [List.mem_erase_of_ne hzx]
          simp [ih, hzx]

def normal (w : Word Nat) : Word Nat :=
  ⟨w.head, reduceSuffix w.head w.tail⟩

private theorem contractLeadingTriple (x : Nat) (xs : List Nat) :
    Derives basis
      (wordOfCons x (x :: x :: xs))
      (wordOfCons x xs) := by
  cases xs with
  | nil =>
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          derivesTripleContraction (Word.singleton x)
  | cons y ys =>
      have h :=
        Derives.appendRight
          (derivesTripleContraction (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem contractTailTriple (head x : Nat) (xs : List Nat) :
    Derives basis
      (wordOfCons head (x :: x :: x :: xs))
      (wordOfCons head (x :: xs)) := by
  have h := Derives.prepend (Word.singleton head)
    (contractLeadingTriple x xs)
  simpa [wordOfCons, Word.append, Word.singleton,
    Word.append_assoc] using h

private theorem deleteHeadPair (head : Nat) (pre rest : List Nat)
    (hcount : rest.count head = 1) :
    Derives basis
      (wordOfCons head (pre ++ head :: rest))
      (wordOfCons head (pre ++ rest.erase head)) := by
  have sourcePerm :
      (pre ++ head :: rest).Perm
        (head :: head :: pre ++ rest.erase head) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = head
    · subst z
      simp only [List.count_cons_self]
      rw [List.count_erase_self, hcount]
    · simp only [List.count_cons_of_ne (Ne.symm hz),
        List.count_erase_of_ne hz]
  exact Derives.trans
    (derivesTailPermutation head sourcePerm) <|
      contractLeadingTriple head (pre ++ rest.erase head)

private theorem deleteThirdSuffixCopy (head x : Nat)
    (pre rest : List Nat) (hcount : rest.count x = 2) :
    Derives basis
      (wordOfCons head (pre ++ x :: rest))
      (wordOfCons head (pre ++ rest.erase x)) := by
  let remainder := (rest.erase x).erase x
  have sourcePerm :
      (pre ++ x :: rest).Perm
        (x :: x :: x :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = x
    · subst z
      simp only [List.count_cons_self]
      have firstErase : (rest.erase x).count x = 1 := by
        rw [List.count_erase_self, hcount]
      have secondErase : ((rest.erase x).erase x).count x = 0 := by
        rw [List.count_erase_self, firstErase]
      simp only [remainder, secondErase, hcount]
    · simp only [List.count_cons_of_ne (Ne.symm hz),
        List.count_erase_of_ne hz, remainder]
  have targetPerm :
      (pre ++ rest.erase x).Perm
        (x :: pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append]
    by_cases hz : z = x
    · subst z
      simp only [List.count_cons_self]
      have firstErase : (rest.erase x).count x = 1 := by
        rw [List.count_erase_self, hcount]
      have secondErase : ((rest.erase x).erase x).count x = 0 := by
        rw [List.count_erase_self, firstErase]
      simp only [remainder, secondErase]
      rw [firstErase]
    · simp only [List.count_cons_of_ne (Ne.symm hz),
        List.count_erase_of_ne hz, remainder]
  exact Derives.trans
    (derivesTailPermutation head sourcePerm) <|
    Derives.trans (contractTailTriple head x (pre ++ remainder)) <|
      derivesTailPermutation head targetPerm.symm

private theorem derivesNormalizeSuffix :
    ∀ head pre xs,
      Derives basis
        (wordOfCons head (pre ++ xs))
        (wordOfCons head (pre ++ reduceSuffix head xs))
  | head, pre, [] => by
      exact Derives.refl _
  | head, pre, x :: xs => by
      have suffixNormal := derivesNormalizeSuffix head (pre ++ [x]) xs
      let reduced := reduceSuffix head xs
      have firstStep :
          Derives basis
            (wordOfCons head (pre ++ x :: xs))
            (wordOfCons head (pre ++ x :: reduced)) := by
        simpa [reduced, List.append_assoc] using suffixNormal
      by_cases hcount : reduced.count x < suffixLimit head x
      · have reducedEq :
            reduceSuffix head (x :: xs) = x :: reduced := by
          simp [reduceSuffix, reduced, hcount]
        rw [reducedEq]
        exact firstStep
      · have countLe :
            reduced.count x ≤ suffixLimit head x := by
          simpa [reduced] using reduceSuffix_count_le head x xs
        have countEq :
            reduced.count x = suffixLimit head x := by
          omega
        have reducedEq :
            reduceSuffix head (x :: xs) = reduced.erase x := by
          simp [reduceSuffix, reduced, hcount]
        rw [reducedEq]
        by_cases hx : x = head
        · subst x
          have headCount : reduced.count head = 1 := by
            simpa [suffixLimit] using countEq
          exact Derives.trans firstStep
            (deleteHeadPair head pre reduced headCount)
        · have suffixCount : reduced.count x = 2 := by
            simpa [suffixLimit, hx] using countEq
          exact Derives.trans firstStep
            (deleteThirdSuffixCopy head x pre reduced suffixCount)
termination_by
  _ _ xs => xs.length

theorem derivesNormal (w : Word Nat) :
    Derives basis w (normal w) := by
  cases w with
  | mk head tail =>
      simpa [normal, wordOfCons] using
        derivesNormalizeSuffix head [] tail

def parityEmbedding :
    Embedding parityIdentityThree.semigroup
      Generated.Catalogue.S4_90.table.semigroup where
  toFun := fun a => ⟨a.val, Nat.lt_trans a.isLt (by decide)⟩
  map_mul := by decide
  injective := by
    intro a b h
    have values : a.val = b.val := by
      simpa using congrArg Fin.val h
    exact Fin.ext values

theorem valid_support (e : Identity Nat)
    (valid : e.SatisfiedBy Generated.Catalogue.S4_90.table.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList :=
  parityIdentityValid_support e
    (parityEmbedding.pullback_identity e valid)

theorem valid_parity (e : Identity Nat)
    (valid : e.SatisfiedBy Generated.Catalogue.S4_90.table.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 :=
  parityIdentityValid_parity e
    (parityEmbedding.pullback_identity e valid)

private def headSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 3 else 2

private theorem headFold_from_two
    (z : Nat) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          Generated.Catalogue.S4_90.mul current (headSeparator z x))
        (2 : Fin 4) = 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        simpa [headSeparator, Generated.Catalogue.S4_90.mul] using ih
      · simpa [headSeparator, Generated.Catalogue.S4_90.mul, hx] using ih

private theorem headFold_from_three
    (z : Nat) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          Generated.Catalogue.S4_90.mul current (headSeparator z x))
        (3 : Fin 4) = 3 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        simpa [headSeparator, Generated.Catalogue.S4_90.mul] using ih
      · simpa [headSeparator, Generated.Catalogue.S4_90.mul, hx] using ih

theorem eval_headSeparator (z : Nat) (w : Word Nat) :
    Generated.Catalogue.S4_90.table.semigroup.eval
        (headSeparator z) w =
      if w.head = z then (3 : Fin 4) else (2 : Fin 4) := by
  cases w with
  | mk head tail =>
      by_cases hz : head = z
      · subst head
        simp only [if_pos]
        change
          tail.foldl
              (fun current x =>
                Generated.Catalogue.S4_90.mul current
                  (headSeparator z x))
              (headSeparator z z) = 3
        rw [show headSeparator z z = (3 : Fin 4) by
          simp [headSeparator]]
        exact headFold_from_three z tail
      · simp only [if_neg hz]
        change
          tail.foldl
              (fun current x =>
                Generated.Catalogue.S4_90.mul current
                  (headSeparator z x))
              (headSeparator z head) = 2
        rw [show headSeparator z head = (2 : Fin 4) by
          simp [headSeparator, hz]]
        exact headFold_from_two z tail

theorem valid_head_eq (e : Identity Nat)
    (valid : e.SatisfiedBy Generated.Catalogue.S4_90.table.semigroup) :
    e.lhs.head = e.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  have evaluated := valid (headSeparator e.lhs.head)
  rw [eval_headSeparator, eval_headSeparator] at evaluated
  simp [Ne.symm headsNe] at evaluated

private theorem mul_power (a : Fin 4) :
    a =
      Generated.Catalogue.S4_90.mul
        (Generated.Catalogue.S4_90.mul a a) a := by
  decide +revert

private theorem mul_suffix_commutative (a b c : Fin 4) :
    Generated.Catalogue.S4_90.mul
        (Generated.Catalogue.S4_90.mul a b) c =
      Generated.Catalogue.S4_90.mul
        (Generated.Catalogue.S4_90.mul a c) b := by
  decide +revert

theorem models :
    Models Generated.Catalogue.S4_90.table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change
      Generated.Catalogue.S4_90.mul
          (Generated.Catalogue.S4_90.mul
            (valuation 0) (valuation 1))
          (valuation 2) =
        Generated.Catalogue.S4_90.mul
          (Generated.Catalogue.S4_90.mul
            (valuation 0) (valuation 2))
          (valuation 1)
    exact mul_suffix_commutative
      (valuation 0) (valuation 1) (valuation 2)
  · intro valuation
    change
      valuation 0 =
        Generated.Catalogue.S4_90.mul
          (Generated.Catalogue.S4_90.mul
            (valuation 0) (valuation 0))
          (valuation 0)
    exact mul_power (valuation 0)

private theorem normalTailPerm
    (u v : Word Nat)
    (heads : u.head = v.head)
    (support : ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parity : ∀ z, u.toList.count z % 2 =
      v.toList.count z % 2) :
    (normal u).tail.Perm (normal v).tail := by
  rw [List.perm_iff_count]
  intro z
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          simp only at heads support parity
          subst vHead
          simp only [normal]
          have leftLe := reduceSuffix_count_le uHead z uTail
          have rightLe := reduceSuffix_count_le uHead z vTail
          have parityEq := reduceSuffix_count_mod_two uHead z uTail
          have parityEqRight := reduceSuffix_count_mod_two uHead z vTail
          by_cases hz : z = uHead
          · subst z
            simp [suffixLimit] at leftLe rightLe
            have wholeParity := parity uHead
            simp only [Word.toList, List.count_cons_self] at wholeParity
            omega
          · have leftMem :
                z ∈ reduceSuffix uHead uTail ↔ z ∈ uTail :=
              mem_reduceSuffix_iff_of_ne uHead z hz uTail
            have rightMem :
                z ∈ reduceSuffix uHead vTail ↔ z ∈ vTail :=
              mem_reduceSuffix_iff_of_ne uHead z hz vTail
            have supportTail : z ∈ uTail ↔ z ∈ vTail := by
              have wholeSupport := support z
              simpa [Word.toList, hz, Ne.symm hz] using wholeSupport
            have normalSupport :
                z ∈ reduceSuffix uHead uTail ↔
                  z ∈ reduceSuffix uHead vTail := by
              rw [leftMem, rightMem, supportTail]
            simp [suffixLimit, hz] at leftLe rightLe
            have wholeParity := parity z
            simp only [Word.toList,
              List.count_cons_of_ne (Ne.symm hz)] at wholeParity
            have leftPos :
                z ∈ reduceSuffix uHead uTail →
                  0 < (reduceSuffix uHead uTail).count z :=
              fun h => List.count_pos_iff.mpr h
            have rightPos :
                z ∈ reduceSuffix uHead vTail →
                  0 < (reduceSuffix uHead vTail).count z :=
              fun h => List.count_pos_iff.mpr h
            by_cases hmem : z ∈ reduceSuffix uHead uTail
            · have rmem := normalSupport.mp hmem
              have lp := leftPos hmem
              have rp := rightPos rmem
              omega
            · have lzero := List.count_eq_zero.mpr hmem
              have rzero := List.count_eq_zero.mpr <| by
                intro hr
                exact hmem (normalSupport.mpr hr)
              omega

/-- Normal suffix-parity representatives have permutationally equal tails
whenever the source words have the same first letter, support, and parity. -/
theorem normal_tail_perm
    (u v : Word Nat)
    (heads : u.head = v.head)
    (support : ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parity : ∀ z, u.toList.count z % 2 =
      v.toList.count z % 2) :
    (normal u).tail.Perm (normal v).tail :=
  normalTailPerm u v heads support parity

/-- Generic unrestricted completeness theorem for the suffix-parity basis.
A model only needs to separate first letters, support, and parity. -/
theorem basis_complete_of_separates
    (T : FiniteTable)
    (modelsT : Models T.semigroup basis)
    (headsT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        e.lhs.head = e.rhs.head)
    (supportT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (parityT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, e.lhs.toList.count z % 2 =
          e.rhs.toList.count z % 2) :
    BasisFor T.semigroup basis := by
  refine ⟨modelsT, ?_⟩
  intro e valid
  have heads := headsT e valid
  have support := supportT e valid
  have parity := parityT e valid
  have lhsNormal := derivesNormal e.lhs
  have rhsNormal := derivesNormal e.rhs
  have middle :
      Derives basis (normal e.lhs) (normal e.rhs) := by
    simpa [normal, wordOfCons, heads] using
      derivesTailPermutation e.lhs.head
        (normalTailPerm e.lhs e.rhs heads support parity)
  exact Derives.trans lhsNormal <|
    Derives.trans middle (Derives.symm rhsNormal)

/-- Kernel-checked unrestricted identity basis theorem for `S4_90`. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S4_90.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S4_90.table
    models valid_head_eq valid_support valid_parity

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S4_90.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using basis_complete.oppositeReversed

end SemigroupBasis.CoRoots.S4_90
