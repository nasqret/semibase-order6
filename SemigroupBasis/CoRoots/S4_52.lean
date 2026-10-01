import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S4_52

open SemigroupBasis
open SemigroupBasis.Examples

def x : Word Nat := Word.singleton 0
def xyy : Word Nat := ⟨0, [1, 1]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xzy : Word Nat := ⟨0, [2, 1]⟩

def suffixCommutationLaw : Identity Nat := ⟨xyz, xzy⟩
def suffixCancellationLaw : Identity Nat := ⟨xyy, x⟩

/-- Edmunds' exact basis `xyz = xzy`, `xyy = x` for `S4_52`. -/
def basis : List (Identity Nat) :=
  [suffixCommutationLaw, suffixCancellationLaw]

def zyx : Word Nat := ⟨2, [1, 0]⟩
def yzx : Word Nat := ⟨1, [2, 0]⟩
def yyx : Word Nat := ⟨1, [1, 0]⟩

/-- The literal reverse-word transform used for the opposite endpoint. -/
def expectedReversedBasis : List (Identity Nat) :=
  [⟨zyx, yzx⟩, ⟨yyx, x⟩]

theorem reversedBasis_eq_expected :
    reversedBasis basis = expectedReversedBasis := by
  rfl

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Swap arbitrary nonempty blocks strictly behind a fixed prefix. -/
theorem derivesSuffixSwap (pre u v : Word Nat) :
    Derives basis
      ((pre ++ u) ++ v) ((pre ++ v) ++ u) := by
  have hbase :
      Derives basis xyz xzy :=
    Derives.fromBasis (e := suffixCommutationLaw) <|
      List.Mem.head _
  have h :=
    Derives.subst hbase (instantiateThreeWords pre u v)
  simpa [basis, suffixCommutationLaw, xyz, xzy,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Delete two adjacent copies of any nonempty block behind a fixed prefix. -/
theorem derivesSuffixCancellation (pre repeated : Word Nat) :
    Derives basis
      ((pre ++ repeated) ++ repeated) pre := by
  have hbase :
      Derives basis xyy x :=
    Derives.fromBasis (e := suffixCancellationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase
      (instantiateThreeWords pre repeated repeated)
  simpa [basis, suffixCancellationLaw, xyy, x,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def appendList (pre : Word Nat) (tail : List Nat) : Word Nat :=
  ⟨pre.head, pre.tail ++ tail⟩

private theorem appendList_cons
    (pre : Word Nat) (head : Nat) (tail : List Nat) :
    appendList pre (head :: tail) =
      pre ++ wordOfCons head tail := by
  apply Word.toList_injective
  simp [appendList, wordOfCons, Word.toList]

private theorem appendList_cons_prefix
    (pre : Word Nat) (head : Nat) (tail : List Nat) :
    appendList pre (head :: tail) =
      appendList (pre ++ Word.singleton head) tail := by
  apply Word.toList_injective
  simp [appendList, Word.toList, List.append_assoc]

/-- Every permutation strictly behind a fixed nonempty prefix is derivable. -/
theorem derivesTailPermutation
    (pre : Word Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis
      (appendList pre left) (appendList pre right) := by
  induction permutation generalizing pre with
  | nil =>
      exact Derives.refl _
  | cons head _ ih =>
      have next := ih (pre ++ Word.singleton head)
      rw [appendList_cons_prefix, appendList_cons_prefix]
      exact next
  | swap first second rest =>
      cases rest with
      | nil =>
          rw [appendList_cons, appendList_cons]
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using
              derivesSuffixSwap pre
                (Word.singleton second) (Word.singleton first)
      | cons next tail =>
          have swapped :=
            Derives.appendRight
              (derivesSuffixSwap pre
                (Word.singleton second) (Word.singleton first))
              (wordOfCons next tail)
          rw [appendList_cons, appendList_cons]
          simpa [wordOfCons, Word.append_assoc] using swapped
  | trans _ _ firstIH secondIH =>
      exact Derives.trans (firstIH pre) (secondIH pre)

private theorem derivesCancelPair
    (pre : Word Nat) (letter : Nat) (rest : List Nat) :
    Derives basis
      (appendList pre (letter :: letter :: rest))
      (appendList pre rest) := by
  cases rest with
  | nil =>
      simpa [appendList, Word.append, Word.singleton,
        Word.append_assoc] using
          derivesSuffixCancellation pre (Word.singleton letter)
  | cons next tail =>
      have cancelled :=
        Derives.appendRight
          (derivesSuffixCancellation pre (Word.singleton letter))
          (wordOfCons next tail)
      simpa [appendList, wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using cancelled

private theorem derivesNormalizeTail :
    ∀ pre tail,
      Derives basis
        (appendList pre tail)
        (appendList pre (parityReduce tail))
  | pre, [] => by
      exact Derives.refl _
  | pre, letter :: tail => by
      have suffixNormal :=
        derivesNormalizeTail
          (pre ++ Word.singleton letter) tail
      have firstStep :
          Derives basis
            (appendList pre (letter :: tail))
            (appendList pre (letter :: parityReduce tail)) := by
        rw [appendList_cons_prefix, appendList_cons_prefix]
        exact suffixNormal
      by_cases present : letter ∈ parityReduce tail
      · have arranged :
            (letter :: parityReduce tail).Perm
              (letter :: letter :: (parityReduce tail).erase letter) :=
          List.Perm.cons letter (List.perm_cons_erase present)
        have reordered :=
          derivesTailPermutation pre arranged
        have reduced :
            parityReduce (letter :: tail) =
              (parityReduce tail).erase letter := by
          simp [parityReduce, present]
        rw [reduced]
        exact Derives.trans firstStep <|
          Derives.trans reordered <|
            derivesCancelPair pre letter
              ((parityReduce tail).erase letter)
      · have reduced :
            parityReduce (letter :: tail) =
              letter :: parityReduce tail := by
          simp [parityReduce, present]
        rw [reduced]
        exact firstStep
termination_by
  _ tail => tail.length

/-- Canonical form: retain the first variable and reduce the suffix modulo two. -/
def normal (word : Word Nat) : Word Nat :=
  ⟨word.head, parityReduce word.tail⟩

theorem derivesNormal (word : Word Nat) :
    Derives basis word (normal word) := by
  cases word with
  | mk head tail =>
      simpa [normal, appendList, Word.singleton] using
        derivesNormalizeTail (Word.singleton head) tail

/-- The left-zero factor is the even-column copy `[1,3]`. -/
def leftZeroEmbedding :
    Embedding leftZeroTwo.semigroup
      Generated.Catalogue.S4_52.table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-- The cyclic factor is the first-row copy `[1,2]`. -/
def cyclicEmbedding :
    Embedding cyclicTwo.semigroup
      Generated.Catalogue.S4_52.table.semigroup where
  toFun := fun value =>
    ⟨value.val, Nat.lt_trans value.isLt (by decide)⟩
  map_mul := by decide
  injective := by
    intro left right equal
    have values : left.val = right.val := by
      simpa using congrArg Fin.val equal
    exact Fin.ext values

private theorem leftZeroValid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftZeroTwo.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  let valuation : Nat → Fin 2 :=
    fun symbol =>
      if symbol = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm headsNe] at evaluated

theorem valid_head_eq (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S4_52.table.semigroup) :
    identity.lhs.head = identity.rhs.head :=
  leftZeroValid_head_eq identity <|
    leftZeroEmbedding.pullback_identity identity valid

theorem valid_parity (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S4_52.table.semigroup) :
    ∀ symbol,
      identity.lhs.toList.count symbol % 2 =
        identity.rhs.toList.count symbol % 2 :=
  cyclicValid_parity_eq identity <|
    cyclicEmbedding.pullback_identity identity valid

private theorem mul_suffixCommutation (left middle right : Fin 4) :
    Generated.Catalogue.S4_52.mul
        (Generated.Catalogue.S4_52.mul left middle) right =
      Generated.Catalogue.S4_52.mul
        (Generated.Catalogue.S4_52.mul left right) middle := by
  decide +revert

private theorem mul_suffixCancellation (left right : Fin 4) :
    Generated.Catalogue.S4_52.mul
        (Generated.Catalogue.S4_52.mul left right) right =
      left := by
  decide +revert

theorem models :
    Models Generated.Catalogue.S4_52.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · intro valuation
    change
      Generated.Catalogue.S4_52.mul
          (Generated.Catalogue.S4_52.mul
            (valuation 0) (valuation 1))
          (valuation 2) =
        Generated.Catalogue.S4_52.mul
          (Generated.Catalogue.S4_52.mul
            (valuation 0) (valuation 2))
          (valuation 1)
    exact mul_suffixCommutation
      (valuation 0) (valuation 1) (valuation 2)
  · intro valuation
    change
      Generated.Catalogue.S4_52.mul
          (Generated.Catalogue.S4_52.mul
            (valuation 0) (valuation 1))
          (valuation 1) =
        valuation 0
    exact mul_suffixCancellation (valuation 0) (valuation 1)

private theorem tailParity_of_totalParity
    (left right : Word Nat)
    (heads : left.head = right.head)
    (parity :
      ∀ symbol,
        left.toList.count symbol % 2 =
          right.toList.count symbol % 2) :
    ∀ symbol,
      left.tail.count symbol % 2 =
        right.tail.count symbol % 2 := by
  intro symbol
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simp only at heads parity
          subst rightHead
          have whole := parity symbol
          by_cases isHead : symbol = leftHead
          · subst symbol
            change
              leftTail.count leftHead % 2 =
                rightTail.count leftHead % 2
            simp only [Word.toList, List.count_cons_self] at whole
            rw [Nat.add_mod, Nat.add_mod] at whole
            omega
          · simpa [Word.toList,
              List.count_cons_of_ne (Ne.symm isHead)] using whole

theorem normal_tail_perm
    (left right : Word Nat)
    (heads : left.head = right.head)
    (parity :
      ∀ symbol,
        left.toList.count symbol % 2 =
          right.toList.count symbol % 2) :
    (normal left).tail.Perm (normal right).tail := by
  simpa [normal] using
    parityReduce_perm_of_parity_eq <|
      tailParity_of_totalParity left right heads parity

/-- Generic unrestricted completeness for fixed-head parity semigroups. -/
theorem basis_complete_of_separates
    (table : FiniteTable)
    (modelsTable : Models table.semigroup basis)
    (headsTable :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          identity.lhs.head = identity.rhs.head)
    (parityTable :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          ∀ symbol,
            identity.lhs.toList.count symbol % 2 =
              identity.rhs.toList.count symbol % 2) :
    BasisFor table.semigroup basis := by
  refine ⟨modelsTable, ?_⟩
  intro identity valid
  have heads := headsTable identity valid
  have parity := parityTable identity valid
  have leftNormal := derivesNormal identity.lhs
  have rightNormal := derivesNormal identity.rhs
  have middle :
      Derives basis (normal identity.lhs) (normal identity.rhs) := by
    simpa [normal, appendList, Word.singleton, heads] using
      derivesTailPermutation
        (Word.singleton identity.lhs.head)
        (normal_tail_perm identity.lhs identity.rhs heads parity)
  exact Derives.trans leftNormal <|
    Derives.trans middle (Derives.symm rightNormal)

/-- Placeholder-free unrestricted identity-basis theorem for `S4_52`. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S4_52.table.semigroup basis :=
  basis_complete_of_separates Generated.Catalogue.S4_52.table
    models valid_head_eq valid_parity

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S4_52.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using basis_complete.oppositeReversed

end SemigroupBasis.CoRoots.S4_52
