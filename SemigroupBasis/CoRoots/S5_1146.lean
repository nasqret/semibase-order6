import SemigroupBasis.Examples.CommutativePositiveModThreeFour
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.Generated.CatalogueOrder5Part09
import SemigroupBasis.Generated.CommutativePositiveModThreeTransfersLayer1
import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_1146

open SemigroupBasis
open SemigroupBasis.Examples

def x : Word Nat := Word.singleton 0
def xxxx : Word Nat := ⟨0, [0, 0, 0]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xzy : Word Nat := ⟨0, [2, 1]⟩

def powerLaw : Identity Nat := ⟨x, xxxx⟩
def suffixCommutationLaw : Identity Nat := ⟨xyz, xzy⟩

/-- The exact basis `x = xxxx`, `xyz = xzy`. -/
def basis : List (Identity Nat) :=
  [powerLaw, suffixCommutationLaw]

def reversedPowerLaw : Identity Nat := ⟨x, xxxx⟩
def reversedSuffixCommutationLaw : Identity Nat :=
  ⟨⟨2, [1, 0]⟩, ⟨1, [2, 0]⟩⟩

def expectedReversedBasis : List (Identity Nat) :=
  [reversedPowerLaw, reversedSuffixCommutationLaw]

theorem reversedBasis_eq_expected :
    reversedBasis basis = expectedReversedBasis := by
  rfl

private def instantiateOneWord (u : Word Nat) : Nat → Word Nat
  | 0 => u
  | n + 1 => Word.singleton (n + 1)

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Contract four copies of an arbitrary nonempty block to one copy. -/
theorem derivesFourContraction (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) u := by
  have hbase : Derives basis xxxx x :=
    Derives.symm <|
      Derives.fromBasis (e := powerLaw) <|
        List.Mem.head _
  have h := Derives.subst hbase (instantiateOneWord u)
  simpa [basis, powerLaw, xxxx, x, instantiateOneWord,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

/-- Swap arbitrary nonempty blocks strictly behind a fixed prefix. -/
theorem derivesSuffixSwap (stem u v : Word Nat) :
    Derives basis
      ((stem ++ u) ++ v) ((stem ++ v) ++ u) := by
  have hbase : Derives basis xyz xzy :=
    Derives.fromBasis (e := suffixCommutationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h :=
    Derives.subst hbase (instantiateThreeWords stem u v)
  simpa [basis, suffixCommutationLaw, xyz, xzy,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def appendList (stem : Word Nat) (tail : List Nat) : Word Nat :=
  ⟨stem.head, stem.tail ++ tail⟩

private theorem appendList_cons
    (stem : Word Nat) (head : Nat) (tail : List Nat) :
    appendList stem (head :: tail) =
      stem ++ wordOfCons head tail := by
  apply Word.toList_injective
  simp [appendList, wordOfCons, Word.toList]

private theorem appendList_cons_prefix
    (stem : Word Nat) (head : Nat) (tail : List Nat) :
    appendList stem (head :: tail) =
      appendList (stem ++ Word.singleton head) tail := by
  apply Word.toList_injective
  simp [appendList, Word.toList, List.append_assoc]

/-- Every permutation strictly behind a fixed nonempty prefix is derivable. -/
theorem derivesTailPermutation
    (stem : Word Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis
      (appendList stem left) (appendList stem right) := by
  induction permutation generalizing stem with
  | nil =>
      exact Derives.refl _
  | cons head _ ih =>
      have next := ih (stem ++ Word.singleton head)
      rw [appendList_cons_prefix, appendList_cons_prefix]
      exact next
  | swap first second rest =>
      cases rest with
      | nil =>
          rw [appendList_cons, appendList_cons]
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using
              derivesSuffixSwap stem
                (Word.singleton second) (Word.singleton first)
      | cons next tail =>
          have swapped :=
            Derives.appendRight
              (derivesSuffixSwap stem
                (Word.singleton second) (Word.singleton first))
              (wordOfCons next tail)
          rw [appendList_cons, appendList_cons]
          simpa [wordOfCons, Word.append_assoc] using swapped
  | trans _ _ firstIH secondIH =>
      exact Derives.trans (firstIH stem) (secondIH stem)

private theorem three_copies_perm (letter : Nat) (letters : List Nat)
    (countEq : letters.count letter = 3) :
    letters.Perm
      (letter :: letter :: letter ::
        (((letters.erase letter).erase letter).erase letter)) := by
  have present : letter ∈ letters :=
    List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase present
  have countOnce : (letters.erase letter).count letter = 2 := by
    rw [List.count_erase_self, countEq]
  have presentOnce : letter ∈ letters.erase letter :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase presentOnce
  have countTwice :
      ((letters.erase letter).erase letter).count letter = 1 := by
    rw [List.count_erase_self, countOnce]
  have presentTwice :
      letter ∈ (letters.erase letter).erase letter :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <| List.Perm.cons letter <|
    second.trans <| List.Perm.cons letter <|
      List.perm_cons_erase presentTwice

private theorem derivesContractFourInTail
    (stem : Word Nat) (letter : Nat) (rest : List Nat) :
    Derives basis
      (appendList stem
        (letter :: letter :: letter :: letter :: rest))
      (appendList stem (letter :: rest)) := by
  cases rest with
  | nil =>
      simpa [appendList, Word.append, Word.singleton,
        Word.append_assoc] using
          Derives.prepend stem
            (derivesFourContraction (Word.singleton letter))
  | cons next tail =>
      have contracted :=
        Derives.appendRight
          (Derives.prepend stem
            (derivesFourContraction (Word.singleton letter)))
          (wordOfCons next tail)
      simpa [appendList, wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using contracted

private theorem derivesLeadingFour
    (letter : Nat) (rest : List Nat) :
    Derives basis
      (wordOfCons letter (letter :: letter :: letter :: rest))
      (wordOfCons letter rest) := by
  cases rest with
  | nil =>
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          derivesFourContraction (Word.singleton letter)
  | cons next tail =>
      have contracted :=
        Derives.appendRight
          (derivesFourContraction (Word.singleton letter))
          (wordOfCons next tail)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using contracted

private theorem derivesPositiveTail :
    ∀ stem tail,
      Derives basis
        (appendList stem tail)
        (appendList stem (positiveModThreeReduce tail))
  | stem, [] => by
      exact Derives.refl _
  | stem, letter :: tail => by
      have suffixNormal :=
        derivesPositiveTail
          (stem ++ Word.singleton letter) tail
      have firstStep :
          Derives basis
            (appendList stem (letter :: tail))
            (appendList stem
              (letter :: positiveModThreeReduce tail)) := by
        rw [appendList_cons_prefix, appendList_cons_prefix]
        exact suffixNormal
      by_cases countSmall :
          (positiveModThreeReduce tail).count letter < 3
      · have reduced :
            positiveModThreeReduce (letter :: tail) =
              letter :: positiveModThreeReduce tail := by
          simp [positiveModThreeReduce, countSmall]
        rw [reduced]
        exact firstStep
      · have countLe :
            (positiveModThreeReduce tail).count letter ≤ 3 :=
          positiveModThreeReduce_count_le_three letter tail
        have countEq :
            (positiveModThreeReduce tail).count letter = 3 := by
          omega
        let remainder :=
          (((positiveModThreeReduce tail).erase letter).erase letter).erase
            letter
        have suffixPerm :
            (positiveModThreeReduce tail).Perm
              (letter :: letter :: letter :: remainder) := by
          simpa [remainder] using
            three_copies_perm letter (positiveModThreeReduce tail) countEq
        have expandedPerm :
            (letter :: positiveModThreeReduce tail).Perm
              (letter :: letter :: letter :: letter :: remainder) :=
          List.Perm.cons letter suffixPerm
        have arranged :=
          derivesTailPermutation stem expandedPerm
        have contracted :=
          derivesContractFourInTail stem letter remainder
        have eraseOnceCount :
            ((positiveModThreeReduce tail).erase letter).count letter = 2 := by
          rw [List.count_erase_self, countEq]
        have eraseTwiceCount :
            (((positiveModThreeReduce tail).erase letter).erase letter).count
                letter = 1 := by
          rw [List.count_erase_self, eraseOnceCount]
        have eraseTwiceHasLetter :
            letter ∈
              ((positiveModThreeReduce tail).erase letter).erase letter :=
          List.count_pos_iff.mp (by omega)
        have reducedPerm :
            (letter :: remainder).Perm
              (((positiveModThreeReduce tail).erase letter).erase letter) := by
          simpa [remainder] using
            (List.perm_cons_erase eraseTwiceHasLetter).symm
        have restored :=
          derivesTailPermutation stem reducedPerm
        have reduced :
            positiveModThreeReduce (letter :: tail) =
              ((positiveModThreeReduce tail).erase letter).erase letter := by
          simp [positiveModThreeReduce, countSmall]
        rw [reduced]
        exact Derives.trans firstStep <|
          Derives.trans arranged <|
            Derives.trans contracted restored
termination_by
  _ tail => tail.length

/-- Canonical suffix after reserving one copy of the first variable. -/
def endpointSuffix (word : Word Nat) : List Nat :=
  (positiveModThreeReduce word.toList).erase word.head

/-- Canonical form: fixed first variable plus positive mod-three suffix. -/
def normal (word : Word Nat) : Word Nat :=
  ⟨word.head, endpointSuffix word⟩

private theorem positiveReduce_cons_erase_of_count_lt
    (head : Nat) (tail : List Nat)
    (countSmall : (positiveModThreeReduce tail).count head < 3) :
    (positiveModThreeReduce (head :: tail)).erase head =
      positiveModThreeReduce tail := by
  simp [positiveModThreeReduce, countSmall]

private theorem positiveReduce_cons_erase_of_count_eq_three
    (head : Nat) (tail : List Nat)
    (countEq : (positiveModThreeReduce tail).count head = 3) :
    (positiveModThreeReduce (head :: tail)).erase head =
      (((positiveModThreeReduce tail).erase head).erase head).erase head := by
  have countNotSmall :
      ¬ (positiveModThreeReduce tail).count head < 3 := by
    omega
  simp [positiveModThreeReduce, countNotSmall]

theorem derivesNormal (word : Word Nat) :
    Derives basis word (normal word) := by
  cases word with
  | mk head tail =>
      have tailNormal :=
        derivesPositiveTail (Word.singleton head) tail
      by_cases countSmall :
          (positiveModThreeReduce tail).count head < 3
      · have endpointEq :
            endpointSuffix ⟨head, tail⟩ =
              positiveModThreeReduce tail := by
          exact positiveReduce_cons_erase_of_count_lt
            head tail countSmall
        simpa [normal, appendList, Word.singleton,
          Word.toList, endpointEq] using tailNormal
      · have countLe :
            (positiveModThreeReduce tail).count head ≤ 3 :=
          positiveModThreeReduce_count_le_three head tail
        have countEq :
            (positiveModThreeReduce tail).count head = 3 := by
          omega
        let remainder :=
          (((positiveModThreeReduce tail).erase head).erase head).erase head
        have suffixPerm :
            (positiveModThreeReduce tail).Perm
              (head :: head :: head :: remainder) := by
          simpa [remainder] using
            three_copies_perm head (positiveModThreeReduce tail) countEq
        have arranged :=
          derivesTailPermutation (Word.singleton head) suffixPerm
        have contracted :=
          derivesLeadingFour head remainder
        have endpointEq :
            endpointSuffix ⟨head, tail⟩ = remainder := by
          simpa [endpointSuffix, Word.toList, remainder] using
            positiveReduce_cons_erase_of_count_eq_three
              head tail countEq
        simpa [normal, appendList, Word.singleton,
          Word.toList, wordOfCons, endpointEq, remainder] using
            Derives.trans tailNormal <|
              Derives.trans arranged contracted

private theorem leftZeroValid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftZeroTwo.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  let valuation : Nat → Fin 2 :=
    fun tested =>
      if tested = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm headsNe] at evaluated

theorem normal_tail_perm
    (left right : Word Nat)
    (heads : left.head = right.head)
    (support :
      ∀ tested,
        tested ∈ left.toList ↔ tested ∈ right.toList)
    (modThree :
      ∀ tested,
        left.toList.count tested % 3 =
          right.toList.count tested % 3) :
    (normal left).tail.Perm (normal right).tail := by
  have reducedPerm :
      (positiveModThreeReduce left.toList).Perm
        (positiveModThreeReduce right.toList) :=
    positiveModThreeReduce_perm support modThree
  have erased := reducedPerm.erase left.head
  simpa [normal, endpointSuffix, heads] using erased

/-- Generic unrestricted completeness for endpoint-suffix mod-three models. -/
theorem basis_complete_of_separates
    (table : FiniteTable)
    (modelsTable : Models table.semigroup basis)
    (headsTable :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          identity.lhs.head = identity.rhs.head)
    (supportTable :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          ∀ tested,
            tested ∈ identity.lhs.toList ↔
              tested ∈ identity.rhs.toList)
    (modThreeTable :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          ∀ tested,
            identity.lhs.toList.count tested % 3 =
              identity.rhs.toList.count tested % 3) :
    BasisFor table.semigroup basis := by
  refine ⟨modelsTable, ?_⟩
  intro identity valid
  have heads := headsTable identity valid
  have support := supportTable identity valid
  have modThree := modThreeTable identity valid
  have leftNormal := derivesNormal identity.lhs
  have rightNormal := derivesNormal identity.rhs
  have middle :
      Derives basis (normal identity.lhs) (normal identity.rhs) := by
    simpa [normal, appendList, Word.singleton, heads] using
      derivesTailPermutation
        (Word.singleton identity.lhs.head)
        (normal_tail_perm identity.lhs identity.rhs
          heads support modThree)
  exact Derives.trans leftNormal <|
    Derives.trans middle (Derives.symm rightNormal)

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, []⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixCommutationLaw := rfl

namespace S5_1146

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_1146.table

def leftZeroEmbedding :
    Embedding leftZeroTwo.semigroup table.semigroup where
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

def residueEmbedding :
    Embedding commutativePositiveModThreeFour.semigroup
      table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨1, by decide⟩
    else if value.val = 2 then ⟨3, by decide⟩
    else ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteSuffixCommutationLaw_map]
    exact table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)

theorem valid_head_eq (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.head = identity.rhs.head :=
  leftZeroValid_head_eq identity <|
    leftZeroEmbedding.pullback_identity identity valid

theorem valid_support (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ tested,
      tested ∈ identity.lhs.toList ↔
        tested ∈ identity.rhs.toList :=
  positiveModThreeValid_support identity <|
    residueEmbedding.pullback_identity identity valid

theorem valid_count_mod_three (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ tested,
      identity.lhs.toList.count tested % 3 =
        identity.rhs.toList.count tested % 3 :=
  positiveModThreeValid_count_mod_three identity <|
    residueEmbedding.pullback_identity identity valid

theorem representative_basis :
    BasisFor table.semigroup basis :=
  basis_complete_of_separates table models valid_head_eq
    valid_support valid_count_mod_three

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end S5_1146

namespace S5_1152

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_1152.table

def leftZeroEmbedding :
    Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def residueEmbedding :
    Embedding
      SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup
      table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨1, by decide⟩
    else if value.val = 2 then ⟨3, by decide⟩
    else ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteSuffixCommutationLaw_map]
    exact table.checkIdentityNat_sound
      finiteSuffixCommutationLaw (by decide)

theorem valid_head_eq (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.head = identity.rhs.head :=
  leftZeroValid_head_eq identity <|
    leftZeroEmbedding.pullback_identity identity valid

theorem valid_support (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ tested,
      tested ∈ identity.lhs.toList ↔
        tested ∈ identity.rhs.toList :=
  SemigroupBasis.Generated.CommutativePositiveModThreeTransfers.S4_125.valid_support
    identity <| residueEmbedding.pullback_identity identity valid

theorem valid_count_mod_three (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ tested,
      identity.lhs.toList.count tested % 3 =
        identity.rhs.toList.count tested % 3 :=
  SemigroupBasis.Generated.CommutativePositiveModThreeTransfers.S4_125.valid_count_mod_three
    identity <| residueEmbedding.pullback_identity identity valid

theorem representative_basis :
    BasisFor table.semigroup basis :=
  basis_complete_of_separates table models valid_head_eq
    valid_support valid_count_mod_three

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end S5_1152

end SemigroupBasis.CoRoots.S5_1146
