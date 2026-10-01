import SemigroupBasis.Examples.FirstCappedMultiplicityFour
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.EmbeddingTransfers
import SemigroupBasis.Generated.S3_8
import SemigroupBasis.Generated.S4_2
import SemigroupBasis.Subdirect

namespace SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap

open SemigroupBasis
open SemigroupBasis.Examples

def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := wordOfCons 0 [0]
def xxx : Word Nat := wordOfCons 0 [0, 0]
def xxy : Word Nat := wordOfCons 0 [0, 1]
def xyx : Word Nat := wordOfCons 0 [1, 0]
def yxx : Word Nat := wordOfCons 1 [0, 0]
def xyz : Word Nat := wordOfCons 0 [1, 2]
def xzy : Word Nat := wordOfCons 0 [2, 1]
def yxz : Word Nat := wordOfCons 1 [0, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def repeatedFirstLaw : Identity Nat := ⟨xxy, xyx⟩
def repeatedPrefixLaw : Identity Nat := ⟨xxy, yxx⟩
def suffixCommutationLaw : Identity Nat := ⟨xyz, xzy⟩
def prefixCommutationLaw : Identity Nat := ⟨xyz, yxz⟩

/-- The committed long-commutative-cap basis, in its fixed lane order. -/
def basis : List (Identity Nat) :=
  [powerLaw, repeatedFirstLaw, repeatedPrefixLaw,
    suffixCommutationLaw, prefixCommutationLaw]

def zyx : Word Nat := wordOfCons 2 [1, 0]
def yzx : Word Nat := wordOfCons 1 [2, 0]
def zxy : Word Nat := wordOfCons 2 [0, 1]

def expectedReversedBasis : List (Identity Nat) :=
  [⟨xx, xxx⟩, ⟨yxx, xyx⟩, ⟨yxx, xxy⟩,
    ⟨zyx, yzx⟩, ⟨zyx, zxy⟩]

theorem reversedBasis_eq_expected :
    reversedBasis basis = expectedReversedBasis := by
  rfl

def candidateBasisSHA256 : String :=
  "f2611117594616699fa99f971106a3358185886c7c3d12548265b86e2425ce86"

def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem capModels :
    Models SemigroupBasis.Generated.S3_8.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_8.table basis toFinThree (by decide)

theorem shortModels :
    Models SemigroupBasis.Generated.S4_2.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_2.table basis toFinThree (by decide)

/-- `S3_8` and `S4_47` expose the same complete commutative exponent-three
theory. This is the only non-reflexive factor equivalence needed below. -/
theorem s3_8_s4_47_sameTheory (identity : Identity Nat) :
    identity.SatisfiedBy
        SemigroupBasis.Generated.S3_8.table.semigroup ↔
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S4_47.table.semigroup := by
  constructor
  · intro valid
    have derivation :=
      SemigroupBasis.Generated.S3_8.representative_basis.2 identity valid
    exact derivation.sound
      SemigroupBasis.Generated.EmbeddingTransfers.S4_47.representative_basis.1
  · intro valid
    have derivation :=
      SemigroupBasis.Generated.EmbeddingTransfers.S4_47.representative_basis.2
        identity valid
    exact derivation.sound
      SemigroupBasis.Generated.S3_8.representative_basis.1

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

/-- Swap the last two nonempty blocks after a fixed nonempty prefix. -/
theorem derivesSuffixSwap (pre u v : Word Nat) :
    Derives basis ((pre ++ u) ++ v) ((pre ++ v) ++ u) := by
  have base : Derives basis xyz xzy :=
    Derives.fromBasis (e := suffixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateThreeWords pre u v)
  have sourceEq :
      xyz.bind (instantiateThreeWords pre u v) = (pre ++ u) ++ v := by
    apply Word.toList_injective
    simp [xyz, wordOfCons, instantiateThreeWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  have targetEq :
      xzy.bind (instantiateThreeWords pre u v) = (pre ++ v) ++ u := by
    apply Word.toList_injective
    simp [xzy, wordOfCons, instantiateThreeWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  rw [sourceEq, targetEq] at substituted
  exact substituted

/-- Swap the first two nonempty blocks before a fixed nonempty suffix. -/
theorem derivesPrefixSwap (u v suffix : Word Nat) :
    Derives basis ((u ++ v) ++ suffix) ((v ++ u) ++ suffix) := by
  have base : Derives basis xyz yxz :=
    Derives.fromBasis (e := prefixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateThreeWords u v suffix)
  have sourceEq :
      xyz.bind (instantiateThreeWords u v suffix) = (u ++ v) ++ suffix := by
    apply Word.toList_injective
    simp [xyz, wordOfCons, instantiateThreeWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  have targetEq :
      yxz.bind (instantiateThreeWords u v suffix) = (v ++ u) ++ suffix := by
    apply Word.toList_injective
    simp [yxz, wordOfCons, instantiateThreeWords, Word.toList_bind,
      Word.toList_append, Word.bind, Word.append, Word.toList,
      List.append_assoc]
  rw [sourceEq, targetEq] at substituted
  exact substituted

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives basis (wordOfCons x xs) (wordOfCons y ys) →
      ListDerives (x :: xs) (y :: ys)

private theorem ListDerives.trans {xs ys zs : List Nat}
    (first : ListDerives xs ys) (second : ListDerives ys zs) :
    ListDerives xs zs := by
  cases first with
  | empty =>
      cases second
      exact ListDerives.empty
  | words firstProof =>
      cases second with
      | words secondProof =>
          exact ListDerives.words
            (Derives.trans firstProof secondProof)

private theorem listDerives_of_perm_with_prefix
    (pre : List Nat) {xs ys : List Nat}
    (permutation : xs.Perm ys)
    (long : 3 ≤ (pre ++ xs).length) :
    ListDerives (pre ++ xs) (pre ++ ys) := by
  induction permutation generalizing pre with
  | nil =>
      cases pre with
      | nil => simp at long
      | cons p ps => exact ListDerives.words (Derives.refl _)
  | cons x permutation ih =>
      have next :=
        ih (pre := pre ++ [x]) <| by
          simpa [List.append_assoc] using long
      simpa [List.append_assoc] using next
  | swap x y xs =>
      cases pre with
      | nil =>
          cases xs with
          | nil => simp at long
          | cons z zs =>
              exact ListDerives.words <| by
                simpa [wordOfCons, Word.singleton, Word.append,
                  Word.append_assoc] using
                    derivesPrefixSwap
                      (Word.singleton y) (Word.singleton x)
                      (wordOfCons z zs)
      | cons p ps =>
          cases xs with
          | nil =>
              exact ListDerives.words <| by
                simpa [wordOfCons, Word.singleton, Word.append,
                  Word.append_assoc] using
                    derivesSuffixSwap
                      (wordOfCons p ps) (Word.singleton y)
                      (Word.singleton x)
          | cons z zs =>
              have swapped :=
                Derives.appendRight
                  (derivesSuffixSwap
                    (wordOfCons p ps) (Word.singleton y)
                    (Word.singleton x))
                  (wordOfCons z zs)
              exact ListDerives.words <| by
                simpa [wordOfCons, Word.singleton, Word.append,
                  Word.append_assoc] using swapped
  | trans first second ihFirst ihSecond =>
      have firstDerivation := ihFirst (pre := pre) long
      have secondDerivation :=
        ihSecond (pre := pre) <| by
          rw [List.length_append, ← first.length_eq]
          simpa [List.length_append] using long
      exact firstDerivation.trans secondDerivation

/-- Every permutation of a word of length at least three is derivable from
the two long commutation laws. -/
theorem derivesLongPermutation (u v : Word Nat)
    (long : 3 ≤ u.toList.length)
    (permutation : u.toList.Perm v.toList) :
    Derives basis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          have lifted :=
            listDerives_of_perm_with_prefix []
              (xs := uHead :: uTail) (ys := vHead :: vTail)
              permutation long
          cases lifted with
          | words derivation => exact derivation

private theorem firstCappedAxiomsDerive
    (identity : Identity Nat)
    (member : identity ∈ firstCappedMultiplicityFourBasis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [firstCappedMultiplicityFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact Derives.fromBasis (e := powerLaw) <| List.Mem.head _
  · exact Derives.fromBasis (e := repeatedFirstLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  · exact Derives.fromBasis (e := suffixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _

theorem derivesFirstCapped {u v : Word Nat}
    (derivation : Derives firstCappedMultiplicityFourBasis u v) :
    Derives basis u v :=
  derivation.transport firstCappedAxiomsDerive

/-- The `S4_2` short-word factor has literal projections and ordered
off-diagonal pairs; every square and every word of length at least three is
in its remaining bulk class. -/
def IsBulk (word : Word Nat) : Prop :=
  (∃ x, word = wordOfCons x [x]) ∨ 3 ≤ word.toList.length

def ShortClass (left right : Word Nat) : Prop :=
  left = right ∨ (IsBulk left ∧ IsBulk right)

private theorem shortClass_symm {left right : Word Nat}
    (same : ShortClass left right) :
    ShortClass right left := by
  rcases same with equal | bulk
  · exact Or.inl equal.symm
  · exact Or.inr ⟨bulk.2, bulk.1⟩

private theorem shortClass_trans {left middle right : Word Nat}
    (first : ShortClass left middle)
    (second : ShortClass middle right) :
    ShortClass left right := by
  rcases first with equal | firstBulk
  · subst middle
    exact second
  · rcases second with equal | secondBulk
    · subst right
      exact Or.inr firstBulk
    · exact Or.inr ⟨firstBulk.1, secondBulk.2⟩

private theorem wordLengthPositive (word : Word Nat) :
    1 ≤ word.toList.length := by
  cases word
  simp [Word.toList]

private theorem bulkLengthAtLeastTwo {word : Word Nat}
    (bulk : IsBulk word) :
    2 ≤ word.toList.length := by
  rcases bulk with ⟨x, rfl⟩ | long
  · simp [wordOfCons, Word.toList]
  · omega

private theorem bulk_prepend (pre : Word Nat) {word : Word Nat}
    (bulk : IsBulk word) :
    IsBulk (pre ++ word) := by
  right
  rw [Word.toList_append, List.length_append]
  have prefixPositive := wordLengthPositive pre
  have wordTwo := bulkLengthAtLeastTwo bulk
  omega

private theorem bulk_append (suffix : Word Nat) {word : Word Nat}
    (bulk : IsBulk word) :
    IsBulk (word ++ suffix) := by
  right
  rw [Word.toList_append, List.length_append]
  have suffixPositive := wordLengthPositive suffix
  have wordTwo := bulkLengthAtLeastTwo bulk
  omega

private theorem list_length_le_flatMap_words
    (letters : List Nat) (substitution : Nat → Word Nat) :
    letters.length ≤
      (letters.flatMap fun letter =>
        (substitution letter).toList).length := by
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have imagePositive := wordLengthPositive (substitution letter)
      omega

private theorem bind_preserves_length
    (word : Word Nat) (substitution : Nat → Word Nat)
    {bound : Nat} (long : bound ≤ word.toList.length) :
    bound ≤ (word.bind substitution).toList.length := by
  rw [Word.toList_bind]
  exact Nat.le_trans long
    (list_length_le_flatMap_words word.toList substitution)

private theorem bulk_bind (substitution : Nat → Word Nat)
    {word : Word Nat} (bulk : IsBulk word) :
    IsBulk (word.bind substitution) := by
  rcases bulk with ⟨x, rfl⟩ | long
  · cases image : substitution x with
    | mk head tail =>
        cases tail with
        | nil =>
            left
            refine ⟨head, ?_⟩
            apply Word.toList_injective
            rw [Word.toList_bind]
            simp [wordOfCons, Word.toList, image]
        | cons next rest =>
            right
            rw [Word.toList_bind]
            simp [wordOfCons, Word.toList, image, List.length_append]
            omega
  · exact Or.inr (bind_preserves_length word substitution long)

private theorem shortClass_prepend (pre : Word Nat)
    {left right : Word Nat} (same : ShortClass left right) :
    ShortClass (pre ++ left) (pre ++ right) := by
  rcases same with equal | bulk
  · exact Or.inl (congrArg (fun word => pre ++ word) equal)
  · exact Or.inr
      ⟨bulk_prepend pre bulk.1, bulk_prepend pre bulk.2⟩

private theorem shortClass_append (suffix : Word Nat)
    {left right : Word Nat} (same : ShortClass left right) :
    ShortClass (left ++ suffix) (right ++ suffix) := by
  rcases same with equal | bulk
  · exact Or.inl (congrArg (fun word => word ++ suffix) equal)
  · exact Or.inr
      ⟨bulk_append suffix bulk.1, bulk_append suffix bulk.2⟩

private theorem shortClass_bind (substitution : Nat → Word Nat)
    {left right : Word Nat} (same : ShortClass left right) :
    ShortClass (left.bind substitution) (right.bind substitution) := by
  rcases same with equal | bulk
  · exact Or.inl (congrArg (fun word => word.bind substitution) equal)
  · exact Or.inr
      ⟨bulk_bind substitution bulk.1, bulk_bind substitution bulk.2⟩

private theorem shortBasisMemberClass
    (identity : Identity Nat)
    (member : identity ∈ commonSquareThreeNilpotentBasis) :
    ShortClass identity.lhs identity.rhs := by
  simp only [commonSquareThreeNilpotentBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Or.inr <| by
      constructor <;> left
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  · exact Or.inr <| by
      constructor
      · exact Or.inl ⟨0, rfl⟩
      · exact Or.inr <| by
          simp [commonSquareThreeNilpotentLongLaw,
            commonSquareThreeNilpotentXYZ, Word.toList]

private theorem shortDerivationClass {left right : Word Nat}
    (derivation : Derives commonSquareThreeNilpotentBasis left right) :
    ShortClass left right := by
  induction derivation with
  | fromBasis member =>
      exact shortBasisMemberClass _ member
  | refl =>
      exact Or.inl rfl
  | symm _ ih =>
      exact shortClass_symm ih
  | trans _ _ ihFirst ihSecond =>
      exact shortClass_trans ihFirst ihSecond
  | prepend pre _ ih =>
      exact shortClass_prepend pre ih
  | appendRight _ suffix ih =>
      exact shortClass_append suffix ih
  | subst _ substitution ih =>
      exact shortClass_bind substitution ih

theorem shortClass_of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_2.table.semigroup) :
    ShortClass identity.lhs identity.rhs := by
  have derivation :=
    SemigroupBasis.Generated.S4_2.representative_basis.2 identity valid
  exact shortDerivationClass derivation

private theorem normalPermutation (identity : Identity Nat)
    (counts : ∀ z,
      min (identity.lhs.toList.count z) 2 =
        min (identity.rhs.toList.count z) 2) :
    (firstCappedNormal identity.lhs).toList.Perm
      (firstCappedNormal identity.rhs).toList := by
  rw [List.perm_iff_count]
  intro z
  rw [firstCappedNormal_count, firstCappedNormal_count, counts z]

private theorem normalizedShortValid (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_2.table.semigroup) :
    (⟨firstCappedNormal identity.lhs,
        firstCappedNormal identity.rhs⟩ : Identity Nat).SatisfiedBy
      SemigroupBasis.Generated.S4_2.table.semigroup := by
  intro valuation
  have leftNormal :=
    derivesFirstCapped (firstCappedDerivesNormal identity.lhs)
  have rightNormal :=
    derivesFirstCapped (firstCappedDerivesNormal identity.rhs)
  exact (leftNormal.sound shortModels valuation).symm.trans <|
    (valid valuation).trans (rightNormal.sound shortModels valuation)

private theorem squareWordsEqualOfPermutation
    {left right : Word Nat} {x y : Nat}
    (leftSquare : left = wordOfCons x [x])
    (rightSquare : right = wordOfCons y [y])
    (permutation : left.toList.Perm right.toList) :
    left = right := by
  have squarePermutation : [x, x].Perm [y, y] := by
    simpa [leftSquare, rightSquare, wordOfCons, Word.toList] using permutation
  have xMember : x ∈ [y, y] :=
    squarePermutation.mem_iff.mp (by simp)
  have equal : x = y := by simpa using xMember
  subst y
  exact leftSquare.trans rightSquare.symm

/-- Completeness of the five laws for the intersection of the cap and short
factor theories. The finite factors supply capped multiplicities and the
short/bulk dichotomy; the proof itself is unrestricted in word length and
variable support. -/
theorem derives_of_factor_valid (identity : Identity Nat)
    (capValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_8.table.semigroup)
    (shortValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_2.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  rcases shortClass_of_valid identity shortValid with equal | bulk
  · rw [equal]
    exact Derives.refl _
  · have counts := exponentValid_capped_count_eq identity capValid
    have permutation := normalPermutation identity counts
    have leftNormal :=
      derivesFirstCapped (firstCappedDerivesNormal identity.lhs)
    have rightNormal :=
      derivesFirstCapped (firstCappedDerivesNormal identity.rhs)
    have normalClass :
        ShortClass (firstCappedNormal identity.lhs)
          (firstCappedNormal identity.rhs) :=
      shortClass_of_valid
        ⟨firstCappedNormal identity.lhs,
          firstCappedNormal identity.rhs⟩
        (normalizedShortValid identity shortValid)
    have middle :
        Derives basis (firstCappedNormal identity.lhs)
          (firstCappedNormal identity.rhs) := by
      rcases normalClass with normalEqual | normalBulk
      · rw [normalEqual]
        exact Derives.refl _
      · rcases normalBulk.1 with ⟨x, leftSquare⟩ | leftLong
        · rcases normalBulk.2 with ⟨y, rightSquare⟩ | rightLong
          · have normalEqual :=
              squareWordsEqualOfPermutation
                leftSquare rightSquare permutation
            rw [normalEqual]
            exact Derives.refl _
          · have rightLengthTwo :
                (firstCappedNormal identity.rhs).toList.length = 2 := by
              calc
                (firstCappedNormal identity.rhs).toList.length =
                    (firstCappedNormal identity.lhs).toList.length :=
                  permutation.length_eq.symm
                _ = 2 := by
                  simp [leftSquare, wordOfCons, Word.toList]
            rw [rightLengthTwo] at rightLong
            omega
        · exact derivesLongPermutation _ _ leftLong permutation
    exact Derives.trans leftNormal <|
      Derives.trans middle (Derives.symm rightNormal)

def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.S4_2.table.semigroup basis where
  leftModels := capModels
  rightModels := shortModels
  complete := derives_of_factor_valid

end SemigroupBasis.Order6.FactorIntersection.LongCommutativeCap
