import SemigroupBasis.Examples.CommutativeParityThree
import SemigroupBasis.Generated.S3_10
import SemigroupBasis.Generated.S3_11
import SemigroupBasis.Generated.S4_2
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityBulkShort

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxxy : Word Nat := w 0 [0, 0, 1]
def xyyy : Word Nat := w 0 [1, 1, 1]
def xxxyz : Word Nat := w 0 [0, 0, 1, 2]
def xxy : Word Nat := w 0 [0, 1]
def xxyyy : Word Nat := w 0 [0, 1, 1, 1]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xyz : Word Nat := w 0 [1, 2]
def xzy : Word Nat := w 0 [2, 1]
def yxz : Word Nat := w 1 [0, 2]

def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def quarticTransferLaw : Identity Nat := ⟨xxxy, xyyy⟩
def longInsertionLaw : Identity Nat := ⟨xxxyz, xyz⟩
def rightPowerLaw : Identity Nat := ⟨xxy, xxyyy⟩
def repeatedMiddleLaw : Identity Nat := ⟨xxy, xyx⟩
def repeatedPrefixLaw : Identity Nat := ⟨xxy, yxx⟩
def suffixCommutationLaw : Identity Nat := ⟨xyz, xzy⟩
def prefixCommutationLaw : Identity Nat := ⟨xyz, yxz⟩

/-- The exact positive-parity/bulk-short candidate basis, in contract order. -/
def basis : List (Identity Nat) :=
  [powerLaw, quarticTransferLaw, longInsertionLaw, rightPowerLaw,
    repeatedMiddleLaw, repeatedPrefixLaw, suffixCommutationLaw,
    prefixCommutationLaw]

def candidateBasisUpToOppositeSHA256 : String :=
  "f278b63c05cfad40c5a95380389c72666303328abfb6826b434b0b88570f0e7d"

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem s3_10_models :
    Models SemigroupBasis.Generated.S3_10.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_10.table basis toFinThree (by decide)

theorem s3_11_models :
    Models SemigroupBasis.Generated.S3_11.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_11.table basis toFinThree (by decide)

theorem s4_2_models :
    Models SemigroupBasis.Generated.S4_2.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_2.table basis toFinThree (by decide)

private def instantiateThreeWords
    (u v q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => q
  | n + 3 => Word.singleton (n + 3)

/-- Swap the final two nonempty blocks after a fixed nonempty prefix. -/
theorem derivesSuffixSwap (pre u v : Word Nat) :
    Derives basis ((pre ++ u) ++ v) ((pre ++ v) ++ u) := by
  have base : Derives basis xyz xzy :=
    Derives.fromBasis (e := suffixCommutationLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords pre u v)
  simpa [basis, suffixCommutationLaw, xyz, xzy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Swap the first two nonempty blocks before a fixed nonempty suffix. -/
theorem derivesPrefixSwap (u v suffix : Word Nat) :
    Derives basis ((u ++ v) ++ suffix) ((v ++ u) ++ suffix) := by
  have base : Derives basis xyz yxz :=
    Derives.fromBasis (e := prefixCommutationLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v suffix)
  simpa [basis, prefixCommutationLaw, xyz, yxz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives basis (w x xs) (w y ys) →
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
                simpa [w, Word.singleton, Word.append,
                  Word.append_assoc] using
                    derivesPrefixSwap
                      (Word.singleton y) (Word.singleton x)
                      (w z zs)
      | cons p ps =>
          cases xs with
          | nil =>
              exact ListDerives.words <| by
                simpa [w, Word.singleton, Word.append,
                  Word.append_assoc] using
                    derivesSuffixSwap
                      (w p ps) (Word.singleton y)
                      (Word.singleton x)
          | cons z zs =>
              have swapped :=
                Derives.appendRight
                  (derivesSuffixSwap
                    (w p ps) (Word.singleton y)
                    (Word.singleton x))
                  (w z zs)
              exact ListDerives.words <| by
                simpa [w, Word.singleton, Word.append,
                  Word.append_assoc] using swapped
  | trans first second ihFirst ihSecond =>
      have firstDerivation := ihFirst (pre := pre) long
      have secondDerivation :=
        ihSecond (pre := pre) <| by
          rw [List.length_append, ← first.length_eq]
          simpa [List.length_append] using long
      exact firstDerivation.trans secondDerivation

/-- Every permutation of a word of length at least three is derivable. -/
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

/-- Insert two additional copies of the first block in a product of three
nonempty blocks. -/
theorem derivesLongInsertion (u v q : Word Nat) :
    Derives basis ((u ++ v) ++ q)
      ((((u ++ u) ++ u) ++ v) ++ q) := by
  have base : Derives basis xyz xxxyz :=
    Derives.symm <|
      Derives.fromBasis (e := longInsertionLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords u v q)
  simpa [basis, longInsertionLaw, xyz, xxxyz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem parityDerivesOfSupportParity
    (u v : Word Nat)
    (supportEq : ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parityEq : ∀ z,
      u.toList.count z % 2 = v.toList.count z % 2) :
    Derives commutativeParityBasis u v := by
  have reducedPerm :=
    positiveParityReduce_perm supportEq parityEq
  have lhsNormal := positiveParityDerivesNormal u
  have rhsNormal := positiveParityDerivesNormal v
  cases hl : positiveParityReduce u.toList with
  | nil =>
      have present :
          u.head ∈ positiveParityReduce u.toList :=
        (mem_positiveParityReduce_iff _ _).mpr
          (by simp [Word.toList])
      exact False.elim (by simpa [hl] using present)
  | cons x xs =>
      cases hr : positiveParityReduce v.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (parityDerivesPermutation
                (w x xs) (w y ys) reducedPerm)
              (Derives.symm rhsNormal)

private theorem bind_append (u v : Word Nat) (σ : Nat → Word Nat) :
    (u ++ v).bind σ = u.bind σ ++ v.bind σ := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (τ σ : Nat → Word Nat) :
    (word.bind τ).bind σ =
      word.bind (fun x => (τ x).bind σ) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem wordLengthPositive (word : Word Nat) :
    1 ≤ word.toList.length := by
  cases word
  simp [Word.toList]

/-- `S4_2` keeps projections and ordered off-diagonal pairs literal. Squares
and every word of length at least three form its remaining class. -/
def IsBulk (word : Word Nat) : Prop :=
  (∃ letter, word = w letter [letter]) ∨ 3 ≤ word.toList.length

private def ShortClass (left right : Word Nat) : Prop :=
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

private theorem bulkLengthAtLeastTwo {word : Word Nat}
    (bulk : IsBulk word) :
    2 ≤ word.toList.length := by
  rcases bulk with ⟨letter, rfl⟩ | long
  · simp [w, Word.toList]
  · omega

private theorem bulk_prepend (pre : Word Nat) {word : Word Nat}
    (bulk : IsBulk word) :
    IsBulk (pre ++ word) := by
  right
  rw [Word.toList_append, List.length_append]
  have prePositive := wordLengthPositive pre
  have wordTwo := bulkLengthAtLeastTwo bulk
  omega

private theorem bulk_append (post : Word Nat) {word : Word Nat}
    (bulk : IsBulk word) :
    IsBulk (word ++ post) := by
  right
  rw [Word.toList_append, List.length_append]
  have postPositive := wordLengthPositive post
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
  rcases bulk with ⟨letter, rfl⟩ | long
  · have bindSquare :
        (w letter [letter]).bind substitution =
          substitution letter ++ substitution letter := rfl
    cases image : substitution letter with
    | mk head tail =>
        cases tail with
        | nil =>
            left
            refine ⟨head, ?_⟩
            rw [bindSquare, image]
            rfl
        | cons next rest =>
            right
            rw [bindSquare, Word.toList_append,
              List.length_append]
            simp [image, Word.toList]
            omega
  · exact Or.inr (bind_preserves_length word substitution long)

private theorem shortClass_prepend (pre : Word Nat)
    {left right : Word Nat} (same : ShortClass left right) :
    ShortClass (pre ++ left) (pre ++ right) := by
  rcases same with equal | bulk
  · exact Or.inl (congrArg (fun word => pre ++ word) equal)
  · exact Or.inr
      ⟨bulk_prepend pre bulk.1, bulk_prepend pre bulk.2⟩

private theorem shortClass_append (post : Word Nat)
    {left right : Word Nat} (same : ShortClass left right) :
    ShortClass (left ++ post) (right ++ post) := by
  rcases same with equal | bulk
  · exact Or.inl (congrArg (fun word => word ++ post) equal)
  · exact Or.inr
      ⟨bulk_append post bulk.1, bulk_append post bulk.2⟩

private theorem shortClass_bind (substitution : Nat → Word Nat)
    {left right : Word Nat} (same : ShortClass left right) :
    ShortClass (left.bind substitution) (right.bind substitution) := by
  rcases same with equal | bulk
  · exact Or.inl
      (congrArg (fun word => word.bind substitution) equal)
  · exact Or.inr
      ⟨bulk_bind substitution bulk.1,
        bulk_bind substitution bulk.2⟩

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
    (derivation :
      Derives commonSquareThreeNilpotentBasis left right) :
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
  | appendRight _ post ih =>
      exact shortClass_append post ih
  | subst _ substitution ih =>
      exact shortClass_bind substitution ih

private theorem shortClass_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_2.table.semigroup) :
    ShortClass identity.lhs identity.rhs := by
  have derivation :=
    SemigroupBasis.Generated.S4_2.representative_basis.2
      identity valid
  exact shortDerivationClass derivation

/-- The parity power step is available after two fixed nonempty markers. -/
theorem derivesContextPower (a b u : Word Nat) :
    Derives basis ((a ++ b) ++ u)
      ((a ++ b) ++ ((u ++ u) ++ u)) := by
  have enter :
      Derives basis ((a ++ b) ++ u) ((u ++ a) ++ b) := by
    apply derivesLongPermutation
    · simp only [Word.toList_append, List.length_append]
      have ha := wordLengthPositive a
      have hb := wordLengthPositive b
      have hu := wordLengthPositive u
      omega
    · rw [List.perm_iff_count]
      intro z
      simp only [Word.toList_append, List.count_append]
      omega
  have expand := derivesLongInsertion u a b
  have exit :
      Derives basis ((((u ++ u) ++ u) ++ a) ++ b)
        ((a ++ b) ++ ((u ++ u) ++ u)) := by
    apply derivesLongPermutation
    · simp only [Word.toList_append, List.length_append]
      have ha := wordLengthPositive a
      have hb := wordLengthPositive b
      have hu := wordLengthPositive u
      omega
    · rw [List.perm_iff_count]
      intro z
      simp only [Word.toList_append, List.count_append]
      omega
  exact enter.trans (expand.trans exit)

/-- Replay `x = xxx`, `xy = yx` after two fixed nonempty markers. -/
theorem liftParity
    {u v : Word Nat}
    (derivation : Derives commutativeParityBasis u v)
    (a b : Word Nat) (σ : Nat → Word Nat) :
    Derives basis
      ((a ++ b) ++ u.bind σ)
      ((a ++ b) ++ v.bind σ) := by
  induction derivation generalizing a b σ with
  | fromBasis member =>
      simp only [commutativeParityBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [parityPowerLaw, parityX, parityXXX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          derivesContextPower a b (σ 0)
      · simpa [parityCommutativityLaw, parityXY, parityYX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc]
          using derivesSuffixSwap (a ++ b) (σ 0) (σ 1)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih a b σ)
  | trans _ _ ihFirst ihSecond =>
      exact Derives.trans (ihFirst a b σ) (ihSecond a b σ)
  | prepend pre _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih a (b ++ pre.bind σ) σ
  | appendRight _ post ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (ih a b σ) (post.bind σ)
  | subst _ τ ih =>
      simpa [bind_bind] using
        ih a b (fun x => (τ x).bind σ)

private def frontedWord (letter : Nat) (word : Word Nat) : Word Nat :=
  w letter (word.toList.erase letter)

private theorem word_perm_frontedWord
    (letter : Nat) (word : Word Nat)
    (present : letter ∈ word.toList) :
    word.toList.Perm (frontedWord letter word).toList := by
  simpa [frontedWord, w, Word.toList] using
    List.perm_cons_erase present

private theorem derivesHeadExpansion
    (letter a b : Nat) (rest : List Nat) :
    Derives basis (w letter (a :: b :: rest))
      ((Word.singleton letter ++ Word.singleton letter) ++
        w letter (a :: b :: rest)) := by
  simpa [w, Word.singleton, Word.append, Word.append_assoc] using
    derivesLongInsertion
      (Word.singleton letter) (Word.singleton a) (w b rest)

/-- Long words are classified exactly by support and positive parity. -/
theorem derivesLongSupportParity
    (u v : Word Nat)
    (uLong : 3 ≤ u.toList.length)
    (vLong : 3 ≤ v.toList.length)
    (supportEq : ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parityEq : ∀ z,
      u.toList.count z % 2 = v.toList.count z % 2) :
    Derives basis u v := by
  let marker := u.head
  have markerInU : marker ∈ u.toList := by
    simp [marker, Word.toList]
  have markerInV : marker ∈ v.toList :=
    (supportEq marker).mp markerInU
  let uFront := frontedWord marker u
  let vFront := frontedWord marker v
  have uPerm : u.toList.Perm uFront.toList :=
    word_perm_frontedWord marker u markerInU
  have vPerm : v.toList.Perm vFront.toList :=
    word_perm_frontedWord marker v markerInV
  have uToFront := derivesLongPermutation u uFront uLong uPerm
  have vToFront := derivesLongPermutation v vFront vLong vPerm
  have uCount : ∀ z,
      u.toList.count z = uFront.toList.count z :=
    List.perm_iff_count.mp uPerm
  have vCount : ∀ z,
      v.toList.count z = vFront.toList.count z :=
    List.perm_iff_count.mp vPerm
  have frontSupport : ∀ z,
      z ∈ uFront.toList ↔ z ∈ vFront.toList := by
    intro z
    rw [← List.count_pos_iff, ← List.count_pos_iff,
      ← uCount z, ← vCount z, List.count_pos_iff,
      List.count_pos_iff]
    exact supportEq z
  have frontParity : ∀ z,
      uFront.toList.count z % 2 =
        vFront.toList.count z % 2 := by
    intro z
    rw [← uCount z, ← vCount z]
    exact parityEq z
  have parityDerivation :=
    parityDerivesOfSupportParity
      uFront vFront frontSupport frontParity
  have lifted :=
    liftParity parityDerivation
      (Word.singleton marker) (Word.singleton marker) Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  cases hu : u.toList.erase marker with
  | nil =>
      have eraseLength := List.length_erase_of_mem markerInU
      rw [hu] at eraseLength
      simp at eraseLength
      omega
  | cons ua ut =>
      cases ut with
      | nil =>
          have eraseLength := List.length_erase_of_mem markerInU
          rw [hu] at eraseLength
          simp at eraseLength
          omega
      | cons ub ur =>
          cases hv : v.toList.erase marker with
          | nil =>
              have eraseLength := List.length_erase_of_mem markerInV
              rw [hv] at eraseLength
              simp at eraseLength
              omega
          | cons va vt =>
              cases vt with
              | nil =>
                  have eraseLength := List.length_erase_of_mem markerInV
                  rw [hv] at eraseLength
                  simp at eraseLength
                  omega
              | cons vb vr =>
                  have expandU :
                      Derives basis uFront
                        ((Word.singleton marker ++
                            Word.singleton marker) ++ uFront) := by
                    simpa [uFront, frontedWord, hu] using
                      derivesHeadExpansion marker ua ub ur
                  have expandV :
                      Derives basis vFront
                        ((Word.singleton marker ++
                            Word.singleton marker) ++ vFront) := by
                    simpa [vFront, frontedWord, hv] using
                      derivesHeadExpansion marker va vb vr
                  exact uToFront.trans <|
                    expandU.trans <|
                    lifted.trans <|
                    (Derives.symm expandV).trans
                      (Derives.symm vToFront)

private def instantiateOneWord (u : Word Nat) : Nat → Word Nat
  | 0 => u
  | n + 1 => Word.singleton (n + 1)

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) (((u ++ u) ++ u) ++ u) := by
  have base : Derives basis xx xxxx :=
    Derives.fromBasis (e := powerLaw) (by simp [basis])
  have substituted := Derives.subst base (instantiateOneWord u)
  simpa [basis, powerLaw, xx, xxxx, w, instantiateOneWord,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem bulk_has_long_representative
    (word : Word Nat)
    (bulk : IsBulk word) :
    ∃ longWord,
      Derives basis word longWord ∧
        3 ≤ longWord.toList.length := by
  rcases bulk with ⟨letter, rfl⟩ | long
  · refine ⟨
      w letter [letter, letter, letter], ?_, ?_⟩
    · simpa [
        w,
        Word.singleton, Word.append, Word.append_assoc] using
          derivesPowerExpansion (Word.singleton letter)
    · simp [w, Word.toList]
  · exact ⟨word, Derives.refl _, long⟩

private theorem derives_of_factor_valid
    (factor : FiniteTable)
    (factorModels : Models factor.semigroup basis)
    (supportOfValid : ∀ identity : Identity Nat,
      identity.SatisfiedBy factor.semigroup →
        ∀ z, z ∈ identity.lhs.toList ↔ z ∈ identity.rhs.toList)
    (parityOfValid : ∀ identity : Identity Nat,
      identity.SatisfiedBy factor.semigroup →
        ∀ z, identity.lhs.toList.count z % 2 =
          identity.rhs.toList.count z % 2)
    (identity : Identity Nat)
    (factorValid : identity.SatisfiedBy factor.semigroup)
    (shortValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_2.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  rcases shortClass_of_valid identity shortValid with equal | bulk
  · rw [equal]
    exact Derives.refl _
  · obtain ⟨leftLong, leftDerivation, leftLength⟩ :=
      bulk_has_long_representative identity.lhs bulk.1
    obtain ⟨rightLong, rightDerivation, rightLength⟩ :=
      bulk_has_long_representative identity.rhs bulk.2
    let normalized : Identity Nat := ⟨leftLong, rightLong⟩
    have normalizedValid : normalized.SatisfiedBy factor.semigroup := by
      intro valuation
      exact
        (leftDerivation.sound factorModels valuation).symm.trans <|
          (factorValid valuation).trans
            (rightDerivation.sound factorModels valuation)
    have middle :=
      derivesLongSupportParity leftLong rightLong
        leftLength rightLength
        (supportOfValid normalized normalizedValid)
        (parityOfValid normalized normalizedValid)
    exact leftDerivation.trans <|
      middle.trans (Derives.symm rightDerivation)

private theorem s3_10_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_10.table.semigroup) :
    ∀ z, z ∈ identity.lhs.toList ↔ z ∈ identity.rhs.toList := by
  simpa [SemigroupBasis.Generated.S3_10.table,
    parityIdentityThree] using
      parityIdentityValid_support identity valid

private theorem s3_10_parity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_10.table.semigroup) :
    ∀ z, identity.lhs.toList.count z % 2 =
      identity.rhs.toList.count z % 2 := by
  simpa [SemigroupBasis.Generated.S3_10.table,
    parityIdentityThree] using
      parityIdentityValid_parity identity valid

private theorem s3_11_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_11.table.semigroup) :
    ∀ z, z ∈ identity.lhs.toList ↔ z ∈ identity.rhs.toList := by
  simpa [SemigroupBasis.Generated.S3_11.table,
    parityZeroThree] using
      parityZeroValid_support identity valid

private theorem s3_11_parity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_11.table.semigroup) :
    ∀ z, identity.lhs.toList.count z % 2 =
      identity.rhs.toList.count z % 2 := by
  simpa [SemigroupBasis.Generated.S3_11.table,
    parityZeroThree] using
      parityZeroValid_parity identity valid

theorem derives_of_s3_10_s4_2_valid
    (identity : Identity Nat)
    (stateValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_10.table.semigroup)
    (shortValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_2.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derives_of_factor_valid SemigroupBasis.Generated.S3_10.table
    s3_10_models s3_10_support s3_10_parity
    identity stateValid shortValid

theorem derives_of_s3_11_s4_2_valid
    (identity : Identity Nat)
    (stateValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_11.table.semigroup)
    (shortValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S4_2.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derives_of_factor_valid SemigroupBasis.Generated.S3_11.table
    s3_11_models s3_11_support s3_11_parity
    identity stateValid shortValid

def s3_10IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_10.table.semigroup
      SemigroupBasis.Generated.S4_2.table.semigroup basis where
  leftModels := s3_10_models
  rightModels := s4_2_models
  complete := derives_of_s3_10_s4_2_valid

def s3_11IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.S4_2.table.semigroup basis where
  leftModels := s3_11_models
  rightModels := s4_2_models
  complete := derives_of_s3_11_s4_2_valid

end SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityBulkShort
