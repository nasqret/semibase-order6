import SemigroupBasis.CoRoots.S5_55Family
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6ParityLengthThreshold

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

def xxxx : Word Nat := w 0 [0, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xxxy : Word Nat := w 0 [0, 0, 1]
def xyyy : Word Nat := w 0 [1, 1, 1]
def xyzz : Word Nat := w 0 [1, 2, 2]
def xxyzth : Word Nat := w 0 [0, 1, 2, 3, 4]
def yzth : Word Nat := w 1 [2, 3, 4]
def xxy : Word Nat := w 0 [0, 1]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xyz : Word Nat := w 0 [1, 2]
def xzy : Word Nat := w 0 [2, 1]
def yxz : Word Nat := w 1 [0, 2]

def quarticPairLaw : Identity Nat := Identity.mk xxxx xxyy
def oddPairTransferLaw : Identity Nat := Identity.mk xxxy xyyy
def freshPairTransferLaw : Identity Nat := Identity.mk xxxy xyzz
def contextualPairDeletionLaw : Identity Nat := Identity.mk xxyzth yzth
def repeatedMiddleLaw : Identity Nat := Identity.mk xxy xyx
def repeatedPrefixLaw : Identity Nat := Identity.mk xxy yxx
def suffixCommutationLaw : Identity Nat := Identity.mk xyz xzy
def prefixCommutationLaw : Identity Nat := Identity.mk xyz yxz

/-- The exact eight-law parity/length-threshold basis. -/
def basis : List (Identity Nat) :=
  [quarticPairLaw, oddPairTransferLaw, freshPairTransferLaw,
    contextualPairDeletionLaw, repeatedMiddleLaw, repeatedPrefixLaw,
    suffixCommutationLaw, prefixCommutationLaw]

def candidateBasisUpToOppositeSHA256 : String :=
  "9439553116916c0a7f253ea64fc5b43ce0ff2ed6115b420666689830fd62a98c"

private def toFinFive : Nat -> Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ => 4

theorem s2_2_models :
    Models SemigroupBasis.Generated.S2_2.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S2_2.table basis toFinFive (by decide)

set_option maxHeartbeats 2000000 in
theorem s5_55_models :
    Models
      SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_55.table basis toFinFive
      (by decide)

set_option maxHeartbeats 2000000 in
theorem s5_192_models :
    Models
      SemigroupBasis.Generated.Catalogue.S5_192.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_192.table basis toFinFive
      (by decide)

private def instantiateThreeWords
    (u v q : Word Nat) : Nat -> Word Nat
  | 0 => u
  | 1 => v
  | 2 => q
  | n + 3 => Word.singleton (n + 3)

private def instantiateFiveWords
    (u v q r s : Word Nat) : Nat -> Word Nat
  | 0 => u
  | 1 => v
  | 2 => q
  | 3 => r
  | 4 => s
  | n + 5 => Word.singleton (n + 5)

/-- Swap the final two nonempty blocks after a fixed nonempty prefix. -/
theorem derivesSuffixSwap (pre u v : Word Nat) :
    Derives basis ((pre ++ u) ++ v) ((pre ++ v) ++ u) := by
  have source : Derives basis xyz xzy :=
    Derives.fromBasis (e := suffixCommutationLaw) (by simp [basis])
  have substituted :=
    Derives.subst source (instantiateThreeWords pre u v)
  simpa [suffixCommutationLaw, xyz, xzy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Swap the first two nonempty blocks before a fixed nonempty suffix. -/
theorem derivesPrefixSwap (u v suffix : Word Nat) :
    Derives basis ((u ++ v) ++ suffix) ((v ++ u) ++ suffix) := by
  have source : Derives basis xyz yxz :=
    Derives.fromBasis (e := prefixCommutationLaw) (by simp [basis])
  have substituted :=
    Derives.subst source (instantiateThreeWords u v suffix)
  simpa [prefixCommutationLaw, xyz, yxz, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private inductive ListDerives : List Nat -> List Nat -> Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives basis (w x xs) (w y ys) ->
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
          exact ListDerives.words (Derives.trans firstProof secondProof)

private theorem listDerives_of_perm_with_prefix
    (pre : List Nat) {xs ys : List Nat}
    (permutation : xs.Perm ys)
    (long : 3 <= (pre ++ xs).length) :
    ListDerives (pre ++ xs) (pre ++ ys) := by
  induction permutation generalizing pre with
  | nil =>
      cases pre with
      | nil => simp at long
      | cons p ps => exact ListDerives.words (Derives.refl _)
  | cons x permutation ih =>
      have next := ih (pre := pre ++ [x]) <| by
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
                      (Word.singleton y) (Word.singleton x) (w z zs)
      | cons p ps =>
          cases xs with
          | nil =>
              exact ListDerives.words <| by
                simpa [w, Word.singleton, Word.append,
                  Word.append_assoc] using
                    derivesSuffixSwap
                      (w p ps) (Word.singleton y) (Word.singleton x)
          | cons z zs =>
              have swapped :=
                Derives.appendRight
                  (derivesSuffixSwap
                    (w p ps) (Word.singleton y) (Word.singleton x))
                  (w z zs)
              exact ListDerives.words <| by
                simpa [w, Word.singleton, Word.append,
                  Word.append_assoc] using swapped
  | trans first second ihFirst ihSecond =>
      have firstDerivation := ihFirst (pre := pre) long
      have secondDerivation := ihSecond (pre := pre) <| by
        rw [List.length_append, ← first.length_eq]
        simpa [List.length_append] using long
      exact firstDerivation.trans secondDerivation

/-- Every permutation of a word of length at least three is derivable. -/
theorem derivesLongPermutation (u v : Word Nat)
    (long : 3 <= u.toList.length)
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

/-- Delete a square when four nonempty factors remain to its right. -/
theorem derivesContextualPairDeletion
    (u a b c d : Word Nat) :
    Derives basis
      (((((u ++ u) ++ a) ++ b) ++ c) ++ d)
      (((a ++ b) ++ c) ++ d) := by
  have source : Derives basis xxyzth yzth :=
    Derives.fromBasis (e := contextualPairDeletionLaw) (by simp [basis])
  have substituted :=
    Derives.subst source (instantiateFiveWords u a b c d)
  simpa [contextualPairDeletionLaw, xxyzth, yzth, w,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private def guard (a b c d : Word Nat) : Word Nat :=
  (((a ++ b) ++ c) ++ d)

/-- Insert a parity-neutral four-copy guard before any word of length at
least four. -/
theorem derivesInsertFour
    (word marker : Word Nat)
    (long : 4 <= word.toList.length) :
    Derives basis word (guard marker marker marker marker ++ word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third more =>
              cases more with
              | nil => simp [Word.toList] at long
              | cons fourth remaining =>
                  let finalBlock : Word Nat := w fourth remaining
                  have firstInsert :
                      Derives basis
                        (w head (second :: third :: fourth :: remaining))
                        ((marker ++ marker) ++
                          w head (second :: third :: fourth :: remaining)) := by
                    have deletion :=
                      derivesContextualPairDeletion marker
                        (Word.singleton head) (Word.singleton second)
                        (Word.singleton third) finalBlock
                    simpa [finalBlock, w, Word.singleton, Word.append,
                      Word.append_assoc] using deletion.symm
                  have secondInsert :
                      Derives basis
                        ((marker ++ marker) ++
                          w head (second :: third :: fourth :: remaining))
                        (guard marker marker marker marker ++
                          w head (second :: third :: fourth :: remaining)) := by
                    have deletion :=
                      derivesContextualPairDeletion marker marker marker
                        (Word.singleton head)
                        (((Word.singleton second ++ Word.singleton third) ++
                          finalBlock))
                    simpa [guard, finalBlock, w, Word.singleton, Word.append,
                      Word.append_assoc] using deletion.symm
                  exact firstInsert.trans secondInsert

/-- Cancellation in the cyclic-two theory is available behind four fixed
nonempty guards. -/
theorem derivesGuardedCancellation
    (a b c d u v : Word Nat) :
    Derives basis
      (guard a b c d ++ ((u ++ u) ++ v))
      (guard a b c d ++ v) := by
  let exposed : Word Nat :=
    (((((u ++ u) ++ a) ++ b) ++ c) ++ (d ++ v))
  let reduced : Word Nat := (((a ++ b) ++ c) ++ (d ++ v))
  have enter :
      Derives basis
        (guard a b c d ++ ((u ++ u) ++ v)) exposed :=
    derivesLongPermutation _ _ (by
      have ha : 1 <= a.toList.length := by cases a <;> simp [Word.toList]
      have hb : 1 <= b.toList.length := by cases b <;> simp [Word.toList]
      have hc : 1 <= c.toList.length := by cases c <;> simp [Word.toList]
      have hd : 1 <= d.toList.length := by cases d <;> simp [Word.toList]
      simp only [guard, Word.toList_append, List.length_append]
      omega) <| by
      rw [List.perm_iff_count]
      intro letter
      simp [exposed, guard, Word.toList_append, List.count_append]
      omega
  have delete : Derives basis exposed reduced := by
    simpa [exposed, reduced, Word.append_assoc] using
      derivesContextualPairDeletion u a b c (d ++ v)
  have exit : Derives basis reduced (guard a b c d ++ v) :=
    derivesLongPermutation _ _ (by
      have ha : 1 <= a.toList.length := by cases a <;> simp [Word.toList]
      have hb : 1 <= b.toList.length := by cases b <;> simp [Word.toList]
      have hc : 1 <= c.toList.length := by cases c <;> simp [Word.toList]
      have hd : 1 <= d.toList.length := by cases d <;> simp [Word.toList]
      simp only [reduced, Word.toList_append, List.length_append]
      omega) <| by
      rw [List.perm_iff_count]
      intro letter
      simp [reduced, guard, Word.toList_append, List.count_append]
  exact enter.trans <| delete.trans exit

private theorem bind_append (u v : Word Nat) (sigma : Nat -> Word Nat) :
    (u ++ v).bind sigma = u.bind sigma ++ v.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (tau sigma : Nat -> Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun x => (tau x).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Replay the complete cyclic-two derivation behind four fixed guards. -/
theorem liftCyclicTwo
    {u v : Word Nat}
    (derivation : Derives cyclicTwoBasis u v)
    (a b c d : Word Nat) (sigma : Nat -> Word Nat) :
    Derives basis
      (guard a b c d ++ u.bind sigma)
      (guard a b c d ++ v.bind sigma) := by
  induction derivation generalizing a b c d sigma with
  | fromBasis member =>
      simp only [cyclicTwoBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · have swapped :=
          derivesSuffixSwap (guard a b c d) (sigma 0) (sigma 1)
        simpa [cyclicCommutativityLaw, cyclicXY, cyclicYX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            swapped
      · simpa [cyclicCancellationLaw, cyclicXXY, cyclicY,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
            derivesGuardedCancellation a b c d (sigma 0) (sigma 1)
  | refl =>
      exact Derives.refl _
  | symm nested inductionHypothesis =>
      exact Derives.symm (inductionHypothesis a b c d sigma)
  | trans first second firstHypothesis secondHypothesis =>
      exact Derives.trans
        (firstHypothesis a b c d sigma)
        (secondHypothesis a b c d sigma)
  | prepend pre nested inductionHypothesis =>
      simpa [guard, bind_append, Word.append_assoc] using
        inductionHypothesis a b c (d ++ pre.bind sigma) sigma
  | appendRight nested post inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis a b c d sigma) (post.bind sigma)
  | subst nested tau inductionHypothesis =>
      simpa [bind_bind] using
        inductionHypothesis a b c d
          (fun x => (tau x).bind sigma)

/-- Every pair of length-at-least-four words with the same cyclic-two value
is derivably equal. -/
theorem derivesLongOfCyclicValid
    (identity : Identity Nat)
    (cyclicValid : identity.SatisfiedBy cyclicTwo.semigroup)
    (leftLong : 4 <= identity.lhs.toList.length)
    (rightLong : 4 <= identity.rhs.toList.length) :
    Derives basis identity.lhs identity.rhs := by
  let marker := Word.singleton identity.lhs.head
  have insertLeft :=
    derivesInsertFour identity.lhs marker leftLong
  have insertRight :=
    derivesInsertFour identity.rhs marker rightLong
  have cyclicDerivation :=
    cyclicTwoBasis_complete.2 identity cyclicValid
  have lifted :=
    liftCyclicTwo cyclicDerivation marker marker marker marker
      Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  exact insertLeft.trans <| lifted.trans insertRight.symm

private theorem all_eq_of_count_eq_length (selected : Nat) :
    forall letters : List Nat,
      letters.count selected = letters.length ->
        forall letter, letter ∈ letters -> letter = selected
  | [], _ => by simp
  | head :: tail, equality => by
      by_cases headSelected : head = selected
      · subst head
        rw [List.count_cons_self, List.length_cons] at equality
        have tailEquality : tail.count selected = tail.length := by omega
        intro letter member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · rfl
        · exact all_eq_of_count_eq_length selected tail
            tailEquality letter member
      · have bound := List.count_le_length (a := selected) (l := tail)
        rw [List.count_cons_of_ne headSelected,
          List.length_cons] at equality
        omega

private theorem count_eq_length_of_all_eq
    (selected : Nat) (letters : List Nat)
    (allEqual : forall letter, letter ∈ letters -> letter = selected) :
    letters.count selected = letters.length := by
  induction letters with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have headSelected : head = selected := allEqual head (by simp)
      subst head
      rw [List.count_cons_self, List.length_cons]
      congr 1
      exact inductionHypothesis <| by
        intro letter member
        exact allEqual letter (by simp [member])

/-- On two length-three words, support plus coordinate parity determines the
entire multiplicity vector. -/
private theorem count_eq_of_support_parity_three
    {first second : List Nat}
    (firstThree : first.length = 3)
    (secondThree : second.length = 3)
    (support : forall letter, letter ∈ first <-> letter ∈ second)
    (parity : forall letter,
      first.count letter % 2 = second.count letter % 2) :
    forall letter, first.count letter = second.count letter := by
  intro selected
  have firstBound := List.count_le_length (a := selected) (l := first)
  have secondBound := List.count_le_length (a := selected) (l := second)
  have positiveIff :
      0 < first.count selected <-> 0 < second.count selected := by
    rw [List.count_pos_iff, List.count_pos_iff]
    exact support selected
  by_cases firstCountThree : first.count selected = 3
  · have firstAll :=
      all_eq_of_count_eq_length selected first (by omega)
    have secondAll :
        forall letter, letter ∈ second -> letter = selected := by
      intro letter member
      exact firstAll letter ((support letter).mpr member)
    have secondCount :=
      count_eq_length_of_all_eq selected second secondAll
    omega
  · by_cases secondCountThree : second.count selected = 3
    · have secondAll :=
        all_eq_of_count_eq_length selected second (by omega)
      have firstAll :
          forall letter, letter ∈ first -> letter = selected := by
        intro letter member
        exact secondAll letter ((support letter).mp member)
      have firstCount :=
        count_eq_length_of_all_eq selected first firstAll
      omega
    · have parityEqual := parity selected
      omega

private theorem derives_of_cyclic_and_exact_class
    (identity : Identity Nat)
    (cyclicValid : identity.SatisfiedBy cyclicTwo.semigroup)
    (exactClass :
      SemigroupBasis.CoRoots.S5_55.ExactBasisClass
        identity.lhs identity.rhs) :
    Derives basis identity.lhs identity.rhs := by
  rcases exactClass with equal | tripleOrLong
  · rw [equal]
    exact Derives.refl _
  · rcases tripleOrLong with
      ⟨leftThree, rightThree, support⟩ |
      ⟨leftLong, rightLong⟩
    · have parity := cyclicValid_parity_eq identity cyclicValid
      exact derivesLongPermutation identity.lhs identity.rhs
        (by omega) <| List.perm_iff_count.mpr <|
          count_eq_of_support_parity_three
            leftThree rightThree support parity
    · exact derivesLongOfCyclicValid
        identity cyclicValid leftLong rightLong

theorem derives_of_s2_2_s5_55_valid
    (identity : Identity Nat)
    (cyclicValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S2_2.table.semigroup)
    (thresholdValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have cyclicValid' : identity.SatisfiedBy cyclicTwo.semigroup := by
    simpa [SemigroupBasis.Generated.S2_2.table, cyclicTwo] using cyclicValid
  exact derives_of_cyclic_and_exact_class identity cyclicValid'
    (SemigroupBasis.CoRoots.S5_55Family.S5_55.valid_exactBasisClass
      identity thresholdValid)

theorem derives_of_s2_2_s5_192_valid
    (identity : Identity Nat)
    (cyclicValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S2_2.table.semigroup)
    (thresholdValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_192.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have cyclicValid' : identity.SatisfiedBy cyclicTwo.semigroup := by
    simpa [SemigroupBasis.Generated.S2_2.table, cyclicTwo] using cyclicValid
  exact derives_of_cyclic_and_exact_class identity cyclicValid'
    (SemigroupBasis.CoRoots.S5_55Family.S5_192.valid_exactBasisClass
      identity thresholdValid)

def s2_2_s5_55_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_55.table.semigroup basis where
  leftModels := s2_2_models
  rightModels := s5_55_models
  complete := derives_of_s2_2_s5_55_valid

def s2_2_s5_192_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_192.table.semigroup basis where
  leftModels := s2_2_models
  rightModels := s5_192_models
  complete := derives_of_s2_2_s5_192_valid

end SemigroupBasis.CoRoots.Order6ParityLengthThreshold
