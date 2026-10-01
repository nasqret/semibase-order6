import SemigroupBasis.Examples.FinalMarkerThree
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_196

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxy : Word Nat := w 0 [0, 1]
def xxxy : Word Nat := w 0 [0, 0, 1]
def xyx : Word Nat := w 0 [1, 0]
def xyy : Word Nat := w 0 [1, 1]
def yxx : Word Nat := w 1 [0, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyz : Word Nat := w 0 [1, 2]
def yxz : Word Nat := w 1 [0, 2]
def xxyz : Word Nat := w 0 [0, 1, 2]

def powerLaw : Identity Nat := ⟨xxx, xxxx⟩
def heavyInsertionLaw : Identity Nat := ⟨xxy, xxxy⟩
def copyLaw : Identity Nat := ⟨xyx, xyy⟩
def rotateLaw : Identity Nat := ⟨xyx, yxx⟩
def leftInsertionLaw : Identity Nat := ⟨xyx, xxyx⟩
def prefixCommutationLaw : Identity Nat := ⟨xyz, yxz⟩
def longInsertionLaw : Identity Nat := ⟨xyz, xxyz⟩

/-- The exact seven-law basis shared by `S5_196` and `S5_197`. -/
def basis : List (Identity Nat) :=
  [powerLaw, heavyInsertionLaw, copyLaw, rotateLaw,
    leftInsertionLaw, prefixCommutationLaw, longInsertionLaw]

def yxxx : Word Nat := w 1 [0, 0, 0]
def yyx : Word Nat := w 1 [1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def zyx : Word Nat := w 2 [1, 0]
def zxy : Word Nat := w 2 [0, 1]
def zyxx : Word Nat := w 2 [1, 0, 0]

/-- The literal reverse-word transform of the seven-law basis. -/
def expectedReversedBasis : List (Identity Nat) :=
  [⟨xxx, xxxx⟩, ⟨yxx, yxxx⟩, ⟨xyx, yyx⟩,
    ⟨xyx, xxy⟩, ⟨xyx, xyxx⟩, ⟨zyx, zxy⟩,
    ⟨zyx, zyxx⟩]

theorem reversedBasis_eq_expected :
    reversedBasis basis = expectedReversedBasis := by
  rfl

def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinThree).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Finite checks on the variables `0,1,2` suffice for the published basis. -/
theorem models_of_finite_checks
    (table : FiniteTable)
    (checks : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checks) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

theorem derivesCopy (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((u ++ v) ++ v) := by
  have base : Derives basis xyx xyy :=
    Derives.fromBasis (e := copyLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [copyLaw, xyx, xyy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesRotate (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((v ++ u) ++ u) := by
  have base : Derives basis xyx yxx :=
    Derives.fromBasis (e := rotateLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [rotateLaw, xyx, yxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Swap the first two nonempty blocks before a fixed nonempty suffix. -/
theorem derivesPrefixSwap (u v suffix : Word Nat) :
    Derives basis ((u ++ v) ++ suffix) ((v ++ u) ++ suffix) := by
  have base : Derives basis xyz yxz :=
    Derives.fromBasis (e := prefixCommutationLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u v suffix)
  simpa [prefixCommutationLaw, xyz, yxz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Duplicate the first nonempty block in a product of three blocks. -/
theorem derivesLongDuplication (u v suffix : Word Nat) :
    Derives basis
      ((u ++ v) ++ suffix) (((u ++ u) ++ v) ++ suffix) := by
  have base : Derives basis xyz xxyz :=
    Derives.fromBasis (e := longInsertionLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords u v suffix)
  simpa [longInsertionLaw, xyz, xxyz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Behind a fixed nonempty marker, replay the final-marker prefix
duplication `uv = uuv`. -/
theorem derivesContextPrefixDuplication
    (marker u v : Word Nat) :
    Derives basis
      (marker ++ (u ++ v))
      (marker ++ ((u ++ u) ++ v)) := by
  have enter := derivesPrefixSwap marker u v
  have duplicate := derivesLongDuplication u marker v
  have moveMarker :=
    Derives.prepend u (derivesPrefixSwap u marker v)
  have exit := derivesPrefixSwap u marker (u ++ v)
  exact Derives.trans
    (by simpa [Word.append_assoc] using enter) <|
    Derives.trans duplicate <|
    Derives.trans
      (by simpa [Word.append_assoc] using moveMarker)
      (by simpa [Word.append_assoc] using exit)

private theorem bind_append
    (u v : Word Nat) (substitution : Nat → Word Nat) :
    (u ++ v).bind substitution =
      u.bind substitution ++ v.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun x => (first x).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Every derivation in the three-element terminal-marker basis can be
replayed behind one fixed nonempty prefix marker. -/
theorem liftFinalMarker
    {u v : Word Nat}
    (derivation : Derives finalMarkerThreeBasis u v)
    (marker : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (marker ++ u.bind substitution)
      (marker ++ v.bind substitution) := by
  induction derivation generalizing marker substitution with
  | fromBasis member =>
      simp only [finalMarkerThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · simpa [finalMarkerPowerLaw, finalMarkerXX, finalMarkerXXX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          derivesContextPrefixDuplication
            marker (substitution 0) (substitution 0)
      · simpa [finalMarkerPrefixDuplicationLaw, finalMarkerXY,
          finalMarkerXXY, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesContextPrefixDuplication
            marker (substitution 0) (substitution 1)
      · simpa [finalMarkerCopyLaw, finalMarkerXYX, finalMarkerXYY,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend marker
            (derivesCopy (substitution 0) (substitution 1))
      · simpa [finalMarkerRotateLaw, finalMarkerXYX, finalMarkerYXX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend marker
            (derivesRotate (substitution 0) (substitution 1))
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih marker substitution)
  | trans _ _ first second =>
      exact Derives.trans
        (first marker substitution) (second marker substitution)
  | prepend stem _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (marker ++ stem.bind substitution) substitution
  | appendRight _ suffix ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (ih marker substitution) (suffix.bind substitution)
  | subst _ first ih =>
      simpa [bind_bind] using
        ih marker (fun x => (first x).bind substitution)

/-- Every permutation of the prefix before a fixed final variable is
derivable from `xyz = yxz`. -/
theorem derivesPrefixPermutation
    {prefix₁ prefix₂ : List Nat}
    (permutation : prefix₁.Perm prefix₂)
    (final : Nat) :
    Derives basis
      (wordOfPrefixFinal prefix₁ final)
      (wordOfPrefixFinal prefix₂ final) := by
  induction permutation with
  | nil =>
      exact Derives.refl _
  | cons x _ ih =>
      simpa using Derives.prepend (Word.singleton x) ih
  | swap x y xs =>
      simpa [Word.append_assoc] using
        derivesPrefixSwap
          (Word.singleton y) (Word.singleton x)
          (wordOfPrefixFinal xs final)
  | trans _ _ first second =>
      exact first.trans second

/-- Insert one extra occurrence of a supported prefix variable. The
two-letter prefix hypothesis is exactly the long-word threshold. -/
theorem derivesInsertSupportedPrefix
    (stem : List Nat) (final marker : Nat)
    (member : marker ∈ stem)
    (prefixLong : 2 ≤ stem.length) :
    Derives basis
      (wordOfPrefixFinal stem final)
      (Word.singleton marker ++
        wordOfPrefixFinal stem final) := by
  have expose :
      stem.Perm (marker :: stem.erase marker) :=
    List.perm_cons_erase member
  have arranged :=
    derivesPrefixPermutation expose final
  have restNonempty : stem.erase marker ≠ [] := by
    intro empty
    have eraseLength := List.length_erase_of_mem member
    rw [empty] at eraseLength
    simp at eraseLength
    omega
  have duplicate :
      Derives basis
        (wordOfPrefixFinal
          (marker :: stem.erase marker) final)
        (wordOfPrefixFinal
          (marker :: marker :: stem.erase marker) final) := by
    cases restEq : stem.erase marker with
    | nil =>
        exact False.elim (restNonempty restEq)
    | cons next rest =>
        have tailEq :
            wordOfCons next rest ++ Word.singleton final =
              wordOfPrefixFinal (next :: rest) final := by
          apply Word.toList_injective
          rw [Word.toList_append, toList_wordOfPrefixFinal]
          simp [wordOfCons, Word.toList]
        simpa only [restEq, wordOfPrefixFinal_cons,
          Word.append_assoc, tailEq] using
          derivesLongDuplication
            (Word.singleton marker)
            (wordOfCons next rest)
            (Word.singleton final)
  have restore :
      (marker :: marker :: stem.erase marker).Perm
        (marker :: stem) :=
    (List.Perm.cons marker expose).symm
  exact arranged.trans <|
    duplicate.trans <| by
      simpa [wordOfPrefixFinal] using
        derivesPrefixPermutation restore final

/-- Support equality without multiplicity. -/
def SameSupport (left right : Word Nat) : Prop :=
  ∀ z, z ∈ left.toList ↔ z ∈ right.toList

/-- The final variable occurs globally exactly once. -/
def SimpleFinal (word : Word Nat) (z : Nat) : Prop :=
  (splitPrefixFinal word).2 = z ∧
    z ∉ (splitPrefixFinal word).1

def SameSimpleFinal (left right : Word Nat) : Prop :=
  ∀ z, SimpleFinal left z ↔ SimpleFinal right z

/-- Short words are literal. Long words are classified by support and by
the identity of the final variable exactly when it occurs once. -/
def ExactBasisClass (left right : Word Nat) : Prop :=
  left = right ∨
    (3 ≤ left.toList.length ∧
      3 ≤ right.toList.length ∧
      SameSupport left right ∧
      SameSimpleFinal left right)

private def LengthClass (left right : Word Nat) : Prop :=
  left = right ∨
    (3 ≤ left.toList.length ∧
      3 ≤ right.toList.length)

private theorem lengthClass_symm
    {left right : Word Nat}
    (same : LengthClass left right) :
    LengthClass right left := by
  rcases same with equal | ⟨leftLong, rightLong⟩
  · exact Or.inl equal.symm
  · exact Or.inr ⟨rightLong, leftLong⟩

private theorem lengthClass_trans
    {left middle right : Word Nat}
    (first : LengthClass left middle)
    (second : LengthClass middle right) :
    LengthClass left right := by
  rcases first with equal | ⟨leftLong, middleLong⟩
  · subst middle
    exact second
  · rcases second with equal | ⟨middleLong', rightLong⟩
    · subst right
      exact Or.inr ⟨leftLong, middleLong⟩
    · exact Or.inr ⟨leftLong, rightLong⟩

private theorem lengthClass_prepend
    (stem : Word Nat) {left right : Word Nat}
    (same : LengthClass left right) :
    LengthClass (stem ++ left) (stem ++ right) := by
  rcases same with equal | ⟨leftLong, rightLong⟩
  · exact Or.inl (congrArg (fun word => stem ++ word) equal)
  · refine Or.inr ⟨?_, ?_⟩ <;>
      simp only [Word.toList_append, List.length_append] <;> omega

private theorem lengthClass_appendRight
    (suffix : Word Nat) {left right : Word Nat}
    (same : LengthClass left right) :
    LengthClass (left ++ suffix) (right ++ suffix) := by
  rcases same with equal | ⟨leftLong, rightLong⟩
  · exact Or.inl (congrArg (fun word => word ++ suffix) equal)
  · refine Or.inr ⟨?_, ?_⟩ <;>
      simp only [Word.toList_append, List.length_append] <;> omega

private theorem list_length_le_flatMap_words
    (letters : List Nat) (substitution : Nat → Word Nat) :
    letters.length ≤
      (letters.flatMap fun letter =>
        (substitution letter).toList).length := by
  induction letters with
  | nil =>
      simp
  | cons letter rest ih =>
      simp only [List.length_cons, List.flatMap_cons,
        List.length_append]
      have imagePositive :
          1 ≤ (substitution letter).toList.length := by
        cases substitution letter
        simp [Word.toList]
      omega

private theorem bind_preserves_long
    (word : Word Nat) (substitution : Nat → Word Nat)
    (long : 3 ≤ word.toList.length) :
    3 ≤ (word.bind substitution).toList.length := by
  rw [Word.toList_bind]
  exact Nat.le_trans long
    (list_length_le_flatMap_words word.toList substitution)

private theorem lengthClass_subst
    (substitution : Nat → Word Nat)
    {left right : Word Nat}
    (same : LengthClass left right) :
    LengthClass
      (left.bind substitution) (right.bind substitution) := by
  rcases same with equal | ⟨leftLong, rightLong⟩
  · exact Or.inl
      (congrArg (fun word => word.bind substitution) equal)
  · exact Or.inr
      ⟨bind_preserves_long left substitution leftLong,
        bind_preserves_long right substitution rightLong⟩

private theorem basis_member_lengthClass
    (identity : Identity Nat) (member : identity ∈ basis) :
    LengthClass identity.lhs identity.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [LengthClass, powerLaw, heavyInsertionLaw, copyLaw,
      rotateLaw, leftInsertionLaw, prefixCommutationLaw,
      longInsertionLaw, xxx, xxxx, xxy, xxxy, xyx, xyy, yxx,
      xxyx, xyz, yxz, xxyz, w, Word.toList]

private theorem derives_lengthClass
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    LengthClass left right := by
  induction derivation with
  | fromBasis member =>
      exact basis_member_lengthClass _ member
  | refl =>
      exact Or.inl rfl
  | symm _ ih =>
      exact lengthClass_symm ih
  | trans _ _ first second =>
      exact lengthClass_trans first second
  | prepend stem _ ih =>
      exact lengthClass_prepend stem ih
  | appendRight _ suffix ih =>
      exact lengthClass_appendRight suffix ih
  | subst _ substitution ih =>
      exact lengthClass_subst substitution ih

private def terminalMarkerSeparator (tested : Nat) : Nat → Fin 3 :=
  fun x => if x = tested then 1 else 2

private def terminalMarkerSemanticValue
    (tested : Nat) (stem : List Nat) (final : Nat) : Fin 3 :=
  if tested ∈ stem then 0
  else if final = tested then 1 else 2

private theorem terminalMarkerEval_separator
    (tested : Nat) (stem : List Nat) (final : Nat) :
    finalMarkerThree.semigroup.eval
        (terminalMarkerSeparator tested)
        (wordOfPrefixFinal stem final) =
      terminalMarkerSemanticValue tested stem final := by
  induction stem with
  | nil =>
      simp [wordOfPrefixFinal, terminalMarkerSeparator,
        terminalMarkerSemanticValue]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append, ih]
      by_cases equal : x = tested
      · subst x
        simp [terminalMarkerSeparator, terminalMarkerSemanticValue,
          finalMarkerThree, FiniteTable.semigroup,
          finalMarkerThreeMul]
      · simp [terminalMarkerSeparator, terminalMarkerSemanticValue,
          finalMarkerThree, FiniteTable.semigroup,
          finalMarkerThreeMul, equal, Ne.symm equal]

private theorem terminalMarkerSemanticValue_ne_two_iff
    (tested : Nat) (stem : List Nat) (final : Nat) :
    terminalMarkerSemanticValue tested stem final ≠ (2 : Fin 3) ↔
      tested ∈ stem ∨ tested = final := by
  by_cases prefixMember : tested ∈ stem
  · simp [terminalMarkerSemanticValue, prefixMember]
  · by_cases finalEq : final = tested
    · subst final
      simp [terminalMarkerSemanticValue, prefixMember]
    · simp [terminalMarkerSemanticValue, prefixMember, finalEq,
        Ne.symm finalEq]

/-- Final-marker validity recovers the complete variable support. -/
theorem finalMarkerValid_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy finalMarkerThree.semigroup) :
    SameSupport identity.lhs identity.rhs := by
  intro tested
  let leftSplit := splitPrefixFinal identity.lhs
  let rightSplit := splitPrefixFinal identity.rhs
  have leftReconstruct :
      wordOfPrefixFinal leftSplit.1 leftSplit.2 = identity.lhs :=
    wordOfPrefixFinal_split identity.lhs
  have rightReconstruct :
      wordOfPrefixFinal rightSplit.1 rightSplit.2 = identity.rhs :=
    wordOfPrefixFinal_split identity.rhs
  have evaluated := valid (terminalMarkerSeparator tested)
  rw [← leftReconstruct, ← rightReconstruct,
    terminalMarkerEval_separator,
    terminalMarkerEval_separator] at evaluated
  rw [← leftReconstruct, ← rightReconstruct,
    toList_wordOfPrefixFinal, toList_wordOfPrefixFinal]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · intro leftMember
    have leftNe :
        terminalMarkerSemanticValue tested
            leftSplit.1 leftSplit.2 ≠ (2 : Fin 3) :=
      (terminalMarkerSemanticValue_ne_two_iff
        tested leftSplit.1 leftSplit.2).2 leftMember
    rw [evaluated] at leftNe
    exact
      (terminalMarkerSemanticValue_ne_two_iff
        tested rightSplit.1 rightSplit.2).1 leftNe
  · intro rightMember
    have rightNe :
        terminalMarkerSemanticValue tested
            rightSplit.1 rightSplit.2 ≠ (2 : Fin 3) :=
      (terminalMarkerSemanticValue_ne_two_iff
        tested rightSplit.1 rightSplit.2).2 rightMember
    rw [← evaluated] at rightNe
    exact
      (terminalMarkerSemanticValue_ne_two_iff
        tested leftSplit.1 leftSplit.2).1 rightNe

/-- Final-marker validity recovers the globally simple final variable. -/
theorem finalMarkerValid_simpleFinal
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy finalMarkerThree.semigroup) :
    SameSimpleFinal identity.lhs identity.rhs := by
  intro tested
  exact finalMarkerValid_splitSimpleFinal_iff identity valid tested

private theorem prefix_signature
    {leftPrefix rightPrefix : List Nat}
    {leftFinal rightFinal : Nat}
    (support :
      ∀ z,
        (z ∈ leftPrefix ∨ z = leftFinal) ↔
          (z ∈ rightPrefix ∨ z = rightFinal))
    (simple :
      ∀ z,
        (leftFinal = z ∧ z ∉ leftPrefix) ↔
          (rightFinal = z ∧ z ∉ rightPrefix)) :
    (∀ z, z ∈ leftPrefix ↔ z ∈ rightPrefix) ∧
      ((leftFinal = rightFinal ∧
          leftFinal ∉ leftPrefix ∧
          rightFinal ∉ rightPrefix) ∨
        (leftFinal ∈ leftPrefix ∧
          rightFinal ∈ rightPrefix)) := by
  by_cases leftRepeated : leftFinal ∈ leftPrefix
  · have rightRepeated : rightFinal ∈ rightPrefix := by
      apply Decidable.byContradiction
      intro rightAbsent
      have rightSimple :
          rightFinal = rightFinal ∧
            rightFinal ∉ rightPrefix :=
        ⟨rfl, rightAbsent⟩
      have leftSimple := (simple rightFinal).mpr rightSimple
      apply leftSimple.2
      rw [← leftSimple.1]
      exact leftRepeated
    have prefixSupport :
        ∀ z, z ∈ leftPrefix ↔ z ∈ rightPrefix := by
      intro z
      constructor
      · intro leftMember
        rcases (support z).mp (Or.inl leftMember) with
          rightMember | finalEq
        · exact rightMember
        · subst z
          exact rightRepeated
      · intro rightMember
        rcases (support z).mpr (Or.inl rightMember) with
          leftMember | finalEq
        · exact leftMember
        · subst z
          exact leftRepeated
    exact ⟨prefixSupport, Or.inr ⟨leftRepeated, rightRepeated⟩⟩
  · have leftSimple :
        leftFinal = leftFinal ∧ leftFinal ∉ leftPrefix :=
      ⟨rfl, leftRepeated⟩
    have rightSimple := (simple leftFinal).mp leftSimple
    have finals : rightFinal = leftFinal := rightSimple.1
    have rightAbsent : rightFinal ∉ rightPrefix := by
      rw [finals]
      exact rightSimple.2
    have prefixSupport :
        ∀ z, z ∈ leftPrefix ↔ z ∈ rightPrefix := by
      intro z
      constructor
      · intro leftMember
        rcases (support z).mp (Or.inl leftMember) with
          rightMember | finalEq
        · exact rightMember
        · exact False.elim <| leftRepeated <| by
            rw [finalEq, finals] at leftMember
            exact leftMember
      · intro rightMember
        rcases (support z).mpr (Or.inl rightMember) with
          leftMember | finalEq
        · exact leftMember
        · exact False.elim <| rightAbsent <| by
            rw [finalEq, ← finals] at rightMember
            exact rightMember
    exact
      ⟨prefixSupport,
        Or.inl ⟨finals.symm, leftRepeated, rightAbsent⟩⟩

private theorem split_signature
    (left right : Word Nat)
    (support : SameSupport left right)
    (simple : SameSimpleFinal left right) :
    (∀ z,
        z ∈ (splitPrefixFinal left).1 ↔
          z ∈ (splitPrefixFinal right).1) ∧
      (((splitPrefixFinal left).2 =
            (splitPrefixFinal right).2 ∧
          (splitPrefixFinal left).2 ∉
            (splitPrefixFinal left).1 ∧
          (splitPrefixFinal right).2 ∉
            (splitPrefixFinal right).1) ∨
        ((splitPrefixFinal left).2 ∈
            (splitPrefixFinal left).1 ∧
          (splitPrefixFinal right).2 ∈
            (splitPrefixFinal right).1)) := by
  apply prefix_signature
  · intro z
    have same := support z
    rw [← wordOfPrefixFinal_split left,
      ← wordOfPrefixFinal_split right,
      toList_wordOfPrefixFinal,
      toList_wordOfPrefixFinal] at same
    simpa using same
  · exact simple

private def PrefixPasses
    (valuation : Nat → Fin 3) (stem : List Nat) : Prop :=
  ∀ z ∈ stem, valuation z = 2

@[simp]
private theorem prefixPasses_cons
    (valuation : Nat → Fin 3) (x : Nat) (xs : List Nat) :
    PrefixPasses valuation (x :: xs) ↔
      valuation x = 2 ∧ PrefixPasses valuation xs := by
  simp [PrefixPasses]

private theorem prefixPasses_congr
    (valuation : Nat → Fin 3)
    {left right : List Nat}
    (support : ∀ z, z ∈ left ↔ z ∈ right) :
    PrefixPasses valuation left ↔
      PrefixPasses valuation right := by
  constructor
  · intro passes z member
    exact passes z ((support z).mpr member)
  · intro passes z member
    exact passes z ((support z).mp member)

private noncomputable instance prefixPassesDecidable
    (valuation : Nat → Fin 3) (stem : List Nat) :
    Decidable (PrefixPasses valuation stem) :=
  Classical.propDecidable _

private theorem finalMarkerEval_general
    (valuation : Nat → Fin 3) (stem : List Nat) (final : Nat) :
    finalMarkerThree.semigroup.eval valuation
        (wordOfPrefixFinal stem final) =
      if PrefixPasses valuation stem then
        valuation final
      else 0 := by
  induction stem with
  | nil =>
      simp [PrefixPasses, wordOfPrefixFinal]
  | cons x xs ih =>
      rw [wordOfPrefixFinal_cons, Semigroup.eval_append,
        Semigroup.eval_singleton, ih]
      by_cases headPasses : valuation x = 2 <;>
        by_cases tailPasses : PrefixPasses valuation xs <;>
        simp [headPasses, tailPasses, finalMarkerThree,
          FiniteTable.semigroup, finalMarkerThreeMul]

/-- Support plus terminal uniqueness is exactly the identity invariant of
the three-element final-marker semigroup. -/
theorem finalMarkerValid_of_signature
    {left right : Word Nat}
    (support : SameSupport left right)
    (simple : SameSimpleFinal left right) :
    (Identity.mk left right).SatisfiedBy
      finalMarkerThree.semigroup := by
  intro valuation
  let leftSplit := splitPrefixFinal left
  let rightSplit := splitPrefixFinal right
  have leftReconstruct :
      wordOfPrefixFinal leftSplit.1 leftSplit.2 = left :=
    wordOfPrefixFinal_split left
  have rightReconstruct :
      wordOfPrefixFinal rightSplit.1 rightSplit.2 = right :=
    wordOfPrefixFinal_split right
  have signature := split_signature left right support simple
  have passes :
      PrefixPasses valuation leftSplit.1 ↔
        PrefixPasses valuation rightSplit.1 :=
    prefixPasses_congr valuation signature.1
  rw [← leftReconstruct, ← rightReconstruct,
    finalMarkerEval_general, finalMarkerEval_general]
  rcases signature.2 with
      ⟨finals, _, _⟩ | ⟨leftRepeated, rightRepeated⟩
  · by_cases leftPasses : PrefixPasses valuation leftSplit.1
    · have rightPasses := passes.mp leftPasses
      simp only [if_pos leftPasses, if_pos rightPasses]
      exact congrArg valuation <| by
        simpa [leftSplit, rightSplit] using finals
    · have rightFails :
          ¬PrefixPasses valuation rightSplit.1 :=
        fun rightPasses => leftPasses (passes.mpr rightPasses)
      simp [leftPasses, rightFails]
  · by_cases leftPasses : PrefixPasses valuation leftSplit.1
    · have rightPasses := passes.mp leftPasses
      have leftFinalPasses :
          valuation leftSplit.2 = (2 : Fin 3) :=
        leftPasses leftSplit.2 leftRepeated
      have rightFinalPasses :
          valuation rightSplit.2 = (2 : Fin 3) :=
        rightPasses rightSplit.2 rightRepeated
      simp [leftPasses, rightPasses,
        leftFinalPasses, rightFinalPasses]
    · have rightFails :
          ¬PrefixPasses valuation rightSplit.1 :=
        fun rightPasses => leftPasses (passes.mpr rightPasses)
      simp [leftPasses, rightFails]

private theorem splitPrefix_length (word : Word Nat) :
    (splitPrefixFinal word).1.length + 1 =
      word.toList.length := by
  have reconstructed :=
    congrArg (fun candidate => candidate.toList.length)
      (wordOfPrefixFinal_split word)
  simpa [toList_wordOfPrefixFinal] using reconstructed

/-- Constructive long-word normal form theorem. A common supported prefix
letter is inserted on both sides, and the final-marker derivation is replayed
behind that fixed anchor. -/
theorem derivesLongOfSignature
    (left right : Word Nat)
    (leftLong : 3 ≤ left.toList.length)
    (rightLong : 3 ≤ right.toList.length)
    (support : SameSupport left right)
    (simple : SameSimpleFinal left right) :
    Derives basis left right := by
  have signature := split_signature left right support simple
  have leftPrefixLong :
      2 ≤ (splitPrefixFinal left).1.length := by
    have lengthEq := splitPrefix_length left
    omega
  have rightPrefixLong :
      2 ≤ (splitPrefixFinal right).1.length := by
    have lengthEq := splitPrefix_length right
    omega
  cases leftPrefixEq : (splitPrefixFinal left).1 with
  | nil =>
      simp [leftPrefixEq] at leftPrefixLong
  | cons marker rest =>
      have markerLeft :
          marker ∈ (splitPrefixFinal left).1 := by
        simp [leftPrefixEq]
      have markerRight :
          marker ∈ (splitPrefixFinal right).1 :=
        (signature.1 marker).mp markerLeft
      have leftInserted :=
        derivesInsertSupportedPrefix
          (splitPrefixFinal left).1
          (splitPrefixFinal left).2 marker
          markerLeft leftPrefixLong
      have rightInserted :=
        derivesInsertSupportedPrefix
          (splitPrefixFinal right).1
          (splitPrefixFinal right).2 marker
          markerRight rightPrefixLong
      rw [wordOfPrefixFinal_split left] at leftInserted
      rw [wordOfPrefixFinal_split right] at rightInserted
      have markerValid :=
        finalMarkerValid_of_signature support simple
      have sourceDerivation :=
        finalMarkerThreeBasis_complete.2
          (Identity.mk left right) markerValid
      have lifted :=
        liftFinalMarker sourceDerivation
          (Word.singleton marker) Word.singleton
      rw [bind_singleton, bind_singleton] at lifted
      exact leftInserted.trans <|
        lifted.trans rightInserted.symm

/-- The seven-law basis is valid in the three-element terminal-marker
semigroup, which supplies the support and unique-final soundness invariant. -/
theorem finalMarkerThree_models_basis :
    Models finalMarkerThree.semigroup basis :=
  models_of_finite_checks finalMarkerThree (by decide)

private theorem derives_exact
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    ExactBasisClass left right := by
  rcases derives_lengthClass derivation with
      equal | ⟨leftLong, rightLong⟩
  · exact Or.inl equal
  · have markerValid :
        (Identity.mk left right).SatisfiedBy
          finalMarkerThree.semigroup := by
      intro valuation
      exact derivation.sound finalMarkerThree_models_basis valuation
    exact Or.inr
      ⟨leftLong, rightLong,
        finalMarkerValid_support (Identity.mk left right) markerValid,
        finalMarkerValid_simpleFinal
          (Identity.mk left right) markerValid⟩

/-- Complete syntactic characterization of derivability from the exact
seven-law basis. -/
theorem derives_iff_exactBasisClass
    {left right : Word Nat} :
    Derives basis left right ↔
      ExactBasisClass left right := by
  constructor
  · exact derives_exact
  · intro same
    rcases same with
        equal |
        ⟨leftLong, rightLong, support, simple⟩
    · subst right
      exact Derives.refl _
    · exact derivesLongOfSignature
        left right leftLong rightLong support simple

private theorem pair_of_length_two
    (word : Word Nat)
    (lengthTwo : word.toList.length = 2) :
    ∃ first final, word = wordOfCons first [final] := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at lengthTwo
      | cons final rest =>
          cases rest with
          | nil =>
              exact ⟨head, final, rfl⟩
          | cons next more =>
              simp [Word.toList] at lengthTwo

/-- Equal support makes singleton words literal. -/
theorem lengthOne_eq_of_support
    (left right : Word Nat)
    (leftOne : left.toList.length = 1)
    (rightOne : right.toList.length = 1)
    (support : SameSupport left right) :
    left = right := by
  cases left with
  | mk leftHead leftTail =>
      cases leftTail with
      | nil =>
          cases right with
          | mk rightHead rightTail =>
              cases rightTail with
              | nil =>
                  have heads : leftHead = rightHead := by
                    have member :=
                      (support leftHead).mp <| by
                        simp [Word.toList]
                    simpa [Word.toList] using member
                  subst rightHead
                  rfl
              | cons next rest =>
                  simp [Word.toList] at rightOne
      | cons next rest =>
          simp [Word.toList] at leftOne

/-- Support plus the simple-final marker makes quadratic words literal. -/
theorem lengthTwo_eq_of_signature
    (left right : Word Nat)
    (leftTwo : left.toList.length = 2)
    (rightTwo : right.toList.length = 2)
    (support : SameSupport left right)
    (simple : SameSimpleFinal left right) :
    left = right := by
  obtain ⟨a, b, rfl⟩ := pair_of_length_two left leftTwo
  obtain ⟨c, d, rfl⟩ := pair_of_length_two right rightTwo
  have pairSupport :
      ∀ z, (z = a ∨ z = b) ↔ (z = c ∨ z = d) := by
    intro z
    simpa [wordOfCons, Word.toList, eq_comm] using support z
  by_cases diagonal : a = b
  · subst b
    have first : c = a := by
      have member := (pairSupport c).mpr (Or.inl rfl)
      simpa using member
    have final : d = a := by
      have member := (pairSupport d).mpr (Or.inr rfl)
      simpa using member
    subst c
    subst d
    rfl
  · have leftSimple :
        SimpleFinal (wordOfCons a [b]) b := by
      change b = b ∧ b ∉ [a]
      exact ⟨rfl, by simpa using (Ne.symm diagonal)⟩
    have rightSimple := (simple b).mp leftSimple
    change d = b ∧ b ∉ [c] at rightSimple
    have final : d = b := rightSimple.1
    have firstMember : c = a ∨ c = b :=
      (pairSupport c).mpr (Or.inl rfl)
    have first : c = a := by
      rcases firstMember with equal | equal
      · exact equal
      · exact False.elim <| rightSimple.2 <| by
          simp [equal]
    subst c
    subst d
    rfl

/-- Generic exact-class separator. A table only has to preserve support,
simple final variables, and the length stratum capped at three. -/
theorem exactBasisClass_of_separates
    (identity : Identity Nat)
    (support : SameSupport identity.lhs identity.rhs)
    (simple : SameSimpleFinal identity.lhs identity.rhs)
    (cappedLength :
      min identity.lhs.toList.length 3 =
        min identity.rhs.toList.length 3) :
    ExactBasisClass identity.lhs identity.rhs := by
  have leftPositive : 0 < identity.lhs.toList.length := by
    simp [Word.toList]
  have rightPositive : 0 < identity.rhs.toList.length := by
    simp [Word.toList]
  by_cases leftOne : identity.lhs.toList.length = 1
  · have rightOne : identity.rhs.toList.length = 1 := by
      omega
    exact Or.inl <|
      lengthOne_eq_of_support
        identity.lhs identity.rhs
        leftOne rightOne support
  · by_cases leftTwo : identity.lhs.toList.length = 2
    · have rightTwo : identity.rhs.toList.length = 2 := by
        omega
      exact Or.inl <|
        lengthTwo_eq_of_signature
          identity.lhs identity.rhs
          leftTwo rightTwo support simple
    · have leftLong : 3 ≤ identity.lhs.toList.length := by
        omega
      have rightLong : 3 ≤ identity.rhs.toList.length := by
        omega
      exact Or.inr
        ⟨leftLong, rightLong, support, simple⟩

/-- Generic completeness theorem once an exact finite-table separator has
been supplied. -/
theorem basis_complete_of_exact
    (table : FiniteTable)
    (models : Models table.semigroup basis)
    (separates :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          ExactBasisClass identity.lhs identity.rhs) :
    BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derives_iff_exactBasisClass.mpr
    (separates identity valid)

end SemigroupBasis.CoRoots.S5_196
