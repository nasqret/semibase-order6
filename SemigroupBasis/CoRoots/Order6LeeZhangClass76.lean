import SemigroupBasis.Examples.ConnectedComponentFourFinal
import SemigroupBasis.Examples.ProjectionQuadraticThree
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Subdirect

set_option maxRecDepth 1000

namespace SemigroupBasis.CoRoots.Order6LeeZhangClass76

open SemigroupBasis
open SemigroupBasis.Examples

def boundedClassIndex : Nat := 76

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxy : Word Nat := w 0 [0, 1]
def xxxy : Word Nat := w 0 [0, 0, 1]
def xyy : Word Nat := w 0 [1, 1]
def xyyy : Word Nat := w 0 [1, 1, 1]
def xyx : Word Nat := w 0 [1, 0]
def yxy : Word Nat := w 1 [0, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]

def rightPowerLaw : Identity Nat := ⟨xxxy, xxy⟩
def leftPowerLaw : Identity Nat := ⟨xyyy, xyy⟩
def rotationLaw : Identity Nat := ⟨xyx, yxy⟩
def alternatingLaw : Identity Nat := ⟨xyx, xyxy⟩

/-- The direct Lee--Zhang Condition 3 basis. -/
def directBasis : List (Identity Nat) :=
  [rightPowerLaw, leftPowerLaw, rotationLaw, alternatingLaw]

/-- The exact catalogue orientation requested by bounded class 76:
`yxxx = yxx`, `yyyx = yyx`, `xyx = yxy`, `xyx = yxyx`. -/
def basis : List (Identity Nat) :=
  reversedBasis directBasis

theorem basis_is_catalogue_orientation :
    basis =
      [⟨w 1 [0, 0, 0], w 1 [0, 0]⟩,
       ⟨w 1 [1, 1, 0], w 1 [1, 0]⟩,
       ⟨w 0 [1, 0], w 1 [0, 1]⟩,
       ⟨w 0 [1, 0], w 1 [0, 1, 0]⟩] := by
  rfl

private def instantiateTwoWords
    (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private theorem bind_append
    (u v : Word Nat) (sigma : Nat → Word Nat) :
    (u ++ v).bind sigma = u.bind sigma ++ v.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (tau sigma : Nat → Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem basisRightPower : Derives directBasis xxxy xxy :=
  Derives.fromBasis (e := rightPowerLaw) (by simp [directBasis])

private theorem basisLeftPower : Derives directBasis xyyy xyy :=
  Derives.fromBasis (e := leftPowerLaw) (by simp [directBasis])

private theorem basisRotation : Derives directBasis xyx yxy :=
  Derives.fromBasis (e := rotationLaw) (by simp [directBasis])

private theorem basisAlternating : Derives directBasis xyx xyxy :=
  Derives.fromBasis (e := alternatingLaw) (by simp [directBasis])

theorem derivesRightPowerExpansion (u suffix : Word Nat) :
    Derives directBasis
      ((u ++ u) ++ suffix) (((u ++ u) ++ u) ++ suffix) := by
  have substituted :=
    Derives.subst basisRightPower (instantiateTwoWords u suffix)
  simpa [rightPowerLaw, xxxy, xxy, w, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted.symm

theorem derivesLeftPowerExpansion (stem u : Word Nat) :
    Derives directBasis
      (stem ++ (u ++ u)) (stem ++ ((u ++ u) ++ u)) := by
  have substituted :=
    Derives.subst basisLeftPower (instantiateTwoWords stem u)
  simpa [leftPowerLaw, xyyy, xyy, w, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted.symm

theorem derivesRotation (u v : Word Nat) :
    Derives directBasis ((u ++ v) ++ u) ((v ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisRotation (instantiateTwoWords u v)
  simpa [rotationLaw, xyx, yxy, w, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesAlternating (u v : Word Nat) :
    Derives directBasis
      ((u ++ v) ++ u) (((u ++ v) ++ u) ++ v) := by
  have substituted :=
    Derives.subst basisAlternating (instantiateTwoWords u v)
  simpa [alternatingLaw, xyx, xyxy, w, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- The fourth law expands the square of every genuinely product-valued
block to its cube. This is the only top-level replacement needed when an
`S4_70` power-law substitution is not protected by an outer context. -/
theorem derivesProductPowerExpansion (u v : Word Nat) :
    Derives directBasis
      ((u ++ v) ++ (u ++ v))
      (((u ++ v) ++ (u ++ v)) ++ (u ++ v)) := by
  have first :=
    Derives.appendRight (derivesAlternating u v) v
  have second :=
    Derives.appendRight
      (Derives.prepend u (derivesAlternating v u)) v
  exact Derives.trans
    (by simpa [Word.append_assoc] using first)
    (by simpa [Word.append_assoc] using second)

/-! ## The five retained `S4_70` laws -/

theorem derivesS4LeftDuplication (u v : Word Nat) :
    Derives directBasis
      ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have first := derivesAlternating u v
  have second :=
    Derives.prepend u (derivesRotation v u)
  exact first.trans <| by
    simpa [Word.append_assoc] using second

theorem derivesS4RightDuplication (u v : Word Nat) :
    Derives directBasis
      ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have first := derivesRotation u v
  have second := derivesAlternating v u
  have third :=
    Derives.appendRight (Derives.symm (derivesRotation u v)) u
  exact first.trans <| second.trans <| by
    simpa [Word.append_assoc] using third

theorem derivesS4MiddleDuplication (u v : Word Nat) :
    Derives directBasis
      ((u ++ v) ++ u) (((u ++ v) ++ v) ++ u) := by
  have first := derivesRotation u v
  have second := derivesAlternating v u
  have third := Derives.prepend v (derivesAlternating u v)
  have fourth :=
    Derives.appendRight
      (Derives.prepend v (derivesRotation u v)) v
  have fifth :=
    Derives.symm (derivesRotation u (v ++ v))
  have thirdStep :
      Derives directBasis
        (((v ++ u) ++ v) ++ u)
        ((((v ++ u) ++ v) ++ u) ++ v) := by
    simpa [Word.append_assoc] using third
  have fourthStep :
      Derives directBasis
        ((((v ++ u) ++ v) ++ u) ++ v)
        ((((v ++ v) ++ u) ++ v) ++ v) := by
    simpa [Word.append_assoc] using fourth
  have fifthStep :
      Derives directBasis
        ((((v ++ v) ++ u) ++ v) ++ v)
        (((u ++ v) ++ v) ++ u) := by
    simpa [Word.append_assoc] using fifth
  exact first.trans <| second.trans <|
    thirdStep.trans <| fourthStep.trans fifthStep

private def SameSupport (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

private theorem SameSupport.refl (word : Word Nat) :
    SameSupport word word := by
  intro letter
  rfl

private theorem SameSupport.symm {left right : Word Nat}
    (same : SameSupport left right) : SameSupport right left := by
  intro letter
  exact (same letter).symm

private theorem SameSupport.trans {left middle right : Word Nat}
    (first : SameSupport left middle)
    (second : SameSupport middle right) : SameSupport left right := by
  intro letter
  exact (first letter).trans (second letter)

private theorem SameSupport.prepend (stem : Word Nat)
    {left right : Word Nat} (same : SameSupport left right) :
    SameSupport (stem ++ left) (stem ++ right) := by
  intro letter
  simp only [Word.toList_append, List.mem_append]
  exact or_congr Iff.rfl (same letter)

private theorem SameSupport.append (suffix : Word Nat)
    {left right : Word Nat} (same : SameSupport left right) :
    SameSupport (left ++ suffix) (right ++ suffix) := by
  intro letter
  simp only [Word.toList_append, List.mem_append]
  exact or_congr (same letter) Iff.rfl

private theorem SameSupport.bind {left right : Word Nat}
    (same : SameSupport left right) (sigma : Nat → Word Nat) :
    SameSupport (left.bind sigma) (right.bind sigma) := by
  intro letter
  simp only [Word.toList_bind, List.mem_flatMap]
  constructor
  · rintro ⟨source, sourceMember, letterMember⟩
    exact ⟨source, (same source).mp sourceMember, letterMember⟩
  · rintro ⟨source, sourceMember, letterMember⟩
    exact ⟨source, (same source).mpr sourceMember, letterMember⟩

private theorem s4BasisLaw_sameSupport
    (identity : Identity Nat)
    (member : identity ∈ connectedComponentFourBasis) :
    SameSupport identity.lhs identity.rhs := by
  simp only [connectedComponentFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    intro letter <;>
    simp [SameSupport, connectedComponentPowerLaw,
      connectedComponentLeftDuplicationLaw,
      connectedComponentMiddleDuplicationLaw,
      connectedComponentRightDuplicationLaw,
      connectedComponentAlternatingLaw,
      connectedComponentRotationLaw,
      connectedComponentXX, connectedComponentXXX,
      connectedComponentXYX, connectedComponentXXYX,
      connectedComponentXYYX, connectedComponentXYXX,
      connectedComponentXYXY, connectedComponentYXY, Word.toList] <;>
    omega

private theorem s4Derives_sameSupport {left right : Word Nat}
    (derivation : Derives connectedComponentFourBasis left right) :
    SameSupport left right := by
  induction derivation with
  | fromBasis member =>
      exact s4BasisLaw_sameSupport _ member
  | refl word =>
      exact SameSupport.refl word
  | symm _ ih =>
      exact ih.symm
  | trans _ _ first second =>
      exact first.trans second
  | prepend stem _ ih =>
      exact ih.prepend stem
  | appendRight _ suffix ih =>
      exact ih.append suffix
  | subst _ sigma ih =>
      exact ih.bind sigma

private def HasTwo (word : Word Nat) : Prop :=
  ∃ first, first ∈ word.toList ∧
    ∃ second, second ∈ word.toList ∧ first ≠ second

private theorem HasTwo.of_sameSupport {left right : Word Nat}
    (same : SameSupport left right) (two : HasTwo left) :
    HasTwo right := by
  rcases two with ⟨first, firstMember, second, secondMember, different⟩
  exact ⟨first, (same first).mp firstMember,
    second, (same second).mp secondMember, different⟩

/-- Replay an arbitrary `S4_70` derivation before one fixed nonempty suffix.
The suffix protects every use of `xx = xxx`. -/
theorem liftS4DerivationBeforeSuffix
    {left right : Word Nat}
    (derivation : Derives connectedComponentFourBasis left right)
    (suffix : Word Nat) (sigma : Nat → Word Nat) :
    Derives directBasis
      (left.bind sigma ++ suffix) (right.bind sigma ++ suffix) := by
  induction derivation generalizing suffix sigma with
  | fromBasis member =>
      simp only [connectedComponentFourBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [connectedComponentPowerLaw,
          connectedComponentXX, connectedComponentXXX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesRightPowerExpansion (sigma 0) suffix
      · simpa [connectedComponentLeftDuplicationLaw,
          connectedComponentXYX, connectedComponentXXYX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesS4LeftDuplication (sigma 0) (sigma 1)) suffix
      · simpa [connectedComponentMiddleDuplicationLaw,
          connectedComponentXYX, connectedComponentXYYX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesS4MiddleDuplication (sigma 0) (sigma 1)) suffix
      · simpa [connectedComponentRightDuplicationLaw,
          connectedComponentXYX, connectedComponentXYXX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesS4RightDuplication (sigma 0) (sigma 1)) suffix
      · simpa [connectedComponentAlternatingLaw,
          connectedComponentXYX, connectedComponentXYXY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight (derivesAlternating (sigma 0) (sigma 1)) suffix
      · simpa [connectedComponentRotationLaw,
          connectedComponentXYX, connectedComponentYXY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight (derivesRotation (sigma 0) (sigma 1)) suffix
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact (ih suffix sigma).symm
  | trans _ _ first second =>
      exact (first suffix sigma).trans (second suffix sigma)
  | prepend stem _ ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind sigma) (ih suffix sigma)
  | appendRight _ post ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (post.bind sigma ++ suffix) sigma
  | subst _ tau ih =>
      simpa [bind_bind] using
        ih suffix (fun letter => (tau letter).bind sigma)

/-- Replay an arbitrary `S4_70` derivation after one fixed nonempty prefix. -/
theorem liftS4DerivationAfterPrefix
    {left right : Word Nat}
    (derivation : Derives connectedComponentFourBasis left right)
    (stem : Word Nat) (sigma : Nat → Word Nat) :
    Derives directBasis
      (stem ++ left.bind sigma) (stem ++ right.bind sigma) := by
  induction derivation generalizing stem sigma with
  | fromBasis member =>
      simp only [connectedComponentFourBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [connectedComponentPowerLaw,
          connectedComponentXX, connectedComponentXXX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesLeftPowerExpansion stem (sigma 0)
      · simpa [connectedComponentLeftDuplicationLaw,
          connectedComponentXYX, connectedComponentXXYX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesS4LeftDuplication (sigma 0) (sigma 1))
      · simpa [connectedComponentMiddleDuplicationLaw,
          connectedComponentXYX, connectedComponentXYYX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesS4MiddleDuplication (sigma 0) (sigma 1))
      · simpa [connectedComponentRightDuplicationLaw,
          connectedComponentXYX, connectedComponentXYXX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesS4RightDuplication (sigma 0) (sigma 1))
      · simpa [connectedComponentAlternatingLaw,
          connectedComponentXYX, connectedComponentXYXY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesAlternating (sigma 0) (sigma 1))
      · simpa [connectedComponentRotationLaw,
          connectedComponentXYX, connectedComponentYXY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesRotation (sigma 0) (sigma 1))
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact (ih stem sigma).symm
  | trans _ _ first second =>
      exact (first stem sigma).trans (second stem sigma)
  | prepend pre _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (stem ++ pre.bind sigma) sigma
  | appendRight _ suffix ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (ih stem sigma) (suffix.bind sigma)
  | subst _ tau ih =>
      simpa [bind_bind] using
        ih stem (fun letter => (tau letter).bind sigma)

private theorem tail_ne_nil_of_hasTwoSquare
    (word : Word Nat) (two : HasTwo (word ++ word)) :
    word.tail ≠ [] := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simpa [HasTwo, Word.toList, Word.append] using two
      | cons next rest =>
          simp

/-- Away from unary words, the direct four-law theory replays every
`S4_70` derivation. Context constructors are delegated to the two protected
transport lemmas above. -/
private theorem liftS4DerivationOfHasTwo
    {left right : Word Nat}
    (derivation : Derives connectedComponentFourBasis left right)
    (sigma : Nat → Word Nat)
    (two : HasTwo (left.bind sigma)) :
    Derives directBasis (left.bind sigma) (right.bind sigma) := by
  induction derivation generalizing sigma with
  | fromBasis member =>
      simp only [connectedComponentFourBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · have product : (sigma 0).tail ≠ [] := by
          apply tail_ne_nil_of_hasTwoSquare (sigma 0)
          simpa [connectedComponentPowerLaw,
            connectedComponentXX, Word.bind, Word.append,
            Word.singleton, Word.append_assoc] using two
        cases value : sigma 0 with
        | mk head tail =>
            cases tail with
            | nil =>
                exact (product (by simpa [value])).elim
            | cons next rest =>
                simpa [connectedComponentPowerLaw,
                  connectedComponentXX, connectedComponentXXX,
                  value, Word.bind, Word.append, Word.singleton,
                  Word.append_assoc] using
                  derivesProductPowerExpansion
                    (Word.singleton head) (Word.mk next rest)
      · simpa [connectedComponentLeftDuplicationLaw,
          connectedComponentXYX, connectedComponentXXYX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesS4LeftDuplication (sigma 0) (sigma 1)
      · simpa [connectedComponentMiddleDuplicationLaw,
          connectedComponentXYX, connectedComponentXYYX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesS4MiddleDuplication (sigma 0) (sigma 1)
      · simpa [connectedComponentRightDuplicationLaw,
          connectedComponentXYX, connectedComponentXYXX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesS4RightDuplication (sigma 0) (sigma 1)
      · simpa [connectedComponentAlternatingLaw,
          connectedComponentXYX, connectedComponentXYXY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesAlternating (sigma 0) (sigma 1)
      · simpa [connectedComponentRotationLaw,
          connectedComponentXYX, connectedComponentYXY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesRotation (sigma 0) (sigma 1)
  | refl =>
      exact Derives.refl _
  | symm derivation ih =>
      apply Derives.symm
      apply ih sigma
      exact HasTwo.of_sameSupport
        ((s4Derives_sameSupport derivation).bind sigma).symm two
  | trans firstDerivation secondDerivation first second =>
      have middleTwo :=
        HasTwo.of_sameSupport
          ((s4Derives_sameSupport firstDerivation).bind sigma) two
      exact (first sigma two).trans (second sigma middleTwo)
  | prepend stem derivation ih =>
      simpa [bind_append, Word.append_assoc] using
        liftS4DerivationAfterPrefix derivation
          (stem.bind sigma) sigma
  | appendRight derivation suffix ih =>
      simpa [bind_append, Word.append_assoc] using
        liftS4DerivationBeforeSuffix derivation
          (suffix.bind sigma) sigma
  | subst derivation tau ih =>
      simpa [bind_bind] using
        ih (fun letter => (tau letter).bind sigma) (by
          simpa [bind_bind] using two)

/-! ## The unary length strata supplied by `S3_4` -/

private theorem allLetters_eq_head_of_not_hasTwo
    (word : Word Nat) (notTwo : ¬HasTwo word) :
    ∀ letter, letter ∈ word.toList → letter = word.head := by
  intro letter member
  by_cases equal : letter = word.head
  · exact equal
  · have contradiction : False := by
      apply notTwo
      refine ⟨letter, member, word.head, ?_, equal⟩
      simp [Word.toList]
    exact contradiction.elim

private theorem list_eq_replicate_of_all_eq
    (letter : Nat) : ∀ letters : List Nat,
    (∀ tested, tested ∈ letters → tested = letter) →
      letters = List.replicate letters.length letter
  | [], _ => rfl
  | head :: tail, allEqual => by
      have headEqual : head = letter :=
        allEqual head (List.Mem.head tail)
      have tailEqual :
          ∀ tested, tested ∈ tail → tested = letter := by
        intro tested member
        exact allEqual tested (List.Mem.tail head member)
      subst head
      simp only [List.length_cons, List.replicate_succ]
      exact congrArg (List.cons letter)
        (list_eq_replicate_of_all_eq letter tail tailEqual)

private theorem unaryWords_eq_of_head_length
    (left right : Word Nat)
    (leftUnary :
      ∀ letter, letter ∈ left.toList → letter = left.head)
    (rightUnary :
      ∀ letter, letter ∈ right.toList → letter = right.head)
    (heads : left.head = right.head)
    (lengths : left.toList.length = right.toList.length) :
    left = right := by
  apply Word.toList_injective
  rw [list_eq_replicate_of_all_eq left.head left.toList leftUnary,
    list_eq_replicate_of_all_eq right.head right.toList rightUnary,
    heads, lengths]

private theorem heads_eq_of_unary_sameSupport
    {left right : Word Nat}
    (leftUnary :
      ∀ letter, letter ∈ left.toList → letter = left.head)
    (same : SameSupport left right) :
    left.head = right.head := by
  have rightHeadInLeft : right.head ∈ left.toList :=
    (same right.head).mpr (by simp [Word.toList])
  exact (leftUnary right.head rightHeadInLeft).symm

private theorem basisUnaryFourToThree (letter : Nat) :
    Derives directBasis (w letter [letter, letter, letter])
      (w letter [letter, letter]) := by
  have substituted :=
    Derives.subst basisRightPower
      (instantiateTwoWords (Word.singleton letter) (Word.singleton letter))
  simpa [rightPowerLaw, xxxy, xxy, w, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesUnaryExtra
    (letter : Nat) : ∀ extra : List Nat,
    (∀ tested, tested ∈ extra → tested = letter) →
      Derives directBasis
        (w letter (letter :: letter :: extra))
        (w letter [letter, letter])
  | [], _ => Derives.refl _
  | next :: rest, allEqual => by
      have nextEqual : next = letter :=
        allEqual next (List.Mem.head rest)
      have restEqual :
          ∀ tested, tested ∈ rest → tested = letter := by
        intro tested member
        exact allEqual tested (List.Mem.tail next member)
      subst next
      cases rest with
      | nil =>
          exact basisUnaryFourToThree letter
      | cons restHead restTail =>
          have first :=
            Derives.appendRight (basisUnaryFourToThree letter)
              (w restHead restTail)
          have second :=
            derivesUnaryExtra letter (restHead :: restTail) restEqual
          refine Derives.trans ?_ second
          simpa [w, Word.append, Word.append_assoc] using first

theorem derivesUnaryLong (word : Word Nat)
    (long : 3 ≤ word.toList.length)
    (unary :
      ∀ letter, letter ∈ word.toList → letter = word.head) :
    Derives directBasis word (w word.head [word.head, word.head]) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third extra =>
              have secondEqual : second = head :=
                unary second (by simp [Word.toList])
              have thirdEqual : third = head :=
                unary third (by simp [Word.toList])
              have extraEqual :
                  ∀ tested, tested ∈ extra → tested = head := by
                intro tested member
                exact unary tested (by simp [Word.toList, member])
              subst second
              subst third
              exact derivesUnaryExtra head extra extraEqual

private def projectionLengthState (length : Nat) : Fin 3 :=
  if length = 1 then 2 else if length = 2 then 1 else 0

private def projectionLengthValuation : Nat → Fin 3 :=
  fun _ => 2

private theorem projectionEval_length (word : Word Nat) :
    projectionQuadraticThree.semigroup.eval
        projectionLengthValuation word =
      projectionLengthState word.toList.length := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          rfl
      | cons second rest =>
          cases rest with
          | nil =>
              rfl
          | cons third extra =>
              simpa [projectionLengthState, Word.toList] using
                projectionQuadraticEval_long projectionLengthValuation
                  head second third extra

private theorem projectionLengthState_capped_injective
    {leftLength rightLength : Nat}
    (leftPositive : 0 < leftLength)
    (rightPositive : 0 < rightLength)
    (equal :
      projectionLengthState leftLength =
        projectionLengthState rightLength) :
    min leftLength 3 = min rightLength 3 := by
  have values := congrArg Fin.val equal
  by_cases leftOne : leftLength = 1
  · subst leftLength
    by_cases rightOne : rightLength = 1
    · subst rightLength
      rfl
    · by_cases rightTwo : rightLength = 2
      · subst rightLength
        simp [projectionLengthState] at values
      · have rightLong : 3 ≤ rightLength := by omega
        simp [projectionLengthState, rightOne, rightTwo] at values
  · by_cases leftTwo : leftLength = 2
    · subst leftLength
      by_cases rightOne : rightLength = 1
      · subst rightLength
        simp [projectionLengthState, leftOne] at values
      · by_cases rightTwo : rightLength = 2
        · subst rightLength
          rfl
        · have rightLong : 3 ≤ rightLength := by omega
          simp [projectionLengthState, rightOne, rightTwo] at values
    · have leftLong : 3 ≤ leftLength := by omega
      by_cases rightOne : rightLength = 1
      · subst rightLength
        simp [projectionLengthState, leftOne, leftTwo] at values
      · by_cases rightTwo : rightLength = 2
        · subst rightLength
          simp [projectionLengthState, leftOne, leftTwo] at values
        · have rightLong : 3 ≤ rightLength := by omega
          simp [Nat.min_eq_right leftLong,
            Nat.min_eq_right rightLong]

theorem projectionValid_cappedLength
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      projectionQuadraticThree.semigroup) :
    min identity.lhs.toList.length 3 =
      min identity.rhs.toList.length 3 := by
  have evaluated := valid projectionLengthValuation
  rw [projectionEval_length, projectionEval_length] at evaluated
  exact projectionLengthState_capped_injective
    (by simp [Word.toList]) (by simp [Word.toList]) evaluated

/-! ## Completeness of the ambient join -/

theorem directCompleteOfFactorValidities
    (identity : Identity Nat)
    (s4Valid : identity.SatisfiedBy connectedComponentFour.semigroup)
    (s3Valid : identity.SatisfiedBy projectionQuadraticThree.semigroup) :
    Derives directBasis identity.lhs identity.rhs := by
  have s4Derivation :=
    connectedComponentFourBasis_complete.2 identity s4Valid
  have sameSupport := s4Derives_sameSupport s4Derivation
  by_cases leftTwo : HasTwo identity.lhs
  · have lifted :=
      liftS4DerivationOfHasTwo s4Derivation Word.singleton (by
        simpa [bind_singleton] using leftTwo)
    simpa [bind_singleton] using lifted
  · have leftUnary :=
      allLetters_eq_head_of_not_hasTwo identity.lhs leftTwo
    have rightNotTwo : ¬HasTwo identity.rhs := by
      intro rightTwo
      exact leftTwo <|
        HasTwo.of_sameSupport sameSupport.symm rightTwo
    have rightUnary :=
      allLetters_eq_head_of_not_hasTwo identity.rhs rightNotTwo
    have heads := heads_eq_of_unary_sameSupport leftUnary sameSupport
    have capped := projectionValid_cappedLength identity s3Valid
    have leftPositive : 0 < identity.lhs.toList.length := by
      simp [Word.toList]
    have rightPositive : 0 < identity.rhs.toList.length := by
      simp [Word.toList]
    by_cases leftOne : identity.lhs.toList.length = 1
    · have rightOne : identity.rhs.toList.length = 1 := by
        omega
      rw [unaryWords_eq_of_head_length identity.lhs identity.rhs
        leftUnary rightUnary heads (leftOne.trans rightOne.symm)]
      exact Derives.refl _
    · by_cases leftPair : identity.lhs.toList.length = 2
      · have rightPair : identity.rhs.toList.length = 2 := by
          omega
        rw [unaryWords_eq_of_head_length identity.lhs identity.rhs
          leftUnary rightUnary heads (leftPair.trans rightPair.symm)]
        exact Derives.refl _
      · have leftLong : 3 ≤ identity.lhs.toList.length := by
          omega
        have rightLong : 3 ≤ identity.rhs.toList.length := by
          omega
        have leftNormal :=
          derivesUnaryLong identity.lhs leftLong leftUnary
        have rightNormal :=
          derivesUnaryLong identity.rhs rightLong rightUnary
        have middle :
            w identity.lhs.head [identity.lhs.head, identity.lhs.head] =
              w identity.rhs.head
                [identity.rhs.head, identity.rhs.head] := by
          rw [heads]
        exact leftNormal.trans <| by
          rw [middle]
          exact rightNormal.symm

private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def finiteBasisOf
    (candidate : List (Identity Nat)) : List (Identity (Fin 2)) :=
  candidate.map fun identity => identity.map toFinTwo

private theorem modelsOfFiniteChecks
    (candidate : List (Identity Nat))
    (roundTrip :
      candidate.all (fun identity =>
        decide ((identity.map toFinTwo).map Fin.val = identity)) = true)
    (table : FiniteTable)
    (checked : (finiteBasisOf candidate).all table.checkIdentity = true) :
    Models table.semigroup candidate := by
  intro identity member
  have finiteMember : identity.map toFinTwo ∈ finiteBasisOf candidate :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinTwo).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp roundTrip) identity member
  rw [restored] at finiteValid
  exact finiteValid

theorem directIntersection :
    IntersectionBasis connectedComponentFour.semigroup
      projectionQuadraticThree.semigroup directBasis where
  leftModels := modelsOfFiniteChecks directBasis (by decide)
    connectedComponentFour (by decide)
  rightModels := modelsOfFiniteChecks directBasis (by decide)
    projectionQuadraticThree (by decide)
  complete := directCompleteOfFactorValidities

private theorem directAxiomsDeriveInCatalogueBasis
    (identity : Identity Nat) (member : identity ∈ directBasis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [directBasis, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · have base :
        Derives basis (w 1 [1, 1, 0]) (w 1 [1, 0]) :=
        Derives.fromBasis (basis := basis)
          (e := ⟨w 1 [1, 1, 0], w 1 [1, 0]⟩) (by
          rw [basis_is_catalogue_orientation]
          simp)
    have renamed :=
      Derives.subst base
        (instantiateTwoWords (Word.singleton 1) (Word.singleton 0))
    simpa [rightPowerLaw, xxxy, xxy, w, instantiateTwoWords,
      Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using renamed
  · have base :
        Derives basis (w 1 [0, 0, 0]) (w 1 [0, 0]) :=
        Derives.fromBasis (basis := basis)
          (e := ⟨w 1 [0, 0, 0], w 1 [0, 0]⟩) (by
          rw [basis_is_catalogue_orientation]
          simp)
    have renamed :=
      Derives.subst base
        (instantiateTwoWords (Word.singleton 1) (Word.singleton 0))
    simpa [leftPowerLaw, xyyy, xyy, w, instantiateTwoWords,
      Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using renamed
  · exact Derives.fromBasis (basis := basis) (e := rotationLaw) (by
      rw [basis_is_catalogue_orientation]
      simp [rotationLaw, xyx, yxy, w])
  · have first : Derives basis xyx yxy :=
        Derives.fromBasis (basis := basis) (e := ⟨xyx, yxy⟩) (by
          rw [basis_is_catalogue_orientation]
          simp [xyx, yxy, w])
    have secondBase : Derives basis xyx (w 1 [0, 1, 0]) :=
      Derives.fromBasis (basis := basis)
        (e := ⟨xyx, w 1 [0, 1, 0]⟩) (by
        rw [basis_is_catalogue_orientation]
        simp [xyx, w])
    have second :=
      Derives.subst secondBase
        (instantiateTwoWords (Word.singleton 1) (Word.singleton 0))
    exact first.trans <| by
      simpa [alternatingLaw, xyxy, yxy, w, instantiateTwoWords,
        Word.bind, Word.append, Word.singleton,
        Word.append_assoc] using second

private theorem basisForOfFactorEmbeddings
    {carrier : Type}
    {target : Semigroup carrier}
    (directModels : Models target directBasis)
    (catalogueModels : Models target basis)
    (s4Embedding : Embedding connectedComponentFour.semigroup target)
    (s3Embedding : Embedding projectionQuadraticThree.semigroup target) :
    BasisFor target basis := by
  have directComplete : BasisFor target directBasis := by
    refine ⟨directModels, ?_⟩
    intro identity valid
    exact directIntersection.complete identity
      (s4Embedding.pullback_identity identity valid)
      (s3Embedding.pullback_identity identity valid)
  exact directComplete.replace catalogueModels
    directAxiomsDeriveInCatalogueBasis

private def row6
    (a b c d e f : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then a else if column = 1 then b else
    if column = 2 then c else if column = 3 then d else
      if column = 4 then e else f

namespace S6_5548

def catalogueTableSha256 : String :=
  "bdc0ecd6a4e79631b32479fbb97e4df01d906748839fce13d0a0257ed1c40fb0"

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 2 0 right else
        if left = 3 then row6 0 0 0 1 0 0 right else
          if left = 4 then row6 0 0 0 0 4 0 right else
            row6 0 0 2 0 2 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 3, 1],
   [1, 1, 1, 2, 1, 1],
   [1, 1, 1, 1, 5, 1],
   [1, 1, 3, 1, 3, 6]]

theorem table_eq_catalogueRows :
    (List.ofFn fun left : Fin 6 =>
      List.ofFn fun right : Fin 6 => (table.mul left right).val + 1) =
      catalogueRows := by
  decide

def s4Embedding :
    Embedding connectedComponentFour.semigroup table.semigroup where
  toFun := fun value : Fin 4 =>
    if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else
      if value = 2 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def s3Embedding :
    Embedding projectionQuadraticThree.semigroup table.semigroup where
  toFun := fun value : Fin 3 =>
    if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else
      (3 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

set_option maxHeartbeats 0 in
theorem directModels : Models table.semigroup directBasis :=
  modelsOfFiniteChecks directBasis (by decide) table (by decide)

set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  modelsOfFiniteChecks basis (by decide) table (by decide)

theorem representative_basis : BasisFor table.semigroup basis :=
  basisForOfFactorEmbeddings directModels models s4Embedding s3Embedding

end S6_5548

namespace S6_5558

def catalogueTableSha256 : String :=
  "01465d494f7cb918213ddfd0817afd2a295ae559d430128767d4ecff40860469"

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 2 0 right else
        if left = 3 then row6 0 0 0 1 2 0 right else
          if left = 4 then row6 0 0 0 0 4 0 right else
            row6 0 0 2 2 2 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 3, 1],
   [1, 1, 1, 2, 3, 1],
   [1, 1, 1, 1, 5, 1],
   [1, 1, 3, 3, 3, 6]]

theorem table_eq_catalogueRows :
    (List.ofFn fun left : Fin 6 =>
      List.ofFn fun right : Fin 6 => (table.mul left right).val + 1) =
      catalogueRows := by
  decide

def s4Embedding :
    Embedding connectedComponentFour.semigroup table.semigroup where
  toFun := fun value : Fin 4 =>
    if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else
      if value = 2 then (5 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def s3Embedding :
    Embedding projectionQuadraticThree.semigroup table.semigroup where
  toFun := fun value : Fin 3 =>
    if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else
      (3 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

set_option maxHeartbeats 0 in
theorem directModels : Models table.semigroup directBasis :=
  modelsOfFiniteChecks directBasis (by decide) table (by decide)

set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  modelsOfFiniteChecks basis (by decide) table (by decide)

theorem representative_basis : BasisFor table.semigroup basis :=
  basisForOfFactorEmbeddings directModels models s4Embedding s3Embedding

end S6_5558

namespace S6_9632

def catalogueTableSha256 : String :=
  "a5a7e3e79f07bfb82d20c068bf13cc786466cb78cb5c659f06784660c7479357"

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 3 4 4 right else
    if left = 1 then row6 0 0 0 3 4 4 right else
      if left = 2 then row6 0 0 1 3 4 4 right else
        if left = 3 then row6 3 3 3 3 3 3 right else
          if left = 4 then row6 3 3 3 3 3 4 right else
            row6 3 3 3 3 3 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) :=
  [[1, 1, 1, 4, 5, 5],
   [1, 1, 1, 4, 5, 5],
   [1, 1, 2, 4, 5, 5],
   [4, 4, 4, 4, 4, 4],
   [4, 4, 4, 4, 4, 5],
   [4, 4, 4, 4, 4, 6]]

theorem table_eq_catalogueRows :
    (List.ofFn fun left : Fin 6 =>
      List.ofFn fun right : Fin 6 => (table.mul left right).val + 1) =
      catalogueRows := by
  decide

def s4Embedding :
    Embedding connectedComponentFour.semigroup table.semigroup where
  toFun := fun value : Fin 4 =>
    if value = 0 then (3 : Fin 6) else if value = 1 then (4 : Fin 6) else
      if value = 2 then (0 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

def s3Embedding :
    Embedding projectionQuadraticThree.semigroup table.semigroup where
  toFun := fun value : Fin 3 =>
    if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else
      (2 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

set_option maxHeartbeats 0 in
theorem directModels : Models table.semigroup directBasis :=
  modelsOfFiniteChecks directBasis (by decide) table (by decide)

set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  modelsOfFiniteChecks basis (by decide) table (by decide)

theorem representative_basis : BasisFor table.semigroup basis :=
  basisForOfFactorEmbeddings directModels models s4Embedding s3Embedding

end S6_9632

end SemigroupBasis.CoRoots.Order6LeeZhangClass76
