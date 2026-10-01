import SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071Raw15Obstruction
import SemigroupBasis.CoRoots.S5_240Completeness

/-!
# Rank071 exact approved B16: guarded complete-lower replay

Fable0407 approves precisely the immutable raw15 plus xyzt=xyyzt.
The negative raw15 theorem remains untouched. Soundness reuses its checked
raw models and missing-bridge validity; no extra displayed law is introduced.
Every lower axiom replays behind an arbitrary nonempty leading guard.
-/

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071SigmaPlusReplay

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071Raw15Obstruction
  (law00 law01 law02 law03 law10 law14 missingLaw)

def basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071Raw15Obstruction.basis ++ [missingLaw]

abbrev displayedBasisSHA256 : String :=
  "3420758b2d067a6b5fc47435b4d40deeb380b37c4f1db78c65249db80c17c605"
abbrev leftTable : FiniteTable :=
  SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071Raw15Obstruction.leftTable
abbrev rightTable : FiniteTable :=
  SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071Raw15Obstruction.rightTable
abbrev lowerBasis : List (Identity Nat) := SemigroupBasis.CoRoots.S5_240.basis
abbrev LowerSignature := SemigroupBasis.CoRoots.S5_240.SameEndpointSuffixSignature

theorem basis_length : basis.length = 16 := by decide

theorem modelsLeft : Models leftTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with old | rfl
  · exact SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071Raw15Obstruction.modelsLeft identity old
  · exact SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071Raw15Obstruction.missingLaw_leftValid

theorem modelsRight : Models rightTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with old | rfl
  · exact SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071Raw15Obstruction.modelsRight identity old
  · exact SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071Raw15Obstruction.missingLaw_rightValid

private def threeWords (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | _ => third

private def fourWords (guard first second third : Word Nat) : Nat → Word Nat
  | 0 => guard
  | 1 => first
  | 2 => second
  | _ => third

theorem derivesPower (block : Word Nat) :
    Derives basis (block ++ block) ((block ++ block) ++ block) := by
  have primitive : Derives basis law00.lhs law00.rhs :=
    Derives.fromBasis (e := law00) (by decide)
  have mapped := Derives.subst primitive (threeWords block block block)
  simpa [law00, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem derivesReturnDuplication (block gap : Word Nat) :
    Derives basis ((block ++ gap) ++ block) (((block ++ block) ++ gap) ++ block) := by
  have primitive : Derives basis law01.lhs law01.rhs :=
    Derives.fromBasis (e := law01) (by decide)
  have mapped := (Derives.subst primitive (threeWords block gap block)).symm
  simpa [law01, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem derivesGuardedMarkerSwitch (guard first second : Word Nat) :
    Derives basis (guard ++ ((first ++ second) ++ second))
      (guard ++ ((second ++ first) ++ first)) := by
  have primitive : Derives basis law14.lhs law14.rhs :=
    Derives.fromBasis (e := law14) (by decide)
  have mapped := Derives.subst primitive (threeWords guard first second)
  simpa [law14, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem derivesGuardedLongInsertion (guard first second third : Word Nat) :
    Derives basis (guard ++ ((first ++ second) ++ third))
      (guard ++ (((first ++ first) ++ second) ++ third)) := by
  have primitive : Derives basis missingLaw.lhs missingLaw.rhs :=
    Derives.fromBasis (e := missingLaw) (by decide)
  have mapped := Derives.subst primitive (fourWords guard first second third)
  simpa [missingLaw, fourWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

/-- The three-edge raw-law square switch, with arbitrary nonempty blocks. -/
theorem derivesSquaresCommute (first second : Word Nat) :
    Derives basis ((first ++ first) ++ (second ++ second))
      ((second ++ second) ++ (first ++ first)) := by
  have step0 : Derives basis ((first ++ first) ++ (second ++ second))
      (((first ++ second) ++ first) ++ first) := by
    have primitive : Derives basis law02.lhs law02.rhs :=
      Derives.fromBasis (e := law02) (by decide)
    have mapped := Derives.subst primitive (threeWords first second first)
    simpa [law02, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  have step1 : Derives basis (((first ++ second) ++ first) ++ first)
      (((second ++ first) ++ second) ++ first) := by
    have primitive : Derives basis law10.lhs law10.rhs :=
      Derives.fromBasis (e := law10) (by decide)
    have mapped := Derives.subst primitive (threeWords first second first)
    simpa [law10, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  have step2 : Derives basis (((second ++ first) ++ second) ++ first)
      ((second ++ second) ++ (first ++ first)) := by
    have primitive : Derives basis law03.lhs law03.rhs :=
      Derives.fromBasis (e := law03) (by decide)
    have mapped := (Derives.subst primitive (threeWords second first first)).symm
    simpa [law03, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped
  exact step0.trans (step1.trans step2)

theorem guardedLowerAxiom (identity : Identity Nat) (member : identity ∈ lowerBasis)
    (substitution : Nat → Word Nat) (guard : Word Nat) :
    Derives basis (guard ++ identity.lhs.bind substitution)
      (guard ++ identity.rhs.bind substitution) := by
  simp only [lowerBasis, SemigroupBasis.CoRoots.S5_240.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · have literal : SemigroupBasis.CoRoots.S5_240.powerLaw =
        (⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.prepend guard (derivesPower (substitution 0))
  · have literal : SemigroupBasis.CoRoots.S5_240.markerSwitchLaw =
        (⟨Word.mk 0 [1, 1], Word.mk 1 [0, 0]⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      derivesGuardedMarkerSwitch guard (substitution 0) (substitution 1)
  · have literal : SemigroupBasis.CoRoots.S5_240.longInsertionLaw =
        (⟨Word.mk 0 [1, 2], Word.mk 0 [0, 1, 2]⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      derivesGuardedLongInsertion guard (substitution 0) (substitution 1) (substitution 2)

private theorem bind_append (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution = left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second = word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) : word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

theorem liftLowerWithPrefix {left right : Word Nat} (derivation : Derives lowerBasis left right)
    (guard : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis (guard ++ left.bind substitution) (guard ++ right.bind substitution) := by
  induction derivation generalizing guard substitution with
  | fromBasis member => exact guardedLowerAxiom _ member substitution guard
  | refl => exact Derives.refl _
  | symm _ induction => exact (induction guard substitution).symm
  | trans _ _ first second => exact (first guard substitution).trans (second guard substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using induction (guard ++ stem.bind substitution) substitution
  | appendRight _ tail induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (induction guard substitution) (tail.bind substitution)
  | subst _ next induction =>
      simpa [bind_bind] using induction guard (fun letter => (next letter).bind substitution)

theorem derivesSamePrefixOfLowerValid (left right guard : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy rightTable.semigroup) :
    Derives basis (guard ++ left) (guard ++ right) := by
  have lower := SemigroupBasis.CoRoots.S5_240.basis_complete.2 (Identity.mk left right) valid
  simpa [bind_singleton] using liftLowerWithPrefix lower guard Word.singleton

/-- Duplicate the actual first letter when it occurs again, at arbitrary length. -/
private theorem split_at_member {head : Nat} {tail : List Nat} (member : head ∈ tail) :
    ∃ before after, tail = before ++ head :: after := by
  induction tail with
  | nil => simp at member
  | cons first rest induction =>
      rcases List.mem_cons.mp member with equal | later
      · subst first
        exact ⟨[], rest, rfl⟩
      · obtain ⟨before, after, shape⟩ := induction later
        exact ⟨first :: before, after, by simp [shape]⟩

theorem derivesOwnHeadDuplicate (head : Nat) (tail : List Nat) (repeated : head ∈ tail) :
    Derives basis (Word.mk head tail) (Word.mk head (head :: tail)) := by
  obtain ⟨before, after, shape⟩ := split_at_member repeated
  rw [shape]
  cases before with
  | nil =>
      have step := derivesPower (Word.singleton head)
      cases after with
      | nil => simpa [Word.append, Word.singleton] using step
      | cons first rest =>
          simpa [Word.append, Word.singleton] using Derives.appendRight step (Word.mk first rest)
  | cons first rest =>
      have step := derivesReturnDuplication (Word.singleton head) (Word.mk first rest)
      cases after with
      | nil => simpa [Word.append, Word.singleton] using step
      | cons last remaining =>
          have extended := Derives.appendRight step (Word.mk last remaining)
          have leftShape :
              (((Word.singleton head ++ Word.mk first rest) ++ Word.singleton head) ++
                Word.mk last remaining) = Word.mk head (first :: (rest ++ head :: last :: remaining)) := by
            apply Word.toList_injective
            simp [Word.toList_append, Word.toList_singleton, Word.toList, List.append_assoc]
          have rightShape :
              ((((Word.singleton head ++ Word.singleton head) ++ Word.mk first rest) ++
                Word.singleton head) ++ Word.mk last remaining) =
                Word.mk head (head :: first :: (rest ++ head :: last :: remaining)) := by
            apply Word.toList_injective
            simp [Word.toList_append, Word.toList_singleton, Word.toList, List.append_assoc]
          rw [leftShape, rightShape] at extended
          exact extended

theorem derivesOwnHeadSquare (word : Word Nat) (repeated : word.head ∈ word.tail) :
    Derives basis word ((Word.singleton word.head ++ Word.singleton word.head) ++ word) := by
  have one : Derives basis word (Word.singleton word.head ++ word) := by
    cases word with
    | mk head tail => exact derivesOwnHeadDuplicate head tail repeated
  have two := Derives.prepend (Word.singleton word.head) one
  simpa only [Word.append_assoc] using one.trans two

end SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank071SigmaPlusReplay
