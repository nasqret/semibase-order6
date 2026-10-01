import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_6
import SemigroupBasis.CoRoots.S5_303Completeness

/-!
# Rank073: exact twelve-law direct basis and guarded lower replay

The frozen contract's canonical basis has opposite orientation. These are its
literal reverse-word laws, in the same order with the same variable names.
The actual factors are S3_6 opposite and S5_303 direct. No extension law or
unguarded square-commutation principle is assumed.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Replay

open SemigroupBasis

def law00 : Identity Nat := ⟨Word.mk 0 [0], Word.mk 0 [0, 0]⟩
def law01 : Identity Nat := ⟨Word.mk 0 [1, 0, 0], Word.mk 0 [1, 0]⟩
def law02 : Identity Nat := ⟨Word.mk 1 [1, 0, 0], Word.mk 0 [1, 0]⟩
def law03 : Identity Nat := ⟨Word.mk 1 [2, 1, 0, 0], Word.mk 0 [1, 2, 0]⟩
def law04 : Identity Nat := ⟨Word.mk 1 [1, 2, 0, 0], Word.mk 0 [1, 2, 0]⟩
def law05 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [0, 1, 0]⟩
def law06 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 1 [0, 1, 0]⟩
def law07 : Identity Nat := ⟨Word.mk 0 [1, 0], Word.mk 0 [1, 1, 0]⟩
def law08 : Identity Nat := ⟨Word.mk 0 [2, 1, 0], Word.mk 0 [1, 2, 0]⟩
def law09 : Identity Nat := ⟨Word.mk 1 [1, 0, 2, 0], Word.mk 0 [1, 2, 0]⟩
def law10 : Identity Nat := ⟨Word.mk 0 [1, 2, 0], Word.mk 1 [0, 1, 2, 0]⟩
def law11 : Identity Nat := ⟨Word.mk 0 [1, 2], Word.mk 0 [1, 1, 2]⟩

def basis : List (Identity Nat) :=
  [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11]

abbrev displayedBasisSHA256 : String :=
  "9b90d0ae56840cea753b5ebf24f4f32fb10b67c60f415e8894fc0005ca16b0ed"

def leftTable : FiniteTable where
  order := 3
  mul first second := Generated.S3_6.table.mul second first
  assoc := by decide

abbrev rightTable : FiniteTable := Generated.Catalogue.S5_303.table
abbrev lowerBasis : List (Identity Nat) := SemigroupBasis.CoRoots.S5_303.basis
abbrev LowerSignature := SemigroupBasis.CoRoots.S5_303.SameContentEndpointSignature

theorem leftTable_is_actual_opposite :
    leftTable.semigroup = Generated.S3_6.table.semigroup.opposite := rfl

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem basis_length : basis.length = 12 := by decide
theorem modelsLeft : Models leftTable.semigroup basis :=
  FiniteCertificate.checkModels_sound leftTable basis toFinThree (by decide)
theorem modelsRight : Models rightTable.semigroup basis :=
  FiniteCertificate.checkModels_sound rightTable basis toFinThree (by decide)

private def threeWords (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | _ => third

theorem derivesPower (block : Word Nat) :
    Derives basis (block ++ block) ((block ++ block) ++ block) := by
  have primitive : Derives basis law00.lhs law00.rhs := Derives.fromBasis (e := law00) (by decide)
  have mapped := Derives.subst primitive (threeWords block block block)
  simpa [law00, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem derivesReturnDuplication (block gap : Word Nat) :
    Derives basis ((block ++ gap) ++ block) (((block ++ block) ++ gap) ++ block) := by
  have primitive : Derives basis law05.lhs law05.rhs := Derives.fromBasis (e := law05) (by decide)
  have mapped := Derives.subst primitive (threeWords block gap block)
  simpa [law05, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem derivesHeadRetarget (first second : Word Nat) :
    Derives basis ((first ++ second) ++ first) (((second ++ first) ++ second) ++ first) := by
  have primitive : Derives basis law06.lhs law06.rhs := Derives.fromBasis (e := law06) (by decide)
  have mapped := Derives.subst primitive (threeWords first second first)
  simpa [law06, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem derivesGuardedDuplication (guard first second : Word Nat) :
    Derives basis (guard ++ (first ++ second)) (guard ++ ((first ++ first) ++ second)) := by
  have primitive : Derives basis law11.lhs law11.rhs := Derives.fromBasis (e := law11) (by decide)
  have mapped := Derives.subst primitive (threeWords guard first second)
  simpa [law11, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

/-- The two association-fixed edges realizing the guarded lower rotate axiom. -/
theorem derivesGuardedRotate (guard first second : Word Nat) :
    Derives basis (guard ++ ((first ++ second) ++ first))
      (guard ++ ((second ++ first) ++ first)) := by
  have expand : Derives basis (guard ++ ((first ++ second) ++ first))
      (guard ++ (((second ++ second) ++ first) ++ first)) := by
    have primitive : Derives basis law02.lhs law02.rhs := Derives.fromBasis (e := law02) (by decide)
    have mapped := (Derives.subst primitive (threeWords first second first)).symm
    simpa [law02, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.prepend guard mapped
  have contract : Derives basis (guard ++ (((second ++ second) ++ first) ++ first))
      (guard ++ ((second ++ first) ++ first)) := by
    simpa only [Word.append_assoc] using
      Derives.appendRight (derivesGuardedDuplication guard second first).symm first
  exact expand.trans contract

theorem derivesInteriorSwap (first second third : Word Nat) :
    Derives basis (((first ++ second) ++ third) ++ first)
      (((first ++ third) ++ second) ++ first) := by
  have primitive : Derives basis law08.lhs law08.rhs := Derives.fromBasis (e := law08) (by decide)
  have mapped := (Derives.subst primitive (threeWords first second third)).symm
  simpa [law08, threeWords, Word.bind, Word.append, Word.singleton, Word.append_assoc] using mapped

theorem guardedLowerAxiom (identity : Identity Nat) (member : identity ∈ lowerBasis)
    (substitution : Nat → Word Nat) (guard : Word Nat) :
    Derives basis (guard ++ identity.lhs.bind substitution) (guard ++ identity.rhs.bind substitution) := by
  simp only [lowerBasis, SemigroupBasis.CoRoots.S5_303.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · have literal : SemigroupBasis.CoRoots.S5_303.prefixDuplicationLaw =
        (⟨Word.mk 0 [1], Word.mk 0 [0, 1]⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      derivesGuardedDuplication guard (substitution 0) (substitution 1)
  · have literal : SemigroupBasis.CoRoots.S5_303.rotateLaw =
        (⟨Word.mk 0 [1, 0], Word.mk 1 [0, 0]⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      derivesGuardedRotate guard (substitution 0) (substitution 1)
  · have literal : SemigroupBasis.CoRoots.S5_303.interiorSwapLaw =
        (⟨Word.mk 0 [1, 2, 0], Word.mk 0 [2, 1, 0]⟩ : Identity Nat) := by decide
    rw [literal]
    simpa [Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      Derives.prepend guard (derivesInteriorSwap (substitution 0) (substitution 1) (substitution 2))

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
  have lower := SemigroupBasis.CoRoots.S5_303.representative_basis.2 (Identity.mk left right) valid
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

theorem derivesOwnHeadPad (word : Word Nat) (repeated : word.head ∈ word.tail) :
    Derives basis word (Word.singleton word.head ++ word) := by
  cases word with
  | mk head tail => exact derivesOwnHeadDuplicate head tail repeated

end SemigroupBasis.CoRoots.Order6Day10.S3_6op.Rank073Replay
