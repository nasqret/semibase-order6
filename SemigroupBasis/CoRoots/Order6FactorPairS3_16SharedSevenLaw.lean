import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_809
import SemigroupBasis.Examples.CommutativeExponentThree
import SemigroupBasis.Examples.LeftRegularBandThree
import SemigroupBasis.Examples.UniqueSeparatorFourNormalForm
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.S3_16
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw

open SemigroupBasis
open SemigroupBasis.Examples

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xyxzz : Word Nat := w 0 [1, 0, 2, 2]
def xyzxz : Word Nat := w 0 [1, 2, 0, 2]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftDeletionLaw : Identity Nat := ⟨xxyx, xyx⟩
def squareInterchangeLaw : Identity Nat := ⟨xxyy, xyxy⟩
def firstDeletionLaw : Identity Nat := ⟨xxyzy, xyxzy⟩
def rightExpansionLaw : Identity Nat := ⟨xyx, xyxx⟩
def middleDeletionLaw : Identity Nat := ⟨xyxzx, xyzx⟩
def doubledSuffixLaw : Identity Nat := ⟨xyxzz, xyzxz⟩

/-- The exact seven-law candidate with canonical packet hash
`f42ccd29e813b6b39d545fb966fdc18595840f3c13a594ec2a124d909e6e8392`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftDeletionLaw, squareInterchangeLaw, firstDeletionLaw,
    rightExpansionLaw, middleDeletionLaw, doubledSuffixLaw]

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- The three-element right regular band, retained as a finite table so that
both candidate and detector soundness are checked exhaustively. -/
def rightRegularBandThreeTable : FiniteTable where
  order := 3
  mul := fun left right => leftRegularBandThreeMul right left
  assoc := by decide

theorem rightRegularBandThreeTable_semigroup :
    rightRegularBandThreeTable.semigroup =
      leftRegularBandThree.semigroup.opposite := by
  rfl

theorem modelsS3_16 :
    Models SemigroupBasis.Generated.S3_16.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_16.table basis toFinThree (by decide)

theorem modelsS5_809 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_809.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_809.table basis toFinThree
      (by decide)

theorem modelsRightRegularBandThree :
    Models rightRegularBandThreeTable.semigroup basis :=
  FiniteCertificate.checkModels_sound
    rightRegularBandThreeTable basis toFinThree (by decide)

theorem modelsCommutativeExponentThree :
    Models commutativeExponentThree.semigroup basis :=
  FiniteCertificate.checkModels_sound
    commutativeExponentThree basis toFinThree (by decide)

/-- The complete `S5_809` presentation is sound in the right-endpoint
detector. Thus every `S5_809` identity preserves its last-occurrence data. -/
theorem s5_809BasisModelsRightRegularBandThree :
    Models rightRegularBandThreeTable.semigroup
      SemigroupBasis.CoRoots.S5_809.basis :=
  FiniteCertificate.checkModels_sound
    rightRegularBandThreeTable SemigroupBasis.CoRoots.S5_809.basis
      toFinThree (by decide)

/-- The complete `S5_809` presentation is also sound in the capped
multiplicity detector. -/
theorem s5_809BasisModelsCommutativeExponentThree :
    Models commutativeExponentThree.semigroup
      SemigroupBasis.CoRoots.S5_809.basis :=
  FiniteCertificate.checkModels_sound
    commutativeExponentThree SemigroupBasis.CoRoots.S5_809.basis
      toFinThree (by decide)

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisPower :
    Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem basisLeftDeletion :
    Derives basis xxyx xyx :=
  Derives.fromBasis (e := leftDeletionLaw) (by simp [basis])

private theorem basisSquareInterchange :
    Derives basis xxyy xyxy :=
  Derives.fromBasis (e := squareInterchangeLaw) (by simp [basis])

private theorem basisFirstDeletion :
    Derives basis xxyzy xyxzy :=
  Derives.fromBasis (e := firstDeletionLaw) (by simp [basis])

private theorem basisRightExpansion :
    Derives basis xyx xyxx :=
  Derives.fromBasis (e := rightExpansionLaw) (by simp [basis])

private theorem basisMiddleDeletion :
    Derives basis xyxzx xyzx :=
  Derives.fromBasis (e := middleDeletionLaw) (by simp [basis])

private theorem basisDoubledSuffix :
    Derives basis xyxzz xyzxz :=
  Derives.fromBasis (e := doubledSuffixLaw) (by simp [basis])

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateThreeWords u u u)
  simpa [xx, xxx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesLeftDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisLeftDeletion (instantiateThreeWords u v v)
  simpa [xxyx, xyx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted.symm

theorem derivesRightDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightExpansion (instantiateThreeWords u v v)
  simpa [xyx, xyxx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesFirstDeletion (u v z : Word Nat) :
    Derives basis ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ u) ++ z) ++ v) := by
  have substituted :=
    Derives.subst basisFirstDeletion (instantiateThreeWords u v z)
  simpa [xxyzy, xyxzy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesMiddleDeletion (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisMiddleDeletion (instantiateThreeWords u v z)
  simpa [xyxzx, xyzx, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- The long `L7` move is not an additional axiom. Duplicate the displayed
second `u`, apply `xxyzy = xyxzy` under the prefix `uv`, and remove the
resulting interior third `u`. -/
theorem derivesL7Long (u v z q : Word Nat) :
    Derives basis
      (((((u ++ v) ++ u) ++ z) ++ q) ++ z)
      (((((u ++ v) ++ z) ++ u) ++ q) ++ z) := by
  have duplicate :=
    Derives.appendRight
      (derivesRightDuplication u v) ((z ++ q) ++ z)
  have switch :=
    Derives.prepend (u ++ v) (derivesFirstDeletion u z q)
  have contract :=
    Derives.appendRight (derivesMiddleDeletion u v z) (q ++ z)
  have duplicate' :
      Derives basis
        (((((u ++ v) ++ u) ++ z) ++ q) ++ z)
        ((((((u ++ v) ++ u) ++ u) ++ z) ++ q) ++ z) := by
    simpa [Word.append_assoc] using duplicate
  have switch' :
      Derives basis
        ((((((u ++ v) ++ u) ++ u) ++ z) ++ q) ++ z)
        ((((((u ++ v) ++ u) ++ z) ++ u) ++ q) ++ z) := by
    simpa [Word.append_assoc] using switch
  have contract' :
      Derives basis
        ((((((u ++ v) ++ u) ++ z) ++ u) ++ q) ++ z)
        (((((u ++ v) ++ z) ++ u) ++ q) ++ z) := by
    simpa [Word.append_assoc] using contract
  exact duplicate'.trans (switch'.trans contract')

theorem derivesL7Medium (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ z) ++ u) ++ z)
      ((((u ++ v) ++ u) ++ z) ++ z) := by
  have substituted :=
    Derives.subst basisDoubledSuffix (instantiateThreeWords u v z)
  simpa [xyxzz, xyzxz, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted.symm

theorem derivesL7Short (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ v)
      ((((u ++ u) ++ v) ++ z) ++ v) :=
  (derivesFirstDeletion u v z).symm

theorem derivesL7Square (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v)
      ((u ++ u) ++ (v ++ v)) := by
  have substituted :=
    Derives.subst basisSquareInterchange
      (instantiateThreeWords u v v)
  simpa [xxyy, xyxy, w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted.symm

/-- All four empty/nonempty-gap forms of the straddling adjacent swap. -/
theorem listDerivesL7
    (x y : Nat) (left right : List Nat) :
    SemigroupBasis.CoRoots.S5_107.ListDerives basis
      ([x] ++ left ++ [y, x] ++ right ++ [y])
      ([x] ++ left ++ [x, y] ++ right ++ [y]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              derivesL7Square (Word.singleton x) (Word.singleton y)
      | cons r rs =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              derivesL7Short
                (Word.singleton x) (Word.singleton y)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons r rs)
  | cons l ls =>
      cases right with
      | nil =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              derivesL7Medium
                (Word.singleton x)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons l ls)
                (Word.singleton y)
      | cons r rs =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              derivesL7Long
                (Word.singleton x)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons l ls)
                (Word.singleton y)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons r rs) |>.symm

private theorem listDerivesDeleteMiddleCore
    (x : Nat) (left right : List Nat) :
    SemigroupBasis.CoRoots.S5_107.ListDerives basis
      ([x] ++ left ++ [x] ++ right ++ [x])
      ([x] ++ left ++ right ++ [x]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              (derivesPowerExpansion (Word.singleton x)).symm
      | cons y ys =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              (derivesLeftDuplication
                (Word.singleton x)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons y ys)).symm
  | cons y ys =>
      cases right with
      | nil =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              (derivesRightDuplication
                (Word.singleton x)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons y ys)).symm
      | cons z zs =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
            simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
              Word.singleton, Word.append, Word.append_assoc,
              List.append_assoc] using
              derivesMiddleDeletion
                (Word.singleton x)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons y ys)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons z zs)

private theorem listDerivesDeleteCurrent
    (pre suffix : List Nat) (x : Nat)
    (past : x ∈ pre) (future : x ∈ suffix) :
    SemigroupBasis.CoRoots.S5_107.ListDerives basis
      (pre ++ x :: suffix) (pre ++ suffix) := by
  rcases List.append_of_mem past with
    ⟨before, left, preShape⟩
  rcases List.append_of_mem future with
    ⟨right, after, suffixShape⟩
  rw [preShape, suffixShape]
  simpa [List.append_assoc] using
    (listDerivesDeleteMiddleCore x left right).context before after

private theorem listDerivesEndpointCapAux
    (pre seen : List Nat)
    (seenInPre : ∀ z ∈ seen, z ∈ pre) :
    ∀ suffix : List Nat,
      SemigroupBasis.CoRoots.S5_107.ListDerives basis
        (pre ++ suffix)
        (pre ++ uniqueSeparatorEndpointCapAux seen suffix)
  | [] => by
      simpa using
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) pre
  | x :: xs => by
      by_cases middle : x ∈ seen ∧ x ∈ xs
      · have xInPre : x ∈ pre := seenInPre x middle.1
        have deleteCurrent :
            SemigroupBasis.CoRoots.S5_107.ListDerives basis
              (pre ++ x :: xs) (pre ++ xs) :=
          listDerivesDeleteCurrent pre xs x xInPre middle.2
        have nextSeenInPre : ∀ z ∈ x :: seen, z ∈ pre := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact xInPre
          · exact seenInPre z hz
        have recurse :=
          listDerivesEndpointCapAux pre (x :: seen) nextSeenInPre xs
        rw [uniqueSeparatorEndpointCapAux, if_pos middle]
        exact deleteCurrent.trans recurse
      · have nextSeenInPre :
            ∀ z ∈ x :: seen, z ∈ pre ++ [x] := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact List.mem_append_right pre (List.Mem.head [])
          · exact List.mem_append_left [x] (seenInPre z hz)
        have recurse :=
          listDerivesEndpointCapAux
            (pre ++ [x]) (x :: seen) nextSeenInPre xs
        rw [uniqueSeparatorEndpointCapAux, if_neg middle]
        simpa [List.append_assoc] using recurse

/-- Every list derives to the cap retaining exactly its first and last
occurrences. -/
theorem listDerivesEndpointCap (letters : List Nat) :
    SemigroupBasis.CoRoots.S5_107.ListDerives basis letters
      (uniqueSeparatorEndpointCap letters) := by
  simpa [uniqueSeparatorEndpointCap] using
    listDerivesEndpointCapAux [] [] (by simp) letters

end SemigroupBasis.CoRoots.Order6FactorPairS3_16SharedSevenLaw
