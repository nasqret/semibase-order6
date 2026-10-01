import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_794
import SemigroupBasis.Examples.UniqueSeparatorFourNormalForm

namespace SemigroupBasis.CoRoots.S5_794

open SemigroupBasis
open SemigroupBasis.Examples

private def instantiateFourWords
    (u v z q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | 3 => q
  | n + 4 => Word.singleton (n + 4)

private theorem basisPower :
    Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) <| by
    simp [basis]

private theorem basisFirstDeletion :
    Derives basis xxzwz xzxwz :=
  Derives.fromBasis (e := firstDeletionLaw) <| by
    simp [basis]

private theorem basisLeftDeletion :
    Derives basis xxzx xzx :=
  Derives.fromBasis (e := leftDeletionLaw) <| by
    simp [basis]

private theorem basisSquareInterchange :
    Derives basis xxzz xzxz :=
  Derives.fromBasis (e := squareInterchangeLaw) <| by
    simp [basis]

private theorem basisRightExpansion :
    Derives basis xyx xyxx :=
  Derives.fromBasis (e := rightExpansionLaw) <| by
    simp [basis]

private theorem basisMixedDeletion :
    Derives basis xyxzwz xyzxwz :=
  Derives.fromBasis (e := mixedDeletionLaw) <| by
    simp [basis]

private theorem basisMiddleDeletion :
    Derives basis xyxzx xyzx :=
  Derives.fromBasis (e := middleDeletionLaw) <| by
    simp [basis]

private theorem basisDoubledSuffix :
    Derives basis xyxzz xyzxz :=
  Derives.fromBasis (e := doubledSuffixLaw) <| by
    simp [basis]

private theorem basisLongRotation :
    Derives basis xyzwxz xyzwzx :=
  Derives.fromBasis (e := longRotationLaw) <| by
    simp [basis]

private theorem basisTerminalSquare :
    Derives basis xyzxz xyzzx :=
  Derives.fromBasis (e := terminalSquareLaw) <| by
    simp [basis]

private theorem basisShortRotation :
    Derives basis xzwxz xzwzx :=
  Derives.fromBasis (e := shortRotationLaw) <| by
    simp [basis]

private theorem basisAlternatingSquare :
    Derives basis xzxz xzzx :=
  Derives.fromBasis (e := alternatingSquareLaw) <| by
    simp [basis]

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateFourWords u u u u)
  simpa [xx, xxx, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesLeftDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisLeftDeletion
      (instantiateFourWords u v v v)
  simpa [xxzx, xzx, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted.symm

theorem derivesRightDuplication (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightExpansion
      (instantiateFourWords u v v v)
  simpa [xyx, xyxx, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesInteriorInsertion (u v z : Word Nat) :
    Derives basis (((u ++ v) ++ z) ++ u)
      ((((u ++ v) ++ u) ++ z) ++ u) := by
  have substituted :=
    Derives.subst basisMiddleDeletion
      (instantiateFourWords u v z z)
  simpa [xyxzx, xyzx, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted.symm

theorem derivesThirdOccurrenceDeletion (u v z : Word Nat) :
    Derives basis ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) :=
  (derivesInteriorInsertion u v z).symm

/-- The long-context member of Edmunds' `L₇`, oriented to move the
second occurrence of `u` left across the adjacent `w`. -/
theorem derivesL7Long (u v w q : Word Nat) :
    Derives basis
      (((((u ++ v) ++ w) ++ u) ++ q) ++ w)
      (((((u ++ v) ++ u) ++ w) ++ q) ++ w) := by
  have substituted :=
    Derives.subst basisMixedDeletion
      (instantiateFourWords u v w q)
  simpa [xyxzwz, xyzxwz, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

/-- The right-gap deletion of `L₇`. -/
theorem derivesL7Medium (u v w : Word Nat) :
    Derives basis
      ((((u ++ v) ++ w) ++ u) ++ w)
      ((((u ++ v) ++ u) ++ w) ++ w) := by
  have substituted :=
    Derives.subst basisDoubledSuffix
      (instantiateFourWords u v w w)
  simpa [xyxzz, xyzxz, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

/-- The left-gap deletion of `L₇`. -/
theorem derivesL7Short (u v w : Word Nat) :
    Derives basis
      ((((u ++ v) ++ u) ++ w) ++ v)
      ((((u ++ u) ++ v) ++ w) ++ v) := by
  have substituted :=
    Derives.subst basisFirstDeletion
      (instantiateFourWords u w v w)
  simpa [xxzwz, xzxwz, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

/-- The both-gaps-deleted member of `L₇`. -/
theorem derivesL7Square (u v : Word Nat) :
    Derives basis
      (((u ++ v) ++ u) ++ v)
      ((u ++ u) ++ (v ++ v)) := by
  have substituted :=
    Derives.subst basisSquareInterchange
      (instantiateFourWords u u v v)
  simpa [xxzz, xzxz, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted.symm

/-- The long-context member of Edmunds' `L₈`. -/
theorem derivesL8Long (u v w q : Word Nat) :
    Derives basis
      (((((u ++ v) ++ w) ++ q) ++ u) ++ w)
      (((((u ++ v) ++ w) ++ q) ++ w) ++ u) := by
  have substituted :=
    Derives.subst basisLongRotation
      (instantiateFourWords u v w q)
  simpa [xyzwxz, xyzwzx, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The right-gap deletion of `L₈`. -/
theorem derivesL8Medium (u v w : Word Nat) :
    Derives basis
      ((((u ++ v) ++ w) ++ u) ++ w)
      ((((u ++ v) ++ w) ++ w) ++ u) := by
  have substituted :=
    Derives.subst basisTerminalSquare
      (instantiateFourWords u v w w)
  simpa [xyzxz, xyzzx, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The left-gap deletion of `L₈`. -/
theorem derivesL8Short (u v w : Word Nat) :
    Derives basis
      ((((u ++ v) ++ w) ++ u) ++ v)
      ((((u ++ v) ++ w) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisShortRotation
      (instantiateFourWords u w v w)
  simpa [xzwxz, xzwzx, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The both-gaps-deleted member of `L₈`. -/
theorem derivesL8Square (u v : Word Nat) :
    Derives basis
      (((u ++ v) ++ u) ++ v)
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisAlternatingSquare
      (instantiateFourWords u u v v)
  simpa [xzxz, xzzx, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Package `L₇` for possibly empty intervening gaps. -/
theorem listDerivesL7
    (x y : Nat) (left right : List Nat) :
    S5_107.ListDerives basis
      ([x] ++ left ++ [y, x] ++ right ++ [y])
      ([x] ++ left ++ [x, y] ++ right ++ [y]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesL7Square (Word.singleton x) (Word.singleton y)
      | cons r rs =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesL7Short
                (Word.singleton x) (Word.singleton y)
                (S5_107.listWordOfCons r rs)
  | cons l ls =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesL7Medium
                (Word.singleton x)
                (S5_107.listWordOfCons l ls)
                (Word.singleton y)
      | cons r rs =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesL7Long
                (Word.singleton x)
                (S5_107.listWordOfCons l ls)
                (Word.singleton y)
                (S5_107.listWordOfCons r rs)

/-- Package `L₈` for possibly empty intervening gaps. -/
theorem listDerivesL8
    (x y : Nat) (left middle : List Nat) :
    S5_107.ListDerives basis
      ([x] ++ left ++ [y] ++ middle ++ [x, y])
      ([x] ++ left ++ [y] ++ middle ++ [y, x]) := by
  cases left with
  | nil =>
      cases middle with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesL8Square (Word.singleton x) (Word.singleton y)
      | cons m ms =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesL8Short
                (Word.singleton x) (Word.singleton y)
                (S5_107.listWordOfCons m ms)
  | cons l ls =>
      cases middle with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesL8Medium
                (Word.singleton x)
                (S5_107.listWordOfCons l ls)
                (Word.singleton y)
      | cons m ms =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesL8Long
                (Word.singleton x)
                (S5_107.listWordOfCons l ls)
                (Word.singleton y)
                (S5_107.listWordOfCons m ms)

private theorem listDerivesDeleteMiddleCore
    (x : Nat) (left right : List Nat) :
    S5_107.ListDerives basis
      ([x] ++ left ++ [x] ++ right ++ [x])
      ([x] ++ left ++ right ++ [x]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (derivesPowerExpansion (Word.singleton x)).symm
      | cons y ys =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (derivesLeftDuplication
                (Word.singleton x)
                (S5_107.listWordOfCons y ys)).symm
  | cons y ys =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              (derivesRightDuplication
                (Word.singleton x)
                (S5_107.listWordOfCons y ys)).symm
      | cons z zs =>
          exact S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton,
              Word.append, Word.append_assoc, List.append_assoc] using
              derivesThirdOccurrenceDeletion
                (Word.singleton x)
                (S5_107.listWordOfCons y ys)
                (S5_107.listWordOfCons z zs)

private theorem listDerivesDeleteCurrent
    (pre suffix : List Nat) (x : Nat)
    (past : x ∈ pre) (future : x ∈ suffix) :
    S5_107.ListDerives basis
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
      S5_107.ListDerives basis
        (pre ++ suffix)
        (pre ++ uniqueSeparatorEndpointCapAux seen suffix)
  | [] => by
      simpa using S5_107.ListDerives.refl (basis := basis) pre
  | x :: xs => by
      by_cases middle : x ∈ seen ∧ x ∈ xs
      · have xInPre : x ∈ pre := seenInPre x middle.1
        have deleteCurrent :
            S5_107.ListDerives basis
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

/-- Every word derives to the cap retaining only its first and last
occurrences. -/
theorem listDerivesEndpointCap (letters : List Nat) :
    S5_107.ListDerives basis letters
      (uniqueSeparatorEndpointCap letters) := by
  simpa [uniqueSeparatorEndpointCap] using
    listDerivesEndpointCapAux [] [] (by simp) letters

end SemigroupBasis.CoRoots.S5_794
