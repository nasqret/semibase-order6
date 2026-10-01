import SemigroupBasis.Order6Subdirect.Hull23_1_S3_11_S5_831
import SemigroupBasis.CoRoots.S5_107ListDerives

/-!
# Hull 23.1 phase-parity moves

This module exposes the elementary list rewrites supplied by the fifteen
literal identities of Lee--Zhang Proposition 23.1.  Every theorem below is
proved by substitution into the corresponding member of `publishedBasis`;
in particular, no derivational result for Proposition 21.1 is transported
into this basis.

The optional words in (23.1b)--(23.1f) are represented by lists.  A
nonempty optional word is substituted as one semigroup word, while an empty
one selects the separately stored no-context identity.  Arbitrary exterior
contexts are then added with list-level congruence.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull23_1PhaseParityMoves

private abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Order6Subdirect.Hull23_1_S3_11_S5_831.publishedBasis

/-- List-level derivability by the literal fifteen-law Proposition 23.1
basis. -/
abbrev HullListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

/-! ## Direct instances of the six displayed law schemes -/

/-- Contextual form of (23.1a), `xxyx = xxxyyy`. -/
theorem hullListDerivesSeed
    (pre post : List Nat) (x y : Nat) :
    HullListDerives
      (pre ++ [x, x, y, x] ++ post)
      (pre ++ [x, x, x, y, y, y] ++ post) := by
  have member :
      (Identity.mk (Word.mk 0 [0, 1, 0])
        (Word.mk 0 [0, 0, 1, 1, 1])) ∈ basis := by
    decide
  have law := Derives.fromBasis member
  let substitution : Nat -> Word Nat :=
    fun index =>
      if index = 0 then Word.singleton x
      else Word.singleton y
  have derived :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (Derives.subst law substitution)
  simpa [Word.toList, Word.bind, substitution, List.append_assoc] using
    derived.context pre post

/-- Contextual form of (23.1b).  The optional word `h` may be empty:
`xhxxx = xhx`. -/
theorem hullListDerivesPowerContract
    (pre post h : List Nat) (x : Nat) :
    HullListDerives
      (pre ++ [x] ++ h ++ [x, x, x] ++ post)
      (pre ++ [x] ++ h ++ [x] ++ post) := by
  cases h with
  | nil =>
      have member :
          (Identity.mk (Word.mk 0 [0, 0, 0])
            (Word.mk 0 [0])) ∈ basis := by
        decide
      have law := Derives.fromBasis member
      let substitution : Nat -> Word Nat :=
        fun _ => Word.singleton x
      have derived :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (Derives.subst law substitution)
      simpa [Word.toList, Word.bind, substitution, List.append_assoc] using
        derived.context pre post
  | cons hHead hTail =>
      let hWord : Word Nat := Word.mk hHead hTail
      have member :
          (Identity.mk (Word.mk 0 [1, 0, 0, 0])
            (Word.mk 0 [1, 0])) ∈ basis := by
        decide
      have law := Derives.fromBasis member
      let substitution : Nat -> Word Nat :=
        fun index =>
          if index = 0 then Word.singleton x
          else hWord
      have derived :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (Derives.subst law substitution)
      simpa [Word.toList, Word.bind, substitution, hWord,
        List.append_assoc] using derived.context pre post

/-- Contextual form of (23.1c).  The optional word `h` may be empty:
`xhyxx = xhyyy`. -/
theorem hullListDerivesParityTransfer
    (pre post h : List Nat) (x y : Nat) :
    HullListDerives
      (pre ++ [x] ++ h ++ [y, x, x] ++ post)
      (pre ++ [x] ++ h ++ [y, y, y] ++ post) := by
  cases h with
  | nil =>
      have member :
          (Identity.mk (Word.mk 0 [1, 0, 0])
            (Word.mk 0 [1, 1, 1])) ∈ basis := by
        decide
      have law := Derives.fromBasis member
      let substitution : Nat -> Word Nat :=
        fun index =>
          if index = 0 then Word.singleton x
          else Word.singleton y
      have derived :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (Derives.subst law substitution)
      simpa [Word.toList, Word.bind, substitution, List.append_assoc] using
        derived.context pre post
  | cons hHead hTail =>
      let hWord : Word Nat := Word.mk hHead hTail
      have member :
          (Identity.mk (Word.mk 0 [1, 2, 0, 0])
            (Word.mk 0 [1, 2, 2, 2])) ∈ basis := by
        decide
      have law := Derives.fromBasis member
      let substitution : Nat -> Word Nat :=
        fun index =>
          if index = 0 then Word.singleton x
          else if index = 1 then hWord
          else Word.singleton y
      have derived :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (Derives.subst law substitution)
      simpa [Word.toList, Word.bind, substitution, hWord,
        List.append_assoc] using derived.context pre post

/-- Contextual form of (23.1d).  The optional word `h` may be empty:
`xhyyyx = xhyx`. -/
theorem hullListDerivesReturnContract
    (pre post h : List Nat) (x y : Nat) :
    HullListDerives
      (pre ++ [x] ++ h ++ [y, y, y, x] ++ post)
      (pre ++ [x] ++ h ++ [y, x] ++ post) := by
  cases h with
  | nil =>
      have member :
          (Identity.mk (Word.mk 0 [1, 1, 1, 0])
            (Word.mk 0 [1, 0])) ∈ basis := by
        decide
      have law := Derives.fromBasis member
      let substitution : Nat -> Word Nat :=
        fun index =>
          if index = 0 then Word.singleton x
          else Word.singleton y
      have derived :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (Derives.subst law substitution)
      simpa [Word.toList, Word.bind, substitution, List.append_assoc] using
        derived.context pre post
  | cons hHead hTail =>
      let hWord : Word Nat := Word.mk hHead hTail
      have member :
          (Identity.mk (Word.mk 0 [1, 2, 2, 2, 0])
            (Word.mk 0 [1, 2, 0])) ∈ basis := by
        decide
      have law := Derives.fromBasis member
      let substitution : Nat -> Word Nat :=
        fun index =>
          if index = 0 then Word.singleton x
          else if index = 1 then hWord
          else Word.singleton y
      have derived :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (Derives.subst law substitution)
      simpa [Word.toList, Word.bind, substitution, hWord,
        List.append_assoc] using derived.context pre post

/-- Contextual form of (23.1e).  Both optional words may be empty:
`xhy kxy = xhy kyx`.  This exchanges the final displayed occurrences after
earlier witnesses for both letters. -/
theorem hullListDerivesExchange
    (pre post h k : List Nat) (x y : Nat) :
    HullListDerives
      (pre ++ [x] ++ h ++ [y] ++ k ++ [x, y] ++ post)
      (pre ++ [x] ++ h ++ [y] ++ k ++ [y, x] ++ post) := by
  cases h with
  | nil =>
      cases k with
      | nil =>
          have member :
              (Identity.mk (Word.mk 0 [1, 0, 1])
                (Word.mk 0 [1, 1, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton x
              else Word.singleton y
          have derived :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
          simpa [Word.toList, Word.bind, substitution,
            List.append_assoc] using derived.context pre post
      | cons kHead kTail =>
          let kWord : Word Nat := Word.mk kHead kTail
          have member :
              (Identity.mk (Word.mk 0 [1, 2, 0, 1])
                (Word.mk 0 [1, 2, 1, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton x
              else if index = 1 then Word.singleton y
              else kWord
          have derived :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
          simpa [Word.toList, Word.bind, substitution, kWord,
            List.append_assoc] using derived.context pre post
  | cons hHead hTail =>
      let hWord : Word Nat := Word.mk hHead hTail
      cases k with
      | nil =>
          have member :
              (Identity.mk (Word.mk 0 [1, 2, 0, 2])
                (Word.mk 0 [1, 2, 2, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton x
              else if index = 1 then hWord
              else Word.singleton y
          have derived :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
          simpa [Word.toList, Word.bind, substitution, hWord,
            List.append_assoc] using derived.context pre post
      | cons kHead kTail =>
          let kWord : Word Nat := Word.mk kHead kTail
          have member :
              (Identity.mk (Word.mk 0 [1, 2, 3, 0, 2])
                (Word.mk 0 [1, 2, 3, 2, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton x
              else if index = 1 then hWord
              else if index = 2 then Word.singleton y
              else kWord
          have derived :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
          simpa [Word.toList, Word.bind, substitution, hWord, kWord,
            List.append_assoc] using derived.context pre post

/-- Contextual form of (23.1f).  Both optional words may be empty:
`yhxy kzz = yhxx kzzxy`.  The terminal square is kept explicit because it
is the anchor used by the phase-parity normalization sweep. -/
theorem hullListDerivesBalance
    (pre post h k : List Nat) (x y z : Nat) :
    HullListDerives
      (pre ++ [y] ++ h ++ [x, y] ++ k ++ [z, z] ++ post)
      (pre ++ [y] ++ h ++ [x, x] ++ k ++ [z, z, x, y] ++ post) := by
  cases h with
  | nil =>
      cases k with
      | nil =>
          have member :
              (Identity.mk (Word.mk 0 [1, 0, 2, 2])
                (Word.mk 0 [1, 1, 2, 2, 1, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton y
              else if index = 1 then Word.singleton x
              else Word.singleton z
          have derived :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
          simpa [Word.toList, Word.bind, substitution,
            List.append_assoc] using derived.context pre post
      | cons kHead kTail =>
          let kWord : Word Nat := Word.mk kHead kTail
          have member :
              (Identity.mk (Word.mk 0 [1, 0, 2, 3, 3])
                (Word.mk 0 [1, 1, 2, 3, 3, 1, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton y
              else if index = 1 then Word.singleton x
              else if index = 2 then kWord
              else Word.singleton z
          have derived :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
          simpa [Word.toList, Word.bind, substitution, kWord,
            List.append_assoc] using derived.context pre post
  | cons hHead hTail =>
      let hWord : Word Nat := Word.mk hHead hTail
      cases k with
      | nil =>
          have member :
              (Identity.mk (Word.mk 0 [1, 2, 0, 3, 3])
                (Word.mk 0 [1, 2, 2, 3, 3, 2, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton y
              else if index = 1 then hWord
              else if index = 2 then Word.singleton x
              else Word.singleton z
          have derived :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
          simpa [Word.toList, Word.bind, substitution, hWord,
            List.append_assoc] using derived.context pre post
      | cons kHead kTail =>
          let kWord : Word Nat := Word.mk kHead kTail
          have member :
              (Identity.mk (Word.mk 0 [1, 2, 0, 3, 4, 4])
                (Word.mk 0 [1, 2, 2, 3, 4, 4, 2, 0])) ∈ basis := by
            decide
          have law := Derives.fromBasis member
          let substitution : Nat -> Word Nat :=
            fun index =>
              if index = 0 then Word.singleton y
              else if index = 1 then hWord
              else if index = 2 then Word.singleton x
              else if index = 3 then kWord
              else Word.singleton z
          have derived :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (Derives.subst law substitution)
          simpa [Word.toList, Word.bind, substitution, hWord, kWord,
            List.append_assoc] using derived.context pre post

end Order6Hull23_1PhaseParityMoves
end CoRoots
end SemigroupBasis
