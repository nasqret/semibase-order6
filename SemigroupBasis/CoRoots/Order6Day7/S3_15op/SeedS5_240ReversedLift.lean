import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank086
import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank051
import SemigroupBasis.CoRoots.S5_107ListDerives

/-!
# Exact reversed S2 rank-051 intersection rebase for rank 086

All fourteen displayed laws of the independently kernel-green S2 rank-051
S5_240-opposite intersection, after reversal, have explicit derivations from
the eight immutable rank-086 displayed laws. Eight witnesses use one step,
three use two steps, two use three steps, and one uses five steps: exactly
25 displayed rewrites with explicit contexts and nonempty substitutions.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_240

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank086.basis

private abbrev sourceBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank051.basis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis

private def w (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- One frozen displayed rewrite with explicit contexts and substitution. -/
private theorem displayedStep
    (law : Identity Nat)
    (member : law ∈ targetBasis)
    (first second third : Word Nat)
    (before after : List Nat) :
    ListDerives
      (before ++
        (law.lhs.bind (instantiateThreeWords first second third)).toList ++
        after)
      (before ++
        (law.rhs.bind (instantiateThreeWords first second third)).toList ++
        after) := by
  exact SemigroupBasis.CoRoots.S5_107.ListDerives.context before after
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (Derives.subst (Derives.fromBasis member)
        (instantiateThreeWords first second third)))

/-- All fourteen reversed S2 axioms have concrete displayed-law witnesses. -/
theorem reversedS2AxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ sourceBasis) :
    Derives targetBasis
      identity.reversed.lhs identity.reversed.rhs := by
  simp only [SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank051.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Derives targetBasis (w 0 [0]) (w 0 [0, 0])
    have step01 :
        ListDerives [0, 0] [0, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law00 (by decide)
          (w 0 []) (w 0 []) (w 0 [])
          [] [])
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 1 [0, 0]) (w 0 [1, 0, 0])
    have step01 :
        ListDerives [1, 0, 0] [0, 1, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law06 (by decide)
          (w 1 []) (w 0 []) (w 0 [])
          [] [])
    have step02 :
        ListDerives [0, 1, 1, 0] [0, 1, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law05 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans (step02))
  · change Derives targetBasis (w 1 [0, 0]) (w 1 [1, 0, 0])
    have step01 :
        ListDerives [1, 0, 0] [1, 1, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law02 (by decide)
          (w 1 []) (w 0 []) (w 0 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 1 [0, 0]) (w 1 [0, 0, 1, 0])
    have step01 :
        ListDerives [1, 0, 0] [1, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law04 (by decide)
          (w 1 []) (w 0 []) (w 0 [])
          [] []).symm
    have step02 :
        ListDerives [1, 0, 1, 0] [1, 0, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law01 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [1] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans (step02))
  · change Derives targetBasis (w 1 [0, 0]) (w 1 [0, 1, 0])
    have step01 :
        ListDerives [1, 0, 0] [1, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law04 (by decide)
          (w 1 []) (w 0 []) (w 0 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 2 [1, 0, 0]) (w 1 [2, 0, 0])
    have step01 :
        ListDerives [2, 1, 0, 0] [2, 1, 0, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law00 (by decide)
          (w 0 []) (w 0 []) (w 0 [])
          [2, 1] [])
    have step02 :
        ListDerives [2, 1, 0, 0, 0] [2, 1, 0, 1, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law04 (by decide)
          (w 1 []) (w 0 []) (w 0 [])
          [2] [0]).symm
    have step03 :
        ListDerives [2, 1, 0, 1, 0, 0] [2, 1, 0, 2, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law05 (by decide)
          (w 2 []) (w 1 [0]) (w 0 [])
          [] []).symm
    have step04 :
        ListDerives [2, 1, 0, 2, 0] [1, 2, 0, 2, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law07 (by decide)
          (w 2 []) (w 1 []) (w 0 [])
          [] [0])
    have step05 :
        ListDerives [1, 2, 0, 2, 0] [1, 2, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law04 (by decide)
          (w 2 []) (w 0 []) (w 0 [])
          [1] [])
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans (step02.trans (step03.trans (step04.trans (step05)))))
  · change Derives targetBasis (w 2 [1, 0, 0]) (w 1 [2, 0, 1, 0])
    have step01 :
        ListDerives [2, 1, 0, 0] [2, 1, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law04 (by decide)
          (w 1 []) (w 0 []) (w 0 [])
          [2] []).symm
    have step02 :
        ListDerives [2, 1, 0, 1, 0] [1, 2, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law07 (by decide)
          (w 1 []) (w 2 []) (w 0 [])
          [] [0]).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans (step02))
  · change Derives targetBasis (w 2 [1, 0, 0]) (w 2 [0, 1, 1, 0])
    have step01 :
        ListDerives [2, 1, 0, 0] [2, 0, 1, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law06 (by decide)
          (w 1 []) (w 0 []) (w 0 [])
          [2] [])
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 2 [1, 0, 0]) (w 1 [0, 2, 1, 0])
    have step01 :
        ListDerives [2, 1, 0, 0] [2, 1, 0, 2, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law04 (by decide)
          (w 2 [1]) (w 0 []) (w 0 [])
          [] []).symm
    have step02 :
        ListDerives [2, 1, 0, 2, 1, 0] [1, 0, 2, 2, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law07 (by decide)
          (w 1 [0]) (w 2 []) (w 2 [])
          [] []).symm
    have step03 :
        ListDerives [1, 0, 2, 2, 1, 0] [1, 0, 2, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law03 (by decide)
          (w 2 []) (w 1 []) (w 0 [])
          [1, 0] [])
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans (step02.trans (step03)))
  · change Derives targetBasis (w 2 [1, 0, 0]) (w 0 [1, 2, 1, 0])
    have step01 :
        ListDerives [2, 1, 0, 0] [2, 1, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law04 (by decide)
          (w 1 []) (w 0 []) (w 0 [])
          [2] []).symm
    have step02 :
        ListDerives [2, 1, 0, 1, 0] [1, 2, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law07 (by decide)
          (w 1 []) (w 2 []) (w 0 [])
          [] [0]).symm
    have step03 :
        ListDerives [1, 2, 0, 1, 0] [0, 1, 2, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law07 (by decide)
          (w 0 []) (w 1 [2]) (w 1 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans (step02.trans (step03)))
  · change Derives targetBasis (w 0 [1, 0]) (w 0 [0, 1, 0])
    have step01 :
        ListDerives [0, 1, 0] [0, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law01 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 2 [0, 1, 0]) (w 0 [2, 1, 0])
    have step01 :
        ListDerives [2, 0, 1, 0] [0, 2, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law07 (by decide)
          (w 0 []) (w 2 []) (w 1 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 2 [1, 1, 0]) (w 2 [1, 2, 0])
    have step01 :
        ListDerives [2, 1, 1, 0] [2, 1, 2, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law05 (by decide)
          (w 2 []) (w 1 []) (w 0 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 2 [1, 0]) (w 2 [2, 1, 0])
    have step01 :
        ListDerives [2, 1, 0] [2, 2, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank086.law03 (by decide)
          (w 2 []) (w 1 []) (w 0 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)

/-- Structural equational rebase from the kernel-green reversed S2 pair. -/
theorem transportReversedS2Derivation
    {left right : Word Nat}
    (derivation : Derives (reversedBasis sourceBasis) left right) :
    Derives targetBasis left right := by
  apply derivation.transport
  intro identity member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  exact reversedS2AxiomDerives source sourceMember

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_240

