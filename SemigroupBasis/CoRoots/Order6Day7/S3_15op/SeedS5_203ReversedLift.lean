import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank080
import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank046
import SemigroupBasis.CoRoots.S5_107ListDerives

/-!
# Exact reversal rebase from the kernel-green S2 rank-046 proof

All eighteen displayed laws of the independently kernel-green S2 rank-046
intersection, after reversal, have explicit derivations from the twelve frozen
rank-080 displayed laws. The complete witness set uses 33 displayed rewrites;
no witness requires more than four steps. Every context and every nonempty
simultaneous substitution is supplied explicitly.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_203

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank080.basis

private abbrev sourceBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank046.basis

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

/-- Replay one frozen law with an explicit nonempty substitution and contexts. -/
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

/-- All eighteen reversed S2 axioms have concrete one-to-four-step witnesses. -/
theorem reversedS2AxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ sourceBasis) :
    Derives targetBasis
      identity.reversed.lhs identity.reversed.rhs := by
  simp only [SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank046.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Derives targetBasis (w 0 [0, 0]) (w 0 [0, 0, 0])
    have step01 :
        ListDerives [0, 0, 0] [0, 0, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law00 (by decide)
          (w 0 []) (w 0 []) (w 0 [])
          [] [])
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 1 [0, 0, 0]) (w 0 [1, 0])
    have step01 :
        ListDerives [1, 0, 0, 0] [0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law08 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 1 [0, 0]) (w 1 [1, 0, 0])
    have step01 :
        ListDerives [1, 0, 0] [1, 1, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law03 (by decide)
          (w 1 []) (w 0 []) (w 0 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 1 [0, 1, 0, 0]) (w 0 [1, 0])
    have step01 :
        ListDerives [1, 0, 1, 0, 0] [0, 1, 1, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law11 (by decide)
          (w 1 []) (w 0 [1]) (w 0 [])
          [] [])
    have step02 :
        ListDerives [0, 1, 1, 0, 0] [0, 1, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law03 (by decide)
          (w 1 []) (w 0 []) (w 0 [])
          [0] [])
    have step03 :
        ListDerives [0, 1, 0, 0] [0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law05 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans (step02.trans step03))
  · change Derives targetBasis (w 2 [1, 0, 0]) (w 1 [2, 0, 0])
    have step01 :
        ListDerives [2, 1, 0, 0] [1, 2, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law11 (by decide)
          (w 2 []) (w 1 []) (w 0 [])
          [] [])
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 0 [1, 0]) (w 0 [0, 1, 0])
    have step01 :
        ListDerives [0, 1, 0] [0, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law02 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 0 [1, 0]) (w 0 [1, 0, 1, 0])
    have step01 :
        ListDerives [0, 1, 0] [0, 1, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law06 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [] [])
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 0 [1, 0]) (w 1 [0, 1, 1, 0])
    have step01 :
        ListDerives [0, 1, 0] [0, 1, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law06 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [] [])
    have step02 :
        ListDerives [0, 1, 0, 1, 0] [0, 1, 1, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law09 (by decide)
          (w 0 []) (w 1 []) (w 1 [])
          [] [0])
    have step03 :
        ListDerives [0, 1, 1, 1, 0] [1, 0, 1, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law11 (by decide)
          (w 1 []) (w 0 []) (w 1 [])
          [] [0]).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans (step02.trans step03))
  · change Derives targetBasis (w 2 [1, 0, 1, 0]) (w 2 [0, 1, 0])
    have step01 :
        ListDerives [2, 1, 0, 1, 0] [2, 1, 0, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law09 (by decide)
          (w 1 []) (w 0 []) (w 0 [])
          [2] [])
    have step02 :
        ListDerives [2, 1, 0, 0, 0] [2, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law08 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [2] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans step02)
  · change Derives targetBasis (w 2 [0, 1, 0]) (w 0 [2, 0, 1, 0])
    have step01 :
        ListDerives [2, 0, 1, 0] [2, 0, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law02 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [2] []).symm
    have step02 :
        ListDerives [2, 0, 0, 1, 0] [2, 0, 0, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law01 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [2] [0]).symm
    have step03 :
        ListDerives [2, 0, 0, 0, 1, 0] [0, 2, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law08 (by decide)
          (w 0 []) (w 2 []) (w 0 [])
          [] [1, 0]).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans (step02.trans step03))
  · change Derives targetBasis (w 2 [0, 1, 0]) (w 1 [2, 0, 1, 0])
    have step01 :
        ListDerives [2, 0, 1, 0] [2, 0, 1, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law06 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [2] [])
    have step02 :
        ListDerives [2, 0, 1, 0, 1, 0] [2, 0, 1, 1, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law09 (by decide)
          (w 0 []) (w 1 []) (w 1 [])
          [2] [0])
    have step03 :
        ListDerives [2, 0, 1, 1, 1, 0] [1, 2, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law08 (by decide)
          (w 1 []) (w 2 [0]) (w 0 [])
          [] [0]).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans (step02.trans step03))
  · change Derives targetBasis (w 2 [0, 1, 0]) (w 2 [0, 1, 1, 0])
    have step01 :
        ListDerives [2, 0, 1, 0] [2, 0, 1, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law07 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [2] [])
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 2 [0, 1, 0]) (w 1 [0, 2, 1, 0])
    have step01 :
        ListDerives [2, 0, 1, 0] [2, 0, 1, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law07 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [2] [])
    have step02 :
        ListDerives [2, 0, 1, 1, 0] [2, 1, 1, 0, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law08 (by decide)
          (w 0 []) (w 1 [1]) (w 0 [])
          [2] [])
    have step03 :
        ListDerives [2, 1, 1, 0, 0, 0] [1, 0, 2, 1, 0, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law11 (by decide)
          (w 1 [0]) (w 2 [1]) (w 0 [])
          [] []).symm
    have step04 :
        ListDerives [1, 0, 2, 1, 0, 0] [1, 0, 2, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law05 (by decide)
          (w 0 []) (w 2 [1]) (w 0 [])
          [1] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans (step02.trans (step03.trans step04)))
  · change Derives targetBasis (w 2 [0, 1, 0]) (w 2 [0, 2, 1, 0])
    have step01 :
        ListDerives [2, 0, 1, 0] [2, 0, 0, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law02 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [2] []).symm
    have step02 :
        ListDerives [2, 0, 0, 1, 0] [2, 0, 2, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law09 (by decide)
          (w 2 []) (w 0 []) (w 1 [])
          [] [0]).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans step02)
  · change Derives targetBasis (w 2 [0, 1, 0]) (w 0 [1, 2, 1, 0])
    have step01 :
        ListDerives [2, 0, 1, 0] [2, 0, 1, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law07 (by decide)
          (w 0 []) (w 1 []) (w 0 [])
          [2] [])
    have step02 :
        ListDerives [2, 0, 1, 1, 0] [0, 2, 1, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law11 (by decide)
          (w 2 []) (w 0 []) (w 1 [])
          [] [0])
    have step03 :
        ListDerives [0, 2, 1, 1, 0] [0, 1, 2, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law10 (by decide)
          (w 0 []) (w 1 []) (w 2 [1])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01.trans (step02.trans step03))
  · change Derives targetBasis (w 1 [1, 0]) (w 1 [1, 1, 0])
    have step01 :
        ListDerives [1, 1, 0] [1, 1, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law01 (by decide)
          (w 1 []) (w 0 []) (w 0 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 2 [1, 1, 0]) (w 2 [1, 2, 0])
    have step01 :
        ListDerives [2, 1, 1, 0] [2, 1, 2, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law09 (by decide)
          (w 2 []) (w 1 []) (w 0 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)
  · change Derives targetBasis (w 2 [1, 0]) (w 2 [2, 1, 0])
    have step01 :
        ListDerives [2, 1, 0] [2, 2, 1, 0] := by
      simpa [instantiateThreeWords, w, Word.bind, Word.toList,
        Word.singleton, Word.append, Word.append_assoc] using
        (displayedStep Rank080.law04 (by decide)
          (w 2 []) (w 1 []) (w 0 [])
          [] []).symm
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
      (step01)

/-- Structural equational rebase from the genuine reversed S2 intersection. -/
theorem transportReversedS2Derivation
    {left right : Word Nat}
    (derivation : Derives (reversedBasis sourceBasis) left right) :
    Derives targetBasis left right := by
  apply derivation.transport
  intro identity member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  exact reversedS2AxiomDerives source sourceMember

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_203
