import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank075
import SemigroupBasis.CoRoots.Order6S5_107InitialIntersection

/-!
# Exact reversed initial-intersection rebase for rank 075

The authenticated rank-075 target contains fifteen displayed laws. Every law
of the independently complete S5_107 initial-intersection presentation,
after word reversal, has a concrete target derivation. Seven attachment laws
use the same explicit two-step hub `12100 -> 11020 -> target`; the remaining
eight source laws are single displayed-law substitutions. No finite-table
truth is promoted to an unrestricted semantic implication.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_108

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank075.basis

private abbrev initialBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6S5_107InitialIntersection.basis

private def w (first : Nat) (rest : List Nat) : Word Nat :=
  Word.mk first rest

private theorem displayed00 :
    Derives targetBasis (w 0 [0]) (w 0 [0, 0]) :=
  Derives.fromBasis (e := ⟨w 0 [0], w 0 [0, 0]⟩) (by decide)

private theorem displayed01 :
    Derives targetBasis (w 0 [0, 1, 0]) (w 0 [1, 0]) :=
  Derives.fromBasis (e := ⟨w 0 [0, 1, 0], w 0 [1, 0]⟩) (by decide)

private theorem displayed02 :
    Derives targetBasis (w 0 [0, 1, 1]) (w 0 [1, 0, 1]) :=
  Derives.fromBasis (e := ⟨w 0 [0, 1, 1], w 0 [1, 0, 1]⟩) (by decide)

private theorem displayed03 :
    Derives targetBasis (w 0 [0, 1, 1]) (w 1 [0, 0, 1]) :=
  Derives.fromBasis (e := ⟨w 0 [0, 1, 1], w 1 [0, 0, 1]⟩) (by decide)

private theorem displayed04 :
    Derives targetBasis (w 0 [0, 1, 1, 2]) (w 0 [1, 1, 0, 2]) :=
  Derives.fromBasis
    (e := ⟨w 0 [0, 1, 1, 2], w 0 [1, 1, 0, 2]⟩) (by decide)

private theorem displayed05 :
    Derives targetBasis (w 0 [0, 1, 2, 1]) (w 0 [0, 2, 1, 1]) :=
  Derives.fromBasis
    (e := ⟨w 0 [0, 1, 2, 1], w 0 [0, 2, 1, 1]⟩) (by decide)

private theorem displayed06 :
    Derives targetBasis (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]) :=
  Derives.fromBasis
    (e := ⟨w 0 [0, 1, 2, 1], w 0 [1, 0, 2, 1]⟩) (by decide)

private theorem displayed07 :
    Derives targetBasis (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 0, 1]) :=
  Derives.fromBasis
    (e := ⟨w 0 [0, 1, 2, 1], w 0 [1, 2, 0, 1]⟩) (by decide)

private theorem displayed08 :
    Derives targetBasis (w 0 [0, 1, 2, 1]) (w 0 [2, 0, 1, 1]) :=
  Derives.fromBasis
    (e := ⟨w 0 [0, 1, 2, 1], w 0 [2, 0, 1, 1]⟩) (by decide)

private theorem displayed09 :
    Derives targetBasis (w 0 [0, 1, 2, 1]) (w 0 [2, 1, 0, 1]) :=
  Derives.fromBasis
    (e := ⟨w 0 [0, 1, 2, 1], w 0 [2, 1, 0, 1]⟩) (by decide)

private theorem displayed10 :
    Derives targetBasis (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]) :=
  Derives.fromBasis
    (e := ⟨w 0 [0, 1, 2, 1], w 1 [0, 0, 2, 1]⟩) (by decide)

private theorem displayed11 :
    Derives targetBasis (w 0 [0, 1, 2, 1]) (w 1 [0, 2, 0, 1]) :=
  Derives.fromBasis
    (e := ⟨w 0 [0, 1, 2, 1], w 1 [0, 2, 0, 1]⟩) (by decide)

private theorem displayed12 :
    Derives targetBasis (w 0 [0, 1, 2, 1]) (w 1 [2, 0, 0, 1]) :=
  Derives.fromBasis
    (e := ⟨w 0 [0, 1, 2, 1], w 1 [2, 0, 0, 1]⟩) (by decide)

private theorem displayed13 :
    Derives targetBasis (w 0 [1, 0]) (w 0 [1, 0, 0]) :=
  Derives.fromBasis (e := ⟨w 0 [1, 0], w 0 [1, 0, 0]⟩) (by decide)

private theorem displayed14 :
    Derives targetBasis (w 0 [1, 0, 2, 0]) (w 0 [2, 0, 1, 0]) :=
  Derives.fromBasis
    (e := ⟨w 0 [1, 0, 2, 0], w 0 [2, 0, 1, 0]⟩) (by decide)

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

private def attachmentRenaming : Nat → Word Nat :=
  instantiateThreeWords
    (Word.singleton 1) (Word.singleton 0) (Word.singleton 2)

/-- Shared frozen displayed-law-08 step: `12100 -> 11020`. -/
theorem derivesAttachmentHub :
    Derives targetBasis (w 1 [2, 1, 0, 0]) (w 1 [1, 0, 2, 0]) := by
  have substituted := Derives.subst displayed08.symm attachmentRenaming
  simpa [attachmentRenaming, instantiateThreeWords, w,
    Word.bind, Word.singleton, Word.append, Word.append_assoc] using
    substituted

/-- Every reversed law of the already complete initial-intersection basis has
an explicit target proof of at most two frozen displayed-law steps. -/
theorem reversedInitialAxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ initialBasis) :
    Derives targetBasis
      identity.reversed.lhs identity.reversed.rhs := by
  simp only [SemigroupBasis.CoRoots.Order6S5_107InitialIntersection.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Derives targetBasis (w 0 [0]) (w 0 [0, 0])
    exact displayed00
  · change Derives targetBasis (w 0 [1, 0]) (w 0 [1, 0, 0])
    exact displayed13
  · change Derives targetBasis (w 0 [1, 0]) (w 0 [0, 1, 0])
    exact displayed01.symm
  · change Derives targetBasis (w 1 [1, 0, 0]) (w 1 [0, 1, 0])
    have substituted := Derives.subst displayed02 attachmentRenaming
    simpa [attachmentRenaming, instantiateThreeWords, w,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using
      substituted
  · change Derives targetBasis (w 1 [1, 0, 0]) (w 0 [1, 1, 0])
    have substituted := Derives.subst displayed03 attachmentRenaming
    simpa [attachmentRenaming, instantiateThreeWords, w,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using
      substituted
  · change Derives targetBasis (w 1 [2, 1, 0, 0]) (w 1 [1, 2, 0, 0])
    have next := Derives.subst displayed05 attachmentRenaming
    apply derivesAttachmentHub.trans
    simpa [attachmentRenaming, instantiateThreeWords, w,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using next
  · change Derives targetBasis (w 1 [2, 1, 0, 0]) (w 1 [2, 0, 1, 0])
    have next := Derives.subst displayed09 attachmentRenaming
    apply derivesAttachmentHub.trans
    simpa [attachmentRenaming, instantiateThreeWords, w,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using next
  · change Derives targetBasis (w 1 [2, 1, 0, 0]) (w 0 [2, 1, 1, 0])
    have next := Derives.subst displayed12 attachmentRenaming
    apply derivesAttachmentHub.trans
    simpa [attachmentRenaming, instantiateThreeWords, w,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using next
  · change Derives targetBasis (w 1 [2, 1, 0, 0]) (w 1 [0, 2, 1, 0])
    have next := Derives.subst displayed07 attachmentRenaming
    apply derivesAttachmentHub.trans
    simpa [attachmentRenaming, instantiateThreeWords, w,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using next
  · change Derives targetBasis (w 1 [2, 1, 0, 0]) (w 0 [1, 2, 1, 0])
    have next := Derives.subst displayed11 attachmentRenaming
    apply derivesAttachmentHub.trans
    simpa [attachmentRenaming, instantiateThreeWords, w,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using next
  · change Derives targetBasis (w 1 [2, 1, 0, 0]) (w 1 [1, 0, 2, 0])
    exact derivesAttachmentHub
  · change Derives targetBasis (w 1 [2, 1, 0, 0]) (w 1 [0, 1, 2, 0])
    have next := Derives.subst displayed06 attachmentRenaming
    apply derivesAttachmentHub.trans
    simpa [attachmentRenaming, instantiateThreeWords, w,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using next
  · change Derives targetBasis (w 1 [2, 1, 0, 0]) (w 0 [1, 1, 2, 0])
    have next := Derives.subst displayed10 attachmentRenaming
    apply derivesAttachmentHub.trans
    simpa [attachmentRenaming, instantiateThreeWords, w,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using next
  · change Derives targetBasis (w 0 [2, 0, 1, 0]) (w 0 [1, 0, 2, 0])
    exact displayed14.symm
  · change Derives targetBasis (w 2 [2, 1, 1, 0]) (w 2 [1, 1, 2, 0])
    have substituted := Derives.subst displayed04
      (instantiateThreeWords
        (Word.singleton 2) (Word.singleton 1) (Word.singleton 0))
    simpa [instantiateThreeWords, w,
      Word.bind, Word.singleton, Word.append, Word.append_assoc] using
      substituted

/-- Structural equational rebase from the reversed complete initial basis. -/
theorem transportReversedInitialDerivation
    {left right : Word Nat}
    (derivation : Derives (reversedBasis initialBasis) left right) :
    Derives targetBasis left right := by
  apply derivation.transport
  intro identity member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  exact reversedInitialAxiomDerives source sourceMember

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_108
