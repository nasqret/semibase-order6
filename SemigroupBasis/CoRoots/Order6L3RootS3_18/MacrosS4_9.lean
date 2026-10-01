import SemigroupBasis.CoRoots.Order6L3RootS3_18.Blocks

/-!
# Generated direct macros for the rank-9 `S4_9` design

Generated mechanically by
`tools/order6/l3_root_s3_18/generate_macros.py` from frozen evidence
SHA-256 `ce08104caa32f3d8c1b70eac7f25608b67bbb3a0b7e1c356816eb1af4aa428bd`.  This file must not be edited by hand.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L3RootS3_18

open SemigroupBasis

private def word (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def instantiateFourWords
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | n + 4 => Word.singleton (n + 4)

/-- Mechanically generated direct instance of displayed law 0. -/
theorem derives9Law00 (V0 V1 : Word Nat) :
    Derives basisS4_9
      (V0 ++ (V0 ++ (V0)))
      (V1 ++ (V1 ++ (V1))) := by
  have base :
      Derives basisS4_9 (word 0 [0, 0]) (word 1 [1, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 0]) (word 1 [1, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 1. -/
theorem derives9Law01 (V0 V1 V2 V3 : Word Nat) :
    Derives basisS4_9
      (V1 ++ (V2 ++ (V3 ++ (V0 ++ (V0 ++ (V0))))))
      (V1 ++ (V2 ++ (V3))) := by
  have base :
      Derives basisS4_9 (word 3 [2, 1, 0, 0, 0]) (word 3 [2, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 3 [2, 1, 0, 0, 0]) (word 3 [2, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V3 V2 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 2. -/
theorem derives9Law02 (V0 V1 : Word Nat) :
    Derives basisS4_9
      (V1 ++ (V0 ++ (V0)))
      (V0 ++ (V1 ++ (V0))) := by
  have base :
      Derives basisS4_9 (word 1 [0, 0]) (word 0 [1, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 1 [0, 0]) (word 0 [1, 0])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 3. -/
theorem derives9Law03 (V0 V1 : Word Nat) :
    Derives basisS4_9
      (V1 ++ (V0 ++ (V0)))
      (V0 ++ (V0 ++ (V1))) := by
  have base :
      Derives basisS4_9 (word 1 [0, 0]) (word 0 [0, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 1 [0, 0]) (word 0 [0, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 4. -/
theorem derives9Law04 (V0 V1 V2 : Word Nat) :
    Derives basisS4_9
      (V2 ++ (V1 ++ (V0)))
      (V1 ++ (V2 ++ (V0))) := by
  have base :
      Derives basisS4_9 (word 2 [1, 0]) (word 1 [2, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 2 [1, 0]) (word 1 [2, 0])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V2 V2)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 5. -/
theorem derives9Law05 (V0 V1 V2 : Word Nat) :
    Derives basisS4_9
      (V2 ++ (V1 ++ (V0)))
      (V2 ++ (V0 ++ (V1))) := by
  have base :
      Derives basisS4_9 (word 2 [1, 0]) (word 2 [0, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 2 [1, 0]) (word 2 [0, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V2 V2)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem generated9DirectLawCount : 6 = 6 := by
  decide

end SemigroupBasis.CoRoots.Order6L3RootS3_18
