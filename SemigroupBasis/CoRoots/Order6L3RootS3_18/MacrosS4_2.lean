import SemigroupBasis.CoRoots.Order6L3RootS3_18.Blocks

/-!
# Generated direct macros for the rank-9 `S4_2` design

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
theorem derives2Law00 (V0 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0))
      (V0 ++ (V0 ++ (V0 ++ (V0 ++ (V0))))) := by
  have base :
      Derives basisS4_2 (word 0 [0]) (word 0 [0, 0, 0, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0]) (word 0 [0, 0, 0, 0])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V0 V0 V0)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 1. -/
theorem derives2Law01 (V0 V1 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0))
      (V1 ++ (V1 ++ (V1 ++ (V0 ++ (V0))))) := by
  have base :
      Derives basisS4_2 (word 0 [0]) (word 1 [1, 1, 0, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0]) (word 1 [1, 1, 0, 0])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 2. -/
theorem derives2Law02 (V0 V1 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0))
      (V1 ++ (V1 ++ (V0 ++ (V1 ++ (V0))))) := by
  have base :
      Derives basisS4_2 (word 0 [0]) (word 1 [1, 0, 1, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0]) (word 1 [1, 0, 1, 0])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 3. -/
theorem derives2Law03 (V0 V1 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0))
      (V1 ++ (V0 ++ (V1 ++ (V1 ++ (V0))))) := by
  have base :
      Derives basisS4_2 (word 0 [0]) (word 1 [0, 1, 1, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0]) (word 1 [0, 1, 1, 0])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 4. -/
theorem derives2Law04 (V0 V1 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0))
      (V0 ++ (V1 ++ (V1 ++ (V1 ++ (V0))))) := by
  have base :
      Derives basisS4_2 (word 0 [0]) (word 0 [1, 1, 1, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0]) (word 0 [1, 1, 1, 0])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 5. -/
theorem derives2Law05 (V0 V1 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0))
      (V1 ++ (V1 ++ (V0 ++ (V0 ++ (V1))))) := by
  have base :
      Derives basisS4_2 (word 0 [0]) (word 1 [1, 0, 0, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0]) (word 1 [1, 0, 0, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 6. -/
theorem derives2Law06 (V0 V1 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0))
      (V1 ++ (V0 ++ (V1 ++ (V0 ++ (V1))))) := by
  have base :
      Derives basisS4_2 (word 0 [0]) (word 1 [0, 1, 0, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0]) (word 1 [0, 1, 0, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 7. -/
theorem derives2Law07 (V0 V1 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0))
      (V0 ++ (V1 ++ (V1 ++ (V0 ++ (V1))))) := by
  have base :
      Derives basisS4_2 (word 0 [0]) (word 0 [1, 1, 0, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0]) (word 0 [1, 1, 0, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 8. -/
theorem derives2Law08 (V0 V1 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0))
      (V1 ++ (V0 ++ (V0 ++ (V1 ++ (V1))))) := by
  have base :
      Derives basisS4_2 (word 0 [0]) (word 1 [0, 0, 1, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0]) (word 1 [0, 0, 1, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 9. -/
theorem derives2Law09 (V0 V1 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0))
      (V0 ++ (V1 ++ (V0 ++ (V1 ++ (V1))))) := by
  have base :
      Derives basisS4_2 (word 0 [0]) (word 0 [1, 0, 1, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0]) (word 0 [1, 0, 1, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 10. -/
theorem derives2Law10 (V0 V1 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0))
      (V0 ++ (V0 ++ (V1 ++ (V1 ++ (V1))))) := by
  have base :
      Derives basisS4_2 (word 0 [0]) (word 0 [0, 1, 1, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0]) (word 0 [0, 1, 1, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 11. -/
theorem derives2Law11 (V0 V1 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0 ++ (V0)))
      (V1 ++ (V1 ++ (V1))) := by
  have base :
      Derives basisS4_2 (word 0 [0, 0]) (word 1 [1, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 0]) (word 1 [1, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 12. -/
theorem derives2Law12 (V0 V1 : Word Nat) :
    Derives basisS4_2
      (V1 ++ (V0 ++ (V0)))
      (V0 ++ (V1 ++ (V0))) := by
  have base :
      Derives basisS4_2 (word 1 [0, 0]) (word 0 [1, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 1 [0, 0]) (word 0 [1, 0])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 13. -/
theorem derives2Law13 (V0 V1 : Word Nat) :
    Derives basisS4_2
      (V1 ++ (V0 ++ (V0)))
      (V0 ++ (V0 ++ (V1))) := by
  have base :
      Derives basisS4_2 (word 1 [0, 0]) (word 0 [0, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 1 [0, 0]) (word 0 [0, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V1 V1)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 14. -/
theorem derives2Law14 (V0 V1 V2 : Word Nat) :
    Derives basisS4_2
      (V2 ++ (V1 ++ (V0)))
      (V1 ++ (V2 ++ (V0))) := by
  have base :
      Derives basisS4_2 (word 2 [1, 0]) (word 1 [2, 0]) :=
    Derives.fromBasis (e := Identity.mk
      (word 2 [1, 0]) (word 1 [2, 0])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V2 V2)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 15. -/
theorem derives2Law15 (V0 V1 V2 : Word Nat) :
    Derives basisS4_2
      (V2 ++ (V1 ++ (V0)))
      (V2 ++ (V0 ++ (V1))) := by
  have base :
      Derives basisS4_2 (word 2 [1, 0]) (word 2 [0, 1]) :=
    Derives.fromBasis (e := Identity.mk
      (word 2 [1, 0]) (word 2 [0, 1])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V2 V2)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Mechanically generated direct instance of displayed law 16. -/
theorem derives2Law16 (V0 V1 V2 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V2))))))
      (V0 ++ (V1 ++ (V2))) := by
  have base :
      Derives basisS4_2 (word 0 [0, 0, 0, 1, 2]) (word 0 [1, 2]) :=
    Derives.fromBasis (e := Identity.mk
      (word 0 [0, 0, 0, 1, 2]) (word 0 [1, 2])) (by decide)
  have substituted :=
    Derives.subst base (instantiateFourWords V0 V1 V2 V2)
  simpa [word, instantiateFourWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem generated2DirectLawCount : 17 = 17 := by
  decide

end SemigroupBasis.CoRoots.Order6L3RootS3_18
