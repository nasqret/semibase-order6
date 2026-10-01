import SemigroupBasis.CoRoots.Order6L3RootS3_18.MacrosS4_9

/-!
# Generated guarded primitives for the rank-9 `S4_9` design

Generated mechanically from the 15 frozen BFS-labelled paths in evidence
SHA-256 `ce08104caa32f3d8c1b70eac7f25608b67bbb3a0b7e1c356816eb1af4aa428bd`.  Every step names its displayed law and exact context through
the generated direct macros.  This file must not be edited by hand.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L3RootS3_18

open SemigroupBasis

/-- Mechanically generated frozen BFS primitive `guarded_swap` (1 step). -/
theorem derives9PrimitiveGuardedSwap (V0 V1 V2 : Word Nat) :
    Derives basisS4_9
      (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V2)))))
      (V1 ++ (V0 ++ (V2 ++ (V2 ++ (V2))))) := by
  have step0 :
      Derives basisS4_9
        (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V2)))))
        (V1 ++ (V0 ++ (V2 ++ (V2 ++ (V2))))) := by
    have contextual := Derives.appendRight (derives9Law04 (V2) (V1) (V0)) (V2 ++ (V2))
    simpa [Word.append_assoc] using contextual
  exact step0

/-- Mechanically generated frozen BFS primitive `append_guard_long` (1 step). -/
theorem derives9PrimitiveAppendGuardLong (V0 V1 V2 V3 : Word Nat) :
    Derives basisS4_9
      (V0 ++ (V1 ++ (V2)))
      (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V3)))))) := by
  have step0 :
      Derives basisS4_9
        (V0 ++ (V1 ++ (V2)))
        (V0 ++ (V1 ++ (V2 ++ (V3 ++ (V3 ++ (V3)))))) := by
    have contextual := Derives.symm (derives9Law01 (V3) (V0) (V1) (V2))
    simpa [Word.append_assoc] using contextual
  exact step0

/-- Mechanically generated frozen BFS primitive `append_guard_long_repeated` (1 step). -/
theorem derives9PrimitiveAppendGuardLongRepeated (V0 V1 V2 : Word Nat) :
    Derives basisS4_9
      (V0 ++ (V0 ++ (V1)))
      (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V2)))))) := by
  have step0 :
      Derives basisS4_9
        (V0 ++ (V0 ++ (V1)))
        (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V2)))))) := by
    have contextual := Derives.symm (derives9Law01 (V2) (V0) (V0) (V1))
    simpa [Word.append_assoc] using contextual
  exact step0

/-- Mechanically generated frozen BFS primitive `guarded_cancel_context_0` (2 steps). -/
theorem derives9PrimitiveGuardedCancelContext0 (V0 V1 V2 : Word Nat) :
    Derives basisS4_9
      (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V2)))))))
      (V1 ++ (V2 ++ (V2 ++ (V2)))) := by
  have step0 :
      Derives basisS4_9
        (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V2)))))))
        (V1 ++ (V2 ++ (V2 ++ (V0 ++ (V0 ++ (V0 ++ (V2))))))) := by
    have contextual := derives9Law04 (V2) (V1 ++ (V2 ++ (V2))) (V0 ++ (V0 ++ (V0)))
    simpa [Word.append_assoc] using contextual
  have step1 :
      Derives basisS4_9
        (V1 ++ (V2 ++ (V2 ++ (V0 ++ (V0 ++ (V0 ++ (V2)))))))
        (V1 ++ (V2 ++ (V2 ++ (V2)))) := by
    have contextual := Derives.appendRight (derives9Law01 (V0) (V1) (V2) (V2)) (V2)
    simpa [Word.append_assoc] using contextual
  exact Derives.trans step0 step1

/-- Mechanically generated frozen BFS primitive `guarded_cancel_context_1` (2 steps). -/
theorem derives9PrimitiveGuardedCancelContext1 (V0 V1 V2 V3 : Word Nat) :
    Derives basisS4_9
      (V3 ++ (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V2))))))))
      (V3 ++ (V1 ++ (V2 ++ (V2 ++ (V2))))) := by
  have step0 :
      Derives basisS4_9
        (V3 ++ (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V2 ++ (V2 ++ (V2))))))))
        (V3 ++ (V1 ++ (V2 ++ (V0 ++ (V0 ++ (V0 ++ (V2 ++ (V2)))))))) := by
    have contextual := Derives.appendRight (Derives.prepend (V3) (derives9Law04 (V2) (V1 ++ (V2)) (V0 ++ (V0 ++ (V0))))) (V2)
    simpa [Word.append_assoc] using contextual
  have step1 :
      Derives basisS4_9
        (V3 ++ (V1 ++ (V2 ++ (V0 ++ (V0 ++ (V0 ++ (V2 ++ (V2))))))))
        (V3 ++ (V1 ++ (V2 ++ (V2 ++ (V2))))) := by
    have contextual := Derives.appendRight (derives9Law01 (V0) (V3) (V1) (V2)) (V2 ++ (V2))
    simpa [Word.append_assoc] using contextual
  exact Derives.trans step0 step1

/-- Mechanically generated frozen BFS primitive `guarded_cancel_context_2` (2 steps). -/
theorem derives9PrimitiveGuardedCancelContext2 (V0 V1 V2 V3 V4 : Word Nat) :
    Derives basisS4_9
      (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V4 ++ (V2 ++ (V2 ++ (V2))))))))
      (V1 ++ (V4 ++ (V2 ++ (V2 ++ (V2))))) := by
  have step0 :
      Derives basisS4_9
        (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V4 ++ (V2 ++ (V2 ++ (V2))))))))
        (V1 ++ (V4 ++ (V2 ++ (V0 ++ (V0 ++ (V0 ++ (V2 ++ (V2)))))))) := by
    have contextual := Derives.appendRight (derives9Law04 (V2) (V1 ++ (V4 ++ (V2))) (V0 ++ (V0 ++ (V0)))) (V2)
    simpa [Word.append_assoc] using contextual
  have step1 :
      Derives basisS4_9
        (V1 ++ (V4 ++ (V2 ++ (V0 ++ (V0 ++ (V0 ++ (V2 ++ (V2))))))))
        (V1 ++ (V4 ++ (V2 ++ (V2 ++ (V2))))) := by
    have contextual := Derives.appendRight (derives9Law01 (V0) (V1) (V4) (V2)) (V2 ++ (V2))
    simpa [Word.append_assoc] using contextual
  exact Derives.trans step0 step1

/-- Mechanically generated frozen BFS primitive `guarded_cancel_context_3` (2 steps). -/
theorem derives9PrimitiveGuardedCancelContext3 (V0 V1 V2 V3 V4 : Word Nat) :
    Derives basisS4_9
      (V3 ++ (V4 ++ (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V4 ++ (V3 ++ (V2 ++ (V2 ++ (V2)))))))))))
      (V3 ++ (V4 ++ (V1 ++ (V4 ++ (V3 ++ (V2 ++ (V2 ++ (V2)))))))) := by
  have step0 :
      Derives basisS4_9
        (V3 ++ (V4 ++ (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V4 ++ (V3 ++ (V2 ++ (V2 ++ (V2)))))))))))
        (V3 ++ (V4 ++ (V1 ++ (V1 ++ (V1 ++ (V1 ++ (V4 ++ (V3 ++ (V2 ++ (V2 ++ (V2))))))))))) := by
    have contextual := Derives.appendRight (Derives.prepend (V3 ++ (V4)) (derives9Law00 (V0) (V1))) (V1 ++ (V4 ++ (V3 ++ (V2 ++ (V2 ++ (V2))))))
    simpa [Word.append_assoc] using contextual
  have step1 :
      Derives basisS4_9
        (V3 ++ (V4 ++ (V1 ++ (V1 ++ (V1 ++ (V1 ++ (V4 ++ (V3 ++ (V2 ++ (V2 ++ (V2)))))))))))
        (V3 ++ (V4 ++ (V1 ++ (V4 ++ (V3 ++ (V2 ++ (V2 ++ (V2)))))))) := by
    have contextual := Derives.appendRight (derives9Law01 (V1) (V3) (V4) (V1)) (V4 ++ (V3 ++ (V2 ++ (V2 ++ (V2)))))
    simpa [Word.append_assoc] using contextual
  exact Derives.trans step0 step1

theorem generated9PrimitiveCount : 7 = 7 := by
  decide

    end SemigroupBasis.CoRoots.Order6L3RootS3_18
