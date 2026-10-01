import SemigroupBasis.CoRoots.Order6L3RootS3_18.MacrosS4_2

/-!
# Generated guarded primitives for the rank-9 `S4_2` design

Generated mechanically from the 15 frozen BFS-labelled paths in evidence
SHA-256 `ce08104caa32f3d8c1b70eac7f25608b67bbb3a0b7e1c356816eb1af4aa428bd`.  Every step names its displayed law and exact context through
the generated direct macros.  This file must not be edited by hand.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L3RootS3_18

open SemigroupBasis

/-- Mechanically generated frozen BFS primitive `guarded_swap` (1 step). -/
theorem derives2PrimitiveGuardedSwap (V0 V1 V2 : Word Nat) :
    Derives basisS4_2
      (V2 ++ (V2 ++ (V2 ++ (V0 ++ (V1)))))
      (V2 ++ (V2 ++ (V2 ++ (V1 ++ (V0))))) := by
  have step0 :
      Derives basisS4_2
        (V2 ++ (V2 ++ (V2 ++ (V0 ++ (V1)))))
        (V2 ++ (V2 ++ (V2 ++ (V1 ++ (V0))))) := by
    have contextual := derives2Law15 (V1) (V0) (V2 ++ (V2 ++ (V2)))
    simpa [Word.append_assoc] using contextual
  exact step0

/-- Mechanically generated frozen BFS primitive `prepend_guard_square` (1 step). -/
theorem derives2PrimitivePrependGuardSquare (V0 V1 V2 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0))
      (V2 ++ (V2 ++ (V2 ++ (V0 ++ (V0))))) := by
  have step0 :
      Derives basisS4_2
        (V0 ++ (V0))
        (V2 ++ (V2 ++ (V2 ++ (V0 ++ (V0))))) := by
    have contextual := derives2Law01 (V0) (V2)
    simpa [Word.append_assoc] using contextual
  exact step0

/-- Mechanically generated frozen BFS primitive `prepend_guard_long` (2 steps). -/
theorem derives2PrimitivePrependGuardLong (V0 V1 V2 V3 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V1 ++ (V3)))
      (V2 ++ (V2 ++ (V2 ++ (V0 ++ (V1 ++ (V3)))))) := by
  have step0 :
      Derives basisS4_2
        (V0 ++ (V1 ++ (V3)))
        (V0 ++ (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V3)))))) := by
    have contextual := Derives.symm (derives2Law16 (V0) (V1) (V3))
    simpa [Word.append_assoc] using contextual
  have step1 :
      Derives basisS4_2
        (V0 ++ (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V3))))))
        (V2 ++ (V2 ++ (V2 ++ (V0 ++ (V1 ++ (V3)))))) := by
    have contextual := Derives.appendRight (derives2Law11 (V0) (V2)) (V0 ++ (V1 ++ (V3)))
    simpa [Word.append_assoc] using contextual
  exact Derives.trans step0 step1

/-- Mechanically generated frozen BFS primitive `prepend_guard_long_repeated` (1 step). -/
theorem derives2PrimitivePrependGuardLongRepeated (V0 V1 V2 : Word Nat) :
    Derives basisS4_2
      (V0 ++ (V0 ++ (V1)))
      (V2 ++ (V2 ++ (V2 ++ (V0 ++ (V0 ++ (V1)))))) := by
  have step0 :
      Derives basisS4_2
        (V0 ++ (V0 ++ (V1)))
        (V2 ++ (V2 ++ (V2 ++ (V0 ++ (V0 ++ (V1)))))) := by
    have contextual := Derives.appendRight (derives2Law01 (V0) (V2)) (V1)
    simpa [Word.append_assoc] using contextual
  exact step0

/-- Mechanically generated frozen BFS primitive `guarded_cancel_context_0` (1 step). -/
theorem derives2PrimitiveGuardedCancelContext0 (V0 V1 V2 : Word Nat) :
    Derives basisS4_2
      (V2 ++ (V2 ++ (V2 ++ (V0 ++ (V0 ++ (V0 ++ (V1)))))))
      (V2 ++ (V2 ++ (V2 ++ (V1)))) := by
  have step0 :
      Derives basisS4_2
        (V2 ++ (V2 ++ (V2 ++ (V0 ++ (V0 ++ (V0 ++ (V1)))))))
        (V2 ++ (V2 ++ (V2 ++ (V1)))) := by
    have contextual := Derives.appendRight (Derives.prepend (V2) (Derives.symm (derives2Law10 (V2) (V0)))) (V1)
    simpa [Word.append_assoc] using contextual
  exact step0

/-- Mechanically generated frozen BFS primitive `guarded_cancel_context_1` (2 steps). -/
theorem derives2PrimitiveGuardedCancelContext1 (V0 V1 V2 V3 : Word Nat) :
    Derives basisS4_2
      (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V0 ++ (V0 ++ (V0 ++ (V1))))))))
      (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V1))))) := by
  have step0 :
      Derives basisS4_2
        (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V0 ++ (V0 ++ (V0 ++ (V1))))))))
        (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V3 ++ (V3 ++ (V3 ++ (V1)))))))) := by
    have contextual := Derives.appendRight (Derives.prepend (V2 ++ (V2 ++ (V2 ++ (V3)))) (derives2Law11 (V0) (V3))) (V1)
    simpa [Word.append_assoc] using contextual
  have step1 :
      Derives basisS4_2
        (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V3 ++ (V3 ++ (V3 ++ (V1))))))))
        (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V1))))) := by
    have contextual := Derives.appendRight (Derives.prepend (V2) (Derives.symm (derives2Law10 (V2) (V3)))) (V3 ++ (V1))
    simpa [Word.append_assoc] using contextual
  exact Derives.trans step0 step1

/-- Mechanically generated frozen BFS primitive `guarded_cancel_context_2` (1 step). -/
theorem derives2PrimitiveGuardedCancelContext2 (V0 V1 V2 V3 V4 : Word Nat) :
    Derives basisS4_2
      (V2 ++ (V2 ++ (V2 ++ (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V4))))))))
      (V2 ++ (V2 ++ (V2 ++ (V1 ++ (V4))))) := by
  have step0 :
      Derives basisS4_2
        (V2 ++ (V2 ++ (V2 ++ (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V4))))))))
        (V2 ++ (V2 ++ (V2 ++ (V1 ++ (V4))))) := by
    have contextual := Derives.appendRight (Derives.prepend (V2) (Derives.symm (derives2Law10 (V2) (V0)))) (V1 ++ (V4))
    simpa [Word.append_assoc] using contextual
  exact step0

/-- Mechanically generated frozen BFS primitive `guarded_cancel_context_3` (2 steps). -/
theorem derives2PrimitiveGuardedCancelContext3 (V0 V1 V2 V3 V4 : Word Nat) :
    Derives basisS4_2
      (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V4 ++ (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V4 ++ (V3)))))))))))
      (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V4 ++ (V1 ++ (V4 ++ (V3)))))))) := by
  have step0 :
      Derives basisS4_2
        (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V4 ++ (V0 ++ (V0 ++ (V0 ++ (V1 ++ (V4 ++ (V3)))))))))))
        (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V4 ++ (V1 ++ (V1 ++ (V1 ++ (V1 ++ (V4 ++ (V3))))))))))) := by
    have contextual := Derives.appendRight (Derives.prepend (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V4))))) (derives2Law11 (V0) (V1))) (V1 ++ (V4 ++ (V3)))
    simpa [Word.append_assoc] using contextual
  have step1 :
      Derives basisS4_2
        (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V4 ++ (V1 ++ (V1 ++ (V1 ++ (V1 ++ (V4 ++ (V3)))))))))))
        (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V4 ++ (V1 ++ (V4 ++ (V3)))))))) := by
    have contextual := Derives.prepend (V2 ++ (V2 ++ (V2 ++ (V3 ++ (V4))))) (derives2Law16 (V1) (V4) (V3))
    simpa [Word.append_assoc] using contextual
  exact Derives.trans step0 step1

theorem generated2PrimitiveCount : 8 = 8 := by
  decide

    end SemigroupBasis.CoRoots.Order6L3RootS3_18
