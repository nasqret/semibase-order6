import SemigroupBasis.CoRoots.Order6SporadicSection18TagPropagation

/-! Actual word substitution inserts a fresh square immediately before or
after the unique selected simple letter. Square-block commutation also converts
an insertion after a block to the same canonical prefix-tag convention. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Actual
open Canonical

def tagLetter (beforeTag : Bool) (marker x : Nat) : List Nat :=
  if x = marker then (if beforeTag then [0, 0, x.succ] else [x.succ, 0, 0]) else [x.succ]

def taggedWord (beforeTag : Bool) (marker : Nat) (letters : List Nat) : List Nat :=
  letters.flatMap (tagLetter beforeTag marker)

def taggedValuation (beforeTag : Bool) (marker : Nat) (valuation : Nat → Fin 6) (x : Nat) : Fin 6 :=
  if x = marker then
    (if beforeTag then tableMul (tableMul (valuation 0) (valuation 0)) (valuation x.succ)
      else tableMul (valuation x.succ) (tableMul (valuation 0) (valuation 0)))
  else valuation x.succ

private theorem assoc_eval (a b c : Fin 6) :
    tableMul (tableMul a b) c = tableMul a (tableMul b c) := table.assoc a b c

theorem run_tagLetter (beforeTag : Bool) (marker x : Nat) (valuation : Nat → Fin 6) (acc : Fin 6) :
    run valuation acc (tagLetter beforeTag marker x) = tableMul acc (taggedValuation beforeTag marker valuation x) := by
  by_cases equal : x = marker <;> cases beforeTag <;>
    simp [tagLetter, taggedValuation, equal, run_cons, run_nil, assoc_eval]

theorem run_taggedWord (beforeTag : Bool) (marker : Nat) (letters : List Nat)
    (valuation : Nat → Fin 6) (acc : Fin 6) :
    run valuation acc (taggedWord beforeTag marker letters) =
      run (taggedValuation beforeTag marker valuation) acc letters := by
  induction letters generalizing acc with
  | nil => rfl
  | cons head tail ih =>
      change run valuation acc (tagLetter beforeTag marker head ++ taggedWord beforeTag marker tail) = _
      rw [run_append, run_tagLetter, run_cons]
      exact ih _

theorem SameEval.taggedWord {left right : List Nat} (same : SameEval left right)
    (beforeTag : Bool) (marker : Nat) :
    SameEval (taggedWord beforeTag marker left) (taggedWord beforeTag marker right) := by
  intro valuation acc
  rw [run_taggedWord, run_taggedWord]
  exact same (taggedValuation beforeTag marker valuation) acc

theorem taggedWord_of_absent (beforeTag : Bool) (marker : Nat) (letters : List Nat)
    (absent : marker ∉ letters) : taggedWord beforeTag marker letters = letters.map Nat.succ := by
  induction letters with
  | nil => rfl
  | cons head tail ih =>
      have notHead : head ≠ marker := by
        intro equal
        apply absent
        exact List.mem_cons.mpr (Or.inl equal.symm)
      have notTail : marker ∉ tail := fun member => absent (List.Mem.tail head member)
      change tagLetter beforeTag marker head ++ taggedWord beforeTag marker tail = head.succ :: tail.map Nat.succ
      rw [tagLetter, if_neg notHead, ih notTail]
      rfl

private theorem taggedWord_append (beforeTag : Bool) (marker : Nat) (left right : List Nat) :
    taggedWord beforeTag marker (left ++ right) = taggedWord beforeTag marker left ++ taggedWord beforeTag marker right :=
  List.flatMap_append

theorem taggedWord_unique (beforeTag : Bool) (marker : Nat) (whole before after : List Nat)
    (shape : whole = before ++ marker :: after) (simple : whole.count marker = 1) :
    taggedWord beforeTag marker whole = before.map Nat.succ ++ tagLetter beforeTag marker marker ++ after.map Nat.succ := by
  have clear := simple_marker_clear whole before after marker shape simple
  have beforeClear : marker ∉ before := fun member => clear (List.mem_append.mpr (Or.inl member))
  have afterClear : marker ∉ after := fun member => clear (List.mem_append.mpr (Or.inr member))
  rw [shape, taggedWord_append]
  change taggedWord beforeTag marker before ++ (tagLetter beforeTag marker marker ++ taggedWord beforeTag marker after) = _
  rw [taggedWord_of_absent beforeTag marker before beforeClear, taggedWord_of_absent beforeTag marker after afterClear]
  simp only [List.append_assoc]

theorem run_tagged_marked_square_suffix (valuation : Nat → Fin 6) (marked : List Nat)
    (nonempty : marked ≠ []) (acc : Fin 6) :
    run valuation acc (squareList (tagBlock marked marked)) =
      run valuation acc (squareList (marked.map Nat.succ) ++ [0, 0]) := by
  have shifted : marked.map Nat.succ ≠ [] := by simpa using nonempty
  have commute : ∀ z e : Fin 6, SquareColor e → tableMul (tableMul z z) e = tableMul e (tableMul z z) := by
    unfold SquareColor
    decide
  rw [run_tagged_marked_square valuation marked nonempty acc,
    commute (valuation 0) (squareValue valuation (marked.map Nat.succ)) (squareValue_color valuation _),
    run_append, run_square_value valuation (marked.map Nat.succ) shifted acc]
  simp only [run_cons, run_nil, assoc_eval]

theorem singleTaggedWord_sameEval_suffix (marked : List Nat) (nonempty : marked ≠ [])
    (before : List Slot) (slot : Slot) (after : List Slot) (selected : slot.block = marked) :
    SameEval (singleTaggedWord marked before slot after)
      ((render before).map Nat.succ ++ slot.gap.map Nat.succ ++
        (squareList slot.block).map Nat.succ ++ [0, 0] ++ (render after).map Nat.succ) := by
  intro valuation acc
  have localEqual : ∀ a, run valuation a (squareList (tagBlock marked slot.block)) =
      run valuation a ((squareList slot.block).map Nat.succ ++ [0, 0]) := by
    intro a
    rw [selected, ← squareList_shift]
    exact run_tagged_marked_square_suffix valuation marked nonempty a
  simp only [singleTaggedWord, run_append]
  rw [localEqual, run_append]

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.run_tagLetter
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.run_taggedWord
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.SameEval.taggedWord
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.taggedWord_of_absent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.taggedWord_unique
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.run_tagged_marked_square_suffix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.singleTaggedWord_sameEval_suffix

end SemigroupBasis.CoRoots.Order6SporadicSection18.Actual
