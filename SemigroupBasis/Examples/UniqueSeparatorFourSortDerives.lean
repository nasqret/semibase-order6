import SemigroupBasis.Examples.UniqueSeparatorFourQuadraticSwap
import SemigroupBasis.Examples.UniqueSeparatorFourNormalForm
import SemigroupBasis.Examples.UniqueSeparatorFourSaturation

namespace SemigroupBasis.Examples

/-- Deterministic ascending order for a quadratic block. -/
def uniqueSeparatorSortQuadratic (letters : List Nat) : List Nat :=
  letters.mergeSort (fun x y : Nat => decide (x ≤ y))

/-- Sort the quadratic block of a segment without moving its separator. -/
def uniqueSeparatorSortSquareSegment
    (segment : UniqueSeparatorSquareSegment) :
    UniqueSeparatorSquareSegment :=
  ⟨uniqueSeparatorSortQuadratic segment.quadratic, segment.separator⟩

/-- Sort every quadratic block while retaining the segment boundaries. -/
def uniqueSeparatorSortSquareSegments
    (segments : List UniqueSeparatorSquareSegment) :
    List UniqueSeparatorSquareSegment :=
  segments.map uniqueSeparatorSortSquareSegment

@[simp]
theorem uniqueSeparatorSortSquareSegment_quadratic
    (segment : UniqueSeparatorSquareSegment) :
    (uniqueSeparatorSortSquareSegment segment).quadratic =
      uniqueSeparatorSortQuadratic segment.quadratic :=
  rfl

@[simp]
theorem uniqueSeparatorSortSquareSegment_separator
    (segment : UniqueSeparatorSquareSegment) :
    (uniqueSeparatorSortSquareSegment segment).separator =
      segment.separator :=
  rfl

theorem uniqueSeparatorSortQuadratic_perm (letters : List Nat) :
    (uniqueSeparatorSortQuadratic letters).Perm letters := by
  exact List.mergeSort_perm _ _

theorem uniqueSeparatorSortSquareSegment_render_perm
    (segment : UniqueSeparatorSquareSegment) :
    (uniqueSeparatorSortSquareSegment segment).render.Perm
      segment.render := by
  exact List.Perm.append
    (uniqueSeparatorSortQuadratic_perm segment.quadratic)
    (List.Perm.refl segment.separator.toList)

theorem uniqueSeparatorSortSquareSegments_render_perm :
    ∀ segments : List UniqueSeparatorSquareSegment,
      (uniqueSeparatorRenderSquareSegments
          (uniqueSeparatorSortSquareSegments segments)).Perm
        (uniqueSeparatorRenderSquareSegments segments)
  | [] => List.Perm.nil
  | segment :: rest => by
      simp only [uniqueSeparatorSortSquareSegments, List.map_cons,
        uniqueSeparatorRenderSquareSegments, List.flatMap_cons]
      exact List.Perm.append
        (uniqueSeparatorSortSquareSegment_render_perm segment)
        (uniqueSeparatorSortSquareSegments_render_perm rest)

theorem uniqueSeparatorSortSquareSegment_sorted
    (segment : UniqueSeparatorSquareSegment) :
    (uniqueSeparatorSortSquareSegment segment).quadratic.Pairwise
      (· ≤ ·) := by
  have transitive :
      ∀ a b c : Nat,
        decide (a ≤ b) = true →
        decide (b ≤ c) = true →
        decide (a ≤ c) = true := by
    intro a b c hab hbc
    exact decide_eq_true
      (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  have total :
      ∀ a b : Nat,
        (decide (a ≤ b) || decide (b ≤ a)) = true := by
    intro a b
    rcases Nat.le_total a b with hab | hba
    · simp [hab]
    · simp [hba]
  exact
    (List.pairwise_mergeSort transitive total
      segment.quadratic).imp
        (fun relation => of_decide_eq_true relation)

theorem uniqueSeparatorSortSquareSegment_nodup
    (segment : UniqueSeparatorSquareSegment)
    (nodup : segment.quadratic.Nodup) :
    (uniqueSeparatorSortSquareSegment segment).quadratic.Nodup :=
  (uniqueSeparatorSortQuadratic_perm segment.quadratic).symm.nodup nodup

theorem uniqueSeparatorSortSquareSegment_nodup_iff
    (segment : UniqueSeparatorSquareSegment) :
    (uniqueSeparatorSortSquareSegment segment).quadratic.Nodup ↔
      segment.quadratic.Nodup :=
  (uniqueSeparatorSortQuadratic_perm segment.quadratic).nodup_iff

theorem uniqueSeparatorSortSquareSegments_sorted
    (segments : List UniqueSeparatorSquareSegment)
    (segment : UniqueSeparatorSquareSegment)
    (member :
      segment ∈ uniqueSeparatorSortSquareSegments segments) :
    segment.quadratic.Pairwise (· ≤ ·) := by
  rcases List.mem_map.mp member with ⟨source, _, rfl⟩
  exact uniqueSeparatorSortSquareSegment_sorted source

theorem uniqueSeparatorSortSquareSegments_nodup
    (segments : List UniqueSeparatorSquareSegment)
    (nodup :
      ∀ segment ∈ segments, segment.quadratic.Nodup)
    (segment : UniqueSeparatorSquareSegment)
    (member :
      segment ∈ uniqueSeparatorSortSquareSegments segments) :
    segment.quadratic.Nodup := by
  rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
  exact uniqueSeparatorSortSquareSegment_nodup source
    (nodup source sourceMember)

/-- A permutation of a quadratic block can be realized by contextual
adjacent swaps, provided every letter in the block has total multiplicity
two in the full word. -/
theorem uniqueSeparatorListDerivesQuadraticPerm
    {source target : List Nat}
    (permutation : source.Perm target) :
    ∀ (pre post : List Nat),
      (∀ z ∈ source,
        (pre ++ source ++ post).count z = 2) →
      UniqueSeparatorListDerives
        (pre ++ source ++ post)
        (pre ++ target ++ post) := by
  induction permutation with
  | nil =>
      intro pre post _
      simpa using UniqueSeparatorListDerives.refl (pre ++ post)
  | @cons x source target permutation ih =>
      intro pre post quadratic
      have tailQuadratic :
          ∀ z ∈ source,
            ((pre ++ [x]) ++ source ++ post).count z = 2 := by
        intro z member
        have count :=
          quadratic z (List.mem_cons_of_mem x member)
        simpa [List.append_assoc] using count
      simpa [List.append_assoc] using
        ih (pre ++ [x]) post tailQuadratic
  | swap x y rest =>
      intro pre post quadratic
      by_cases equal : y = x
      · subst y
        simpa [List.append_assoc] using
          UniqueSeparatorListDerives.refl
            (pre ++ x :: x :: rest ++ post)
      · have yQuadratic :
            (pre ++ (y :: x :: (rest ++ post))).count y = 2 := by
          simpa [List.append_assoc] using
            quadratic y (by simp)
        have xQuadratic :
            (pre ++ (y :: x :: (rest ++ post))).count x = 2 := by
          simpa [List.append_assoc] using
            quadratic x (by simp)
        simpa [List.append_assoc] using
          uniqueSeparatorListDerivesAdjacentQuadraticSwap
            (pre := pre) (post := rest ++ post)
            equal yQuadratic xQuadratic
  | @trans source middle target first second ihFirst ihSecond =>
      intro pre post quadratic
      have firstStep := ihFirst pre post quadratic
      have middleQuadratic :
          ∀ z ∈ middle,
            (pre ++ middle ++ post).count z = 2 := by
        intro z member
        have sourceMember : z ∈ source :=
          first.mem_iff.mpr member
        have sourceCount := quadratic z sourceMember
        have countEquality :
            (pre ++ source ++ post).count z =
              (pre ++ middle ++ post).count z := by
          simp only [List.count_append]
          rw [first.count z]
        rw [← countEquality]
        exact sourceCount
      exact firstStep.trans
        (ihSecond pre post middleQuadratic)

theorem uniqueSeparatorSortSquareSegment_derives
    (segment : UniqueSeparatorSquareSegment)
    (pre post : List Nat)
    (quadratic :
      ∀ z ∈ segment.quadratic,
        (pre ++ segment.render ++ post).count z = 2) :
    UniqueSeparatorListDerives
      (pre ++ segment.render ++ post)
      (pre ++
        (uniqueSeparatorSortSquareSegment segment).render ++ post) := by
  have blockDerivation :=
    uniqueSeparatorListDerivesQuadraticPerm
      (uniqueSeparatorSortQuadratic_perm
        segment.quadratic).symm
      pre (segment.separator.toList ++ post)
      (by
        intro z member
        simpa [UniqueSeparatorSquareSegment.render,
          List.append_assoc] using quadratic z member)
  simpa [UniqueSeparatorSquareSegment.render,
    uniqueSeparatorSortSquareSegment,
    List.append_assoc] using blockDerivation

/-- Sort all quadratic blocks in context. The multiplicity premise refers
to the complete rendered word, so later segment derivations retain access to
the two global occurrences after earlier blocks have been sorted. -/
theorem uniqueSeparatorSortSquareSegments_derives_context :
    ∀ (segments : List UniqueSeparatorSquareSegment)
      (pre post : List Nat),
      (∀ segment ∈ segments, ∀ z ∈ segment.quadratic,
        (pre ++
          uniqueSeparatorRenderSquareSegments segments ++ post).count z =
            2) →
      UniqueSeparatorListDerives
        (pre ++
          uniqueSeparatorRenderSquareSegments segments ++ post)
        (pre ++
          uniqueSeparatorRenderSquareSegments
            (uniqueSeparatorSortSquareSegments segments) ++ post)
  | [], pre, post, _ => by
      simpa [uniqueSeparatorSortSquareSegments,
        uniqueSeparatorRenderSquareSegments] using
          UniqueSeparatorListDerives.refl (pre ++ post)
  | segment :: rest, pre, post, quadratic => by
      let sortedSegment := uniqueSeparatorSortSquareSegment segment
      have segmentQuadratic :
          ∀ z ∈ segment.quadratic,
            (pre ++ segment.render ++
              (uniqueSeparatorRenderSquareSegments rest ++ post)).count z =
                2 := by
        intro z member
        simpa [uniqueSeparatorRenderSquareSegments,
          List.append_assoc] using
            quadratic segment (by simp) z member
      have firstStep :
          UniqueSeparatorListDerives
            (pre ++ segment.render ++
              (uniqueSeparatorRenderSquareSegments rest ++ post))
            (pre ++ sortedSegment.render ++
              (uniqueSeparatorRenderSquareSegments rest ++ post)) := by
        simpa [sortedSegment] using
          uniqueSeparatorSortSquareSegment_derives
            segment pre
            (uniqueSeparatorRenderSquareSegments rest ++ post)
            segmentQuadratic
      have restQuadratic :
          ∀ candidate ∈ rest, ∀ z ∈ candidate.quadratic,
            ((pre ++ sortedSegment.render) ++
              uniqueSeparatorRenderSquareSegments rest ++ post).count z =
                2 := by
        intro candidate candidateMember z member
        have originalCount :
            (pre ++ segment.render ++
              uniqueSeparatorRenderSquareSegments rest ++ post).count z =
                2 := by
          simpa [uniqueSeparatorRenderSquareSegments,
            List.append_assoc] using
              quadratic candidate (by simp [candidateMember]) z member
        have countEquality :
            ((pre ++ sortedSegment.render) ++
              uniqueSeparatorRenderSquareSegments rest ++ post).count z =
              (pre ++ segment.render ++
                uniqueSeparatorRenderSquareSegments rest ++ post).count z := by
          simp only [List.count_append]
          rw [show sortedSegment.render.count z =
              segment.render.count z by
            exact
              (uniqueSeparatorSortSquareSegment_render_perm
                segment).count z]
        exact countEquality.trans originalCount
      have restStep :=
        uniqueSeparatorSortSquareSegments_derives_context
          rest (pre ++ sortedSegment.render) post restQuadratic
      have firstStep' :
          UniqueSeparatorListDerives
            (pre ++ segment.render ++
              uniqueSeparatorRenderSquareSegments rest ++ post)
            ((pre ++ sortedSegment.render) ++
              uniqueSeparatorRenderSquareSegments rest ++ post) := by
        simpa [List.append_assoc] using firstStep
      simpa [sortedSegment, uniqueSeparatorSortSquareSegments,
        uniqueSeparatorRenderSquareSegments,
        List.append_assoc] using firstStep'.trans restStep

theorem uniqueSeparatorSortSquareSegments_derives
    (segments : List UniqueSeparatorSquareSegment)
    (quadratic :
      ∀ segment ∈ segments, ∀ z ∈ segment.quadratic,
        (uniqueSeparatorRenderSquareSegments segments).count z = 2) :
    UniqueSeparatorListDerives
      (uniqueSeparatorRenderSquareSegments segments)
      (uniqueSeparatorRenderSquareSegments
        (uniqueSeparatorSortSquareSegments segments)) := by
  simpa using
    uniqueSeparatorSortSquareSegments_derives_context
      segments [] [] (by simpa using quadratic)

/-- After endpoint capping, every quadratic member of a split segment has
global count two, so all segment blocks can be sorted derivably. -/
theorem uniqueSeparatorSortSplitLinear_derives
    (xs : List Nat) (limited : UniqueSeparatorTwoLimited xs) :
    UniqueSeparatorListDerives xs
      (uniqueSeparatorRenderSquareSegments
        (uniqueSeparatorSortSquareSegments
          (uniqueSeparatorSplitLinear xs))) := by
  have derivation :=
    uniqueSeparatorSortSquareSegments_derives
      (uniqueSeparatorSplitLinear xs)
      (by
        intro segment segmentMember z member
        rw [uniqueSeparatorRender_splitLinear xs]
        exact uniqueSeparatorSplitLinear_quadratic_count_two
          xs limited segment segmentMember z member)
  simpa [uniqueSeparatorRender_splitLinear xs] using derivation

/-- The sorting phase only needs the saturation postcondition's multiplicity
contract; it does not depend on the implementation of saturation. -/
theorem uniqueSeparatorSortSplitLinear_derives_of_saturationPostcondition
    {source output : List Nat}
    (postcondition :
      UniqueSeparatorSaturationPostcondition source output) :
    UniqueSeparatorListDerives output
      (uniqueSeparatorRenderSquareSegments
        (uniqueSeparatorSortSquareSegments
          (uniqueSeparatorSplitLinear output))) := by
  have limited : UniqueSeparatorTwoLimited output := by
    intro z
    by_cases member : z ∈ output
    · rcases postcondition.memberCountOneOrTwo z member with
        countOne | countTwo
      · omega
      · omega
    · rw [List.count_eq_zero.mpr member]
      omega
  exact uniqueSeparatorSortSplitLinear_derives output limited

/-- Concrete sorting target after endpoint capping and `L₄` saturation. -/
theorem uniqueSeparatorSortEndpointCapSaturateSplit_derives
    (xs : List Nat) :
    UniqueSeparatorListDerives
      (uniqueSeparatorSaturate
        (uniqueSeparatorEndpointCap xs))
      (uniqueSeparatorRenderSquareSegments
        (uniqueSeparatorSortSquareSegments
          (uniqueSeparatorSplitLinear
            (uniqueSeparatorSaturate
              (uniqueSeparatorEndpointCap xs))))) :=
  uniqueSeparatorSortSplitLinear_derives_of_saturationPostcondition
    (uniqueSeparatorEndpointCapSaturate_postcondition xs)

/-- The endpoint-capped word derives through saturation and then through
deterministic sorting of every quadratic segment. -/
theorem uniqueSeparatorEndpointCapSaturateSort_derives
    (xs : List Nat) :
    UniqueSeparatorListDerives
      (uniqueSeparatorEndpointCap xs)
      (uniqueSeparatorRenderSquareSegments
        (uniqueSeparatorSortSquareSegments
          (uniqueSeparatorSplitLinear
            (uniqueSeparatorSaturate
              (uniqueSeparatorEndpointCap xs))))) := by
  exact
    (uniqueSeparatorEndpointCapSaturate_postcondition xs).derives.trans
      (uniqueSeparatorSortEndpointCapSaturateSplit_derives xs)

end SemigroupBasis.Examples
