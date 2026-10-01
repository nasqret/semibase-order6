import SemigroupBasis.CoRoots.Order6SporadicSection25F3NoCuts
import SemigroupBasis.CoRoots.Order6SporadicSection25ComponentIsolation

/-! Exact B0 cuts isolate BOTH actual factors on each nonempty side.
The affine factor uses its true unit; B0 uses proved one-sided padding. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator
open SemigroupBasis

theorem exactCut_separator_absent {letters left right : List Nat} {separator : Nat}
    (cut : Examples.UniqueSeparatorFourExactCut letters left separator right) :
    separator ∉ left ∧ separator ∉ right := by
  have counted := cut.2.1
  rw [cut.1, List.count_append, List.count_cons_self] at counted
  constructor
  · intro member
    have positive := List.count_pos_iff.mpr member
    omega
  · intro member
    have positive := List.count_pos_iff.mpr member
    omega

theorem exactCut_back_disjoint {letters left right : List Nat} {separator : Nat}
    (cut : Examples.UniqueSeparatorFourExactCut letters left separator right) :
    ∀ letter, letter ∈ separator :: right → letter ∉ left := by
  intro letter member inLeft
  rcases List.mem_cons.mp member with rfl | inRight
  · exact (exactCut_separator_absent cut).1 inLeft
  · exact cut.2.2 letter inLeft inRight

theorem exactCut_front_disjoint {letters left right : List Nat} {separator : Nat}
    (cut : Examples.UniqueSeparatorFourExactCut letters left separator right) :
    ∀ letter, letter ∈ left ++ [separator] → letter ∉ right := by
  intro letter member inRight
  rcases List.mem_append.mp member with inLeft | last
  · exact cut.2.2 letter inLeft inRight
  · have equal : letter = separator := List.mem_singleton.mp last
    subst letter
    exact (exactCut_separator_absent cut).2 inRight

theorem filter_sameWordSupport (keep target : Word Nat)
    (same : SameWordSupport keep target) :
    target.toList.filter (fun letter => decide (letter ∈ keep.toList)) = target.toList := by
  apply filter_all_kept
  intro letter member
  exact decide_eq_true ((same letter).mpr member)

theorem exactCut_prefix_factors (identity : Identity Nat)
    (leftFront rightFront : Word Nat) (leftBack rightBack : List Nat) (separator : Nat)
    (leftCut : Examples.UniqueSeparatorFourExactCut identity.lhs.toList leftFront.toList separator leftBack)
    (rightCut : Examples.UniqueSeparatorFourExactCut identity.rhs.toList rightFront.toList separator rightBack)
    (same : SameWordSupport leftFront rightFront)
    (separatorValid : identity.SatisfiedBy semigroup)
    (affineValid : identity.SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite) :
    (⟨leftFront,rightFront⟩ : Identity Nat).SatisfiedBy semigroup ∧
      (⟨leftFront,rightFront⟩ : Identity Nat).SatisfiedBy
        Generated.Catalogue.S4_96.table.semigroup.opposite := by
  let leftBackWord : Word Nat := ⟨separator, leftBack⟩
  let rightBackWord : Word Nat := ⟨separator, rightBack⟩
  have leftWhole : identity.lhs = leftFront ++ leftBackWord := by
    apply Word.toList_injective
    simpa only [Word.toList_append, leftBackWord, Word.toList] using leftCut.1
  have rightWhole : identity.rhs = rightFront ++ rightBackWord := by
    apply Word.toList_injective
    simpa only [Word.toList_append, rightBackWord, Word.toList] using rightCut.1
  have leftDisjoint : ∀ letter, letter ∈ leftBackWord.toList → letter ∉ leftFront.toList :=
    exactCut_back_disjoint leftCut
  have rightDisjoint : ∀ letter, letter ∈ rightBackWord.toList → letter ∉ rightFront.toList :=
    exactCut_back_disjoint rightCut
  have splitValid : (⟨leftFront ++ leftBackWord, rightFront ++ rightBackWord⟩ : Identity Nat).SatisfiedBy semigroup := by
    intro valuation
    change semigroup.eval valuation (leftFront ++ leftBackWord) =
      semigroup.eval valuation (rightFront ++ rightBackWord)
    rw [← leftWhole, ← rightWhole]
    exact separatorValid valuation
  have leftDiscard : leftBackWord.toList.filter (fun letter => decide (letter ∈ leftFront.toList)) = [] :=
    filter_disjoint_support leftBackWord.toList leftFront.toList leftDisjoint
  have rightDiscard : rightBackWord.toList.filter (fun letter => decide (letter ∈ leftFront.toList)) = [] :=
    filter_disjoint_support rightBackWord.toList leftFront.toList
      (fun letter member inFront => rightDisjoint letter member ((same letter).mp inFront))
  have leftFilter : identity.lhs.toList.filter (fun letter => decide (letter ∈ leftFront.toList)) = leftFront.toList := by
    rw [leftWhole, Word.toList_append, List.filter_append, filter_to_own_support, leftDiscard, List.append_nil]
  have rightFilter : identity.rhs.toList.filter (fun letter => decide (letter ∈ leftFront.toList)) = rightFront.toList := by
    rw [rightWhole, Word.toList_append, List.filter_append,
      filter_sameWordSupport leftFront rightFront same, rightDiscard, List.append_nil]
  exact ⟨valid_prefix_restrict leftFront leftBackWord rightFront rightBackWord splitValid same leftDisjoint rightDisjoint,
    actualAffineValid_restrict_filter identity affineValid
      (fun letter => decide (letter ∈ leftFront.toList)) leftFront rightFront leftFilter rightFilter⟩

theorem exactCut_suffix_factors (identity : Identity Nat)
    (leftFront rightFront : List Nat) (leftBack rightBack : Word Nat) (separator : Nat)
    (leftCut : Examples.UniqueSeparatorFourExactCut identity.lhs.toList leftFront separator leftBack.toList)
    (rightCut : Examples.UniqueSeparatorFourExactCut identity.rhs.toList rightFront separator rightBack.toList)
    (same : SameWordSupport leftBack rightBack)
    (separatorValid : identity.SatisfiedBy semigroup)
    (affineValid : identity.SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite) :
    (⟨leftBack,rightBack⟩ : Identity Nat).SatisfiedBy semigroup ∧
      (⟨leftBack,rightBack⟩ : Identity Nat).SatisfiedBy
        Generated.Catalogue.S4_96.table.semigroup.opposite := by
  let leftFrontWord := Examples.connectedComponentWordOfNonempty (leftFront ++ [separator]) (by simp)
  let rightFrontWord := Examples.connectedComponentWordOfNonempty (rightFront ++ [separator]) (by simp)
  have leftFrontList : leftFrontWord.toList = leftFront ++ [separator] :=
    Examples.connectedComponentWordOfNonempty_toList _ _
  have rightFrontList : rightFrontWord.toList = rightFront ++ [separator] :=
    Examples.connectedComponentWordOfNonempty_toList _ _
  have leftWhole : identity.lhs = leftFrontWord ++ leftBack := by
    apply Word.toList_injective
    rw [Word.toList_append, leftFrontList]
    simpa only [List.append_assoc, List.singleton_append] using leftCut.1
  have rightWhole : identity.rhs = rightFrontWord ++ rightBack := by
    apply Word.toList_injective
    rw [Word.toList_append, rightFrontList]
    simpa only [List.append_assoc, List.singleton_append] using rightCut.1
  have leftDisjoint : ∀ letter, letter ∈ leftFrontWord.toList → letter ∉ leftBack.toList := by
    rw [leftFrontList]
    exact exactCut_front_disjoint leftCut
  have rightDisjoint : ∀ letter, letter ∈ rightFrontWord.toList → letter ∉ rightBack.toList := by
    rw [rightFrontList]
    exact exactCut_front_disjoint rightCut
  have splitValid : (⟨leftFrontWord ++ leftBack, rightFrontWord ++ rightBack⟩ : Identity Nat).SatisfiedBy semigroup := by
    intro valuation
    change semigroup.eval valuation (leftFrontWord ++ leftBack) =
      semigroup.eval valuation (rightFrontWord ++ rightBack)
    rw [← leftWhole, ← rightWhole]
    exact separatorValid valuation
  have leftDiscard : leftFrontWord.toList.filter (fun letter => decide (letter ∈ leftBack.toList)) = [] :=
    filter_disjoint_support leftFrontWord.toList leftBack.toList leftDisjoint
  have rightDiscard : rightFrontWord.toList.filter (fun letter => decide (letter ∈ leftBack.toList)) = [] :=
    filter_disjoint_support rightFrontWord.toList leftBack.toList
      (fun letter member inBack => rightDisjoint letter member ((same letter).mp inBack))
  have leftFilter : identity.lhs.toList.filter (fun letter => decide (letter ∈ leftBack.toList)) = leftBack.toList := by
    rw [leftWhole, Word.toList_append, List.filter_append, leftDiscard, filter_to_own_support, List.nil_append]
  have rightFilter : identity.rhs.toList.filter (fun letter => decide (letter ∈ leftBack.toList)) = rightBack.toList := by
    rw [rightWhole, Word.toList_append, List.filter_append, rightDiscard,
      filter_sameWordSupport leftBack rightBack same, List.nil_append]
  exact ⟨valid_suffix_restrict leftFrontWord leftBack rightFrontWord rightBack splitValid same leftDisjoint rightDisjoint,
    actualAffineValid_restrict_filter identity affineValid
      (fun letter => decide (letter ∈ leftBack.toList)) leftBack rightBack leftFilter rightFilter⟩

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.exactCut_separator_absent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.exactCut_back_disjoint
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.exactCut_front_disjoint
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.filter_sameWordSupport
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.exactCut_prefix_factors
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.exactCut_suffix_factors

end SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator
