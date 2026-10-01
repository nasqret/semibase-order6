import SemigroupBasis.Examples.UniqueSeparatorFourInvariant

/-! The actual B0 separator factor has no global identity element. Its
right-local unit 3 and left-local unit 2 nevertheless isolate the two sides
of an exact separator, with the lost idempotent recovered from support. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator
open SemigroupBasis

abbrev semigroup := Examples.uniqueSeparatorFour.semigroup

def SameWordSupport (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

theorem foldl_eval_congr_support {S : Type} (G : Semigroup S)
    (first second : Nat → S) (letters : List Nat) :
    (∀ letter, letter ∈ letters → first letter = second letter) →
    ∀ initial,
      letters.foldl (fun value letter => G.mul value (first letter)) initial =
        letters.foldl (fun value letter => G.mul value (second letter)) initial := by
  induction letters with
  | nil => intro _ _; rfl
  | cons head tail ih =>
      intro agree initial
      simp only [List.foldl_cons]
      rw [agree head (List.Mem.head _)]
      exact ih (fun letter member => agree letter (List.mem_cons_of_mem head member)) _

theorem eval_congr_support {S : Type} (G : Semigroup S)
    (first second : Nat → S) (word : Word Nat)
    (agree : ∀ letter, letter ∈ word.toList → first letter = second letter) :
    G.eval first word = G.eval second word := by
  have headEqual : first word.head = second word.head := agree word.head (List.Mem.head _)
  change word.tail.foldl (fun value letter => G.mul value (first letter)) (first word.head) =
    word.tail.foldl (fun value letter => G.mul value (second letter)) (second word.head)
  rw [headEqual]
  exact foldl_eval_congr_support G first second word.tail
    (fun letter member => agree letter (List.mem_cons_of_mem word.head member)) _

theorem foldl_eq_isolated_point {S : Type} (G : Semigroup S) (point : S)
    (isolated : ∀ first second, G.mul first second = point ↔ first = point ∧ second = point)
    (valuation : Nat → S) (letters : List Nat) :
    ∀ initial,
      letters.foldl (fun value letter => G.mul value (valuation letter)) initial = point ↔
        initial = point ∧ ∀ letter, letter ∈ letters → valuation letter = point := by
  induction letters with
  | nil => intro initial; simp
  | cons head tail ih =>
      intro initial
      rw [List.foldl_cons, ih, isolated]
      constructor
      · rintro ⟨⟨initialEqual, headEqual⟩, tailEqual⟩
        refine ⟨initialEqual, ?_⟩
        intro letter member
        rcases List.mem_cons.mp member with rfl | inTail
        · exact headEqual
        · exact tailEqual letter inTail
      · rintro ⟨initialEqual, all⟩
        exact ⟨⟨initialEqual, all head (List.Mem.head _)⟩,
          fun letter member => all letter (List.mem_cons_of_mem head member)⟩

theorem eval_eq_isolated_point {S : Type} (G : Semigroup S) (point : S)
    (isolated : ∀ first second, G.mul first second = point ↔ first = point ∧ second = point)
    (valuation : Nat → S) (word : Word Nat) :
    G.eval valuation word = point ↔
      ∀ letter, letter ∈ word.toList → valuation letter = point := by
  change word.tail.foldl (fun value letter => G.mul value (valuation letter)) (valuation word.head) = point ↔ _
  rw [foldl_eq_isolated_point G point isolated]
  constructor
  · rintro ⟨headEqual, tailEqual⟩ letter member
    rcases List.mem_cons.mp member with rfl | inTail
    · exact headEqual
    · exact tailEqual letter inTail
  · intro all
    exact ⟨all word.head (List.Mem.head _),
      fun letter member => all letter (List.mem_cons_of_mem word.head member)⟩

theorem sameSupport_eval_point {S : Type} (G : Semigroup S) (point : S)
    (isolated : ∀ first second, G.mul first second = point ↔ first = point ∧ second = point)
    (valuation : Nat → S) (left right : Word Nat)
    (same : SameWordSupport left right) :
    G.eval valuation left = point ↔ G.eval valuation right = point := by
  rw [eval_eq_isolated_point G point isolated, eval_eq_isolated_point G point isolated]
  exact ⟨fun all letter member => all letter ((same letter).mpr member),
    fun all letter member => all letter ((same letter).mp member)⟩

theorem product_eq_two (first second : Fin 4) :
    semigroup.mul first second = (2 : Fin 4) ↔ first = 2 ∧ second = 2 := by
  decide +revert

theorem product_eq_three (first second : Fin 4) :
    semigroup.mul first second = (3 : Fin 4) ↔ first = 3 ∧ second = 3 := by
  decide +revert

theorem rightPad_injective (first second : Fin 4)
    (padded : semigroup.mul first (3 : Fin 4) = semigroup.mul second (3 : Fin 4))
    (sameTwo : first = 2 ↔ second = 2) : first = second := by
  decide +revert

theorem leftPad_injective (first second : Fin 4)
    (padded : semigroup.mul (2 : Fin 4) first = semigroup.mul (2 : Fin 4) second)
    (sameThree : first = 3 ↔ second = 3) : first = second := by
  decide +revert

def supportMask (keep : Word Nat) (outside : Fin 4) (valuation : Nat → Fin 4) : Nat → Fin 4 :=
  fun letter => if letter ∈ keep.toList then valuation letter else outside

theorem mask_eval_kept (keep target : Word Nat) (outside : Fin 4)
    (valuation : Nat → Fin 4) (same : SameWordSupport keep target) :
    semigroup.eval (supportMask keep outside valuation) target = semigroup.eval valuation target := by
  apply eval_congr_support
  intro letter member
  exact if_pos ((same letter).mpr member)

theorem mask_eval_disjoint (keep target : Word Nat) (outside : Fin 4)
    (valuation : Nat → Fin 4) (idempotent : outside = 2 ∨ outside = 3)
    (disjoint : ∀ letter, letter ∈ target.toList → letter ∉ keep.toList) :
    semigroup.eval (supportMask keep outside valuation) target = outside := by
  have isolated : ∀ first second, semigroup.mul first second = outside ↔
      first = outside ∧ second = outside := by
    rcases idempotent with rfl | rfl
    · exact product_eq_two
    · exact product_eq_three
  apply (eval_eq_isolated_point semigroup outside isolated _ target).mpr
  intro letter member
  exact if_neg (disjoint letter member)

theorem valid_prefix_restrict (leftFront leftBack rightFront rightBack : Word Nat)
    (valid : (⟨leftFront ++ leftBack, rightFront ++ rightBack⟩ : Identity Nat).SatisfiedBy semigroup)
    (same : SameWordSupport leftFront rightFront)
    (leftDisjoint : ∀ letter, letter ∈ leftBack.toList → letter ∉ leftFront.toList)
    (rightDisjoint : ∀ letter, letter ∈ rightBack.toList → letter ∉ rightFront.toList) :
    (⟨leftFront, rightFront⟩ : Identity Nat).SatisfiedBy semigroup := by
  intro valuation
  let masked := supportMask leftFront (3 : Fin 4) valuation
  have leftKept : semigroup.eval masked leftFront = semigroup.eval valuation leftFront :=
    mask_eval_kept leftFront leftFront 3 valuation (fun _ => Iff.rfl)
  have rightKept : semigroup.eval masked rightFront = semigroup.eval valuation rightFront :=
    mask_eval_kept leftFront rightFront 3 valuation same
  have leftDiscarded : semigroup.eval masked leftBack = (3 : Fin 4) :=
    mask_eval_disjoint leftFront leftBack 3 valuation (Or.inr rfl) leftDisjoint
  have rightDiscarded : semigroup.eval masked rightBack = (3 : Fin 4) :=
    mask_eval_disjoint leftFront rightBack 3 valuation (Or.inr rfl)
      (fun letter member inFront => rightDisjoint letter member ((same letter).mp inFront))
  have leftEvaluation : semigroup.eval masked (leftFront ++ leftBack) =
      semigroup.mul (semigroup.eval valuation leftFront) (3 : Fin 4) := by
    rw [Semigroup.eval_append, leftKept, leftDiscarded]
  have rightEvaluation : semigroup.eval masked (rightFront ++ rightBack) =
      semigroup.mul (semigroup.eval valuation rightFront) (3 : Fin 4) := by
    rw [Semigroup.eval_append, rightKept, rightDiscarded]
  have padded : semigroup.mul (semigroup.eval valuation leftFront) (3 : Fin 4) =
      semigroup.mul (semigroup.eval valuation rightFront) (3 : Fin 4) :=
    leftEvaluation.symm.trans ((valid masked).trans rightEvaluation)
  exact rightPad_injective _ _ padded
    (sameSupport_eval_point semigroup (2 : Fin 4) product_eq_two valuation leftFront rightFront same)

theorem valid_suffix_restrict (leftFront leftBack rightFront rightBack : Word Nat)
    (valid : (⟨leftFront ++ leftBack, rightFront ++ rightBack⟩ : Identity Nat).SatisfiedBy semigroup)
    (same : SameWordSupport leftBack rightBack)
    (leftDisjoint : ∀ letter, letter ∈ leftFront.toList → letter ∉ leftBack.toList)
    (rightDisjoint : ∀ letter, letter ∈ rightFront.toList → letter ∉ rightBack.toList) :
    (⟨leftBack, rightBack⟩ : Identity Nat).SatisfiedBy semigroup := by
  intro valuation
  let masked := supportMask leftBack (2 : Fin 4) valuation
  have leftKept : semigroup.eval masked leftBack = semigroup.eval valuation leftBack :=
    mask_eval_kept leftBack leftBack 2 valuation (fun _ => Iff.rfl)
  have rightKept : semigroup.eval masked rightBack = semigroup.eval valuation rightBack :=
    mask_eval_kept leftBack rightBack 2 valuation same
  have leftDiscarded : semigroup.eval masked leftFront = (2 : Fin 4) :=
    mask_eval_disjoint leftBack leftFront 2 valuation (Or.inl rfl) leftDisjoint
  have rightDiscarded : semigroup.eval masked rightFront = (2 : Fin 4) :=
    mask_eval_disjoint leftBack rightFront 2 valuation (Or.inl rfl)
      (fun letter member inBack => rightDisjoint letter member ((same letter).mp inBack))
  have leftEvaluation : semigroup.eval masked (leftFront ++ leftBack) =
      semigroup.mul (2 : Fin 4) (semigroup.eval valuation leftBack) := by
    rw [Semigroup.eval_append, leftDiscarded, leftKept]
  have rightEvaluation : semigroup.eval masked (rightFront ++ rightBack) =
      semigroup.mul (2 : Fin 4) (semigroup.eval valuation rightBack) := by
    rw [Semigroup.eval_append, rightDiscarded, rightKept]
  have padded : semigroup.mul (2 : Fin 4) (semigroup.eval valuation leftBack) =
      semigroup.mul (2 : Fin 4) (semigroup.eval valuation rightBack) :=
    leftEvaluation.symm.trans ((valid masked).trans rightEvaluation)
  exact leftPad_injective _ _ padded
    (sameSupport_eval_point semigroup (3 : Fin 4) product_eq_three valuation leftBack rightBack same)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.foldl_eval_congr_support
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.eval_congr_support
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.foldl_eq_isolated_point
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.eval_eq_isolated_point
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.sameSupport_eval_point
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.product_eq_two
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.product_eq_three
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.rightPad_injective
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.leftPad_injective
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.mask_eval_kept
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.mask_eval_disjoint
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.valid_prefix_restrict
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.valid_suffix_restrict

end SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator
