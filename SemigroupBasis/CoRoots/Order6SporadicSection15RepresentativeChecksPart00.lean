import SemigroupBasis.CoRoots.Order6SporadicSection15

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

namespace RepresentativeChecksInternal

/-- Exhaustive associativity check with only three length-six traversals. -/
def checkAssociative6 (operation : Fin 6 → Fin 6 → Fin 6) : Bool :=
  (List.finRange 6).all fun a =>
    (List.finRange 6).all fun b =>
      (List.finRange 6).all fun c =>
        decide (operation (operation a b) c = operation a (operation b c))

theorem associative_of_checkAssociative6
    (operation : Fin 6 → Fin 6 → Fin 6)
    (checked : checkAssociative6 operation = true) :
    ∀ a b c, operation (operation a b) c = operation a (operation b c) := by
  intro a b c
  have checkedA := (List.all_eq_true.mp checked) a (List.mem_finRange a)
  have checkedB := (List.all_eq_true.mp checkedA) b (List.mem_finRange b)
  have checkedC := (List.all_eq_true.mp checkedB) c (List.mem_finRange c)
  exact of_decide_eq_true checkedC

theorem foldl_eval_congr
    (semigroup : Semigroup S)
    (leftValuation rightValuation : α → S) :
    ∀ (letters : List α) (initial : S),
      (∀ letter, letter ∈ letters →
        leftValuation letter = rightValuation letter) →
      letters.foldl
          (fun value letter => semigroup.mul value (leftValuation letter))
          initial =
        letters.foldl
          (fun value letter => semigroup.mul value (rightValuation letter))
          initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply foldl_eval_congr semigroup
      intro tested member
      exact agree tested (List.Mem.tail letter member)

theorem eval_congr_on_support
    (semigroup : Semigroup S)
    (leftValuation rightValuation : α → S)
    (word : Word α)
    (agree :
      ∀ letter, letter ∈ word.toList →
        leftValuation letter = rightValuation letter) :
    semigroup.eval leftValuation word =
      semigroup.eval rightValuation word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [agree head (by simp [Word.toList])]
      apply foldl_eval_congr semigroup
      intro letter member
      exact agree letter (List.Mem.tail head member)

/-- A seven-coordinate valuation assembled without function updates or a list
of all `T.order ^ 7` assignments. -/
def valuation7 {S : Type u}
    (a0 a1 a2 a3 a4 a5 a6 : S) : Fin 7 → S :=
  Fin.cases a0 <| Fin.cases a1 <| Fin.cases a2 <| Fin.cases a3 <|
    Fin.cases a4 <| Fin.cases a5 <| Fin.cases a6 Fin.elim0

theorem valuation7_eta {S : Type u} (valuation : Fin 7 → S) :
    valuation7 (valuation 0) (valuation 1) (valuation 2)
      (valuation 3) (valuation 4) (valuation 5) (valuation 6) = valuation := by
  funext i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => Fin.elim0 i) i

def identityUses7 (identity : Identity (Fin 7))
    (letter : Fin 7) : Bool :=
  decide
    (letter ∈ identity.lhs.toList ∨
      letter ∈ identity.rhs.toList)

/-- Enumerate one coordinate only when the identity reads it. -/
def checkUsedValue (values : List S) (used : Bool)
    (default : S) (check : S → Bool) : Bool :=
  if used then values.all check else check default

theorem checkUsedValue_sound {values : List S} {used : Bool}
    {default target : S} {check : S → Bool}
    (checked : checkUsedValue values used default check = true)
    (targetMember : target ∈ values) :
    check (if used then target else default) = true := by
  cases used with
  | false => simpa [checkUsedValue] using checked
  | true =>
      have every : values.all check = true := by
        simpa [checkUsedValue] using checked
      simpa using (List.all_eq_true.mp every) target targetMember

/-- Support-bounded checker with seven fixed scalar slots. Every traversal has
length `T.order`, absent coordinates are skipped, and no nested valuation
closures are retained during reduction. -/
def checkIdentityOnSupport (T : FiniteTable)
    (default : Fin T.order) (identity : Identity (Fin 7)) : Bool :=
  checkUsedValue (List.finRange T.order) (identityUses7 identity 0) default fun a0 =>
    checkUsedValue (List.finRange T.order) (identityUses7 identity 1) default fun a1 =>
      checkUsedValue (List.finRange T.order) (identityUses7 identity 2) default fun a2 =>
        checkUsedValue (List.finRange T.order) (identityUses7 identity 3) default fun a3 =>
          checkUsedValue (List.finRange T.order) (identityUses7 identity 4) default fun a4 =>
            checkUsedValue (List.finRange T.order) (identityUses7 identity 5) default fun a5 =>
              checkUsedValue (List.finRange T.order) (identityUses7 identity 6) default fun a6 =>
                decide
                  (T.semigroup.eval (valuation7 a0 a1 a2 a3 a4 a5 a6)
                      identity.lhs =
                    T.semigroup.eval (valuation7 a0 a1 a2 a3 a4 a5 a6)
                      identity.rhs)

theorem checkIdentityOnSupport_sound (T : FiniteTable)
    (default : Fin T.order) (identity : Identity (Fin 7))
    (checked : checkIdentityOnSupport T default identity = true) :
    identity.SatisfiedBy T.semigroup := by
  intro target
  unfold checkIdentityOnSupport at checked
  have checked0 := checkUsedValue_sound checked
    (List.mem_finRange (target 0))
  have checked1 := checkUsedValue_sound checked0
    (List.mem_finRange (target 1))
  have checked2 := checkUsedValue_sound checked1
    (List.mem_finRange (target 2))
  have checked3 := checkUsedValue_sound checked2
    (List.mem_finRange (target 3))
  have checked4 := checkUsedValue_sound checked3
    (List.mem_finRange (target 4))
  have checked5 := checkUsedValue_sound checked4
    (List.mem_finRange (target 5))
  have checked6 := checkUsedValue_sound checked5
    (List.mem_finRange (target 6))
  have concrete := of_decide_eq_true checked6
  let selected : Fin 7 → Fin T.order := fun letter =>
    if identityUses7 identity letter then target letter else default
  change
    T.semigroup.eval
        (valuation7 (selected 0) (selected 1) (selected 2) (selected 3)
          (selected 4) (selected 5) (selected 6)) identity.lhs =
      T.semigroup.eval
        (valuation7 (selected 0) (selected 1) (selected 2) (selected 3)
          (selected 4) (selected 5) (selected 6)) identity.rhs at concrete
  have selectedConcrete :
      T.semigroup.eval selected identity.lhs =
        T.semigroup.eval selected identity.rhs := by
    simpa only [valuation7_eta] using concrete
  calc
    T.semigroup.eval target identity.lhs =
        T.semigroup.eval selected identity.lhs := by
      apply eval_congr_on_support
      intro letter member
      simp [selected, identityUses7, member]
    _ = T.semigroup.eval selected identity.rhs := selectedConcrete
    _ = T.semigroup.eval target identity.rhs := by
      apply eval_congr_on_support
      intro letter member
      simp [selected, identityUses7, member]

theorem checkIdentity_complete (T : FiniteTable)
    (identity : Identity (Fin variables))
    (valid : identity.SatisfiedBy T.semigroup) :
    T.checkIdentity identity = true := by
  unfold FiniteTable.checkIdentity
  apply List.all_eq_true.mpr
  intro valuation _
  exact decide_eq_true (valid valuation)

theorem all_of_take_drop (predicate : α → Bool)
    (items : List α) (count : Nat)
    (front : (items.take count).all predicate = true)
    (back : (items.drop count).all predicate = true) :
    items.all predicate = true := by
  rw [← List.take_append_drop count items, List.all_append]
  simp [front, back]

theorem models_of_bounded_checks (T : FiniteTable)
    (default : Fin T.order)
    (checked :
      finiteBasis.all (checkIdentityOnSupport T default) = true) :
    Models T.semigroup basis :=
  models_of_finite_checks T <| by
    apply List.all_eq_true.mpr
    intro identity member
    exact checkIdentity_complete T identity <|
      checkIdentityOnSupport_sound T default identity <|
        (List.all_eq_true.mp checked) identity member

end RepresentativeChecksInternal
end SemigroupBasis.CoRoots.Order6SporadicSection15
