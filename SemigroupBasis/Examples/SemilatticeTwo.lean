import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Multiplication for the two-element meet semilattice. -/
def semilatticeTwoMul (a b : Fin 2) : Fin 2 :=
  if a = 0 then 0 else b

/-- The two-element semilattice with stored table `[[1,1],[1,2]]`. -/
def semilatticeTwo : FiniteTable where
  order := 2
  mul := semilatticeTwoMul
  assoc := by decide

def semilatticeX : Word Nat := Word.singleton 0
def semilatticeXX : Word Nat := ⟨0, [0]⟩
def semilatticeXY : Word Nat := ⟨0, [1]⟩
def semilatticeYX : Word Nat := ⟨1, [0]⟩

def semilatticeIdempotenceLaw : Identity Nat :=
  ⟨semilatticeXX, semilatticeX⟩

def semilatticeCommutativityLaw : Identity Nat :=
  ⟨semilatticeXY, semilatticeYX⟩

def semilatticeBasis : List (Identity Nat) :=
  [semilatticeIdempotenceLaw, semilatticeCommutativityLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem semilatticeDerivesIdempotence (u : Word Nat) :
    Derives semilatticeBasis (u ++ u) u := by
  have hbase :
      Derives semilatticeBasis semilatticeXX semilatticeX :=
    Derives.fromBasis (e := semilatticeIdempotenceLaw) <| by
      exact List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [semilatticeBasis, semilatticeIdempotenceLaw, semilatticeXX,
    semilatticeX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton] using h

theorem semilatticeDerivesCommutativity (u v : Word Nat) :
    Derives semilatticeBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives semilatticeBasis semilatticeXY semilatticeYX :=
    Derives.fromBasis (e := semilatticeCommutativityLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [semilatticeBasis, semilatticeCommutativityLaw, semilatticeXY,
    semilatticeYX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton] using h

/-- A letter already in a word can be appended without changing its value
modulo commutativity and idempotence. -/
theorem semilatticeDerivesAppendMember (w : Word Nat) (x : Nat)
    (hx : x ∈ w.toList) :
    Derives semilatticeBasis w (w ++ Word.singleton x) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp only [Word.toList, List.mem_singleton] at hx
          subst x
          exact Derives.symm
            (semilatticeDerivesIdempotence (Word.singleton head))
      | cons next rest =>
          let suffix : Word Nat := ⟨next, rest⟩
          simp only [Word.toList, List.mem_cons] at hx
          rcases hx with hxHead | hxTail
          · subst x
            have duplicateHead :
                Derives semilatticeBasis
                  (Word.singleton head)
                  (Word.singleton head ++ Word.singleton head) :=
              Derives.symm
                (semilatticeDerivesIdempotence (Word.singleton head))
            have duplicateBeforeSuffix :=
              Derives.appendRight duplicateHead suffix
            have moveDuplicate :
                Derives semilatticeBasis
                  (Word.singleton head ++
                    (Word.singleton head ++ suffix))
                  (Word.singleton head ++
                    (suffix ++ Word.singleton head)) :=
              Derives.prepend (Word.singleton head)
                (semilatticeDerivesCommutativity
                  (Word.singleton head) suffix)
            exact Derives.trans
              (by
                simpa [suffix, Word.append_assoc] using duplicateBeforeSuffix)
              (by
                simpa [suffix, Word.append_assoc] using moveDuplicate)
          · have suffixMembership : x ∈ suffix.toList := by
              simpa [suffix, Word.toList] using hxTail
            have suffixStep :=
              semilatticeDerivesAppendMember suffix x suffixMembership
            have prefixed := Derives.prepend (Word.singleton head) suffixStep
            simpa [suffix, Word.append_assoc] using prefixed

/-- Support/content expansion: if every requested letter already occurs in
`w`, appending the entire list is derivable. -/
theorem semilatticeDerivesAppendList (w : Word Nat) (xs : List Nat)
    (hcontent : ∀ x, x ∈ xs → x ∈ w.toList) :
    Derives semilatticeBasis w ⟨w.head, w.tail ++ xs⟩ := by
  induction xs generalizing w with
  | nil =>
      simpa using Derives.refl w
  | cons x xs ih =>
      have hx : x ∈ w.toList :=
        hcontent x (List.Mem.head xs)
      have firstStep :=
        semilatticeDerivesAppendMember w x hx
      have remainingContent :
          ∀ y, y ∈ xs →
            y ∈ (w ++ Word.singleton x).toList := by
        intro y hy
        rw [Word.toList_append]
        exact List.mem_append_left _ <|
          hcontent y (List.Mem.tail x hy)
      have restStep :=
        ih (w ++ Word.singleton x) remainingContent
      exact Derives.trans firstStep <| by
        simpa [Word.append, Word.singleton, List.append_assoc] using restStep

/-- A word derives to the shared-content expansion `u ++ v` whenever every
letter of `v` occurs in `u`. -/
theorem semilatticeDerivesContentExpansion (u v : Word Nat)
    (hcontent : ∀ x, x ∈ v.toList → x ∈ u.toList) :
    Derives semilatticeBasis u (u ++ v) := by
  have h := semilatticeDerivesAppendList u v.toList hcontent
  simpa [Word.toList, Word.append] using h

private theorem semilatticeMul_eq_one_iff (a b : Fin 2) :
    semilatticeTwoMul a b = (1 : Fin 2) ↔
      a = (1 : Fin 2) ∧ b = (1 : Fin 2) := by
  decide +revert

private theorem semilatticeMul_idempotent (a : Fin 2) :
    semilatticeTwoMul a a = a := by
  decide +revert

private theorem semilatticeMul_commutative (a b : Fin 2) :
    semilatticeTwoMul a b = semilatticeTwoMul b a := by
  decide +revert

private theorem semilatticeFold_eq_one_iff
    (valuation : Nat → Fin 2) (xs : List Nat) (acc : Fin 2) :
    xs.foldl
        (fun current x => semilatticeTwoMul current (valuation x)) acc =
          (1 : Fin 2) ↔
      acc = (1 : Fin 2) ∧
        ∀ x, x ∈ xs → valuation x = (1 : Fin 2) := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil, List.not_mem_nil, false_implies,
        forall_const, and_true]
  | cons x xs ih =>
      rw [List.foldl_cons, ih, semilatticeMul_eq_one_iff]
      constructor
      · rintro ⟨⟨hacc, hx⟩, hxs⟩
        exact ⟨hacc, fun y hy => by
          simp only [List.mem_cons] at hy
          rcases hy with hy | hy
          · simpa [hy] using hx
          · exact hxs y hy⟩
      · rintro ⟨hacc, hall⟩
        exact ⟨⟨hacc, hall x (List.Mem.head xs)⟩,
          fun y hy => hall y (List.Mem.tail x hy)⟩

theorem semilatticeEval_eq_one_iff (valuation : Nat → Fin 2)
    (w : Word Nat) :
    semilatticeTwo.semigroup.eval valuation w = (1 : Fin 2) ↔
      ∀ x, x ∈ w.toList → valuation x = (1 : Fin 2) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x => semilatticeTwoMul current (valuation x))
            (valuation head) = (1 : Fin 2) ↔
          ∀ x, x ∈ head :: tail → valuation x = (1 : Fin 2)
      rw [semilatticeFold_eq_one_iff]
      constructor
      · rintro ⟨hhead, htail⟩ x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx
        · simpa [hx] using hhead
        · exact htail x hx
      · intro hall
        exact ⟨hall head (List.Mem.head tail),
          fun x hx => hall x (List.Mem.tail head hx)⟩

private def supportSeparator (z : Nat) : Nat → Fin 2 :=
  fun x => if x = z then 0 else 1

theorem semilatticeSeparator_eq_one_iff (z : Nat) (w : Word Nat) :
    semilatticeTwo.semigroup.eval (supportSeparator z) w = (1 : Fin 2) ↔
      z ∉ w.toList := by
  rw [semilatticeEval_eq_one_iff]
  constructor
  · intro hall hz
    have := hall z hz
    simp [supportSeparator] at this
  · intro hz x hx
    have hne : x ≠ z := by
      intro h
      apply hz
      simpa [h] using hx
    simp [supportSeparator, hne]

theorem semilatticeValid_support_eq (e : Identity Nat)
    (valid : e.SatisfiedBy semilatticeTwo.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (supportSeparator z)
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    have rhsOne :
        semilatticeTwo.semigroup.eval (supportSeparator z) e.rhs =
          (1 : Fin 2) :=
      (semilatticeSeparator_eq_one_iff z e.rhs).2 hr
    have lhsNotOne :
        semilatticeTwo.semigroup.eval (supportSeparator z) e.lhs ≠
          (1 : Fin 2) := by
      intro lhsOne
      exact (semilatticeSeparator_eq_one_iff z e.lhs).1 lhsOne hl
    exact lhsNotOne (evaluated.trans rhsOne)
  · intro hr
    apply Decidable.byContradiction
    intro hl
    have lhsOne :
        semilatticeTwo.semigroup.eval (supportSeparator z) e.lhs =
          (1 : Fin 2) :=
      (semilatticeSeparator_eq_one_iff z e.lhs).2 hl
    have rhsNotOne :
        semilatticeTwo.semigroup.eval (supportSeparator z) e.rhs ≠
          (1 : Fin 2) := by
      intro rhsOne
      exact (semilatticeSeparator_eq_one_iff z e.rhs).1 rhsOne hr
    exact rhsNotOne (evaluated.symm.trans lhsOne)

theorem semilatticeBasis_models :
    Models semilatticeTwo.semigroup semilatticeBasis := by
  intro e he
  simp only [semilatticeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change semilatticeTwoMul (valuation 0) (valuation 0) = valuation 0
    exact semilatticeMul_idempotent (valuation 0)
  · intro valuation
    change semilatticeTwoMul (valuation 0) (valuation 1) =
      semilatticeTwoMul (valuation 1) (valuation 0)
    exact semilatticeMul_commutative (valuation 0) (valuation 1)

theorem semilatticeBasis_complete :
    BasisFor semilatticeTwo.semigroup semilatticeBasis := by
  refine ⟨semilatticeBasis_models, ?_⟩
  intro e valid
  have supportEq := semilatticeValid_support_eq e valid
  have lhsExpansion :
      Derives semilatticeBasis e.lhs (e.lhs ++ e.rhs) :=
    semilatticeDerivesContentExpansion e.lhs e.rhs
      (fun x hx => (supportEq x).2 hx)
  have rhsExpansion :
      Derives semilatticeBasis e.rhs (e.rhs ++ e.lhs) :=
    semilatticeDerivesContentExpansion e.rhs e.lhs
      (fun x hx => (supportEq x).1 hx)
  exact Derives.trans lhsExpansion <|
    Derives.trans (semilatticeDerivesCommutativity e.lhs e.rhs)
      (Derives.symm rhsExpansion)

end SemigroupBasis.Examples
