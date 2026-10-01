import SemigroupBasis.CoRoots.Order6SporadicSection26AlphaNormalization

/-! Tighten arbitrary positive alpha powers to one or two copies. A head
with a later occurrence retains only one copy. All reductions are explicit
raw-basis derivations; no bounded semantic test is a proof premise. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection26.F7
open SemigroupBasis

theorem headRun_absorb_seen (head extra : Nat) (after : List Nat)
    (seen : head ∈ after) : ListDerives (headRun head extra ++ after) (head :: after) := by
  induction extra with
  | zero => exact S5_107.ListDerives.refl (basis := basis) (head :: after)
  | succ n ih =>
      have later : head ∈ List.replicate n head ++ after := by simp [seen]
      have raw := (duplicateFirstOfSeen head (List.replicate n head ++ after) later).symm
      have first : ListDerives (headRun head (n + 1) ++ after) (headRun head n ++ after) := by
        simpa [headRun, List.replicate_succ] using raw
      exact first.trans ih

theorem headRun_positive_cap (head n : Nat) :
    ListDerives (headRun head (n + 1)) (headRun head 1) := by
  induction n with
  | zero => exact S5_107.ListDerives.refl (basis := basis) (headRun head 1)
  | succ n ih =>
      have raw := (listPower head).append (List.replicate n head)
      have first : ListDerives (headRun head (n + 1 + 1)) (headRun head (n + 1)) := by
        simpa [headRun, List.replicate_succ] using raw
      exact first.trans ih

theorem headRun_cap (head extra : Nat) :
    ListDerives (headRun head extra) (headRun head (min extra 1)) := by
  cases extra with
  | zero => exact S5_107.ListDerives.refl (basis := basis) (headRun head 0)
  | succ n =>
      have bound : 1 ≤ Nat.succ n := Nat.succ_le_succ (Nat.zero_le n)
      simpa only [Nat.min_eq_right bound] using headRun_positive_cap head n

def reducedExtra (head extra : Nat) (after : List Nat) : Nat :=
  if head ∈ after then 0 else min extra 1

theorem reducedExtra_le_one (head extra : Nat) (after : List Nat) :
    reducedExtra head extra after ≤ 1 := by
  unfold reducedExtra
  split
  · decide
  · exact Nat.min_le_right extra 1

theorem reducedExtra_one_missing (head extra : Nat) (after : List Nat)
    (one : reducedExtra head extra after = 1) : head ∉ after := by
  intro seen
  simp [reducedExtra, seen] at one

theorem headRun_reduce (head extra : Nat) (after : List Nat) :
    ListDerives (headRun head extra ++ after)
      (headRun head (reducedExtra head extra after) ++ after) := by
  by_cases seen : head ∈ after
  · simpa [reducedExtra, seen, headRun] using headRun_absorb_seen head extra after seen
  · simpa only [reducedExtra, if_neg seen] using (headRun_cap head extra).append after

namespace AlphaForm

def tighten (form : AlphaForm) (after : List Nat) : AlphaForm :=
  match form with
  | nil => nil
  | snoc init head extra tail =>
      let reduced := reducedExtra head extra (tail.toList ++ after)
      let suffix := (headRun head reduced ++ tail.toList) ++ after
      snoc (init.tighten suffix) head reduced tail

def TightAfter : AlphaForm → List Nat → Prop
  | nil, _ => True
  | snoc init head extra tail, after =>
      extra ≤ 1 ∧ (extra = 1 → head ∉ tail.toList ++ after) ∧
        init.TightAfter ((headRun head extra ++ tail.toList) ++ after)

theorem heads_tighten (form : AlphaForm) (after : List Nat) :
    (form.tighten after).heads = form.heads := by
  induction form generalizing after with
  | nil => rfl
  | snoc init head extra tail ih => simp [tighten, heads, ih]

theorem valid_tighten (form : AlphaForm) (after : List Nat) (valid : form.Valid) :
    (form.tighten after).Valid := by
  induction form generalizing after with
  | nil => trivial
  | snoc init head extra tail ih =>
      rcases valid with ⟨initValid, fresh, earlier⟩
      simp only [tighten]
      refine ⟨ih _ initValid, ?_, ?_⟩
      · simpa only [heads_tighten] using fresh
      · simpa only [heads_tighten] using earlier

theorem tightAfter_tighten (form : AlphaForm) (after : List Nat) :
    (form.tighten after).TightAfter after := by
  induction form generalizing after with
  | nil => trivial
  | snoc init head extra tail ih =>
      dsimp only [tighten, TightAfter]
      exact ⟨reducedExtra_le_one head extra (tail.toList ++ after),
        reducedExtra_one_missing head extra (tail.toList ++ after), ih _⟩

theorem derives_tighten (form : AlphaForm) (after : List Nat) :
    ListDerives (form.render ++ after) ((form.tighten after).render ++ after) := by
  induction form generalizing after with
  | nil => exact S5_107.ListDerives.refl (basis := basis) after
  | snoc init head extra tail ih =>
      let reduced := reducedExtra head extra (tail.toList ++ after)
      have first :
          ListDerives (init.render ++ ((headRun head extra ++ tail.toList) ++ after))
            (init.render ++ ((headRun head reduced ++ tail.toList) ++ after)) := by
        simpa only [List.append_assoc] using
          (headRun_reduce head extra (tail.toList ++ after)).prepend init.render
      have remaining := ih ((headRun head reduced ++ tail.toList) ++ after)
      simpa only [render, tighten, List.append_assoc] using first.trans remaining

end AlphaForm

def normalizeCanonical (letters : List Nat) : AlphaForm :=
  (normalizeAlpha letters).tighten []

theorem normalizeCanonical_valid (letters : List Nat) : (normalizeCanonical letters).Valid :=
  AlphaForm.valid_tighten (normalizeAlpha letters) [] (normalizeAlpha_valid letters)

theorem normalizeCanonical_tight (letters : List Nat) :
    (normalizeCanonical letters).TightAfter [] :=
  AlphaForm.tightAfter_tighten (normalizeAlpha letters) []

theorem derives_normalizeCanonical (letters : List Nat) :
    ListDerives letters (normalizeCanonical letters).render := by
  have reduction : ListDerives (normalizeAlpha letters).render (normalizeCanonical letters).render := by
    simpa only [normalizeCanonical, List.append_nil] using
      AlphaForm.derives_tighten (normalizeAlpha letters) []
  exact (derives_normalizeAlpha letters).trans reduction

theorem exists_canonical_alpha (word : Word Nat) :
    ∃ form : AlphaForm, form.Valid ∧ form.TightAfter [] ∧ form.render ≠ [] ∧
      ListDerives word.toList form.render := by
  refine ⟨normalizeCanonical word.toList, normalizeCanonical_valid word.toList,
    normalizeCanonical_tight word.toList, ?_, derives_normalizeCanonical word.toList⟩
  exact S5_107.ListDerives.target_ne_nil (derives_normalizeCanonical word.toList)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.headRun_absorb_seen
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.headRun_positive_cap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.headRun_cap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.reducedExtra_le_one
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.reducedExtra_one_missing
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.headRun_reduce
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.heads_tighten
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.valid_tighten
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.tightAfter_tighten
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.AlphaForm.derives_tighten
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.normalizeCanonical_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.normalizeCanonical_tight
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.derives_normalizeCanonical
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.exists_canonical_alpha
end SemigroupBasis.CoRoots.Order6SporadicSection26.F7
