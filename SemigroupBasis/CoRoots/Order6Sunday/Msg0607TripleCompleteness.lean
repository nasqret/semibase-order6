import SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleScan
import SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleInvariants

set_option maxRecDepth 100000

/-!
Completeness of Σ4 for S6_14887, S6_14888, S6_14895 and their opposites.

`normalForm` (Msg0607TripleScan) is a function of the semantic invariants
(Msg0607TripleInvariants); validity on a table pulls back along the embedded
copies of `L21` and `T2`, so two table-equal words have the same invariants,
the same normal form, and are Σ4-derivable from each other.
-/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleCompleteness

open SemigroupBasis
open Msg0607TripleTables
open Msg0607TripleRules
open Msg0607TripleSwap
open Msg0607TripleScan
open Msg0607TripleInvariants

/-! ## `ini` is the semantic first-occurrence order -/

theorem filter_filter_ne (w seen : List Nat) (x : Nat) :
    (w.filter fun c => decide (c ∉ seen)).filter (fun c => decide (c ≠ x)) =
      w.filter fun c => decide (c ∉ seen ++ [x]) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro c _
  by_cases hs : c ∈ seen <;> by_cases hx : c = x <;> simp [hs, hx]

theorem iniScan_fst_eq :
    ∀ (w seen junk : List Nat),
      (iniScan seen junk w).1 = seen ++ iniRec (w.filter fun c => decide (c ∉ seen))
  | [], seen, junk => by simp [iniScan, iniRec, iniFuel]
  | x :: w, seen, junk => by
      by_cases mem : x ∈ seen
      · rw [iniScan, if_pos mem, iniScan_fst_eq w seen (junk ++ [x])]
        rw [List.filter_cons_of_neg (by simp [mem])]
      · rw [iniScan, if_neg mem, iniScan_fst_eq w (seen ++ [x]) junk]
        rw [List.filter_cons_of_pos (by simp [mem]), iniRec_cons, filter_filter_ne]
        simp

theorem ini_eq_iniRec (w : List Nat) : ini w = iniRec w := by
  unfold ini
  rw [iniScan_fst_eq]
  have : (w.filter fun c => decide (c ∉ ([] : List Nat))) = w := List.filter_eq_self.mpr (by simp)
  rw [this]
  rfl

/-! ## The markers are the semantic last-occurrence order -/

theorem iniRec_append_singleton :
    ∀ (n : Nat) (L : List Nat) (x : Nat), L.length ≤ n →
      iniRec (L ++ [x]) = if x ∈ L then iniRec L else iniRec L ++ [x] := by
  intro n
  induction n with
  | zero =>
      intro L x length
      have empty : L = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp length)
      subst empty
      simp [iniRec, iniFuel]
  | succ n ih =>
      intro L x length
      cases L with
      | nil => simp [iniRec, iniFuel]
      | cons a L =>
          rw [List.cons_append, iniRec_cons, iniRec_cons]
          by_cases hx : x = a
          · have memCons : x ∈ a :: L := by simp [hx]
            have filterEq : (L ++ [x]).filter (fun c => decide (c ≠ a)) =
                L.filter (fun c => decide (c ≠ a)) := by
              rw [List.filter_append]
              simp [hx]
            rw [if_pos memCons, filterEq]
          · have filterEq : (L ++ [x]).filter (fun c => decide (c ≠ a)) =
                L.filter (fun c => decide (c ≠ a)) ++ [x] := by
              rw [List.filter_append]
              simp [hx]
            rw [filterEq]
            have shorter : (L.filter fun c => decide (c ≠ a)).length ≤ n := by
              have := List.length_filter_le (fun c => decide (c ≠ a)) L
              simp only [List.length_cons] at length
              omega
            rw [ih _ x shorter]
            by_cases memL : x ∈ L
            · have memF : x ∈ L.filter fun c => decide (c ≠ a) :=
                List.mem_filter.mpr ⟨memL, by simp [hx]⟩
              have memCons : x ∈ a :: L := List.mem_cons_of_mem a memL
              rw [if_pos memF, if_pos memCons]
            · have memF : x ∉ L.filter fun c => decide (c ≠ a) :=
                fun h => memL (List.mem_filter.mp h).1
              have memCons : x ∉ a :: L := by
                intro h
                rcases List.mem_cons.mp h with h | h
                · exact hx h
                · exact memL h
              rw [if_neg memF, if_neg memCons]
              rfl

theorem markers_lastScan_eq_fin :
    ∀ (w current : List Nat), markers (lastScan current w) = fin w
  | [], current => by simp [lastScan, markers, fin, iniRec, iniFuel]
  | x :: w, current => by
      have snoc := iniRec_append_singleton w.reverse.length w.reverse x (Nat.le_refl _)
      by_cases mem : x ∈ w
      · rw [lastScan, if_pos mem, markers_lastScan_eq_fin w (current ++ [x])]
        unfold fin
        rw [List.reverse_cons, snoc, if_pos (List.mem_reverse.mpr mem)]
      · rw [lastScan, if_neg mem, markers_cons, markers_lastScan_eq_fin w []]
        unfold fin
        rw [List.reverse_cons, snoc, if_neg (fun h => mem (List.mem_reverse.mp h))]
        simp

/-! ## Structural facts about the scanner factors -/

theorem mem_renderFactors_wellformed :
    ∀ (F : List (List Nat × Nat)), Wellformed F → ∀ c ∈ renderFactors F, c ∈ markers F
  | [], _, c, mem => by simp [renderFactors] at mem
  | (block, marker) :: rest, wellformed, c, mem => by
      obtain ⟨blockLater, restWellformed⟩ := wellformed
      rw [renderFactors, List.mem_append, List.mem_cons] at mem
      rw [markers_cons, List.mem_cons]
      rcases mem with inBlock | rfl | inRest
      · rcases blockLater c inBlock with rfl | later
        · exact Or.inl rfl
        · exact Or.inr later
      · exact Or.inl rfl
      · exact Or.inr (mem_renderFactors_wellformed rest restWellformed c inRest)

theorem marker_not_mem_renderFactors (block : List Nat) (marker : Nat) (rest : List (List Nat × Nat))
    (wellformed : Wellformed ((block, marker) :: rest))
    (nodup : (markers ((block, marker) :: rest)).Nodup) : marker ∉ renderFactors rest := by
  intro mem
  have inMarkers := mem_renderFactors_wellformed rest wellformed.2 marker mem
  rw [markers_cons] at nodup
  exact (List.nodup_cons.mp nodup).1 inMarkers

theorem exists_prefix_suffixAfterLast (z : Nat) :
    ∀ w : List Nat, z ∈ w → ∃ P, w = P ++ suffixAfterLast z w
  | [], mem => by simp at mem
  | c :: w, mem => by
      by_cases inRest : z ∈ w
      · obtain ⟨P, hP⟩ := exists_prefix_suffixAfterLast z w inRest
        refine ⟨c :: P, ?_⟩
        rw [suffixAfterLast, if_pos inRest, List.cons_append, ← hP]
      · have hc : c = z := by
          simp only [List.mem_cons] at mem
          rcases mem with h | h
          · exact h.symm
          · exact absurd h inRest
        subst hc
        refine ⟨[c], ?_⟩
        rw [suffixAfterLast, if_neg inRest, if_pos rfl]
        rfl

theorem mem_of_mem_suffixAfterLast (z c : Nat) (w : List Nat) (mem : c ∈ suffixAfterLast z w) : c ∈ w := by
  by_cases hz : z ∈ w
  · obtain ⟨P, hP⟩ := exists_prefix_suffixAfterLast z w hz
    rw [hP]
    exact List.mem_append_right _ mem
  · rw [suffixAfterLast_of_not_mem z w hz] at mem
    simp at mem

/-- The suffix after the next marker. -/
theorem suffixAfterLast_step (w : List Nat) (z : Nat) (S : List Nat) (z' : Nat) (R : List Nat)
    (memZ : z ∈ w) (suffix : suffixAfterLast z w = S ++ z' :: R) (absent : z' ∉ R) :
    suffixAfterLast z' w = R ∧ z' ∈ w := by
  obtain ⟨P, hP⟩ := exists_prefix_suffixAfterLast z w memZ
  rw [suffix] at hP
  constructor
  · rw [hP, ← List.append_assoc]
    exact suffixAfterLast_append_cons z' (P ++ S) R absent
  · rw [hP]
    simp

theorem count_split (c : Nat) (S : List Nat) (z : Nat) (R : List Nat) :
    (S ++ z :: R).count c = S.count c + (if z = c then 1 else 0) + R.count c := by
  rw [List.count_append, List.count_cons]
  by_cases h : z = c
  · subst h
    simp
    omega
  · have : (z == c) = false := by simpa using h
    simp [this, h]

/-! ## Equal invariants give equal normal forms -/

theorem renderCanonFactors_eq {u v : List Nat} (same : SameInvariants u v) :
    ∀ (Fu Fv : List (List Nat × Nat)) (z : Nat),
      markers Fu = markers Fv → Wellformed Fu → Wellformed Fv →
      (markers Fu).Nodup → (markers Fv).Nodup → z ∈ u →
      suffixAfterLast z u = renderFactors Fu → suffixAfterLast z v = renderFactors Fv →
      renderCanonFactors Fu = renderCanonFactors Fv
  | [], Fv, z, markersEq, _, _, _, _, _, _, _ => by
      have : Fv = [] := by
        cases Fv with
        | nil => rfl
        | cons f rest => simp [markers] at markersEq
      subst this
      rfl
  | (S, z') :: Fu', Fv, z, markersEq, wfU, wfV, nodupU, nodupV, memZ, sufU, sufV => by
      cases Fv with
      | nil => simp [markers] at markersEq
      | cons g Fv' =>
          obtain ⟨T, z''⟩ := g
          rw [markers_cons, markers_cons] at markersEq
          have headEq : z' = z'' := (List.cons.inj markersEq).1
          subst headEq
          have tailEq : markers Fu' = markers Fv' := (List.cons.inj markersEq).2
          have absentU := marker_not_mem_renderFactors S z' Fu' wfU nodupU
          have absentV := marker_not_mem_renderFactors T z' Fv' wfV nodupV
          rw [renderFactors] at sufU sufV
          obtain ⟨sufU', memZ'⟩ := suffixAfterLast_step u z S z' _ memZ sufU absentU
          have memZv : z ∈ v := (same.support z).mp memZ
          obtain ⟨sufV', _⟩ := suffixAfterLast_step v z T z' _ memZv sufV absentV
          have canonEq : canon S = canon T := by
            apply canon_eq_of_parity
            intro c
            have countU := congrArg (fun l => l.count c) sufU
            have countV := congrArg (fun l => l.count c) sufV
            simp only at countU countV
            rw [count_split] at countU countV
            have parityZ := same.suffix z c memZ
            have parityZ' := same.suffix z' c memZ'
            rw [sufU'] at parityZ'
            rw [sufV'] at parityZ'
            omega
          rw [renderCanonFactors, renderCanonFactors, canonEq]
          congr 2
          exact renderCanonFactors_eq same Fu' Fv' z' tailEq wfU.2 wfV.2
            (List.nodup_cons.mp (by rwa [markers_cons] at nodupU)).2
            (List.nodup_cons.mp (by rwa [markers_cons] at nodupV)).2
            memZ' sufU' sufV'

theorem normalForm_eq_of_sameInvariants {u v : List Nat} (same : SameInvariants u v) :
    normalForm u = normalForm v := by
  have finEq : markers (lastScan [] u) = markers (lastScan [] v) := by
    rw [markers_lastScan_eq_fin, markers_lastScan_eq_fin]
    exact same.fin
  have iniEq : ini u = ini v := by
    rw [ini_eq_iniRec, ini_eq_iniRec]
    exact same.ini
  cases shapeU : lastScan [] u with
  | nil =>
      cases shapeV : lastScan [] v with
      | nil =>
          have uEmpty : u = [] := by
            cases u with
            | nil => rfl
            | cons h t => exact absurd shapeU (lastScan_ne_nil (h :: t) [] (by simp))
          have vEmpty : v = [] := by
            cases v with
            | nil => rfl
            | cons h t => exact absurd shapeV (lastScan_ne_nil (h :: t) [] (by simp))
          subst uEmpty
          subst vEmpty
          rfl
      | cons g Fv =>
          rw [shapeU, shapeV] at finEq
          simp [markers] at finEq
  | cons f Fu =>
      cases shapeV : lastScan [] v with
      | nil =>
          rw [shapeU, shapeV] at finEq
          simp [markers] at finEq
      | cons g Fv =>
          obtain ⟨S, z⟩ := f
          obtain ⟨T, z'⟩ := g
          rw [shapeU, shapeV, markers_cons, markers_cons] at finEq
          have headEq : z = z' := (List.cons.inj finEq).1
          subst headEq
          have tailEq : markers Fu = markers Fv := (List.cons.inj finEq).2
          -- nonempty words
          have uNonempty : u ≠ [] := by
            intro h
            subst h
            simp [lastScan] at shapeU
          have vNonempty : v ≠ [] := by
            intro h
            subst h
            simp [lastScan] at shapeV
          have renderU := renderFactors_lastScan u [] uNonempty
          have renderV := renderFactors_lastScan v [] vNonempty
          rw [shapeU, renderFactors, List.nil_append] at renderU
          rw [shapeV, renderFactors, List.nil_append] at renderV
          have wfU := lastScan_wellformed u [] (by simp)
          have wfV := lastScan_wellformed v [] (by simp)
          rw [shapeU] at wfU
          rw [shapeV] at wfV
          have nodupU := markers_lastScan_nodup u []
          have nodupV := markers_lastScan_nodup v []
          rw [shapeU] at nodupU
          rw [shapeV] at nodupV
          have absentU := marker_not_mem_renderFactors S z Fu wfU nodupU
          have absentV := marker_not_mem_renderFactors T z Fv wfV nodupV
          have sufU : suffixAfterLast z u = renderFactors Fu := by
            conv => lhs; rw [← renderU]
            exact suffixAfterLast_append_cons z S _ absentU
          have sufV : suffixAfterLast z v = renderFactors Fv := by
            conv => lhs; rw [← renderV]
            exact suffixAfterLast_append_cons z T _ absentV
          have memZU : z ∈ u := by rw [← renderU]; simp
          -- middle parities
          have middleEq : canon (rest u ++ u ++ S) = canon (rest v ++ v ++ T) := by
            apply canon_eq_of_parity
            intro c
            rw [List.count_append, List.count_append, List.count_append, List.count_append]
            have countU := congrArg (fun l => l.count c) renderU
            have countV := congrArg (fun l => l.count c) renderV
            simp only at countU countV
            rw [count_split, ← sufU] at countU
            rw [count_split, ← sufV] at countV
            have parity := same.parity c
            have suffixParity := same.suffix z c memZU
            by_cases memU : c ∈ u
            · have memV : c ∈ v := (same.support c).mp memU
              have restU := count_rest c u memU
              have restV := count_rest c v memV
              omega
            · have memV : c ∉ v := fun h => memU ((same.support c).mpr h)
              have restU := count_rest_of_not_mem c u memU
              have restV := count_rest_of_not_mem c v memV
              have zeroU : u.count c = 0 := List.count_eq_zero.mpr memU
              have zeroV : v.count c = 0 := List.count_eq_zero.mpr memV
              have zeroS : S.count c = 0 := by
                apply List.count_eq_zero.mpr
                intro h
                apply memU
                rw [← renderU]
                exact List.mem_append_left _ h
              have zeroT : T.count c = 0 := by
                apply List.count_eq_zero.mpr
                intro h
                apply memV
                rw [← renderV]
                exact List.mem_append_left _ h
              omega
          have tailsEq := renderCanonFactors_eq same Fu Fv z tailEq wfU.2 wfV.2
            (List.nodup_cons.mp (by rwa [markers_cons] at nodupU)).2
            (List.nodup_cons.mp (by rwa [markers_cons] at nodupV)).2
            memZU sufU sufV
          simp only [normalForm, shapeU, shapeV]
          rw [iniEq, middleEq, tailsEq]

/-! ## Word level -/

theorem normalForm_ne_nil (word : Word Nat) : normalForm word.toList ≠ [] := by
  cases word with
  | mk head tail =>
      apply S5_107.ListDerives.target_ne_nil
      simpa [Word.toList] using listDerivesNormalForm (head :: tail)

private def wordOfListOr (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

def normalWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (normalForm word.toList)

theorem toList_normalWord (word : Word Nat) :
    (normalWord word).toList = normalForm word.toList := by
  unfold normalWord
  cases shape : normalForm word.toList with
  | nil => exact False.elim (normalForm_ne_nil word shape)
  | cons head tail => rfl

theorem derivesNormalWord (word : Word Nat) : Derives basis word (normalWord word) := by
  cases word with
  | mk head tail =>
      have listDerivation :
          ListDerives (head :: tail) (normalForm (Word.mk head tail).toList) := by
        simpa [Word.toList] using listDerivesNormalForm (head :: tail)
      obtain ⟨targetHead, targetTail, targetListEq, wordDerivation⟩ :=
        S5_107.ListDerives.from_cons listDerivation
      have targetWordEq :
          S5_107.listWordOfCons targetHead targetTail = normalWord (Word.mk head tail) := by
        apply Word.toList_injective
        rw [toList_normalWord]
        simpa [S5_107.listWordOfCons] using targetListEq.symm
      rw [targetWordEq] at wordDerivation
      simpa [S5_107.listWordOfCons] using wordDerivation

theorem derivesOfSameInvariants (u v : Word Nat) (same : SameInvariants u.toList v.toList) :
    Derives basis u v := by
  have normalEq : normalWord u = normalWord v := by
    apply Word.toList_injective
    rw [toList_normalWord, toList_normalWord]
    exact normalForm_eq_of_sameInvariants same
  have left := derivesNormalWord u
  rw [normalEq] at left
  exact left.trans (derivesNormalWord v).symm

/-- Completeness for any table containing `L21` and `T2`. -/
theorem complete {carrier : Type} {semigroup : Semigroup carrier}
    (leftZero : Embedding L21.table.semigroup semigroup)
    (transformation : Embedding T2.table.semigroup semigroup)
    (identity : Identity Nat) (valid : identity.SatisfiedBy semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfSameInvariants _ _
    (sameInvariants_of_valid identity (leftZero.pullback_identity identity valid)
      (transformation.pullback_identity identity valid))

/-! ## Endpoints -/

theorem S6_14887_basisFor : BasisFor S6_14887.table.semigroup basis :=
  ⟨S6_14887.tableModels, complete S6_14887.leftZeroEmbedding S6_14887.transformationEmbedding⟩

theorem S6_14887_oppositeBasisFor :
    BasisFor S6_14887.table.semigroup.opposite (reversedBasis basis) :=
  S6_14887_basisFor.oppositeReversed

theorem S6_14888_basisFor : BasisFor S6_14888.table.semigroup basis :=
  ⟨S6_14888.tableModels, complete S6_14888.leftZeroEmbedding S6_14888.transformationEmbedding⟩

theorem S6_14888_oppositeBasisFor :
    BasisFor S6_14888.table.semigroup.opposite (reversedBasis basis) :=
  S6_14888_basisFor.oppositeReversed

theorem S6_14895_basisFor : BasisFor S6_14895.table.semigroup basis :=
  ⟨S6_14895.tableModels, complete S6_14895.leftZeroEmbedding S6_14895.transformationEmbedding⟩

theorem S6_14895_oppositeBasisFor :
    BasisFor S6_14895.table.semigroup.opposite (reversedBasis basis) :=
  S6_14895_basisFor.oppositeReversed

end SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleCompleteness

#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleCompleteness.derivesNormalWord
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleCompleteness.derivesOfSameInvariants
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleCompleteness.S6_14887_basisFor
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleCompleteness.S6_14887_oppositeBasisFor
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleCompleteness.S6_14888_basisFor
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleCompleteness.S6_14888_oppositeBasisFor
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleCompleteness.S6_14895_basisFor
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleCompleteness.S6_14895_oppositeBasisFor
