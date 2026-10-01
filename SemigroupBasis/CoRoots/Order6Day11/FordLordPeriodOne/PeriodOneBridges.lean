import SemigroupBasis.CoRoots.Order6Day11.FordLordPeriodOne.PeriodOnePresentation
import SemigroupBasis.CoRoots.Order6FordLord980Normal

/-! Eleven reversed predecessor laws through seventeen typed B11 edges. No search bound is a premise. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordPeriodOne

open SemigroupBasis

private def surround (front : Option (Word Nat)) (middle : Word Nat)
    (suffix : Option (Word Nat)) : Word Nat :=
  match front, suffix with
  | none, none => middle
  | some first, none => first ++ middle
  | none, some last => middle ++ last
  | some first, some last => (first ++ middle) ++ last

private theorem displayedForward (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat → Word Nat) (front suffix : Option (Word Nat)) :
    Derives basis (surround front (identity.lhs.bind substitution) suffix)
      (surround front (identity.rhs.bind substitution) suffix) := by
  have instantiated := (Derives.fromBasis member).subst substitution
  cases front with
  | none =>
      cases suffix with
      | none => exact instantiated
      | some last => exact Derives.appendRight instantiated last
  | some first =>
      cases suffix with
      | none => exact Derives.prepend first instantiated
      | some last => exact Derives.appendRight (Derives.prepend first instantiated) last

private theorem displayedBackward (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat → Word Nat) (front suffix : Option (Word Nat)) :
    Derives basis (surround front (identity.rhs.bind substitution) suffix)
      (surround front (identity.lhs.bind substitution) suffix) :=
  (displayedForward identity member substitution front suffix).symm

/-- Literal bridge xx=xxx. -/
theorem reversed980Law00 :
    Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) := by
    exact displayedForward law00 (show law00 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xyxx=xyx. -/
theorem reversed980Law01 :
    Derives basis (Word.mk 0 [1, 0, 0]) (Word.mk 0 [1, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [1, 0, 0]) (Word.mk 0 [1, 0]) := by
    exact displayedBackward law02 (show law02 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge yyxx=yxyx. -/
theorem reversed980Law02 :
    Derives basis (Word.mk 1 [1, 0, 0]) (Word.mk 1 [0, 1, 0]) := by
  have edge00 : Derives basis (Word.mk 1 [1, 0, 0]) (Word.mk 1 [0, 1, 0]) := by
    exact displayedForward law03 (show law03 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge yyxx=yxxy. -/
theorem reversed980Law03 :
    Derives basis (Word.mk 1 [1, 0, 0]) (Word.mk 1 [0, 0, 1]) := by
  have edge00 : Derives basis (Word.mk 1 [1, 0, 0]) (Word.mk 1 [0, 0, 1]) := by
    exact displayedForward law04 (show law04 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge zyyxx=zxyyx. -/
theorem reversed980Law04 :
    Derives basis (Word.mk 2 [1, 1, 0, 0]) (Word.mk 2 [0, 1, 1, 0]) := by
  have edge00 : Derives basis (Word.mk 2 [1, 1, 0, 0]) (Word.mk 2 [0, 1, 1, 0]) := by
    exact displayedForward law06 (show law06 ∈ basis by decide)
      (fun | 0 => (Word.mk 2 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge yzyxx=yzxyx. -/
theorem reversed980Law05 :
    Derives basis (Word.mk 1 [2, 1, 0, 0]) (Word.mk 1 [2, 0, 1, 0]) := by
  have edge00 : Derives basis (Word.mk 1 [2, 1, 0, 0]) (Word.mk 1 [2, 1, 0, 0, 0]) := by
    exact displayedForward law00 (show law00 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) (some (Word.mk 1 [2, 1])) none
  have edge01 : Derives basis (Word.mk 1 [2, 1, 0, 0, 0]) (Word.mk 1 [2, 0, 1, 0, 0]) := by
    exact displayedForward law08 (show law08 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 2 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  have edge02 : Derives basis (Word.mk 1 [2, 0, 1, 0, 0]) (Word.mk 1 [2, 0, 1, 0]) := by
    exact displayedBackward law02 (show law02 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) (some (Word.mk 1 [2])) none
  exact ((edge00).trans edge01).trans edge02

/-- Literal bridge yzyxx=yzxxy. -/
theorem reversed980Law06 :
    Derives basis (Word.mk 1 [2, 1, 0, 0]) (Word.mk 1 [2, 0, 0, 1]) := by
  have edge00 : Derives basis (Word.mk 1 [2, 1, 0, 0]) (Word.mk 1 [2, 1, 1, 0, 0]) := by
    exact displayedForward law02 (show law02 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 2 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none (some (Word.mk 0 [0]))
  have edge01 : Derives basis (Word.mk 1 [2, 1, 1, 0, 0]) (Word.mk 1 [2, 1, 0, 0, 1]) := by
    exact displayedForward law04 (show law04 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) (some (Word.mk 1 [2])) none
  have edge02 : Derives basis (Word.mk 1 [2, 1, 0, 0, 1]) (Word.mk 1 [2, 0, 0, 1]) := by
    exact displayedBackward law05 (show law05 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 2 []) | 2 => (Word.mk 0 [0]) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact ((edge00).trans edge01).trans edge02

/-- Literal bridge xyx=xxyx. -/
theorem reversed980Law07 :
    Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 1, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 1, 0]) := by
    exact displayedForward law01 (show law01 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xzxyx=xzyx. -/
theorem reversed980Law08 :
    Derives basis (Word.mk 0 [2, 0, 1, 0]) (Word.mk 0 [2, 1, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [2, 0, 1, 0]) (Word.mk 0 [2, 1, 0]) := by
    exact displayedBackward law05 (show law05 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 2 []) | 2 => (Word.mk 1 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge zzxyx=zxzyx. -/
theorem reversed980Law09 :
    Derives basis (Word.mk 2 [2, 0, 1, 0]) (Word.mk 2 [0, 2, 1, 0]) := by
  have edge00 : Derives basis (Word.mk 2 [2, 0, 1, 0]) (Word.mk 2 [2, 2, 0, 1, 0]) := by
    exact displayedForward law00 (show law00 ∈ basis by decide)
      (fun | 0 => (Word.mk 2 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none (some (Word.mk 0 [1, 0]))
  have edge01 : Derives basis (Word.mk 2 [2, 2, 0, 1, 0]) (Word.mk 2 [2, 0, 2, 1, 0]) := by
    exact displayedForward law08 (show law08 ∈ basis by decide)
      (fun | 0 => (Word.mk 2 []) | 1 => (Word.mk 2 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 1 []) | _ => Word.singleton 0) none none
  have edge02 : Derives basis (Word.mk 2 [2, 0, 2, 1, 0]) (Word.mk 2 [0, 2, 1, 0]) := by
    exact displayedBackward law01 (show law01 ∈ basis by decide)
      (fun | 0 => (Word.mk 2 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none (some (Word.mk 1 [0]))
  exact ((edge00).trans edge01).trans edge02

/-- Literal bridge yxzyx=yxzxy. -/
theorem reversed980Law10 :
    Derives basis (Word.mk 1 [0, 2, 1, 0]) (Word.mk 1 [0, 2, 0, 1]) := by
  have edge00 : Derives basis (Word.mk 1 [0, 2, 1, 0]) (Word.mk 1 [0, 2, 0, 1]) := by
    exact displayedForward law07 (show law07 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

theorem reversed980LawsDerive (identity : Identity Nat)
    (member : identity ∈ reversedBasis SemigroupBasis.CoRoots.Order6FordLord980.basis) :
    Derives basis identity.lhs identity.rhs := by
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  simp only [SemigroupBasis.CoRoots.Order6FordLord980.basis, List.mem_cons, List.not_mem_nil, or_false] at originalMember
  rcases originalMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reversed980Law00
  · exact reversed980Law01
  · exact reversed980Law02
  · exact reversed980Law03
  · exact reversed980Law04
  · exact reversed980Law05
  · exact reversed980Law06
  · exact reversed980Law07
  · exact reversed980Law08
  · exact reversed980Law09
  · exact reversed980Law10

theorem replayReversed980 {left right : Word Nat}
    (derived : Derives (reversedBasis SemigroupBasis.CoRoots.Order6FordLord980.basis) left right) :
    Derives basis left right := derived.transport reversed980LawsDerive

end SemigroupBasis.CoRoots.Order6Day11.FordLordPeriodOne
