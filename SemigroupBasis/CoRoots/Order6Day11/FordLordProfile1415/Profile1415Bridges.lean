import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415.Profile1415Presentation
import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.Profile15Completeness
import SemigroupBasis.CoRoots.Order6LeeZhangCondition14EndpointNormal

/-! Twenty-two predecessor laws, replayed through twenty-four typed B32 edges. No bound or factor premise is smuggled into a transport. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415

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

/-- Literal bridge xx=xxxx. -/
theorem aLaw00 :
    Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0]) := by
    exact displayedForward law00 (show law00 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xyx=xxxyx. -/
theorem aLaw01 :
    Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 0, 1, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 0, 1, 0]) := by
    exact displayedForward law01 (show law01 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xyx=xxyxx. -/
theorem aLaw02 :
    Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 1, 0, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 1, 0, 0]) := by
    exact displayedForward law02 (show law02 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xyx=xyxxx. -/
theorem aLaw03 :
    Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 0, 0, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 0, 0, 0]) := by
    exact displayedForward law04 (show law04 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xxyy=xyxy. -/
theorem aLaw04 :
    Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 0, 1]) := by
  have edge00 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 0, 1]) := by
    exact displayedForward law28 (show law28 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xxyy=xyyx. -/
theorem aLaw05 :
    Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]) := by
    exact displayedForward law29 (show law29 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xxyxz=xyxxz. -/
theorem aLaw06 :
    Derives basis (Word.mk 0 [0, 1, 0, 2]) (Word.mk 0 [1, 0, 0, 2]) := by
  have edge00 : Derives basis (Word.mk 0 [0, 1, 0, 2]) (Word.mk 0 [1, 0, 0, 2]) := by
    exact displayedForward law13 (show law13 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xxyyy=xyyyx. -/
theorem aLaw07 :
    Derives basis (Word.mk 0 [0, 1, 1, 1]) (Word.mk 0 [1, 1, 1, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [0, 1, 1, 1]) (Word.mk 0 [1, 1, 1, 0]) := by
    exact displayedForward law19 (show law19 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 1 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xxyzx=xyxzx. -/
theorem aLaw08 :
    Derives basis (Word.mk 0 [0, 1, 2, 0]) (Word.mk 0 [1, 0, 2, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [0, 1, 2, 0]) (Word.mk 0 [1, 0, 2, 0]) := by
    exact displayedForward law16 (show law16 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xxyzx=xyzxx. -/
theorem aLaw09 :
    Derives basis (Word.mk 0 [0, 1, 2, 0]) (Word.mk 0 [1, 2, 0, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [0, 1, 2, 0]) (Word.mk 0 [1, 2, 0, 0]) := by
    exact displayedForward law17 (show law17 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xxyzy=xyxzy. -/
theorem aLaw10 :
    Derives basis (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [1, 0, 2, 1]) := by
  have edge00 : Derives basis (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [1, 0, 2, 1]) := by
    exact displayedForward law18 (show law18 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xyxzz=xyzxz. -/
theorem aLaw11 :
    Derives basis (Word.mk 0 [1, 0, 2, 2]) (Word.mk 0 [1, 2, 0, 2]) := by
  have edge00 : Derives basis (Word.mk 0 [1, 0, 2, 2]) (Word.mk 0 [1, 2, 0, 2]) := by
    exact displayedForward law22 (show law22 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xyxzz=xyzzx. -/
theorem aLaw12 :
    Derives basis (Word.mk 0 [1, 0, 2, 2]) (Word.mk 0 [1, 2, 2, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [1, 0, 2, 2]) (Word.mk 0 [1, 2, 2, 0]) := by
    exact displayedForward law23 (show law23 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xyyzy=xyzyy. -/
theorem aLaw13 :
    Derives basis (Word.mk 0 [1, 1, 2, 1]) (Word.mk 0 [1, 2, 1, 1]) := by
  have edge00 : Derives basis (Word.mk 0 [1, 1, 2, 1]) (Word.mk 0 [1, 2, 1, 1]) := by
    exact displayedForward law24 (show law24 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xyzxy=xyzyx. -/
theorem aLaw14 :
    Derives basis (Word.mk 0 [1, 2, 0, 1]) (Word.mk 0 [1, 2, 1, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [1, 2, 0, 1]) (Word.mk 0 [0, 1, 2, 1]) := by
    exact displayedBackward law20 (show law20 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  have edge01 : Derives basis (Word.mk 0 [0, 1, 2, 1]) (Word.mk 0 [1, 2, 1, 0]) := by
    exact displayedForward law21 (show law21 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact (edge00).trans edge01

/-- Literal bridge xxyx=xyxx. -/
theorem aLaw15 :
    Derives basis (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0, 0]) := by
    exact displayedForward law27 (show law27 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xxxx=xx. -/
theorem c14Law00 :
    Derives basis (Word.mk 0 [0, 0, 0]) (Word.mk 0 [0]) := by
  have edge00 : Derives basis (Word.mk 0 [0, 0, 0]) (Word.mk 0 [0]) := by
    exact displayedBackward law00 (show law00 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xyyyx=xyx. -/
theorem c14Law01 :
    Derives basis (Word.mk 0 [1, 1, 1, 0]) (Word.mk 0 [1, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [1, 1, 1, 0]) (Word.mk 0 [1, 0]) := by
    exact displayedBackward law07 (show law07 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xyxxx=xyx. -/
theorem c14Law02 :
    Derives basis (Word.mk 0 [1, 0, 0, 0]) (Word.mk 0 [1, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [1, 0, 0, 0]) (Word.mk 0 [1, 0]) := by
    exact displayedBackward law04 (show law04 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xxyx=xyxx. -/
theorem c14Law03 :
    Derives basis (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0, 0]) := by
    exact displayedForward law27 (show law27 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xyxzx=xxyzx. -/
theorem c14Law04 :
    Derives basis (Word.mk 0 [1, 0, 2, 0]) (Word.mk 0 [0, 1, 2, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [1, 0, 2, 0]) (Word.mk 0 [0, 1, 2, 0]) := by
    exact displayedBackward law16 (show law16 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact edge00

/-- Literal bridge xyxy=xyyx. -/
theorem c14Law05 :
    Derives basis (Word.mk 0 [1, 0, 1]) (Word.mk 0 [1, 1, 0]) := by
  have edge00 : Derives basis (Word.mk 0 [1, 0, 1]) (Word.mk 0 [1, 1, 0, 0, 0]) := by
    exact displayedForward law03 (show law03 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) (some (Word.mk 0 [])) none
  have edge01 : Derives basis (Word.mk 0 [1, 1, 0, 0, 0]) (Word.mk 0 [1, 1, 0]) := by
    exact displayedBackward law04 (show law04 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 [1]) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0) none none
  exact (edge00).trans edge01

theorem aBasisLawsDerive (identity : Identity Nat) (member : identity ∈ SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact aLaw00
  · exact aLaw01
  · exact aLaw02
  · exact aLaw03
  · exact aLaw04
  · exact aLaw05
  · exact aLaw06
  · exact aLaw07
  · exact aLaw08
  · exact aLaw09
  · exact aLaw10
  · exact aLaw11
  · exact aLaw12
  · exact aLaw13
  · exact aLaw14
  · exact aLaw15

theorem condition14LawsDerive (identity : Identity Nat) (member : identity ∈ SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.basis) :
    Derives basis identity.lhs identity.rhs := by
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  simp only [SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.finiteBasis, List.mem_cons, List.not_mem_nil, or_false] at originalMember
  rcases originalMember with rfl | rfl | rfl | rfl | rfl | rfl
  · exact c14Law00
  · exact c14Law01
  · exact c14Law02
  · exact c14Law03
  · exact c14Law04
  · exact c14Law05

theorem replayA {left right : Word Nat} (derivation : Derives SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.basis left right) :
    Derives basis left right := derivation.transport aBasisLawsDerive

theorem replayCondition14 {left right : Word Nat} (derivation : Derives SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.basis left right) :
    Derives basis left right := derivation.transport condition14LawsDerive

theorem replayCondition14List {left right : List Nat}
    (derivation : CoRoots.S5_107.ListDerives SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.basis left right) :
    CoRoots.S5_107.ListDerives basis left right := by
  cases derivation with
  | empty => exact .empty
  | words derived => exact .words (replayCondition14 derived)

theorem derivesOfAKey (left right : Word Nat)
    (same : SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.KeyTheory.SameKey left.toList right.toList) :
    Derives basis left right := replayA (SemigroupBasis.CoRoots.Order6Day11.FordLordProfile15.Alignment.derivesOfSameKey left right same)

end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415
