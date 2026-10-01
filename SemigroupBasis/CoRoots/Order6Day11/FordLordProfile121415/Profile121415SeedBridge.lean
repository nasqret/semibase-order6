import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile121415.Profile121415Presentation
import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_796OppositeFixedHead

/-! Exact 21-edge replay of the seventeen reversed frozen seed laws.
The pre-existing converse is unrestricted. No finite search bound is used
as a premise, and every displayed-law intermediate is explicitly typed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile121415

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day7.S3_11

abbrev seedBasis : List (Identity Nat) := reversedBasis Rank001.basis

private def surround (front : Option (Word Nat)) (middle : Word Nat)
    (suffix : Option (Word Nat)) : Word Nat :=
  match front, suffix with
  | none, none => middle
  | some first, none => first ++ middle
  | none, some last => middle ++ last
  | some first, some last => (first ++ middle) ++ last

private theorem displayedForward
    (identity : Identity Nat) (member : identity ∈ basis)
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

private theorem displayedBackward
    (identity : Identity Nat) (member : identity ∈ basis)
    (substitution : Nat → Word Nat) (front suffix : Option (Word Nat)) :
    Derives basis (surround front (identity.rhs.bind substitution) suffix)
      (surround front (identity.lhs.bind substitution) suffix) :=
  (displayedForward identity member substitution front suffix).symm

/-- xx=xxxx, the literal reverse of frozen seed law00. -/
theorem reversedSeedLaw00 :
    Derives basis Rank001.law00.reversed.lhs Rank001.law00.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0]) := by
    exact displayedForward law00
      (show law00 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- xyxxx=xyx, the literal reverse of frozen seed law01. -/
theorem reversedSeedLaw01 :
    Derives basis Rank001.law01.reversed.lhs Rank001.law01.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 0 [1, 0, 0, 0]) (Word.mk 0 [1, 0]) := by
    exact displayedBackward law04
      (show law04 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- xyxx=xxyx, the literal reverse of frozen seed law02. -/
theorem reversedSeedLaw02 :
    Derives basis Rank001.law02.reversed.lhs Rank001.law02.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 0 [1, 0, 0]) (Word.mk 0 [0, 1, 0]) := by
    exact displayedForward law08
      (show law08 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- xxyxx=xyx, the literal reverse of frozen seed law03. -/
theorem reversedSeedLaw03 :
    Derives basis Rank001.law03.reversed.lhs Rank001.law03.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 0 [0, 1, 0, 0]) (Word.mk 0 [1, 0]) := by
    exact displayedBackward law02
      (show law02 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- zxyxx=zyyxy, the literal reverse of frozen seed law04. -/
theorem reversedSeedLaw04 :
    Derives basis Rank001.law04.reversed.lhs Rank001.law04.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 2 [0, 1, 0, 0]) (Word.mk 2 [1, 1, 0, 1]) := by
    exact displayedBackward law16
      (show law16 ∈ basis by decide)
      (fun | 0 => (Word.mk 2 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- yyxx=yxyx, the literal reverse of frozen seed law05. -/
theorem reversedSeedLaw05 :
    Derives basis Rank001.law05.reversed.lhs Rank001.law05.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 1 [1, 0, 0]) (Word.mk 1 [0, 1, 0]) := by
    exact displayedForward law21
      (show law21 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- yyxx=yxxy, the literal reverse of frozen seed law06. -/
theorem reversedSeedLaw06 :
    Derives basis Rank001.law06.reversed.lhs Rank001.law06.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 1 [1, 0, 0]) (Word.mk 1 [0, 0, 1]) := by
    exact displayedForward law22
      (show law22 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- zyyxx=zxyyx, the literal reverse of frozen seed law07. -/
theorem reversedSeedLaw07 :
    Derives basis Rank001.law07.reversed.lhs Rank001.law07.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 2 [1, 1, 0, 0]) (Word.mk 2 [0, 1, 1, 0]) := by
    exact displayedForward law19
      (show law19 ∈ basis by decide)
      (fun | 0 => (Word.mk 2 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- yzyxx=yzxyx, the literal reverse of frozen seed law08. -/
theorem reversedSeedLaw08 :
    Derives basis Rank001.law08.reversed.lhs Rank001.law08.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 1 [2, 1, 0, 0]) (Word.mk 1 [2, 1, 0, 0, 0, 0]) := by
    exact displayedForward law00
      (show law00 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      (some (Word.mk 1 [2, 1])) none
  have edge01 :
      Derives basis (Word.mk 1 [2, 1, 0, 0, 0, 0]) (Word.mk 1 [2, 0, 1, 0, 0, 0]) := by
    exact displayedForward law23
      (show law23 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 2 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none (some (Word.mk 0 []))
  have edge02 :
      Derives basis (Word.mk 1 [2, 0, 1, 0, 0, 0]) (Word.mk 1 [2, 0, 1, 0]) := by
    exact displayedBackward law04
      (show law04 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      (some (Word.mk 1 [2])) none
  exact edge00.trans (edge01.trans (edge02))

/-- yzyxx=yyxzx, the literal reverse of frozen seed law09. -/
theorem reversedSeedLaw09 :
    Derives basis Rank001.law09.reversed.lhs Rank001.law09.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 1 [2, 1, 0, 0]) (Word.mk 1 [1, 0, 2, 0]) := by
    exact displayedBackward law15
      (show law15 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- yzyxx=yzxxy, the literal reverse of frozen seed law10. -/
theorem reversedSeedLaw10 :
    Derives basis Rank001.law10.reversed.lhs Rank001.law10.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 1 [2, 1, 0, 0]) (Word.mk 1 [1, 0, 2, 0]) := by
    exact displayedBackward law15
      (show law15 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  have edge01 :
      Derives basis (Word.mk 1 [1, 0, 2, 0]) (Word.mk 1 [0, 0, 2, 1]) := by
    exact displayedForward law14
      (show law14 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 0 []) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  have edge02 :
      Derives basis (Word.mk 1 [0, 0, 2, 1]) (Word.mk 1 [2, 0, 0, 1]) := by
    exact displayedForward law08
      (show law08 ∈ basis by decide)
      (fun | 0 => (Word.mk 1 []) | 1 => (Word.mk 0 [0]) | 2 => (Word.mk 2 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00.trans (edge01.trans (edge02))

/-- xyx=xxxyx, the literal reverse of frozen seed law11. -/
theorem reversedSeedLaw11 :
    Derives basis Rank001.law11.reversed.lhs Rank001.law11.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 0, 1, 0]) := by
    exact displayedForward law01
      (show law01 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- xyx=xyyyx, the literal reverse of frozen seed law12. -/
theorem reversedSeedLaw12 :
    Derives basis Rank001.law12.reversed.lhs Rank001.law12.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 1, 1, 0]) := by
    exact displayedForward law07
      (show law07 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- xyx=xyyxy, the literal reverse of frozen seed law13. -/
theorem reversedSeedLaw13 :
    Derives basis Rank001.law13.reversed.lhs Rank001.law13.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 1, 0, 1]) := by
    exact displayedForward law06
      (show law06 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- xyx=xyxyy, the literal reverse of frozen seed law14. -/
theorem reversedSeedLaw14 :
    Derives basis Rank001.law14.reversed.lhs Rank001.law14.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [1, 0, 1, 1]) := by
    exact displayedForward law05
      (show law05 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- xyx=xxyyy, the literal reverse of frozen seed law15. -/
theorem reversedSeedLaw15 :
    Derives basis Rank001.law15.reversed.lhs Rank001.law15.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 0 [1, 0]) (Word.mk 0 [0, 1, 1, 1]) := by
    exact displayedForward law03
      (show law03 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 1 []) | 2 => (Word.mk 0 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- xzyx=xyzx, the literal reverse of frozen seed law16. -/
theorem reversedSeedLaw16 :
    Derives basis Rank001.law16.reversed.lhs Rank001.law16.reversed.rhs := by
  have edge00 :
      Derives basis (Word.mk 0 [2, 1, 0]) (Word.mk 0 [1, 2, 0]) := by
    exact displayedForward law08
      (show law08 ∈ basis by decide)
      (fun | 0 => (Word.mk 0 []) | 1 => (Word.mk 2 []) | 2 => (Word.mk 1 []) | 3 => (Word.mk 0 []) | _ => Word.singleton 0)
      none none
  exact edge00

/-- Every premise of the old converse is a consequence of the exact new basis. -/
theorem seedLawsDerive (identity : Identity Nat) (member : identity ∈ seedBasis) :
    Derives basis identity.lhs identity.rhs := by
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  simp only [Rank001.basis, List.mem_cons, List.not_mem_nil, or_false] at originalMember
  rcases originalMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reversedSeedLaw00
  · exact reversedSeedLaw01
  · exact reversedSeedLaw02
  · exact reversedSeedLaw03
  · exact reversedSeedLaw04
  · exact reversedSeedLaw05
  · exact reversedSeedLaw06
  · exact reversedSeedLaw07
  · exact reversedSeedLaw08
  · exact reversedSeedLaw09
  · exact reversedSeedLaw10
  · exact reversedSeedLaw11
  · exact reversedSeedLaw12
  · exact reversedSeedLaw13
  · exact reversedSeedLaw14
  · exact reversedSeedLaw15
  · exact reversedSeedLaw16

/-- Unrestricted replay, with both contexts and all nonempty substitutions. -/
theorem replaySeed {left right : Word Nat} (derivation : Derives seedBasis left right) :
    Derives basis left right :=
  derivation.transport seedLawsDerive

/-- The existing complete signature theorem is now proved in C/25. -/
theorem derivesOfSameSignature {left right : Word Nat}
    (same : SeedS5_796Opposite.SameFixedHeadParitySeparatorSignature left right) :
    Derives basis left right :=
  replaySeed (SeedS5_796Opposite.derivesOfSameFixedHeadParitySeparatorSignature same)

end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile121415
