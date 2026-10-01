import SemigroupBasis.CoRoots.Order6S6_3372FinalRepeatedSupportV2Prelude
import SemigroupBasis.CoRoots.S5_303Semantics
import SemigroupBasis.CoRoots.S5_83Factors
import SemigroupBasis.Transfer

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6S6_3372CorrectedBasis

open SemigroupBasis

namespace Recorded

abbrev table :=
  SemigroupBasis.CoRoots.Order6S6_3372FinalRepeatedSupportV2.table

end Recorded

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xyz : Word Nat := w 0 [1, 2]
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xyzt : Word Nat := w 0 [1, 2, 3]
def yxzt : Word Nat := w 1 [0, 2, 3]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def eraseSquareLaw : Identity Nat := ⟨xxyz, xyz⟩
def gatherFinalLaw : Identity Nat := ⟨xyx, yxx⟩
def prefixSwapLaw : Identity Nat := ⟨xyzt, yxzt⟩

/-- The corrected four-law candidate for `S6_3372`. -/
def basis : List (Identity Nat) :=
  [powerLaw, eraseSquareLaw, gatherFinalLaw, prefixSwapLaw]

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteEraseSquareLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def finiteGatherFinalLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finitePrefixSwapLaw : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 3]⟩, ⟨1, [0, 2, 3]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem finiteEraseSquareLaw_map :
    finiteEraseSquareLaw.map Fin.val = eraseSquareLaw := rfl

theorem finiteGatherFinalLaw_map :
    finiteGatherFinalLaw.map Fin.val = gatherFinalLaw := rfl

theorem finitePrefixSwapLaw_map :
    finitePrefixSwapLaw.map Fin.val = prefixSwapLaw := rfl

/-- Exhaustive finite reflection establishes validity of the corrected
candidate in the exact catalogue table. -/
theorem basis_models : Models Recorded.table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact Recorded.table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteEraseSquareLaw_map]
    exact Recorded.table.checkIdentityNat_sound finiteEraseSquareLaw (by
      set_option maxRecDepth 10000 in
        decide)
  · rw [← finiteGatherFinalLaw_map]
    exact Recorded.table.checkIdentityNat_sound finiteGatherFinalLaw (by decide)
  · rw [← finitePrefixSwapLaw_map]
    exact Recorded.table.checkIdentityNat_sound finitePrefixSwapLaw (by decide)

private def instantiateFourWords
    (u v q r : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => q
  | 3 => r
  | n + 4 => Word.singleton (n + 4)

private theorem powerLaw_mem : powerLaw ∈ basis := by
  simp [basis]

private theorem eraseSquareLaw_mem : eraseSquareLaw ∈ basis := by
  simp [basis]

private theorem gatherFinalLaw_mem : gatherFinalLaw ∈ basis := by
  simp [basis]

private theorem prefixSwapLaw_mem : prefixSwapLaw ∈ basis := by
  simp [basis]

/-- Expand a square of an arbitrary nonempty block to its cube. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have base : Derives basis xx xxx :=
    Derives.fromBasis (e := powerLaw) powerLaw_mem
  have substituted :=
    Derives.subst base (instantiateFourWords u u u u)
  simpa [powerLaw, xx, xxx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

/-- Delete a duplicate nonempty block before two nonempty suffix blocks. -/
theorem derivesPrefixContraction (u v q : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ q) ((u ++ v) ++ q) := by
  have base : Derives basis xxyz xyz :=
    Derives.fromBasis (e := eraseSquareLaw) eraseSquareLaw_mem
  have substituted :=
    Derives.subst base (instantiateFourWords u v q q)
  simpa [eraseSquareLaw, xxyz, xyz, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesPrefixInsertion (u v q : Word Nat) :
    Derives basis ((u ++ v) ++ q) (((u ++ u) ++ v) ++ q) :=
  (derivesPrefixContraction u v q).symm

/-- Gather a repeated final block into a terminal square. -/
theorem derivesGather (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((v ++ u) ++ u) := by
  have base : Derives basis xyx yxx :=
    Derives.fromBasis (e := gatherFinalLaw) gatherFinalLaw_mem
  have substituted :=
    Derives.subst base (instantiateFourWords u v v v)
  simpa [gatherFinalLaw, xyx, yxx, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Swap arbitrary nonempty prefix blocks before two fixed nonempty suffix
blocks. -/
theorem derivesPrefixSwap (u v q r : Word Nat) :
    Derives basis (((u ++ v) ++ q) ++ r)
      (((v ++ u) ++ q) ++ r) := by
  have base : Derives basis xyzt yxzt :=
    Derives.fromBasis (e := prefixSwapLaw) prefixSwapLaw_mem
  have substituted :=
    Derives.subst base (instantiateFourWords u v q r)
  simpa [prefixSwapLaw, xyzt, yxzt, w, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- The old `xyx = xyyx` law is redundant in the corrected basis. -/
theorem derivesRepeatFinal (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ v) ++ u) := by
  have gathered := derivesGather u v
  have inserted := derivesPrefixInsertion v u u
  have regrouped := (derivesGather u (v ++ v)).symm
  exact gathered.trans <| inserted.trans <| by
    simpa [Word.append_assoc] using regrouped

/-- The old guarded swap is a consequence of gather, prefix swap, and gather
backwards. -/
theorem derivesGuardedSwap (u v q : Word Nat) :
    Derives basis (((u ++ v) ++ q) ++ u)
      (((u ++ q) ++ v) ++ u) := by
  have gathered := derivesGather u (v ++ q)
  have swapped := derivesPrefixSwap v q u u
  have regrouped := (derivesGather u (q ++ v)).symm
  have gathered' :
      Derives basis (((u ++ v) ++ q) ++ u)
        (((v ++ q) ++ u) ++ u) := by
    simpa [Word.append_assoc] using gathered
  have regrouped' :
      Derives basis (((q ++ v) ++ u) ++ u)
        (((u ++ q) ++ v) ++ u) := by
    simpa [Word.append_assoc] using regrouped
  exact gathered'.trans <| swapped.trans regrouped'

/-- The literal five-element `S5_83` subsemigroup on target elements
`0,1,2,3,4`. -/
def s5_83Embedding :
    Embedding
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup
      Recorded.table.semigroup where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (1 : Fin 6) else
        if value = 2 then (2 : Fin 6) else
          if value = 3 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

/-- The literal `S5_303` subsemigroup on target elements `0,2,1,4,5`. -/
def s5_303Embedding :
    Embedding
      SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup
      Recorded.table.semigroup where
  toFun := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6) else
      if value = 1 then (2 : Fin 6) else
        if value = 2 then (1 : Fin 6) else
          if value = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right
    exact by decide +revert

theorem s5_83_models :
    Models SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup basis := by
  intro identity member
  exact s5_83Embedding.pullback_identity identity
    (basis_models identity member)

theorem s5_303_models :
    Models SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup basis := by
  intro identity member
  exact s5_303Embedding.pullback_identity identity
    (basis_models identity member)

/-- Every target-valid identity has both lower-order semantic signatures.
Their conjunction is exactly the normal-form invariant used below. -/
theorem valid_signatures
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy Recorded.table.semigroup) :
    SemigroupBasis.CoRoots.S5_303.SameContentEndpointSignature
        identity.lhs identity.rhs ∧
      SemigroupBasis.CoRoots.S5_83.SameTerminalUniqueSuffixSignature
        identity.lhs identity.rhs := by
  constructor
  · exact SemigroupBasis.CoRoots.S5_303.valid_signature identity
      (s5_303Embedding.pullback_identity identity valid)
  · exact SemigroupBasis.CoRoots.S5_83Factors.S5_83.valid_signature identity
      (s5_83Embedding.pullback_identity identity valid)

end SemigroupBasis.CoRoots.Order6S6_3372CorrectedBasis
