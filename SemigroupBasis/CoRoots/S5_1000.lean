import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.CatalogueOrder5Part08

namespace SemigroupBasis.CoRoots.S5_1000

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxxx : Word Nat := w 0 [0, 0, 0, 0]
def xy : Word Nat := w 0 [1]
def xxxxy : Word Nat := w 0 [0, 0, 0, 1]
def xyz : Word Nat := w 0 [1, 2]
def yxz : Word Nat := w 1 [0, 2]
def xxxyy : Word Nat := w 0 [0, 0, 1, 1]
def xxyyx : Word Nat := w 0 [0, 1, 1, 0]

def powerLaw : Identity Nat := ⟨xx, xxxxx⟩
def prefixExpansionLaw : Identity Nat := ⟨xy, xxxxy⟩
def prefixSwapLaw : Identity Nat := ⟨xyz, yxz⟩
def finalMoveLaw : Identity Nat := ⟨xxxyy, xxyyx⟩

/-- The exact common basis
`xx = xxxxx`, `xy = xxxxy`, `xyz = yxz`, `xxxyy = xxyyx`. -/
def basis : List (Identity Nat) :=
  [powerLaw, prefixExpansionLaw, prefixSwapLaw, finalMoveLaw]

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0, 0]⟩⟩

def finitePrefixExpansionLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 0, 0, 1]⟩⟩

def finitePrefixSwapLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def finiteFinalMoveLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1, 1]⟩, ⟨0, [0, 1, 1, 0]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem finitePrefixExpansionLaw_map :
    finitePrefixExpansionLaw.map Fin.val = prefixExpansionLaw := rfl

theorem finitePrefixSwapLaw_map :
    finitePrefixSwapLaw.map Fin.val = prefixSwapLaw := rfl

theorem finiteFinalMoveLaw_map :
    finiteFinalMoveLaw.map Fin.val = finalMoveLaw := rfl

/-- Exhaustive checks of the four finite-variable laws yield `Models` over
natural-number variables. -/
theorem models_of_finite_checks
    (table : FiniteTable)
    (powerChecked : table.checkIdentity finitePowerLaw = true)
    (prefixExpansionChecked :
      table.checkIdentity finitePrefixExpansionLaw = true)
    (prefixSwapChecked :
      table.checkIdentity finitePrefixSwapLaw = true)
    (finalMoveChecked : table.checkIdentity finiteFinalMoveLaw = true) :
    Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw powerChecked
  · rw [← finitePrefixExpansionLaw_map]
    exact table.checkIdentityNat_sound
      finitePrefixExpansionLaw prefixExpansionChecked
  · rw [← finitePrefixSwapLaw_map]
    exact table.checkIdentityNat_sound
      finitePrefixSwapLaw prefixSwapChecked
  · rw [← finiteFinalMoveLaw_map]
    exact table.checkIdentityNat_sound finiteFinalMoveLaw finalMoveChecked

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem powerLaw_mem : powerLaw ∈ basis := by
  simp [basis]

private theorem prefixExpansionLaw_mem : prefixExpansionLaw ∈ basis := by
  simp [basis]

private theorem prefixSwapLaw_mem : prefixSwapLaw ∈ basis := by
  simp [basis]

private theorem finalMoveLaw_mem : finalMoveLaw ∈ basis := by
  simp [basis]

/-- Expand two copies of a nonempty block to five copies. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((((u ++ u) ++ u) ++ u) ++ u) := by
  have base : Derives basis xx xxxxx :=
    Derives.fromBasis (e := powerLaw) powerLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u u u)
  simpa [powerLaw, xx, xxxxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Insert three copies of a nonempty prefix block before a nonempty suffix. -/
theorem derivesPrefixExpansion (u v : Word Nat) :
    Derives basis (u ++ v) ((((u ++ u) ++ u) ++ u) ++ v) := by
  have base : Derives basis xy xxxxy :=
    Derives.fromBasis (e := prefixExpansionLaw) prefixExpansionLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [prefixExpansionLaw, xy, xxxxy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Swap adjacent nonempty prefix blocks while retaining a nonempty suffix. -/
theorem derivesPrefixSwap (u v z : Word Nat) :
    Derives basis ((u ++ v) ++ z) ((v ++ u) ++ z) := by
  have base : Derives basis xyz yxz :=
    Derives.fromBasis (e := prefixSwapLaw) prefixSwapLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [prefixSwapLaw, xyz, yxz, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Move one copy of the first block behind two copies of the final block. -/
theorem derivesFinalMove (u v : Word Nat) :
    Derives basis
      ((((u ++ u) ++ u) ++ v) ++ v)
      ((((u ++ u) ++ v) ++ v) ++ u) := by
  have base : Derives basis xxxyy xxyyx :=
    Derives.fromBasis (e := finalMoveLaw) finalMoveLaw_mem
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [finalMoveLaw, xxxyy, xxyyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Retarget a repeated final block by the concrete chain
`uvv -> u^4 v^2 -> u^3 v^2 u`. -/
theorem derivesRepeatedFinalRetarget (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ v)
      (((((u ++ u) ++ u) ++ v) ++ v) ++ u) := by
  have expand := derivesPrefixExpansion u (v ++ v)
  have move := Derives.prepend u (derivesFinalMove u v)
  apply Derives.trans
  · simpa [Word.append_assoc] using expand
  · simpa [Word.append_assoc] using move

namespace S5_1000

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_1000.table

set_option maxRecDepth 100000 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)
    (by decide) (by decide)

end S5_1000

namespace S5_1003

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_1003.table

set_option maxRecDepth 100000 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide) (by decide)
    (by decide) (by decide)

end S5_1003

end SemigroupBasis.CoRoots.S5_1000
