import SemigroupBasis.CoRoots.Order6LeeLiP2G4Injection
import SemigroupBasis.CoRoots.Order6LeeLiP2G4SeparationDataS6_8232
import SemigroupBasis.CoRoots.Order6LeeLiP2G4SeparationDataS6_8233
import SemigroupBasis.CoRoots.Order6LeeLiP2G4SeparationDataS6_10988
import SemigroupBasis.CoRoots.Order6LeeLiP2G4SeparationDataS6_10989
import SemigroupBasis.CoRoots.Order6LeeLiP2G4SeparationDataS6_11124
import SemigroupBasis.CoRoots.Order6LeeLiP2G4SeparationDataS6_11126

/-!
# G4 order-six member endpoints

The shared G4 normalization and merge-collapse argument lives in
`Order6LeeLiP2G4Injection`. Each concrete member supplies its finite table,
the three-law model check, and an injective semantic fingerprint on the fixed
1,424-word four-generator inventory.
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G4.Members

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6LeeLiP2G4

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

namespace S6_8232

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_8232Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basisG4 :=
  FiniteCertificate.checkModels_sound table basisG4 toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  S6_8232Data.separatorValuations.map fun values =>
    S6_8232Data.evalWord values word

theorem fingerprints_eq :
    Injection.canonicalInventory.map
        (Injection.memberFingerprint semigroup
          S6_8232Data.separatorValuations) =
      S6_8232Data.fingerprints := by
  calc
    _ = Injection.canonicalInventory.map
          (fun letters => fingerprint (Injection.canonicalWord letters)) := by
      rfl
    _ = (Injection.canonicalInventory.map Injection.canonicalWord).map
          fingerprint := by
      rw [List.map_map]
      apply List.map_congr_left
      intro letters _
      rfl
    _ = S6_8233Data.canonicals.map fingerprint := by
      rw [Injection.canonicalWords_eq_separationData]
    _ = S6_8232Data.canonicals.map fingerprint := by
      rfl
    _ = S6_8232Data.fingerprints := by
      rfl

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map
      (Injection.memberFingerprint semigroup
        S6_8232Data.separatorValuations)).Nodup := by
  rw [fingerprints_eq]
  exact S6_8232Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basisG4 :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_8232Data.separatorValuations fingerprints_nodup

end S6_8232

namespace S6_8233

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_8233Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basisG4 :=
  FiniteCertificate.checkModels_sound table basisG4 toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  S6_8233Data.separatorValuations.map fun values =>
    S6_8233Data.evalWord values word

theorem fingerprints_eq :
    Injection.canonicalInventory.map
        (Injection.memberFingerprint semigroup
          S6_8233Data.separatorValuations) =
      S6_8233Data.fingerprints := by
  calc
    _ = Injection.canonicalInventory.map
          (fun letters => fingerprint (Injection.canonicalWord letters)) := by
      rfl
    _ = (Injection.canonicalInventory.map Injection.canonicalWord).map
          fingerprint := by
      rw [List.map_map]
      apply List.map_congr_left
      intro letters _
      rfl
    _ = S6_8233Data.canonicals.map fingerprint := by
      rw [Injection.canonicalWords_eq_separationData]
    _ = S6_8233Data.fingerprints := by
      rfl

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map
      (Injection.memberFingerprint semigroup
        S6_8233Data.separatorValuations)).Nodup := by
  rw [fingerprints_eq]
  exact S6_8233Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basisG4 :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_8233Data.separatorValuations fingerprints_nodup

end S6_8233

namespace S6_10988

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_10988Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basisG4 :=
  FiniteCertificate.checkModels_sound table basisG4 toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  S6_10988Data.separatorValuations.map fun values =>
    S6_10988Data.evalWord values word

theorem fingerprints_eq :
    Injection.canonicalInventory.map
        (Injection.memberFingerprint semigroup
          S6_10988Data.separatorValuations) =
      S6_10988Data.fingerprints := by
  calc
    _ = Injection.canonicalInventory.map
          (fun letters => fingerprint (Injection.canonicalWord letters)) := by
      rfl
    _ = (Injection.canonicalInventory.map Injection.canonicalWord).map
          fingerprint := by
      rw [List.map_map]
      apply List.map_congr_left
      intro letters _
      rfl
    _ = S6_8233Data.canonicals.map fingerprint := by
      rw [Injection.canonicalWords_eq_separationData]
    _ = S6_10988Data.canonicals.map fingerprint := by
      rfl
    _ = S6_10988Data.fingerprints := by
      rfl

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map
      (Injection.memberFingerprint semigroup
        S6_10988Data.separatorValuations)).Nodup := by
  rw [fingerprints_eq]
  exact S6_10988Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basisG4 :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_10988Data.separatorValuations fingerprints_nodup

end S6_10988

namespace S6_10989

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_10989Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basisG4 :=
  FiniteCertificate.checkModels_sound table basisG4 toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  S6_10989Data.separatorValuations.map fun values =>
    S6_10989Data.evalWord values word

theorem fingerprints_eq :
    Injection.canonicalInventory.map
        (Injection.memberFingerprint semigroup
          S6_10989Data.separatorValuations) =
      S6_10989Data.fingerprints := by
  calc
    _ = Injection.canonicalInventory.map
          (fun letters => fingerprint (Injection.canonicalWord letters)) := by
      rfl
    _ = (Injection.canonicalInventory.map Injection.canonicalWord).map
          fingerprint := by
      rw [List.map_map]
      apply List.map_congr_left
      intro letters _
      rfl
    _ = S6_8233Data.canonicals.map fingerprint := by
      rw [Injection.canonicalWords_eq_separationData]
    _ = S6_10989Data.canonicals.map fingerprint := by
      rfl
    _ = S6_10989Data.fingerprints := by
      rfl

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map
      (Injection.memberFingerprint semigroup
        S6_10989Data.separatorValuations)).Nodup := by
  rw [fingerprints_eq]
  exact S6_10989Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basisG4 :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_10989Data.separatorValuations fingerprints_nodup

end S6_10989

namespace S6_11124

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_11124Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basisG4 :=
  FiniteCertificate.checkModels_sound table basisG4 toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  S6_11124Data.separatorValuations.map fun values =>
    S6_11124Data.evalWord values word

theorem fingerprints_eq :
    Injection.canonicalInventory.map
        (Injection.memberFingerprint semigroup
          S6_11124Data.separatorValuations) =
      S6_11124Data.fingerprints := by
  calc
    _ = Injection.canonicalInventory.map
          (fun letters => fingerprint (Injection.canonicalWord letters)) := by
      rfl
    _ = (Injection.canonicalInventory.map Injection.canonicalWord).map
          fingerprint := by
      rw [List.map_map]
      apply List.map_congr_left
      intro letters _
      rfl
    _ = S6_8233Data.canonicals.map fingerprint := by
      rw [Injection.canonicalWords_eq_separationData]
    _ = S6_11124Data.canonicals.map fingerprint := by
      rfl
    _ = S6_11124Data.fingerprints := by
      rfl

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map
      (Injection.memberFingerprint semigroup
        S6_11124Data.separatorValuations)).Nodup := by
  rw [fingerprints_eq]
  exact S6_11124Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basisG4 :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_11124Data.separatorValuations fingerprints_nodup

end S6_11124

namespace S6_11126

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_11126Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basisG4 :=
  FiniteCertificate.checkModels_sound table basisG4 toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  S6_11126Data.separatorValuations.map fun values =>
    S6_11126Data.evalWord values word

theorem fingerprints_eq :
    Injection.canonicalInventory.map
        (Injection.memberFingerprint semigroup
          S6_11126Data.separatorValuations) =
      S6_11126Data.fingerprints := by
  calc
    _ = Injection.canonicalInventory.map
          (fun letters => fingerprint (Injection.canonicalWord letters)) := by
      rfl
    _ = (Injection.canonicalInventory.map Injection.canonicalWord).map
          fingerprint := by
      rw [List.map_map]
      apply List.map_congr_left
      intro letters _
      rfl
    _ = S6_8233Data.canonicals.map fingerprint := by
      rw [Injection.canonicalWords_eq_separationData]
    _ = S6_11126Data.canonicals.map fingerprint := by
      rfl
    _ = S6_11126Data.fingerprints := by
      rfl

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map
      (Injection.memberFingerprint semigroup
        S6_11126Data.separatorValuations)).Nodup := by
  rw [fingerprints_eq]
  exact S6_11126Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basisG4 :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_11126Data.separatorValuations fingerprints_nodup

end S6_11126

end SemigroupBasis.CoRoots.Order6LeeLiP2G4.Members
