import SemigroupBasis.CoRoots.Order6LeeLiP2G3Injection
import SemigroupBasis.CoRoots.Order6LeeLiP2G3SeparationDataS6_8221
import SemigroupBasis.CoRoots.Order6LeeLiP2G3SeparationDataS6_8226
import SemigroupBasis.CoRoots.Order6LeeLiP2G3SeparationDataS6_10982
import SemigroupBasis.CoRoots.Order6LeeLiP2G3SeparationDataS6_11128
import SemigroupBasis.CoRoots.Order6LeeLiP2G3SeparationDataS6_11331
import SemigroupBasis.CoRoots.Order6LeeLiP2G3SeparationDataS6_11579

/-!
# G3 order-six member endpoints

The shared G3 normalization and merge-collapse argument lives in
`Order6LeeLiP2G3Injection`. Each concrete member supplies its finite table,
the three-law model check, and an injective semantic fingerprint on the fixed
544-element four-generator inventory.
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G3.Members

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6LeeLiP2G3

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

namespace S6_8221

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_8221Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  S6_8221Data.separatorValuations.map fun values =>
    S6_8221Data.evalWord values word

theorem fingerprints_eq :
    Injection.canonicalInventory.map
        (Injection.memberFingerprint semigroup
          S6_8221Data.separatorValuations) =
      S6_8221Data.fingerprints := by
  calc
    _ = Injection.canonicalInventory.map
          (fun key => fingerprint (Injection.canonicalWord key)) := by rfl
    _ = (Injection.canonicalInventory.map Injection.canonicalWord).map
          fingerprint := by
      rw [List.map_map]
      apply List.map_congr_left
      intro key _
      rfl
    _ = S6_8221Data.canonicals.map fingerprint := by
      rw [Injection.canonicalWords_eq_separationData]
    _ = S6_8221Data.fingerprints := by
      simpa only [fingerprint] using S6_8221Data.fingerprints_eq_map.symm

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map
      (Injection.memberFingerprint semigroup
        S6_8221Data.separatorValuations)).Nodup := by
  rw [fingerprints_eq]
  exact S6_8221Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_8221Data.separatorValuations fingerprints_nodup

end S6_8221

namespace S6_8226

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_8226Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  S6_8226Data.separatorValuations.map fun values =>
    S6_8226Data.evalWord values word

theorem fingerprints_eq :
    Injection.canonicalInventory.map
        (Injection.memberFingerprint semigroup
          S6_8226Data.separatorValuations) =
      S6_8226Data.fingerprints := by
  calc
    _ = Injection.canonicalInventory.map
          (fun key => fingerprint (Injection.canonicalWord key)) := by rfl
    _ = (Injection.canonicalInventory.map Injection.canonicalWord).map
          fingerprint := by
      rw [List.map_map]
      apply List.map_congr_left
      intro key _
      rfl
    _ = S6_8221Data.canonicals.map fingerprint := by
      rw [Injection.canonicalWords_eq_separationData]
    _ = S6_8226Data.fingerprints := by
      simpa only [fingerprint] using S6_8226Data.fingerprints_eq_map.symm

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map
      (Injection.memberFingerprint semigroup
        S6_8226Data.separatorValuations)).Nodup := by
  rw [fingerprints_eq]
  exact S6_8226Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_8226Data.separatorValuations fingerprints_nodup

end S6_8226

namespace S6_10982

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_10982Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  S6_10982Data.separatorValuations.map fun values =>
    S6_10982Data.evalWord values word

theorem fingerprints_eq :
    Injection.canonicalInventory.map
        (Injection.memberFingerprint semigroup
          S6_10982Data.separatorValuations) =
      S6_10982Data.fingerprints := by
  calc
    _ = Injection.canonicalInventory.map
          (fun key => fingerprint (Injection.canonicalWord key)) := by rfl
    _ = (Injection.canonicalInventory.map Injection.canonicalWord).map
          fingerprint := by
      rw [List.map_map]
      apply List.map_congr_left
      intro key _
      rfl
    _ = S6_8221Data.canonicals.map fingerprint := by
      rw [Injection.canonicalWords_eq_separationData]
    _ = S6_10982Data.fingerprints := by
      simpa only [fingerprint] using S6_10982Data.fingerprints_eq_map.symm

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map
      (Injection.memberFingerprint semigroup
        S6_10982Data.separatorValuations)).Nodup := by
  rw [fingerprints_eq]
  exact S6_10982Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_10982Data.separatorValuations fingerprints_nodup

end S6_10982

namespace S6_11128

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_11128Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  S6_11128Data.separatorValuations.map fun values =>
    S6_11128Data.evalWord values word

theorem fingerprints_eq :
    Injection.canonicalInventory.map
        (Injection.memberFingerprint semigroup
          S6_11128Data.separatorValuations) =
      S6_11128Data.fingerprints := by
  calc
    _ = Injection.canonicalInventory.map
          (fun key => fingerprint (Injection.canonicalWord key)) := by rfl
    _ = (Injection.canonicalInventory.map Injection.canonicalWord).map
          fingerprint := by
      rw [List.map_map]
      apply List.map_congr_left
      intro key _
      rfl
    _ = S6_8221Data.canonicals.map fingerprint := by
      rw [Injection.canonicalWords_eq_separationData]
    _ = S6_11128Data.fingerprints := by
      simpa only [fingerprint] using S6_11128Data.fingerprints_eq_map.symm

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map
      (Injection.memberFingerprint semigroup
        S6_11128Data.separatorValuations)).Nodup := by
  rw [fingerprints_eq]
  exact S6_11128Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_11128Data.separatorValuations fingerprints_nodup

end S6_11128

namespace S6_11331

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_11331Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  S6_11331Data.separatorValuations.map fun values =>
    S6_11331Data.evalWord values word

theorem fingerprints_eq :
    Injection.canonicalInventory.map
        (Injection.memberFingerprint semigroup
          S6_11331Data.separatorValuations) =
      S6_11331Data.fingerprints := by
  calc
    _ = Injection.canonicalInventory.map
          (fun key => fingerprint (Injection.canonicalWord key)) := by rfl
    _ = (Injection.canonicalInventory.map Injection.canonicalWord).map
          fingerprint := by
      rw [List.map_map]
      apply List.map_congr_left
      intro key _
      rfl
    _ = S6_8221Data.canonicals.map fingerprint := by
      rw [Injection.canonicalWords_eq_separationData]
    _ = S6_11331Data.fingerprints := by
      simpa only [fingerprint] using S6_11331Data.fingerprints_eq_map.symm

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map
      (Injection.memberFingerprint semigroup
        S6_11331Data.separatorValuations)).Nodup := by
  rw [fingerprints_eq]
  exact S6_11331Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_11331Data.separatorValuations fingerprints_nodup

end S6_11331

namespace S6_11579

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_11579Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  S6_11579Data.separatorValuations.map fun values =>
    S6_11579Data.evalWord values word

theorem fingerprints_eq :
    Injection.canonicalInventory.map
        (Injection.memberFingerprint semigroup
          S6_11579Data.separatorValuations) =
      S6_11579Data.fingerprints := by
  calc
    _ = Injection.canonicalInventory.map
          (fun key => fingerprint (Injection.canonicalWord key)) := by rfl
    _ = (Injection.canonicalInventory.map Injection.canonicalWord).map
          fingerprint := by
      rw [List.map_map]
      apply List.map_congr_left
      intro key _
      rfl
    _ = S6_8221Data.canonicals.map fingerprint := by
      rw [Injection.canonicalWords_eq_separationData]
    _ = S6_11579Data.fingerprints := by
      simpa only [fingerprint] using S6_11579Data.fingerprints_eq_map.symm

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map
      (Injection.memberFingerprint semigroup
        S6_11579Data.separatorValuations)).Nodup := by
  rw [fingerprints_eq]
  exact S6_11579Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_11579Data.separatorValuations fingerprints_nodup

end S6_11579

end SemigroupBasis.CoRoots.Order6LeeLiP2G3.Members
