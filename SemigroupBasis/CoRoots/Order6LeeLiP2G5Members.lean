import SemigroupBasis.CoRoots.Order6LeeLiP2G5Injection
import SemigroupBasis.CoRoots.Order6LeeLiP2G5SeparationDataS6_13172
import SemigroupBasis.CoRoots.Order6LeeLiP2G5SeparationDataS6_13173
import SemigroupBasis.CoRoots.Order6LeeLiP2G5SeparationDataS6_13197
import SemigroupBasis.CoRoots.Order6LeeLiP2G5SeparationDataS6_13198
import SemigroupBasis.CoRoots.Order6LeeLiP2G5SeparationDataS6_13778
import SemigroupBasis.CoRoots.Order6LeeLiP2G5SeparationDataS6_14270
import SemigroupBasis.CoRoots.Order6LeeLiP2G5SeparationDataS6_14537

/-!
# G5 order-six member endpoints

The shared G5 normalization and merge-collapse argument lives in
`Order6LeeLiP2G5Injection`. Each concrete member supplies its finite table,
the one-law model check, and an injective semantic fingerprint on the fixed
30-word three-generator inventory.
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G5.Members

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6LeeLiP2G5

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

/-!
Use the explicit 30-word list already certified by the first separation-data
module.  This keeps the family-level inventory computation separate from each
concrete semigroup evaluation below.
-/
private def explicitCanonicalInventory : List (Word Nat) :=
  S6_13172Data.expectedCanonicals

private theorem canonicalInventory_eq_explicit :
    Injection.canonicalInventory = explicitCanonicalInventory := by
  exact S6_13172Data.canonicals_eq_expected

namespace S6_13172

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_13172Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  Injection.memberFingerprint semigroup S6_13172Data.separatorValuations word

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem explicit_fingerprints_eq :
    explicitCanonicalInventory.map fingerprint =
      S6_13172Data.expectedFingerprints := by
  decide

theorem fingerprints_eq :
    Injection.canonicalInventory.map fingerprint = S6_13172Data.fingerprints := by
  rw [canonicalInventory_eq_explicit, explicit_fingerprints_eq,
    S6_13172Data.fingerprints_eq_expected]

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map fingerprint).Nodup := by
  rw [fingerprints_eq]
  exact S6_13172Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_13172Data.separatorValuations fingerprints_nodup

end S6_13172

namespace S6_13173

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_13173Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  Injection.memberFingerprint semigroup S6_13173Data.separatorValuations word

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem explicit_fingerprints_eq :
    explicitCanonicalInventory.map fingerprint =
      S6_13173Data.expectedFingerprints := by
  decide

theorem fingerprints_eq :
    Injection.canonicalInventory.map fingerprint = S6_13173Data.fingerprints := by
  rw [canonicalInventory_eq_explicit, explicit_fingerprints_eq,
    S6_13173Data.fingerprints_eq_expected]

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map fingerprint).Nodup := by
  rw [fingerprints_eq]
  exact S6_13173Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_13173Data.separatorValuations fingerprints_nodup

end S6_13173

namespace S6_13197

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_13197Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  Injection.memberFingerprint semigroup S6_13197Data.separatorValuations word

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem explicit_fingerprints_eq :
    explicitCanonicalInventory.map fingerprint =
      S6_13197Data.expectedFingerprints := by
  decide

theorem fingerprints_eq :
    Injection.canonicalInventory.map fingerprint = S6_13197Data.fingerprints := by
  rw [canonicalInventory_eq_explicit, explicit_fingerprints_eq,
    S6_13197Data.fingerprints_eq_expected]

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map fingerprint).Nodup := by
  rw [fingerprints_eq]
  exact S6_13197Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_13197Data.separatorValuations fingerprints_nodup

end S6_13197

namespace S6_13198

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_13198Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  Injection.memberFingerprint semigroup S6_13198Data.separatorValuations word

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem explicit_fingerprints_eq :
    explicitCanonicalInventory.map fingerprint =
      S6_13198Data.expectedFingerprints := by
  decide

theorem fingerprints_eq :
    Injection.canonicalInventory.map fingerprint = S6_13198Data.fingerprints := by
  rw [canonicalInventory_eq_explicit, explicit_fingerprints_eq,
    S6_13198Data.fingerprints_eq_expected]

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map fingerprint).Nodup := by
  rw [fingerprints_eq]
  exact S6_13198Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_13198Data.separatorValuations fingerprints_nodup

end S6_13198

namespace S6_13778

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_13778Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  Injection.memberFingerprint semigroup S6_13778Data.separatorValuations word

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem explicit_fingerprints_eq :
    explicitCanonicalInventory.map fingerprint =
      S6_13778Data.expectedFingerprints := by
  decide

theorem fingerprints_eq :
    Injection.canonicalInventory.map fingerprint = S6_13778Data.fingerprints := by
  rw [canonicalInventory_eq_explicit, explicit_fingerprints_eq,
    S6_13778Data.fingerprints_eq_expected]

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map fingerprint).Nodup := by
  rw [fingerprints_eq]
  exact S6_13778Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_13778Data.separatorValuations fingerprints_nodup

end S6_13778

namespace S6_14270

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_14270Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  Injection.memberFingerprint semigroup S6_14270Data.separatorValuations word

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem explicit_fingerprints_eq :
    explicitCanonicalInventory.map fingerprint =
      S6_14270Data.expectedFingerprints := by
  decide

theorem fingerprints_eq :
    Injection.canonicalInventory.map fingerprint = S6_14270Data.fingerprints := by
  rw [canonicalInventory_eq_explicit, explicit_fingerprints_eq,
    S6_14270Data.fingerprints_eq_expected]

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map fingerprint).Nodup := by
  rw [fingerprints_eq]
  exact S6_14270Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_14270Data.separatorValuations fingerprints_nodup

end S6_14270

namespace S6_14537

def mul (a b : Fin 6) : Fin 6 :=
  ⟨S6_14537Data.mul a.val b.val % 6, Nat.mod_lt _ (by decide)⟩

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
theorem models : Models semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinFour (by decide)

def fingerprint (word : Word Nat) : List Nat :=
  Injection.memberFingerprint semigroup S6_14537Data.separatorValuations word

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem explicit_fingerprints_eq :
    explicitCanonicalInventory.map fingerprint =
      S6_14537Data.expectedFingerprints := by
  decide

theorem fingerprints_eq :
    Injection.canonicalInventory.map fingerprint = S6_14537Data.fingerprints := by
  rw [canonicalInventory_eq_explicit, explicit_fingerprints_eq,
    S6_14537Data.fingerprints_eq_expected]

theorem fingerprints_nodup :
    (Injection.canonicalInventory.map fingerprint).Nodup := by
  rw [fingerprints_eq]
  exact S6_14537Data.fingerprints_nodup

theorem basisFor : BasisFor semigroup basis :=
  Injection.basisFor_of_fingerprints semigroup models
    S6_14537Data.separatorValuations fingerprints_nodup

end S6_14537

end SemigroupBasis.CoRoots.Order6LeeLiP2G5.Members
