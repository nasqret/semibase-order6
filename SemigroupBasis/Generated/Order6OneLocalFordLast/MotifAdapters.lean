import SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma
import SemigroupBasis.Normalization.OneLocalFordLast

/-!
# Exact-Sigma derivation adapters by rewrite motif

Every object below is an actual `Derives` witness obtained from membership
in its exact displayed system. `DerivedLaw.instantiate` then supplies
all word substitutions without another search.
-/

namespace SemigroupBasis.Generated.Order6OneLocalFordLast.MotifAdapters

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

namespace Sigma_086f172522f9551c

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_086f172522f9551c.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 []) (w 0 [0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1]) (w 0 [1, 0, 1, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1]) (w 0 [1, 1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0, 1]) (w 0 [1, 1])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0, 2]) (w 0 [1, 2])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw10 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 0, 1]) (w 0 [1, 1])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw11 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 0, 2]) (w 0 [1, 2])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw4, balanced_binaryLaw8]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw9]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw3, count_change_binaryLaw5, count_change_binaryLaw6, count_change_binaryLaw10]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw7, count_change_localLaw11]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 11 := by
  decide

end Sigma_086f172522f9551c

namespace Sigma_17bbc703ba9dbee0

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_17bbc703ba9dbee0.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1, 2]) (w 0 [1, 1, 0, 2])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 2, 2]) (w 2 [0, 1, 0, 2])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw10 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 1]) (w 0 [2, 1, 1])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw3, balanced_binaryLaw4]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw5, balanced_localLaw6, balanced_localLaw9, balanced_localLaw10]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw7]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw8]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 10 := by
  decide

end Sigma_17bbc703ba9dbee0

namespace Sigma_2c9cb34de943739e

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_2c9cb34de943739e.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0]) (w 0 [0, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0, 1]) (w 0 [0, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1]) (w 0 [0, 1, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1]) (w 1 [0, 1])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [0, 1, 2, 2])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [2, 0, 1, 2])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 2 [0, 1, 2, 2])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 1]) (w 0 [1, 1, 1])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 1, 2]) (w 0 [1, 2])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw3, count_change_binaryLaw4, count_change_binaryLaw8]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw5, count_change_localLaw6, count_change_localLaw7, count_change_localLaw9]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 9 := by
  decide

end Sigma_2c9cb34de943739e

namespace Sigma_2fbaaa66a46422c3

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_2fbaaa66a46422c3.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0]) (w 0 [0, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0, 1]) (w 0 [0, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1]) (w 0 [1, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 2])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 2]) (w 0 [1, 2])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw3, count_change_binaryLaw4, count_change_binaryLaw5]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw6, count_change_localLaw7]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 7 := by
  decide

end Sigma_2fbaaa66a46422c3

namespace Sigma_5b78bf5b916fda2a

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_5b78bf5b916fda2a.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0, 1, 1]) (w 1 [0, 0, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw10 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw11 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw12 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 2, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw13 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw3, balanced_binaryLaw4, balanced_binaryLaw6, balanced_binaryLaw7, balanced_binaryLaw8]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw9, balanced_localLaw10, balanced_localLaw11, balanced_localLaw12]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw5, count_change_binaryLaw13]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 13 := by
  decide

end Sigma_5b78bf5b916fda2a

namespace Sigma_628cd88d24637e89

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_628cd88d24637e89.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0]) (w 0 [0, 0, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 1, 2]) (w 0 [2, 1, 1])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw2, balanced_binaryLaw3]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw4]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 4 := by
  decide

end Sigma_628cd88d24637e89

namespace Sigma_699898150b01acc0

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_699898150b01acc0.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 1, 2])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 2, 1]) (w 0 [1, 2, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw10 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw11 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 1, 2]) (w 0 [1, 2])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw12 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw13 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 1]) (w 0 [1, 2, 1, 2])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw12]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw3, count_change_binaryLaw7, count_change_binaryLaw8]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw4, count_change_localLaw5, count_change_localLaw6, count_change_localLaw9, count_change_localLaw10, count_change_localLaw11, count_change_localLaw13]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 13 := by
  decide

end Sigma_699898150b01acc0

namespace Sigma_6e291332acfa2508

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_6e291332acfa2508.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0, 0, 1]) (w 0 [1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 1, 1, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 1, 1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw10 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 2, 0])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw4, balanced_binaryLaw5, balanced_binaryLaw6, balanced_binaryLaw7]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw8, balanced_localLaw9, balanced_localLaw10]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw3]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 10 := by
  decide

end Sigma_6e291332acfa2508

namespace Sigma_6e5b151c213af3dd

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_6e5b151c213af3dd.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 1, 2]) (w 0 [1, 2])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw3]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw4]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw5, count_change_binaryLaw6, count_change_binaryLaw7]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw8]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 8 := by
  decide

end Sigma_6e5b151c213af3dd

namespace Sigma_78b43a0acdd4f5a3

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_78b43a0acdd4f5a3.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1]) (w 0 [1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 1]) (w 0 [2, 1, 1])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw4, balanced_localLaw5]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw3]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 5 := by
  decide

end Sigma_78b43a0acdd4f5a3

namespace Sigma_799d6f5645f1ae36

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_799d6f5645f1ae36.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0]) (w 0 [0, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0, 1]) (w 0 [0, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 2])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 1])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 2]) (w 0 [1, 2])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw3, count_change_binaryLaw5]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw4, count_change_localLaw6]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 6 := by
  decide

end Sigma_799d6f5645f1ae36

namespace Sigma_93a811f26898d3d0

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_93a811f26898d3d0.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 2])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 1])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw5]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw4]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw3]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 5 := by
  decide

end Sigma_93a811f26898d3d0

namespace Sigma_93f39e2d4dde80c3

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_93f39e2d4dde80c3.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 1 [0, 1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 1 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 1, 2]) (w 0 [1, 2])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 0]) (w 1 [0, 1, 2, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw10 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 0]) (w 1 [1, 0, 2, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw11 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 0]) (w 1 [1, 2, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw12 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 0]) (w 1 [2, 1, 0, 0])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw8]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw3, count_change_binaryLaw4, count_change_binaryLaw5, count_change_binaryLaw6]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw7, count_change_localLaw9, count_change_localLaw10, count_change_localLaw11, count_change_localLaw12]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 12 := by
  decide

end Sigma_93f39e2d4dde80c3

namespace Sigma_947d9ea41e9770e5

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_947d9ea41e9770e5.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0]) (w 0 [0, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0, 1]) (w 0 [0, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1]) (w 0 [1, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 2])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2]) (w 0 [2, 1, 2])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw3, count_change_binaryLaw4, count_change_binaryLaw5]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw6, count_change_localLaw7]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 7 := by
  decide

end Sigma_947d9ea41e9770e5

namespace Sigma_968e763319b37dc8

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_968e763319b37dc8.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 1 [0, 1])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 2]) (w 0 [1, 1, 0, 2])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 1, 2, 0]) (w 0 [1, 2, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw10 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw11 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 1]) (w 0 [1, 2, 2])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw10]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw3, count_change_binaryLaw6]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw4, count_change_localLaw5, count_change_localLaw7, count_change_localLaw8, count_change_localLaw9, count_change_localLaw11]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 11 := by
  decide

end Sigma_968e763319b37dc8

namespace Sigma_b38ba0cb580369ae

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_b38ba0cb580369ae.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1, 2]) (w 0 [1, 1, 0, 2])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 1]) (w 0 [2, 1, 1])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw3]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw4, balanced_localLaw7]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw5]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw6]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 7 := by
  decide

end Sigma_b38ba0cb580369ae

namespace Sigma_ba4e34217dcb083d

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_ba4e34217dcb083d.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0, 1, 1]) (w 1 [0, 0, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw10 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw11 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw12 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 2, 2]) (w 2 [0, 1, 0, 2])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw13 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 1]) (w 0 [2, 1, 1])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw3, balanced_binaryLaw4, balanced_binaryLaw6, balanced_binaryLaw7, balanced_binaryLaw8]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw9, balanced_localLaw11, balanced_localLaw12, balanced_localLaw13]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw5, count_change_binaryLaw10]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 13 := by
  decide

end Sigma_ba4e34217dcb083d

namespace Sigma_cdd7bcfee1652ef1

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_cdd7bcfee1652ef1.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 1, 1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw10 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 1]) (w 0 [2, 1, 1])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw3, balanced_binaryLaw5, balanced_binaryLaw6, balanced_binaryLaw7]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw9, balanced_localLaw10]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw4, count_change_binaryLaw8]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 10 := by
  decide

end Sigma_cdd7bcfee1652ef1

namespace Sigma_de3d4e9ae533e928

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_de3d4e9ae533e928.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw10 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 2, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw11 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw12 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 1, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw13 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 0, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw14 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw15 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 1, 1, 2]) (w 0 [1, 2])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw16 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 1, 2, 1]) (w 0 [1, 2, 2, 2])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw3, balanced_binaryLaw5, balanced_binaryLaw6]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw8, balanced_localLaw9, balanced_localLaw10]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw4, count_change_binaryLaw7, count_change_binaryLaw11, count_change_binaryLaw12, count_change_binaryLaw13, count_change_binaryLaw14]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw15, count_change_localLaw16]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 16 := by
  decide

end Sigma_de3d4e9ae533e928

namespace Sigma_e90b38ad3e5293c8

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_e90b38ad3e5293c8.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 1, 2, 2]) (w 0 [2, 1, 1, 2])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw3]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw4, balanced_localLaw6]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw5]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 6 := by
  decide

end Sigma_e90b38ad3e5293c8

namespace Sigma_eb2ae10f901ecada

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_eb2ae10f901ecada.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 2, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 1, 2, 2]) (w 0 [2, 1, 1, 2])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw3, balanced_binaryLaw4]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw5, balanced_localLaw6, balanced_localLaw7, balanced_localLaw9]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw8]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 9 := by
  decide

end Sigma_eb2ae10f901ecada

namespace Sigma_f137c52fe49d8093

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_f137c52fe49d8093.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 []) (w 0 [0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1]) (w 0 [1, 0, 1, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1]) (w 0 [1, 1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0, 1]) (w 0 [1, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0, 0, 1]) (w 0 [1, 1])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2]) (w 0 [2, 1, 2, 2])
  derives := Derives.fromBasis (by decide)

def count_change_localLaw10 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2]) (w 0 [2, 2, 1, 2])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw11 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 2, 1]) (w 0 [2, 1, 1])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw4, balanced_binaryLaw7]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw11]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw3, count_change_binaryLaw5, count_change_binaryLaw6, count_change_binaryLaw8]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_localLaw9, count_change_localLaw10]

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 11 := by
  decide

end Sigma_f137c52fe49d8093

namespace Sigma_fa3011392afb2dee

abbrev basis : List (Identity Nat) := DisplayedSigma.Sigma_fa3011392afb2dee.basis

def powerLaw1 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0]) (w 0 [0, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw2 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw3 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw4 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw5 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw6 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_binaryLaw7 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 1, 1, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw8 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw9 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0])
  derives := Derives.fromBasis (by decide)

def balanced_localLaw10 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 2, 0])
  derives := Derives.fromBasis (by decide)

def count_change_binaryLaw11 : OneLocalFordLast.DerivedLaw basis where
  identity := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0])
  derives := Derives.fromBasis (by decide)

/-- The unique index/period law of this exact system. -/
def powerAdapter : OneLocalFordLast.DerivedLaw basis :=
  powerLaw1

/-- The power law instantiated by arbitrary nonempty words. -/
theorem derivesPowerInstance
    (substitution : Nat → Word Nat) :
    Derives basis
      (powerAdapter.identity.lhs.bind substitution)
      (powerAdapter.identity.rhs.bind substitution) :=
  OneLocalFordLast.DerivedLaw.instantiate
    powerAdapter substitution

def powerLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [powerLaw1]

def balanced_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_binaryLaw3, balanced_binaryLaw5, balanced_binaryLaw6, balanced_binaryLaw7]

def balanced_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [balanced_localLaw8, balanced_localLaw9, balanced_localLaw10]

def count_change_binaryLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  [count_change_binaryLaw2, count_change_binaryLaw4, count_change_binaryLaw11]

def count_change_localLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def support_changeLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  []

def allLaws : List (OneLocalFordLast.DerivedLaw basis) :=
  powerLaws ++ balanced_binaryLaws ++ balanced_localLaws ++ count_change_binaryLaws ++ count_change_localLaws ++ support_changeLaws

theorem allLaws_length : allLaws.length = 11 := by
  decide

end Sigma_fa3011392afb2dee

end SemigroupBasis.Generated.Order6OneLocalFordLast.MotifAdapters
