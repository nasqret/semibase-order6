import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71SimpleCrossingMoves

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis

/-!
# Finite glue for the count-two event normalizer

The first/last/count renderer is complete for each fixed descriptor, but that
descriptor is not itself invariant under the two factor theories. At width
three and length five, exactly five semantic classes cross descriptor values.
The following derivations expose one generator for each nontrivial glue class,
using only the exact displayed 14-law basis.
-/

/-- Glue class `xxyy = xyyx`: displayed law 4. -/
theorem derivesGlueXxyyXyyx (x y : Word Nat) :
    Derives basis
      (((x ++ x) ++ y) ++ y)
      (((x ++ y) ++ y) ++ x) :=
  derivesLaw04 x y

/-- Glue class `xxyyz = xyyxz`: law 4 under right context. -/
theorem derivesGlueXxyyzXyyxz (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ y) ++ z)
      ((((x ++ y) ++ y) ++ x) ++ z) :=
  Derives.appendRight (derivesLaw04 x y) z

/-- Glue class `xyxzz = xyzzx`: displayed law 11. -/
theorem derivesGlueXyxzzXyzzx (x y z : Word Nat) :
    Derives basis
      ((((x ++ y) ++ x) ++ z) ++ z)
      ((((x ++ y) ++ z) ++ z) ++ x) :=
  derivesLaw11 x y z

/-- Glue class `xyyzz = xyzzy`: law 4 under left context. -/
theorem derivesGlueXyyzzXyzzy (x y z : Word Nat) :
    Derives basis
      ((((x ++ y) ++ y) ++ z) ++ z)
      ((((x ++ y) ++ z) ++ z) ++ y) := by
  have contextual :=
    Derives.prepend x (derivesLaw04 y z)
  simpa [Word.append_assoc] using contextual

/-- Glue class `xyzxy = xyzyx`: reversed law 12 followed by law 13. -/
theorem derivesGlueXyzxyXyzyx (x y z : Word Nat) :
    Derives basis
      ((((x ++ y) ++ z) ++ x) ++ y)
      ((((x ++ y) ++ z) ++ y) ++ x) :=
  (derivesLaw12 x z y).symm.trans
    (derivesLaw13 x z y)

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71
