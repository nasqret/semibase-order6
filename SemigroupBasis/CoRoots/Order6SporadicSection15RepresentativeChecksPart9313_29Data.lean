import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart9313_00

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_9313

namespace Checks

/-- The unique Section 15 basis identity at zero-based position 27. -/
def identity27 : Identity (Fin 7) :=
  ⟨⟨0, [4, 1, 5, 0, 6, 1]⟩, ⟨0, [4, 0, 5, 1, 6, 1]⟩⟩

/-- The unique Section 15 basis identity at zero-based position 19. -/
def identity19 : Identity (Fin 7) :=
  ⟨⟨0, [4, 1, 5, 0, 6, 1]⟩, ⟨1, [4, 0, 5, 0, 6, 1]⟩⟩

def tableValue0 : Fin table.order := ⟨0, by decide⟩
def tableValue1 : Fin table.order := ⟨1, by decide⟩
def tableValue2 : Fin table.order := ⟨2, by decide⟩
def tableValue3 : Fin table.order := ⟨3, by decide⟩
def tableValue4 : Fin table.order := ⟨4, by decide⟩
def tableValue5 : Fin table.order := ⟨5, by decide⟩

theorem tableValues :
    List.finRange table.order =
      [tableValue0, tableValue1, tableValue2,
        tableValue3, tableValue4, tableValue5] := by
  decide

/-- The support-bounded check for identity 27 with its first coordinate fixed.
Splitting this outer coordinate keeps each kernel reduction below the WMI
persistent service's memory bound. -/
def checkIdentity27At0 (a0 : Fin table.order) : Bool :=
  checkUsedValue (List.finRange table.order) (identityUses7 identity27 1)
      defaultValue fun a1 =>
    checkUsedValue (List.finRange table.order) (identityUses7 identity27 2)
        defaultValue fun a2 =>
      checkUsedValue (List.finRange table.order) (identityUses7 identity27 3)
          defaultValue fun a3 =>
        checkUsedValue (List.finRange table.order) (identityUses7 identity27 4)
            defaultValue fun a4 =>
          checkUsedValue (List.finRange table.order) (identityUses7 identity27 5)
              defaultValue fun a5 =>
            checkUsedValue (List.finRange table.order) (identityUses7 identity27 6)
                defaultValue fun a6 =>
              decide
                (table.semigroup.eval (valuation7 a0 a1 a2 a3 a4 a5 a6)
                    identity27.lhs =
                  table.semigroup.eval (valuation7 a0 a1 a2 a3 a4 a5 a6)
                    identity27.rhs)

def checkIdentity19At0 (a0 : Fin table.order) : Bool :=
  checkUsedValue (List.finRange table.order) (identityUses7 identity19 1)
      defaultValue fun a1 =>
    checkUsedValue (List.finRange table.order) (identityUses7 identity19 2)
        defaultValue fun a2 =>
      checkUsedValue (List.finRange table.order) (identityUses7 identity19 3)
          defaultValue fun a3 =>
        checkUsedValue (List.finRange table.order) (identityUses7 identity19 4)
            defaultValue fun a4 =>
          checkUsedValue (List.finRange table.order) (identityUses7 identity19 5)
              defaultValue fun a5 =>
            checkUsedValue (List.finRange table.order) (identityUses7 identity19 6)
                defaultValue fun a6 =>
              decide
                (table.semigroup.eval (valuation7 a0 a1 a2 a3 a4 a5 a6)
                    identity19.lhs =
                  table.semigroup.eval (valuation7 a0 a1 a2 a3 a4 a5 a6)
                    identity19.rhs)

theorem identity27_slice :
    (finiteBasis.drop 27).take 1 = [identity27] := by
  decide

theorem identity19_slice :
    (finiteBasis.drop 19).take 1 = [identity19] := by
  decide

theorem checkIdentity27_decompose :
    checkIdentityOnSupport table defaultValue identity27 =
      (List.finRange table.order).all checkIdentity27At0 := by
  rfl

theorem checkIdentity19_decompose :
    checkIdentityOnSupport table defaultValue identity19 =
      (List.finRange table.order).all checkIdentity19At0 := by
  rfl

end Checks

end S6_9313
end SemigroupBasis.CoRoots.Order6SporadicSection15
