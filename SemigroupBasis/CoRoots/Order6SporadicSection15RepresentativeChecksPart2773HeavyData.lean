import SemigroupBasis.CoRoots.Order6SporadicSection15RepresentativeChecksPart2773_00

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis
open RepresentativeChecksInternal

namespace S6_2773.Checks

def identity19 : Identity (Fin 7) :=
  ⟨⟨0, [4, 1, 5, 0, 6, 1]⟩, ⟨1, [4, 0, 5, 0, 6, 1]⟩⟩

def identity27 : Identity (Fin 7) :=
  ⟨⟨0, [4, 1, 5, 0, 6, 1]⟩, ⟨0, [4, 0, 5, 1, 6, 1]⟩⟩

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

def checkIdentityAt0 (identity : Identity (Fin 7))
    (a0 : Fin table.order) : Bool :=
  checkUsedValue (List.finRange table.order) (identityUses7 identity 1)
      defaultValue fun a1 =>
    checkUsedValue (List.finRange table.order) (identityUses7 identity 2)
        defaultValue fun a2 =>
      checkUsedValue (List.finRange table.order) (identityUses7 identity 3)
          defaultValue fun a3 =>
        checkUsedValue (List.finRange table.order) (identityUses7 identity 4)
            defaultValue fun a4 =>
          checkUsedValue (List.finRange table.order) (identityUses7 identity 5)
              defaultValue fun a5 =>
            checkUsedValue (List.finRange table.order) (identityUses7 identity 6)
                defaultValue fun a6 =>
              decide
                (table.semigroup.eval (valuation7 a0 a1 a2 a3 a4 a5 a6)
                    identity.lhs =
                  table.semigroup.eval (valuation7 a0 a1 a2 a3 a4 a5 a6)
                    identity.rhs)

theorem identity19_slice :
    (finiteBasis.drop 19).take 1 = [identity19] := by
  decide

theorem identity27_slice :
    (finiteBasis.drop 27).take 1 = [identity27] := by
  decide

theorem checkIdentity19_decompose :
    checkIdentityOnSupport table defaultValue identity19 =
      (List.finRange table.order).all (checkIdentityAt0 identity19) := by
  rfl

theorem checkIdentity27_decompose :
    checkIdentityOnSupport table defaultValue identity27 =
      (List.finRange table.order).all (checkIdentityAt0 identity27) := by
  rfl

end S6_2773.Checks
end SemigroupBasis.CoRoots.Order6SporadicSection15
