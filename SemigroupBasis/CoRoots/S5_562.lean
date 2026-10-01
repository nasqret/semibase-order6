import SemigroupBasis.AffineParityInflation
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Generated.S4_96
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_562

open SemigroupBasis
open SemigroupBasis.Examples

def xy : Word Nat := ⟨0, [1]⟩
def xxxy : Word Nat := ⟨0, [0, 0, 1]⟩
def xyxyxy : Word Nat := ⟨0, [1, 0, 1, 0, 1]⟩
def xyyy : Word Nat := ⟨0, [1, 1, 1]⟩
def xyxx : Word Nat := ⟨0, [1, 0, 0]⟩
def xyyx : Word Nat := ⟨0, [1, 1, 0]⟩
def xyxy : Word Nat := ⟨0, [1, 0, 1]⟩

def yx : Word Nat := ⟨1, [0]⟩
def yxxx : Word Nat := ⟨1, [0, 0, 0]⟩
def yxyxyx : Word Nat := ⟨1, [0, 1, 0, 1, 0]⟩
def yyyx : Word Nat := ⟨1, [1, 1, 0]⟩

def rightContextLaw : Identity Nat := ⟨xy, xxxy⟩
def productPowerLaw : Identity Nat := ⟨xy, xyxyxy⟩
def leftContextLaw : Identity Nat := ⟨xy, xyyy⟩
def rightSquareReturnLaw : Identity Nat := ⟨xyxx, xy⟩
def middleSquareLaw : Identity Nat := ⟨xyyx, xyxy⟩

/-- The exact authoritative basis for the stored `S5_562` table. -/
def basis : List (Identity Nat) :=
  [rightContextLaw, productPowerLaw, leftContextLaw,
    rightSquareReturnLaw, middleSquareLaw]

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def bridgeRightContextLaw : Identity Nat := ⟨yx, yxxx⟩
def bridgeProductPowerLaw : Identity Nat := ⟨yx, yxyxyx⟩
def bridgeLeftContextLaw : Identity Nat := ⟨yx, yyyx⟩

/--
The literal reverse-word basis produced from
`AffineParityInflation.basis`.
-/
def bridgeBasis : List (Identity Nat) :=
  [rightSquareReturnLaw, bridgeRightContextLaw,
    bridgeProductPowerLaw, bridgeLeftContextLaw, middleSquareLaw]

theorem bridgeBasis_eq_reversedAffineParityBasis :
    bridgeBasis =
      reversedBasis SemigroupBasis.AffineParityInflation.basis := by
  decide

def swapXY : Nat → Word Nat
  | 0 => Word.singleton 1
  | 1 => Word.singleton 0
  | n + 2 => Word.singleton (n + 2)

private theorem basisAxiomsDeriveBridge
    (identity : Identity Nat) (member : identity ∈ basis) :
    Derives bridgeBasis identity.lhs identity.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · have base :
        Derives bridgeBasis
          bridgeLeftContextLaw.lhs bridgeLeftContextLaw.rhs :=
      Derives.fromBasis (e := bridgeLeftContextLaw) <|
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ (List.Mem.head _)
    have renamed := Derives.subst base swapXY
    simpa [rightContextLaw, bridgeLeftContextLaw, xy, xxxy,
      yx, yyyx, swapXY, Word.bind, Word.singleton, Word.append,
      Word.append_assoc]
      using renamed
  · have base :
        Derives bridgeBasis
          bridgeProductPowerLaw.lhs bridgeProductPowerLaw.rhs :=
      Derives.fromBasis (e := bridgeProductPowerLaw) <|
        List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)
    have renamed := Derives.subst base swapXY
    simpa [productPowerLaw, bridgeProductPowerLaw, xy, xyxyxy,
      yx, yxyxyx, swapXY, Word.bind, Word.singleton, Word.append,
      Word.append_assoc]
      using renamed
  · have base :
        Derives bridgeBasis
          bridgeRightContextLaw.lhs bridgeRightContextLaw.rhs :=
      Derives.fromBasis (e := bridgeRightContextLaw) <|
        List.Mem.tail _ (List.Mem.head _)
    have renamed := Derives.subst base swapXY
    simpa [leftContextLaw, bridgeRightContextLaw, xy, xyyy,
      yx, yxxx, swapXY, Word.bind, Word.singleton, Word.append,
      Word.append_assoc]
      using renamed
  · exact Derives.fromBasis (e := rightSquareReturnLaw) <|
      List.Mem.head _
  · exact Derives.fromBasis (e := middleSquareLaw) <|
      List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ (List.Mem.head _)

private theorem bridgeAxiomsDeriveBasis
    (identity : Identity Nat) (member : identity ∈ bridgeBasis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [bridgeBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Derives.fromBasis (e := rightSquareReturnLaw) <|
      List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)
  · have base :
        Derives basis leftContextLaw.lhs leftContextLaw.rhs :=
      Derives.fromBasis (e := leftContextLaw) <|
        List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)
    have renamed := Derives.subst base swapXY
    simpa [bridgeRightContextLaw, leftContextLaw, yx, yxxx,
      xy, xyyy, swapXY, Word.bind, Word.singleton, Word.append,
      Word.append_assoc]
      using renamed
  · have base :
        Derives basis productPowerLaw.lhs productPowerLaw.rhs :=
      Derives.fromBasis (e := productPowerLaw) <|
        List.Mem.tail _ (List.Mem.head _)
    have renamed := Derives.subst base swapXY
    simpa [bridgeProductPowerLaw, productPowerLaw, yx, yxyxyx,
      xy, xyxyxy, swapXY, Word.bind, Word.singleton, Word.append,
      Word.append_assoc]
      using renamed
  · have base :
        Derives basis rightContextLaw.lhs rightContextLaw.rhs :=
      Derives.fromBasis (e := rightContextLaw) <|
        List.Mem.head _
    have renamed := Derives.subst base swapXY
    simpa [bridgeLeftContextLaw, rightContextLaw, yx, yyyx,
      xy, xxxy, swapXY, Word.bind, Word.singleton, Word.append,
      Word.append_assoc]
      using renamed
  · exact Derives.fromBasis (e := middleSquareLaw) <|
      List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ (List.Mem.head _)

private theorem basisModelsOfBridge
    {S : Type u} {G : Semigroup S}
    (complete : BasisFor G bridgeBasis) :
    Models G basis := by
  intro identity member valuation
  exact
    Derives.sound complete.1
      (basisAxiomsDeriveBridge identity member) valuation

theorem basisCompleteOfBridge
    {S : Type u} {G : Semigroup S}
    (complete : BasisFor G bridgeBasis) :
    BasisFor G basis :=
  complete.replace (basisModelsOfBridge complete)
    bridgeAxiomsDeriveBasis

theorem basisCompleteOfReversedAffineParity
    {S : Type u} {G : Semigroup S}
    (complete :
      BasisFor G
        (reversedBasis SemigroupBasis.AffineParityInflation.basis)) :
    BasisFor G basis := by
  apply basisCompleteOfBridge
  rw [bridgeBasis_eq_reversedAffineParityBasis]
  exact complete

/--
Reverse both the source and target orientation of an inflation while keeping
the same element representatives.
-/
def oppositeTargetInflation
    {A : Type u} {B : Type v}
    {source : Semigroup A} {target : Semigroup B}
    (inflation : Inflation source.opposite target) :
    Inflation source target.opposite where
  embedding :=
    { toFun := inflation.embedding.toFun
      map_mul := by
        intro a b
        exact inflation.embedding.map_mul b a
      injective := inflation.embedding.injective }
  retract := inflation.retract
  retract_embedding := inflation.retract_embedding
  product_represented := by
    intro a b
    exact inflation.product_represented b a

theorem oppositeTargetInflation_proper
    {A : Type u} {B : Type v}
    {source : Semigroup A} {target : Semigroup B}
    {inflation : Inflation source.opposite target}
    (proper : inflation.Proper) :
    (oppositeTargetInflation inflation).Proper := by
  rcases proper with ⟨outside, outsideImage⟩
  exact ⟨outside, outsideImage⟩

/-- The recorded one-based image `[3,4,1,5]` embeds `S4_96ᵒᵖ`. -/
def embedding :
    Embedding SemigroupBasis.Generated.S4_96.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_562.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (2 : Fin 5)
    else if a = 1 then (3 : Fin 5)
    else if a = 2 then (0 : Fin 5)
    else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

/--
The recorded representatives are `[1,1,3,4,5]`; the corresponding source
retraction is `[3,3,1,2,4]`.
-/
def inflation :
    Inflation SemigroupBasis.Generated.S4_96.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_562.table.semigroup where
  embedding := embedding
  retract := fun b : Fin 5 =>
    if b = 0 then (2 : Fin 4)
    else if b = 1 then (2 : Fin 4)
    else if b = 2 then (0 : Fin 4)
    else if b = 3 then (1 : Fin 4)
    else (3 : Fin 4)
  retract_embedding := by
    intro a
    exact by decide +revert
  product_represented := by
    intro a b
    exact by decide +revert

def embeddingImageOneBased : List Nat :=
  List.ofFn fun a : Fin 4 => (embedding.toFun a).val + 1

theorem embeddingImageOneBased_certificate :
    embeddingImageOneBased = [3, 4, 1, 5] := by
  decide

def retractionRepresentativeImageOneBased : List Nat :=
  List.ofFn fun b : Fin 5 =>
    (embedding.toFun (inflation.retract b)).val + 1

theorem retractionRepresentativeImageOneBased_certificate :
    retractionRepresentativeImageOneBased = [1, 1, 3, 4, 5] := by
  decide

theorem proper : inflation.Proper := by
  refine ⟨(1 : Fin 5), ?_⟩
  intro a
  exact by decide +revert

theorem oriented_source_basis :
    BasisFor SemigroupBasis.Generated.S4_96.table.semigroup.opposite
      (reversedBasis affineParityFourBasis) :=
  SemigroupBasis.Generated.S4_96.opposite_basis

def proofInflation :
    Inflation SemigroupBasis.Generated.S4_96.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_562.table.semigroup.opposite :=
  oppositeTargetInflation inflation

theorem proofInflation_proper : proofInflation.Proper :=
  oppositeTargetInflation_proper proper

theorem target_opposite_affine_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_562.table.semigroup.opposite
      SemigroupBasis.AffineParityInflation.basis :=
  SemigroupBasis.Inflation.inheritAffineParityBasis
    proofInflation proofInflation_proper
      SemigroupBasis.Generated.S4_96.representative_basis

theorem reversed_affine_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_562.table.semigroup
      (reversedBasis SemigroupBasis.AffineParityInflation.basis) := by
  simpa using target_opposite_affine_basis.oppositeReversed

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_562.table.semigroup
      basis :=
  basisCompleteOfReversedAffineParity reversed_affine_basis

theorem opposite_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_562.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.S5_562
