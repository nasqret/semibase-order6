import SemigroupBasis.GroupLikeCollapse
import SemigroupBasis.InverseSemigroup
import SemigroupBasis.MatrixUnits

namespace SemigroupBasis
namespace Semigroup

/-- A two-sided zero element of an explicitly supplied semigroup. -/
def IsZero (G : Semigroup S) (z : S) : Prop :=
  (∀ x, G.mul z x = z) ∧ (∀ x, G.mul x z = z)

namespace IsZero

theorem unique {G : Semigroup S} {a b : S}
    (ha : G.IsZero a) (hb : G.IsZero b) : a = b := by
  calc
    a = G.mul a b := (ha.1 b).symm
    _ = b := hb.2 a

theorem mul_right_isZero {G : Semigroup S} {z : S}
    (hz : G.IsZero z) (x : S) : G.IsZero (G.mul z x) := by
  rw [hz.1 x]
  exact hz

theorem mul_left_isZero {G : Semigroup S} {z : S}
    (hz : G.IsZero z) (x : S) : G.IsZero (G.mul x z) := by
  rw [hz.2 x]
  exact hz

end IsZero

/-- Distinct idempotents multiply to a zero element. -/
def IdempotentsOrthogonal (G : Semigroup S) : Prop :=
  ∀ {e f}, G.IsIdempotent e → G.IsIdempotent f → e ≠ f →
    G.IsZero (G.mul e f)

/-- In an inverse semigroup satisfying `x^2 = x^3`, range and source
idempotents jointly determine an element. -/
theorem IsInverseSemigroup.eq_of_range_eq_source_eq
    {G : Semigroup S} (inverseSemigroup : G.IsInverseSemigroup)
    (squareEqualsCube : G.SquareEqualsCube) {a b : S}
    (rangeEq : inverseSemigroup.range a = inverseSemigroup.range b)
    (sourceEq : inverseSemigroup.source a = inverseSemigroup.source b) :
    a = b := by
  let c := G.mul (inverseSemigroup.inverse a) b
  have rangeC : inverseSemigroup.range c = inverseSemigroup.source a := by
    change
      G.mul (G.mul (inverseSemigroup.inverse a) b)
          (inverseSemigroup.inverse
            (G.mul (inverseSemigroup.inverse a) b)) =
        G.mul (inverseSemigroup.inverse a) a
    rw [inverseSemigroup.inverse_mul, inverseSemigroup.inverse_inverse]
    calc
      G.mul (G.mul (inverseSemigroup.inverse a) b)
          (G.mul (inverseSemigroup.inverse b) a) =
          G.mul (inverseSemigroup.inverse a)
            (G.mul (inverseSemigroup.range b) a) := by
        simp only [IsInverseSemigroup.range, G.assoc]
      _ = G.mul (inverseSemigroup.inverse a)
          (G.mul (inverseSemigroup.range a) a) := by
        rw [rangeEq]
      _ = G.mul (inverseSemigroup.inverse a) a := by
        rw [inverseSemigroup.range_mul_eq]
  have sourceC : inverseSemigroup.source c = inverseSemigroup.source b := by
    change
      G.mul
          (inverseSemigroup.inverse
            (G.mul (inverseSemigroup.inverse a) b))
          (G.mul (inverseSemigroup.inverse a) b) =
        G.mul (inverseSemigroup.inverse b) b
    rw [inverseSemigroup.inverse_mul, inverseSemigroup.inverse_inverse]
    calc
      G.mul (G.mul (inverseSemigroup.inverse b) a)
          (G.mul (inverseSemigroup.inverse a) b) =
          G.mul (inverseSemigroup.inverse b)
            (G.mul (inverseSemigroup.range a) b) := by
        simp only [IsInverseSemigroup.range, G.assoc]
      _ = G.mul (inverseSemigroup.inverse b)
          (G.mul (inverseSemigroup.range b) b) := by
        rw [rangeEq]
      _ = G.mul (inverseSemigroup.inverse b) b := by
        rw [inverseSemigroup.range_mul_eq]
  have rangeSourceC :
      inverseSemigroup.range c = inverseSemigroup.source c := by
    calc
      inverseSemigroup.range c = inverseSemigroup.source a := rangeC
      _ = inverseSemigroup.source b := sourceEq
      _ = inverseSemigroup.source c := sourceC.symm
  have inverseMulSquare :
      G.mul (inverseSemigroup.inverse c) (G.mul c c) = c := by
    calc
      G.mul (inverseSemigroup.inverse c) (G.mul c c) =
          G.mul (G.mul (inverseSemigroup.inverse c) c) c :=
        (G.assoc _ _ _).symm
      _ = G.mul (inverseSemigroup.source c) c := rfl
      _ = G.mul (inverseSemigroup.range c) c := by
        rw [rangeSourceC]
      _ = c := inverseSemigroup.range_mul_eq c
  have cEqSquare : c = G.mul c c := by
    calc
      c = G.mul (inverseSemigroup.inverse c) (G.mul c c) :=
        inverseMulSquare.symm
      _ = G.mul (inverseSemigroup.inverse c)
          (G.mul (G.mul c c) c) := by
        exact congrArg (fun value => G.mul (inverseSemigroup.inverse c) value)
          (squareEqualsCube c)
      _ = G.mul
          (G.mul (inverseSemigroup.inverse c) (G.mul c c)) c :=
        (G.assoc _ _ _).symm
      _ = G.mul c c :=
        congrArg (fun value => G.mul value c) inverseMulSquare
  have cIdempotent : G.IsIdempotent c := cEqSquare.symm
  have cEqRange : c = inverseSemigroup.range c := by
    change c = G.mul c (inverseSemigroup.inverse c)
    rw [inverseSemigroup.inverse_eq_self_of_isIdempotent cIdempotent]
    exact cIdempotent.symm
  have cEqSourceA : c = inverseSemigroup.source a :=
    cEqRange.trans rangeC
  calc
    a = G.mul a (inverseSemigroup.source a) :=
      (inverseSemigroup.mul_source_eq a).symm
    _ = G.mul a c := by rw [cEqSourceA]
    _ = G.mul a (G.mul (inverseSemigroup.inverse a) b) := rfl
    _ = G.mul (G.mul a (inverseSemigroup.inverse a)) b :=
      (G.assoc _ _ _).symm
    _ = G.mul (inverseSemigroup.range a) b := rfl
    _ = G.mul (inverseSemigroup.range b) b := by rw [rangeEq]
    _ = b := inverseSemigroup.range_mul_eq b

/-- An inverse semigroup with orthogonal idempotents and `x^2 = x^3`
embeds into matrix units indexed by its nonzero idempotents. -/
theorem exists_matrixUnitEmbedding
    {S : Type u} {G : Semigroup S}
    (inverseSemigroup : G.IsInverseSemigroup)
    (orthogonal : G.IdempotentsOrthogonal)
    (squareEqualsCube : G.SquareEqualsCube) :
    ∃ (I : Type u) (decEq : DecidableEq I),
      Nonempty (Embedding G (@MatrixUnit.semigroup I decEq)) := by
  classical
  let I := {e : S // G.IsIdempotent e ∧ ¬ G.IsZero e}
  let decEq : DecidableEq I := inferInstance
  have rangeNotZero :
      ∀ {x : S}, ¬ G.IsZero x → ¬ G.IsZero (inverseSemigroup.range x) := by
    intro x xNotZero rangeZero
    apply xNotZero
    have xEqRange : x = inverseSemigroup.range x := by
      calc
        x = G.mul (inverseSemigroup.range x) x :=
          (inverseSemigroup.range_mul_eq x).symm
        _ = inverseSemigroup.range x := rangeZero.1 x
    rw [xEqRange]
    exact rangeZero
  have sourceNotZero :
      ∀ {x : S}, ¬ G.IsZero x → ¬ G.IsZero (inverseSemigroup.source x) := by
    intro x xNotZero sourceZero
    apply xNotZero
    have xEqSource : x = inverseSemigroup.source x := by
      calc
        x = G.mul x (inverseSemigroup.source x) :=
          (inverseSemigroup.mul_source_eq x).symm
        _ = inverseSemigroup.source x := sourceZero.2 x
    rw [xEqSource]
    exact sourceZero
  let rangeIndex : ∀ (x : S), ¬ G.IsZero x → I :=
    fun x xNotZero =>
      ⟨inverseSemigroup.range x,
        inverseSemigroup.range_isIdempotent x,
        rangeNotZero xNotZero⟩
  let sourceIndex : ∀ (x : S), ¬ G.IsZero x → I :=
    fun x xNotZero =>
      ⟨inverseSemigroup.source x,
        inverseSemigroup.source_isIdempotent x,
        sourceNotZero xNotZero⟩
  let toFun : S → MatrixUnit I := fun x =>
    if xZero : G.IsZero x then
      MatrixUnit.zero
    else
      MatrixUnit.ofIndices (rangeIndex x xZero) (sourceIndex x xZero)
  refine ⟨I, decEq, ⟨{
    toFun := toFun
    map_mul := ?_
    injective := ?_
  }⟩⟩
  · intro x y
    change toFun (G.mul x y) =
      MatrixUnit.mul (toFun x) (toFun y)
    by_cases xZero : G.IsZero x
    · have productZero : G.IsZero (G.mul x y) :=
        xZero.mul_right_isZero y
      simp [toFun, xZero, productZero, MatrixUnit.zero,
        MatrixUnit.ofIndices, MatrixUnit.mul]
    by_cases yZero : G.IsZero y
    · have productZero : G.IsZero (G.mul x y) :=
        yZero.mul_left_isZero x
      simp [toFun, xZero, yZero, productZero, MatrixUnit.zero,
        MatrixUnit.ofIndices, MatrixUnit.mul]
    by_cases coordinatesMatch :
        inverseSemigroup.source x = inverseSemigroup.range y
    · have rangeProduct :
          inverseSemigroup.range (G.mul x y) =
            inverseSemigroup.range x := by
        change
          G.mul (G.mul x y)
              (inverseSemigroup.inverse (G.mul x y)) =
            G.mul x (inverseSemigroup.inverse x)
        rw [inverseSemigroup.inverse_mul]
        calc
          G.mul (G.mul x y)
              (G.mul (inverseSemigroup.inverse y)
                (inverseSemigroup.inverse x)) =
              G.mul x
                (G.mul (inverseSemigroup.range y)
                  (inverseSemigroup.inverse x)) := by
            simp only [IsInverseSemigroup.range, G.assoc]
          _ = G.mul x
              (G.mul (inverseSemigroup.source x)
                (inverseSemigroup.inverse x)) := by
            rw [← coordinatesMatch]
          _ = G.mul (G.mul x (inverseSemigroup.source x))
              (inverseSemigroup.inverse x) :=
            (G.assoc _ _ _).symm
          _ = G.mul x (inverseSemigroup.inverse x) := by
            rw [inverseSemigroup.mul_source_eq]
      have sourceProduct :
          inverseSemigroup.source (G.mul x y) =
            inverseSemigroup.source y := by
        change
          G.mul (inverseSemigroup.inverse (G.mul x y))
              (G.mul x y) =
            G.mul (inverseSemigroup.inverse y) y
        rw [inverseSemigroup.inverse_mul]
        calc
          G.mul
              (G.mul (inverseSemigroup.inverse y)
                (inverseSemigroup.inverse x))
              (G.mul x y) =
              G.mul (inverseSemigroup.inverse y)
                (G.mul (inverseSemigroup.source x) y) := by
            simp only [IsInverseSemigroup.source, G.assoc]
          _ = G.mul (inverseSemigroup.inverse y)
              (G.mul (inverseSemigroup.range y) y) := by
            rw [coordinatesMatch]
          _ = G.mul (inverseSemigroup.inverse y) y := by
            rw [inverseSemigroup.range_mul_eq]
      have productNotZero : ¬ G.IsZero (G.mul x y) := by
        intro productZero
        apply xZero
        have xEqProduct : x = G.mul x y := by
          calc
            x = G.mul x (inverseSemigroup.source x) :=
              (inverseSemigroup.mul_source_eq x).symm
            _ = G.mul x (inverseSemigroup.range y) := by
              rw [coordinatesMatch]
            _ = G.mul x
                (G.mul y (inverseSemigroup.inverse y)) := rfl
            _ = G.mul (G.mul x y) (inverseSemigroup.inverse y) :=
              (G.assoc _ _ _).symm
            _ = G.mul x y := productZero.1 _
        rw [xEqProduct]
        exact productZero
      have middleIndexEq :
          sourceIndex x xZero = rangeIndex y yZero :=
        Subtype.ext coordinatesMatch
      have rangeIndexEq :
          rangeIndex (G.mul x y) productNotZero = rangeIndex x xZero :=
        Subtype.ext rangeProduct
      have sourceIndexEq :
          sourceIndex (G.mul x y) productNotZero = sourceIndex y yZero :=
        Subtype.ext sourceProduct
      simp [toFun, xZero, yZero, productNotZero, MatrixUnit.zero,
        MatrixUnit.ofIndices, MatrixUnit.mul, middleIndexEq, rangeIndexEq,
        sourceIndexEq]
    · have middleZero :
          G.IsZero
            (G.mul (inverseSemigroup.source x)
              (inverseSemigroup.range y)) :=
        orthogonal
          (inverseSemigroup.source_isIdempotent x)
          (inverseSemigroup.range_isIdempotent y)
          coordinatesMatch
      have productEqMiddle :
          G.mul x y =
            G.mul (inverseSemigroup.source x)
              (inverseSemigroup.range y) := by
        calc
          G.mul x y =
              G.mul (G.mul x (inverseSemigroup.source x))
                (G.mul (inverseSemigroup.range y) y) := by
            rw [inverseSemigroup.mul_source_eq,
              inverseSemigroup.range_mul_eq]
          _ = G.mul x
              (G.mul (inverseSemigroup.source x)
                (G.mul (inverseSemigroup.range y) y)) :=
            G.assoc _ _ _
          _ = G.mul x
              (G.mul
                (G.mul (inverseSemigroup.source x)
                  (inverseSemigroup.range y)) y) := by
            rw [G.assoc]
          _ = G.mul x
              (G.mul (inverseSemigroup.source x)
                (inverseSemigroup.range y)) := by
            rw [middleZero.1]
          _ = G.mul (inverseSemigroup.source x)
              (inverseSemigroup.range y) := middleZero.2 x
      have productZero : G.IsZero (G.mul x y) := by
        rw [productEqMiddle]
        exact middleZero
      have middleIndexNe :
          sourceIndex x xZero ≠ rangeIndex y yZero := by
        intro indexEq
        apply coordinatesMatch
        exact congrArg (fun index : I => index.1) indexEq
      simp [toFun, xZero, yZero, productZero, MatrixUnit.zero,
        MatrixUnit.ofIndices, MatrixUnit.mul, middleIndexNe]
  · intro a b imagesEqual
    by_cases aZero : G.IsZero a
    · by_cases bZero : G.IsZero b
      · exact aZero.unique bZero
      · have impossible :
            (none : MatrixUnit I) =
              some (rangeIndex b bZero, sourceIndex b bZero) := by
          simpa [toFun, aZero, bZero, MatrixUnit.zero,
            MatrixUnit.ofIndices] using imagesEqual
        cases impossible
    · by_cases bZero : G.IsZero b
      · have impossible :
            some (rangeIndex a aZero, sourceIndex a aZero) =
              (none : MatrixUnit I) := by
          simpa [toFun, aZero, bZero, MatrixUnit.zero,
            MatrixUnit.ofIndices] using imagesEqual
        cases impossible
      · have pairEq :
            (rangeIndex a aZero, sourceIndex a aZero) =
              (rangeIndex b bZero, sourceIndex b bZero) := by
          exact Option.some.inj <| by
            simpa [toFun, aZero, bZero, MatrixUnit.zero,
              MatrixUnit.ofIndices] using imagesEqual
        have rangeIndexEq := congrArg Prod.fst pairEq
        have sourceIndexEq := congrArg Prod.snd pairEq
        have rangeEq :
            inverseSemigroup.range a = inverseSemigroup.range b :=
          congrArg (fun index : I => index.1) rangeIndexEq
        have sourceEq :
            inverseSemigroup.source a = inverseSemigroup.source b :=
          congrArg (fun index : I => index.1) sourceIndexEq
        exact inverseSemigroup.eq_of_range_eq_source_eq
          squareEqualsCube rangeEq sourceEq

end Semigroup
end SemigroupBasis
