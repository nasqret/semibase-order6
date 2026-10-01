import SemigroupBasis.TransferPower

namespace SemigroupBasis
namespace Semigroup

/-- An equivalence relation on a semigroup that is compatible with multiplication. -/
structure Congruence (G : Semigroup S) extends Setoid S where
  mul_compat :
    ∀ {a₁ a₂ b₁ b₂},
      r a₁ a₂ →
      r b₁ b₂ →
      r (G.mul a₁ b₁) (G.mul a₂ b₂)

namespace Congruence

/-- Congruences are ordered by containment of their underlying relations. -/
instance {S : Type u} {G : Semigroup S} : LE (Congruence G) where
  le C D := ∀ {a b : S}, C.r a b → D.r a b

theorem mul_compat_left {G : Semigroup S} (C : Congruence G)
    (a : S) {b c : S} (h : C.r b c) :
    C.r (G.mul a b) (G.mul a c) :=
  C.mul_compat (C.toSetoid.iseqv.refl a) h

theorem mul_compat_right {G : Semigroup S} (C : Congruence G)
    {a b : S} (h : C.r a b) (c : S) :
    C.r (G.mul a c) (G.mul b c) :=
  C.mul_compat h (C.toSetoid.iseqv.refl c)

/-- The carrier obtained by quotienting by a semigroup congruence. -/
abbrev Quotient {S : Type u} {G : Semigroup S}
    (C : Congruence G) : Type u :=
  _root_.Quotient C.toSetoid

/-- The equivalence class of an element. -/
def classOf {S : Type u} {G : Semigroup S} (C : Congruence G)
    (a : S) : C.Quotient :=
  _root_.Quotient.mk C.toSetoid a

/-- Multiplication on quotient classes before it is packaged as a semigroup. -/
def quotientMul {S : Type u} {G : Semigroup S}
    (C : Congruence G) (x y : C.Quotient) : C.Quotient :=
  _root_.Quotient.liftOn₂ x y
    (fun a b => C.classOf (G.mul a b))
    (by
      intro a₁ b₁ a₂ b₂ h₁ h₂
      exact _root_.Quotient.sound (C.mul_compat h₁ h₂))

/-- The semigroup structure induced on the quotient carrier. -/
def quotientSemigroup {S : Type u} {G : Semigroup S}
    (C : Congruence G) : Semigroup C.Quotient where
  mul := C.quotientMul
  assoc := by
    intro x y z
    refine _root_.Quotient.inductionOn x ?_
    intro a
    refine _root_.Quotient.inductionOn y ?_
    intro b
    refine _root_.Quotient.inductionOn z ?_
    intro c
    change
      C.classOf (G.mul (G.mul a b) c) =
        C.classOf (G.mul a (G.mul b c))
    exact congrArg C.classOf (G.assoc a b c)

@[simp]
theorem quotientSemigroup_mul_classOf {S : Type u} {G : Semigroup S}
    (C : Congruence G) (a b : S) :
    C.quotientSemigroup.mul (C.classOf a) (C.classOf b) =
      C.classOf (G.mul a b) :=
  rfl

/-- The canonical homomorphism from a semigroup to its congruence quotient. -/
def projection {S : Type u} {G : Semigroup S}
    (C : Congruence G) : Hom G C.quotientSemigroup where
  toFun := C.classOf
  map_mul := by
    intro a b
    rfl

@[simp]
theorem projection_apply {S : Type u} {G : Semigroup S}
    (C : Congruence G) (a : S) :
    C.projection.toFun a = C.classOf a :=
  rfl

/-- A homomorphism constant on congruence classes descends to the quotient. -/
def lift {S : Type u} {T : Type v} {G : Semigroup S} {H : Semigroup T}
    (C : Congruence G) (f : Hom G H)
    (identifies : ∀ {a b : S}, C.r a b → f.toFun a = f.toFun b) :
    Hom C.quotientSemigroup H where
  toFun := _root_.Quotient.lift f.toFun (by
    intro a b h
    exact identifies h)
  map_mul := by
    intro x y
    refine _root_.Quotient.inductionOn x ?_
    intro a
    refine _root_.Quotient.inductionOn y ?_
    intro b
    exact f.map_mul a b

@[simp]
theorem lift_classOf {S : Type u} {T : Type v}
    {G : Semigroup S} {H : Semigroup T}
    (C : Congruence G) (f : Hom G H)
    (identifies : ∀ {a b : S}, C.r a b → f.toFun a = f.toFun b)
    (a : S) :
    (C.lift f identifies).toFun (C.classOf a) = f.toFun a :=
  rfl

/-- Related elements determine the same quotient class. -/
theorem sound {S : Type u} {G : Semigroup S} (C : Congruence G)
    {a b : S} (h : C.r a b) :
    C.classOf a = C.classOf b :=
  _root_.Quotient.sound h

/-- Equality of quotient classes is exactly the congruence relation. -/
theorem classOf_eq_iff {S : Type u} {G : Semigroup S}
    (C : Congruence G) {a b : S} :
    C.classOf a = C.classOf b ↔ C.r a b := by
  constructor
  · intro h
    exact _root_.Quotient.exact h
  · intro h
    exact C.sound h

theorem projection_sound {S : Type u} {G : Semigroup S}
    (C : Congruence G) {a b : S} (h : C.r a b) :
    C.projection.toFun a = C.projection.toFun b :=
  C.sound h

theorem projection_eq_iff {S : Type u} {G : Semigroup S}
    (C : Congruence G) {a b : S} :
    C.projection.toFun a = C.projection.toFun b ↔ C.r a b :=
  C.classOf_eq_iff

/-- Containment of congruences induces the canonical map between quotients. -/
def factor {S : Type u} {G : Semigroup S}
    (C D : Congruence G) (hCD : C ≤ D) :
    Hom C.quotientSemigroup D.quotientSemigroup :=
  C.lift D.projection (by
    intro a b h
    exact D.projection_sound (hCD h))

@[simp]
theorem factor_classOf {S : Type u} {G : Semigroup S}
    (C D : Congruence G) (hCD : C ≤ D) (a : S) :
    (C.factor D hCD).toFun (C.classOf a) = D.classOf a :=
  rfl

theorem projection_surjective {S : Type u} {G : Semigroup S}
    (C : Congruence G) : Function.Surjective C.projection.toFun := by
  intro q
  refine _root_.Quotient.inductionOn q ?_
  intro a
  exact ⟨a, rfl⟩

/-- The canonical projection, equipped with a chosen representative of each class. -/
noncomputable def projectionSplitSurjection
    {S : Type u} {G : Semigroup S} (C : Congruence G) :
    SplitSurjection G C.quotientSemigroup where
  toFun := C.projection.toFun
  map_mul := C.projection.map_mul
  preimage := fun q => Classical.choose (C.projection_surjective q)
  right_inverse := fun q =>
    Classical.choose_spec (C.projection_surjective q)

end Congruence
end Semigroup
end SemigroupBasis
