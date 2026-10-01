import SemigroupBasis.CoRoots.Order6Day15.B33.B33Tables

namespace SemigroupBasis.CoRoots.Order6Day15.B33

theorem sound6225_01 (x : Fin 6) :
    (mul6225 x x) = (mul6225 (mul6225 (mul6225 x x) x) x) :=
  (by decide : ∀ x : Fin 6, (mul6225 x x) = (mul6225 (mul6225 (mul6225 x x) x) x)) x

theorem sound6225_02 (x y : Fin 6) :
    (mul6225 (mul6225 x y) x) = (mul6225 (mul6225 (mul6225 (mul6225 x x) y) y) y) :=
  (by decide : ∀ x y : Fin 6, (mul6225 (mul6225 x y) x) = (mul6225 (mul6225 (mul6225 (mul6225 x x) y) y) y)) x y

theorem sound6225_03 (x y z : Fin 6) :
    (mul6225 (mul6225 x y) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) y) y) z) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 x y) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) y) y) z)) x y z

theorem sound6225_04 (x y : Fin 6) :
    (mul6225 (mul6225 x y) x) = (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) x) :=
  (by decide : ∀ x y : Fin 6, (mul6225 (mul6225 x y) x) = (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) x)) x y

theorem sound6225_05 (x y : Fin 6) :
    (mul6225 (mul6225 x y) x) = (mul6225 (mul6225 (mul6225 (mul6225 x x) y) x) x) :=
  (by decide : ∀ x y : Fin 6, (mul6225 (mul6225 x y) x) = (mul6225 (mul6225 (mul6225 (mul6225 x x) y) x) x)) x y

theorem sound6225_06 (x y : Fin 6) :
    (mul6225 (mul6225 x y) x) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) x) x) :=
  (by decide : ∀ x y : Fin 6, (mul6225 (mul6225 x y) x) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) x) x)) x y

theorem sound6225_07 (x y : Fin 6) :
    (mul6225 (mul6225 x y) x) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) y) y) :=
  (by decide : ∀ x y : Fin 6, (mul6225 (mul6225 x y) x) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) y) y)) x y

theorem sound6225_08 (x y : Fin 6) :
    (mul6225 (mul6225 x y) x) = (mul6225 (mul6225 (mul6225 (mul6225 x y) y) x) y) :=
  (by decide : ∀ x y : Fin 6, (mul6225 (mul6225 x y) x) = (mul6225 (mul6225 (mul6225 (mul6225 x y) y) x) y)) x y

theorem sound6225_09 (x y : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) y) = (mul6225 (mul6225 (mul6225 (mul6225 x x) y) x) y) :=
  (by decide : ∀ x y : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) y) = (mul6225 (mul6225 (mul6225 (mul6225 x x) y) x) y)) x y

theorem sound6225_10 (x y : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) y) = (mul6225 (mul6225 (mul6225 (mul6225 x x) y) y) x) :=
  (by decide : ∀ x y : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) y) = (mul6225 (mul6225 (mul6225 (mul6225 x x) y) y) x)) x y

theorem sound6225_11 (x y : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) x) y) :=
  (by decide : ∀ x y : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) x) y)) x y

theorem sound6225_12 (x y : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) y) x) :=
  (by decide : ∀ x y : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) y) x)) x y

theorem sound6225_13 (x y : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) y) x) x) :=
  (by decide : ∀ x y : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) y) x) x)) x y

theorem sound6225_14 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) z) = (mul6225 (mul6225 (mul6225 (mul6225 x x) y) x) z) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) z) = (mul6225 (mul6225 (mul6225 (mul6225 x x) y) x) z)) x y z

theorem sound6225_15 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) x) z) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) x) y) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) x) z)) x y z

theorem sound6225_16 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) y) y) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) y) z) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) y) y) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) y) z)) x y z

theorem sound6225_17 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) y) y) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) y) x) z) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) y) y) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) y) x) z)) x y z

theorem sound6225_18 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) x) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) z) x) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) x) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) z) x)) x y z

theorem sound6225_19 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) x) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) x) x) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) x) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) x) x)) x y z

theorem sound6225_20 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) z) y) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) z) y)) x y z

theorem sound6225_21 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) y) z) x) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) y) z) x)) x y z

theorem sound6225_22 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) x) y) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) x) y)) x y z

theorem sound6225_23 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) y) x) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) y) x)) x y z

theorem sound6225_24 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) z) z) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) z) z)) x y z

theorem sound6225_25 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) x) z) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) x) z)) x y z

theorem sound6225_26 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) z) x) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) z) x)) x y z

theorem sound6225_27 (x y z t : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) t) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) z) t) :=
  (by decide : ∀ x y z t : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) t) = (mul6225 (mul6225 (mul6225 (mul6225 x y) x) z) t)) x y z t

theorem sound6225_28 (x y z t : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) t) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) x) t) :=
  (by decide : ∀ x y z t : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x x) y) z) t) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) x) t)) x y z t

theorem sound6225_29 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x y) y) z) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) y) y) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x y) y) z) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) y) y)) x y z

theorem sound6225_30 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x y) y) z) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) z) z) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x y) y) z) y) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) z) z)) x y z

theorem sound6225_31 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x y) y) z) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) y) z) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x y) y) z) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) y) z)) x y z

theorem sound6225_32 (x y z : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x y) y) z) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) z) y) :=
  (by decide : ∀ x y z : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x y) y) z) z) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) z) y)) x y z

theorem sound6225_33 (x y z t : Fin 6) :
    (mul6225 (mul6225 (mul6225 (mul6225 x y) y) z) t) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) y) t) :=
  (by decide : ∀ x y z t : Fin 6, (mul6225 (mul6225 (mul6225 (mul6225 x y) y) z) t) = (mul6225 (mul6225 (mul6225 (mul6225 x y) z) y) t)) x y z t

theorem models6225 : Models table6225.semigroup basis := by
  intro e member
  simp only [basis,
    SemigroupBasis.CoRoots.Order6Sunday.Msg0513B33FiveSlotCountermodel.basis,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro v
    exact sound6225_01 (v 0)
  · intro v
    exact sound6225_02 (v 0) (v 1)
  · intro v
    exact sound6225_03 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_04 (v 0) (v 1)
  · intro v
    exact sound6225_05 (v 0) (v 1)
  · intro v
    exact sound6225_06 (v 0) (v 1)
  · intro v
    exact sound6225_07 (v 0) (v 1)
  · intro v
    exact sound6225_08 (v 0) (v 1)
  · intro v
    exact sound6225_09 (v 0) (v 1)
  · intro v
    exact sound6225_10 (v 0) (v 1)
  · intro v
    exact sound6225_11 (v 0) (v 1)
  · intro v
    exact sound6225_12 (v 0) (v 1)
  · intro v
    exact sound6225_13 (v 0) (v 1)
  · intro v
    exact sound6225_14 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_15 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_16 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_17 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_18 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_19 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_20 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_21 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_22 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_23 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_24 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_25 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_26 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_27 (v 0) (v 1) (v 2) (v 3)
  · intro v
    exact sound6225_28 (v 0) (v 1) (v 2) (v 3)
  · intro v
    exact sound6225_29 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_30 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_31 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_32 (v 0) (v 1) (v 2)
  · intro v
    exact sound6225_33 (v 0) (v 1) (v 2) (v 3)

end SemigroupBasis.CoRoots.Order6Day15.B33
