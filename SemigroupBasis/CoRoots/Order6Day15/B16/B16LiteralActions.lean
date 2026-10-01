import SemigroupBasis.CoRoots.Order6Day15.B16.B16ContinuationKey
import SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Literal

abbrev s6432 : Semigroup (Fin 6) :=
  SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite.S6_6432.table.semigroup

abbrev s6439 : Semigroup (Fin 6) :=
  SemigroupBasis.CoRoots.Order6Sunday.Msg0514RepairedSixteenLawFinite.S6_6439.table.semigroup

def split6432 : SplitAction s6432 where
  zero := 0
  Pos := fun a => 3 ≤ a.val
  Low := fun a => a.val < 3
  cover := by decide
  zero_low := by decide
  zero_mul := by decide
  mul_zero := by decide
  positive_positive := by decide
  positive_low := by decide
  low_positive := by decide
  low_low := by decide

def split6439 : SplitAction s6439 where
  zero := 0
  Pos := fun a => 3 ≤ a.val
  Low := fun a => a.val < 3
  cover := by decide
  zero_low := by decide
  zero_mul := by decide
  mul_zero := by decide
  positive_positive := by decide
  positive_low := by decide
  low_positive := by decide
  low_low := by decide

def positiveEmbed (a : Fin 3) : Fin 6 :=
  ⟨a.val + 3, Nat.add_lt_add_right a.isLt 3⟩

def idealEmbed (i : Fin 2) : Fin 6 := if i = 0 then 1 else 2

theorem positiveEmbed_injective : Function.Injective positiveEmbed := by
  have checked : ∀ a b : Fin 3, positiveEmbed a = positiveEmbed b → a = b := by decide
  intro a b h
  exact checked a b h

theorem positiveEmbed_hom6432 : ∀ a b : Fin 3,
    s6432.mul (positiveEmbed a) (positiveEmbed b) = positiveEmbed (positive.mul a b) := by
  decide

theorem positiveEmbed_hom6439 : ∀ a b : Fin 3,
    s6439.mul (positiveEmbed a) (positiveEmbed b) = positiveEmbed (positive.mul a b) := by
  decide

/-- Code0 is empty action; codes1,2,3 are the three positive products. -/
def continuationCode : Option (Fin 3) → Fin 4
  | none => 0
  | some a => ⟨a.val + 1, Nat.add_lt_add_right a.isLt 1⟩

theorem continuationCode_injective : Function.Injective continuationCode := by
  intro p q h
  cases p with
  | none =>
      cases q with
      | none => rfl
      | some b =>
          have checked : ∀ b : Fin 3, continuationCode none ≠ continuationCode (some b) := by decide
          exact False.elim (checked b h)
  | some a =>
      cases q with
      | none =>
          have checked : ∀ a : Fin 3, continuationCode (some a) ≠ continuationCode none := by decide
          exact False.elim (checked a h)
      | some b =>
          have checked : ∀ a b : Fin 3,
              continuationCode (some a) = continuationCode (some b) → a = b := by decide
          exact congrArg some (checked a b h)

def continuationAction (S : Semigroup (Fin 6)) : Fin 4 → Fin 2 → Fin 6
  | 0, i => idealEmbed i
  | 1, i => S.mul (idealEmbed i) (positiveEmbed 0)
  | 2, i => S.mul (idealEmbed i) (positiveEmbed 1)
  | _, i => S.mul (idealEmbed i) (positiveEmbed 2)

theorem action6432_injective : Function.Injective (continuationAction s6432) := by
  have checked : ∀ p q : Fin 4,
      (∀ i : Fin 2, continuationAction s6432 p i = continuationAction s6432 q i) → p = q := by decide
  intro p q h
  exact checked p q (fun i => congrFun h i)

theorem action6439_injective : Function.Injective (continuationAction s6439) := by
  have checked : ∀ p q : Fin 4,
      (∀ i : Fin 2, continuationAction s6439 p i = continuationAction s6439 q i) → p = q := by decide
  intro p q h
  exact checked p q (fun i => congrFun h i)

def optionalAction (S : Semigroup (Fin 6)) (p : Option (Fin 3)) : Fin 2 → Fin 6 :=
  continuationAction S (continuationCode p)

theorem optionalAction_empty (S : Semigroup (Fin 6)) (i : Fin 2) :
    optionalAction S none i = idealEmbed i := rfl

theorem optionalAction_some6432 : ∀ (p : Fin 3) (i : Fin 2),
    optionalAction s6432 (some p) i = s6432.mul (idealEmbed i) (positiveEmbed p) := by decide

theorem optionalAction_some6439 : ∀ (p : Fin 3) (i : Fin 2),
    optionalAction s6439 (some p) i = s6439.mul (idealEmbed i) (positiveEmbed p) := by decide

theorem optionalAction_faithful6432 (p q : Option (Fin 3))
    (h : ∀ i : Fin 2, optionalAction s6432 p i = optionalAction s6432 q i) : p = q := by
  have actions : continuationAction s6432 (continuationCode p) =
      continuationAction s6432 (continuationCode q) := funext h
  exact continuationCode_injective (action6432_injective actions)

theorem optionalAction_faithful6439 (p q : Option (Fin 3))
    (h : ∀ i : Fin 2, optionalAction s6439 p i = optionalAction s6439 q i) : p = q := by
  have actions : continuationAction s6439 (continuationCode p) =
      continuationAction s6439 (continuationCode q) := funext h
  exact continuationCode_injective (action6439_injective actions)

theorem sections6432 (xs : List (Fin 6)) : ValueSections split6432 xs :=
  value_sections split6432 xs

theorem sections6439 (xs : List (Fin 6)) : ValueSections split6439 xs :=
  value_sections split6439 xs

theorem oneLow6432 (pre post : List (Fin 6)) (i : Fin 6)
    (hi : i.val < 3) (hp : ∀ x ∈ pre, 3 ≤ x.val) :
    evalValues s6432 (pre ++ i :: post) = some (runTail s6432 i post) :=
  evalValues_one_low split6432 pre post i hi hp

theorem oneLow6439 (pre post : List (Fin 6)) (i : Fin 6)
    (hi : i.val < 3) (hp : ∀ x ∈ pre, 3 ≤ x.val) :
    evalValues s6439 (pre ++ i :: post) = some (runTail s6439 i post) :=
  evalValues_one_low split6439 pre post i hi hp

theorem twoLow6432 (pre mid post : List (Fin 6)) (i j : Fin 6)
    (hi : i.val < 3) (hj : j.val < 3) :
    evalValues s6432 (pre ++ i :: (mid ++ j :: post)) = some 0 :=
  evalValues_two_low split6432 pre mid post i j hi hj

theorem twoLow6439 (pre mid post : List (Fin 6)) (i j : Fin 6)
    (hi : i.val < 3) (hj : j.val < 3) :
    evalValues s6439 (pre ++ i :: (mid ++ j :: post)) = some 0 :=
  evalValues_two_low split6439 pre mid post i j hi hj

theorem samePKey_action6432 {u v : Word Nat} (h : SamePKey u v)
    (rho : Nat → Fin 3) (a : Fin 6) :
    runTail s6432 a (u.toList.map (fun x => positiveEmbed (rho x))) =
      runTail s6432 a (v.toList.map (fun x => positiveEmbed (rho x))) :=
  samePKey_continuation s6432 positiveEmbed positiveEmbed_hom6432 h rho a

theorem samePKey_action6439 {u v : Word Nat} (h : SamePKey u v)
    (rho : Nat → Fin 3) (a : Fin 6) :
    runTail s6439 a (u.toList.map (fun x => positiveEmbed (rho x))) =
      runTail s6439 a (v.toList.map (fun x => positiveEmbed (rho x))) :=
  samePKey_continuation s6439 positiveEmbed positiveEmbed_hom6439 h rho a

end SemigroupBasis.CoRoots.Order6Day15.B16.Literal
