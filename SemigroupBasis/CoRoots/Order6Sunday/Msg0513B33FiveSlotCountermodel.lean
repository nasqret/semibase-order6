import SemigroupBasis.FiniteCertificate
import SemigroupBasis.TransferPower
import SemigroupBasis.Generated.CatalogueOrder3

/-!
Negative boundary for the literal uniform five-letter normal form proposed in
the msg-0513 kit for S6_6225/S6_9878.  This is not a refutation of B33, a
separation of the reported M7 gap pairs, or a completeness endpoint.

The already-certified catalogue semigroup S3_10 records absent / positive-even /
odd occurrences.  Its fourth power models the unchanged ordered 33 laws.  The
word xxyztz has no representative of length at most five in this model, hence
no such representative is derivable from B33.  Other natural-number letters
are sent to the identity, so the negative theorem is not limited to four
variable names.  A variable-length, five-block recipe is a different claim.

The only exhaustive proof steps below have explicitly finite inputs.  Their
initial resource bounds are fixed here, before the first warm invocation.
-/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0513B33FiveSlotCountermodel

/-- Exact ordered basis from the completed job 21787442; x=0, y=1, z=2, t=3. -/
def basis : List (Identity Nat) :=
  [ ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩, -- L01 xx=xxxx
    ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1, 1]⟩⟩, -- L02 xyx=xxyyy
    ⟨⟨0, [1, 2]⟩, ⟨0, [1, 1, 1, 2]⟩⟩, -- L03 xyz=xyyyz
    ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 1, 0]⟩⟩, -- L04 xyx=xxxyx
    ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0, 0]⟩⟩, -- L05 xyx=xxyxx
    ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩, -- L06 xyx=xyxxx
    ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1, 1]⟩⟩, -- L07 xyx=xyxyy
    ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0, 1]⟩⟩, -- L08 xyx=xyyxy
    ⟨⟨0, [0, 0, 1, 1]⟩, ⟨0, [0, 1, 0, 1]⟩⟩, -- L09 xxxyy=xxyxy
    ⟨⟨0, [0, 0, 1, 1]⟩, ⟨0, [0, 1, 1, 0]⟩⟩, -- L10 xxxyy=xxyyx
    ⟨⟨0, [0, 0, 1, 1]⟩, ⟨0, [1, 0, 0, 1]⟩⟩, -- L11 xxxyy=xyxxy
    ⟨⟨0, [0, 0, 1, 1]⟩, ⟨0, [1, 0, 1, 0]⟩⟩, -- L12 xxxyy=xyxyx
    ⟨⟨0, [0, 0, 1, 1]⟩, ⟨0, [1, 1, 0, 0]⟩⟩, -- L13 xxxyy=xyyxx
    ⟨⟨0, [0, 0, 1, 2]⟩, ⟨0, [0, 1, 0, 2]⟩⟩, -- L14 xxxyz=xxyxz
    ⟨⟨0, [0, 0, 1, 2]⟩, ⟨0, [1, 0, 0, 2]⟩⟩, -- L15 xxxyz=xyxxz
    ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 0, 1, 2]⟩⟩, -- L16 xxyyz=xyxyz
    ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩, -- L17 xxyyz=xyyxz
    ⟨⟨0, [0, 1, 2, 0]⟩, ⟨0, [1, 0, 2, 0]⟩⟩, -- L18 xxyzx=xyxzx
    ⟨⟨0, [0, 1, 2, 0]⟩, ⟨0, [1, 2, 0, 0]⟩⟩, -- L19 xxyzx=xyzxx
    ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 0, 2, 1]⟩⟩, -- L20 xxyzy=xyxzy
    ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 1, 2, 0]⟩⟩, -- L21 xxyzy=xyyzx
    ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 2, 0, 1]⟩⟩, -- L22 xxyzy=xyzxy
    ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩, -- L23 xxyzy=xyzyx
    ⟨⟨0, [0, 1, 2, 2]⟩, ⟨0, [1, 0, 2, 2]⟩⟩, -- L24 xxyzz=xyxzz
    ⟨⟨0, [0, 1, 2, 2]⟩, ⟨0, [1, 2, 0, 2]⟩⟩, -- L25 xxyzz=xyzxz
    ⟨⟨0, [0, 1, 2, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩, -- L26 xxyzz=xyzzx
    ⟨⟨0, [0, 1, 2, 3]⟩, ⟨0, [1, 0, 2, 3]⟩⟩, -- L27 xxyzt=xyxzt
    ⟨⟨0, [0, 1, 2, 3]⟩, ⟨0, [1, 2, 0, 3]⟩⟩, -- L28 xxyzt=xyzxt
    ⟨⟨0, [1, 1, 2, 1]⟩, ⟨0, [1, 2, 1, 1]⟩⟩, -- L29 xyyzy=xyzyy
    ⟨⟨0, [1, 1, 2, 1]⟩, ⟨0, [1, 2, 2, 2]⟩⟩, -- L30 xyyzy=xyzzz
    ⟨⟨0, [1, 1, 2, 2]⟩, ⟨0, [1, 2, 1, 2]⟩⟩, -- L31 xyyzz=xyzyz
    ⟨⟨0, [1, 1, 2, 2]⟩, ⟨0, [1, 2, 2, 1]⟩⟩, -- L32 xyyzz=xyzzy
    ⟨⟨0, [1, 1, 2, 3]⟩, ⟨0, [1, 2, 1, 3]⟩⟩ ] -- L33 xyyzt=xyzyt

abbrev base : Semigroup (Fin 3) := Generated.Catalogue.S3_10.table.semigroup
abbrev power : Semigroup (Fin 4 → Fin 3) := base.pi (Fin 4)

private def toFinite (n : Nat) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Soundness of these exact 33 laws, including the finite-name round trip. -/
theorem baseModels : Models base basis :=
  FiniteCertificate.checkModels_sound Generated.Catalogue.S3_10.table basis toFinite (by decide)

/-- Ordinary coordinatewise preservation, not a completeness transfer. -/
theorem powerModels : Models power basis := by
  intro identity member
  exact identity.satisfiedByPi base (Fin 4) (baseModels identity member)

/-- Slot zero is the identity; slots one through four are the four generators. -/
def slotValue (s : Fin 5) : Fin 4 → Fin 3 :=
  fun i => if s.val = i.val + 1 then 1 else 2

private def letterSlot : Nat → Fin 5
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | _ => 0

def valuation (n : Nat) : Fin 4 → Fin 3 := slotValue (letterSlot n)

def witness : Word Nat := ⟨0, [0, 1, 2, 3, 2]⟩

def target (i : Fin 4) : Fin 3 :=
  if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 0 else 1

theorem witness_eval : power.eval valuation witness = target := by
  funext i
  exact (by decide : ∀ j : Fin 4, power.eval valuation witness j = target j) i

private theorem mul_empty (value : Fin 4 → Fin 3) :
    power.mul value (slotValue 0) = value := by
  funext i
  exact (by decide : ∀ a : Fin 3, ∀ j : Fin 4, base.mul a (slotValue 0 j) = a) (value i) i

def fiveSlotEval (a b c d e : Fin 5) : Fin 4 → Fin 3 :=
  power.mul (power.mul (power.mul (power.mul (slotValue a) (slotValue b))
    (slotValue c)) (slotValue d)) (slotValue e)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem fiveSlots_differ :
    ∀ a b c d e : Fin 5, ∃ i : Fin 4, fiveSlotEval a b c d e i ≠ target i := by
  decide

theorem fiveSlots_ne (a b c d e : Fin 5) : fiveSlotEval a b c d e ≠ target := by
  intro equal
  obtain ⟨i, different⟩ := fiveSlots_differ a b c d e
  exact different (congrFun equal i)

/-- Five padded slots cover every Nat word of length at most five. -/
private theorem short_slots (word : Word Nat) (bound : word.toList.length ≤ 5) :
    ∃ a b c d e : Fin 5, power.eval valuation word = fiveSlotEval a b c d e := by
  rcases word with ⟨a, tail⟩
  cases tail with
  | nil =>
      refine ⟨letterSlot a, 0, 0, 0, 0, ?_⟩
      simp only [Semigroup.eval, List.foldl_nil, valuation, fiveSlotEval, mul_empty]
  | cons b tail =>
      cases tail with
      | nil =>
          refine ⟨letterSlot a, letterSlot b, 0, 0, 0, ?_⟩
          simp only [Semigroup.eval, List.foldl_cons, List.foldl_nil, valuation,
            fiveSlotEval, mul_empty]
      | cons c tail =>
          cases tail with
          | nil =>
              refine ⟨letterSlot a, letterSlot b, letterSlot c, 0, 0, ?_⟩
              simp only [Semigroup.eval, List.foldl_cons, List.foldl_nil, valuation,
                fiveSlotEval, mul_empty]
          | cons d tail =>
              cases tail with
              | nil =>
                  refine ⟨letterSlot a, letterSlot b, letterSlot c, letterSlot d, 0, ?_⟩
                  simp only [Semigroup.eval, List.foldl_cons, List.foldl_nil, valuation,
                    fiveSlotEval, mul_empty]
              | cons e tail =>
                  cases tail with
                  | nil =>
                      exact ⟨letterSlot a, letterSlot b, letterSlot c, letterSlot d,
                        letterSlot e, rfl⟩
                  | cons f tail =>
                      simp only [Word.toList, List.length_cons] at bound
                      omega

theorem short_eval_ne (word : Word Nat) (bound : word.toList.length ≤ 5) :
    power.eval valuation word ≠ target := by
  intro equal
  obtain ⟨a, b, c, d, e, representation⟩ := short_slots word bound
  exact fiveSlots_ne a b c d e (representation.symm.trans equal)

/-- A negative derivability theorem; no unrestricted positive field is supplied. -/
theorem noShortDerivation (word : Word Nat) (bound : word.toList.length ≤ 5) :
    ¬ Derives basis witness word := by
  intro derivation
  have equal := Derives.sound powerModels derivation valuation
  exact short_eval_ne word bound (equal.symm.trans witness_eval)

/-- Refutes only the literal uniform length-five interpretation of the kit. -/
theorem noUniformFiveLetterBound :
    ¬ (∀ word : Word Nat, ∃ normal : Word Nat,
      normal.toList.length ≤ 5 ∧ Derives basis word normal) := by
  intro normalizes
  obtain ⟨normal, bound, derivation⟩ := normalizes witness
  exact noShortDerivation normal bound derivation

end SemigroupBasis.CoRoots.Order6Sunday.Msg0513B33FiveSlotCountermodel
