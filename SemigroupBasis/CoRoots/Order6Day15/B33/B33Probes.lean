import SemigroupBasis.CoRoots.Order6Day15.B33.B33Eval
import SemigroupBasis.CoRoots.Order6Day15.B33.B33Key

namespace SemigroupBasis.CoRoots.Order6Day15.B33

variable {S : Type u} {G : Semigroup S}

def firstJoin : Option Bool → Option Bool → Option Bool
  | none,b => b
  | some a,_ => some a

/-- Concrete multiplication facts needed by the normal-form separating valuations. -/
structure Probes (G : Semigroup S) where
  order : Option Bool → S
  order_injective : Function.Injective order
  order_mul : ∀ a b, G.mul (order a) (order b) = order (firstJoin a b)
  parity : Bool → S
  parity_injective : Function.Injective parity
  parity_mul : ∀ a b, G.mul (parity a) (parity b) = parity (Bool.xor a b)
  same_unit : parity false = order none
  head : S
  dead : S
  head_ne_dead : head ≠ dead
  head_square : G.mul head head = dead
  dead_head : G.mul dead head = dead
  head_unit : G.mul head (order none) = head
  dead_unit : G.mul dead (order none) = dead
  tail : S
  tail_ne_zero : tail ≠ order (some false)
  unit_tail : G.mul (order none) tail = tail
  tail_square : G.mul tail tail = order (some false)
  zero_tail : G.mul (order (some false)) tail = order (some false)

def firstEval (v : Nat → Option Bool) : List Nat → Option Bool
  | [] => none
  | a :: xs => firstJoin (v a) (firstEval v xs)

theorem firstEval_congr (xs : List Nat) (v u : Nat → Option Bool)
    (same : ∀ a, a ∈ xs → v a = u a) : firstEval v xs = firstEval u xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [firstEval,firstEval,same a (by simp),ih (fun b h => same b (by simp [h]))]

theorem nodup_eq_of_firstEval (xs ys : List Nat) (hx : xs.Nodup) (hy : ys.Nodup)
    (same : ∀ v : Nat → Option Bool, firstEval v xs = firstEval v ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons b bs =>
      have impossible := same (fun _ => some true)
      simp [firstEval,firstJoin] at impossible
  | cons a xs ih =>
    cases ys with
    | nil =>
      have impossible := same (fun _ => some true)
      simp [firstEval,firstJoin] at impossible
    | cons b bs =>
      have ab : a = b := by
        by_cases equal : a = b
        · exact equal
        have different : a ≠ b := equal
        have ba : b ≠ a := Ne.symm different
        have impossible := same (fun x => if x = a then some false else some true)
        simp [firstEval,firstJoin,ba] at impossible
      subst b
      have tails : xs = bs := by
        apply ih _ (List.nodup_cons.mp hx).2 (List.nodup_cons.mp hy).2
        intro v
        let masked : Nat → Option Bool := fun x => if x = a then none else v x
        have maskedEq := same masked
        have left : firstEval masked xs = firstEval v xs := by
          apply firstEval_congr
          intro x member
          have xa : x ≠ a := by intro equal; subst x; exact (List.nodup_cons.mp hx).1 member
          simp [masked,xa]
        have right : firstEval masked bs = firstEval v bs := by
          apply firstEval_congr
          intro x member
          have xa : x ≠ a := by intro equal; subst x; exact (List.nodup_cons.mp hy).1 member
          simp [masked,xa]
        simpa only [firstEval,masked,if_pos rfl,firstJoin,left,right] using maskedEq
      rw [tails]

theorem order_power (P : Probes G) (p : Power) (a : Option Bool) :
    p.value G (P.order a) = P.order a := by
  have idempotent : firstJoin a a = a := by cases a <;> rfl
  cases p <;> simp only [Power.value,P.order_mul,idempotent]

/-- Empty and all-unit values are identified only for the order probe. -/
def orderTotal (P : Probes G) : Option S → S
  | none => P.order none
  | some a => a

theorem order_eval (P : Probes G) (v : Nat → Option Bool) (bs : List Block) :
    orderTotal P (evalBlocks G (fun x => P.order (v x)) bs) =
      P.order (firstEval v (letters bs)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [evalBlocks_cons,order_power]
    simp only [letters_cons,firstEval]
    cases tailValue : evalBlocks G (fun x => P.order (v x)) bs with
    | none =>
      have tailOrder : P.order none = P.order (firstEval v (letters bs)) := by
        simpa only [tailValue,orderTotal] using ih
      have tailEmpty := P.order_injective tailOrder
      rw [← tailEmpty]
      cases v b.letter <;> rfl
    | some value =>
      have tailOrder : value = P.order (firstEval v (letters bs)) := by
        simpa only [tailValue,orderTotal] using ih
      simp only [optMul,orderTotal,tailOrder,P.order_mul]

theorem letters_eq_of_eval (P : Probes G) (bs cs : List Block)
    (hb : (letters bs).Nodup) (hc : (letters cs).Nodup)
    (same : ∀ v, evalBlocks G v bs = evalBlocks G v cs) : letters bs = letters cs := by
  apply nodup_eq_of_firstEval _ _ hb hc
  intro v
  apply P.order_injective
  rw [← order_eval P v bs,← order_eval P v cs,same]

end SemigroupBasis.CoRoots.Order6Day15.B33
