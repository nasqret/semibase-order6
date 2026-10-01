import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

def leftZeroTwo : FiniteTable where
  order := 2
  mul := fun a _ => a
  assoc := by intros; rfl

def xy : Word (Fin 2) := ⟨0, [1]⟩
def x : Word (Fin 2) := Word.singleton 0
def leftZeroLaw : Identity (Fin 2) := ⟨xy, x⟩

theorem leftZeroLaw_valid : leftZeroLaw.SatisfiedBy leftZeroTwo.semigroup :=
  leftZeroTwo.checkIdentity_sound leftZeroLaw (by decide)

def natXY : Word Nat := ⟨0, [1]⟩
def natX : Word Nat := Word.singleton 0
def leftZeroBasisLaw : Identity Nat := ⟨natXY, natX⟩
def leftZeroBasis : List (Identity Nat) := [leftZeroBasisLaw]

private def instantiateTwo (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | _ => v

theorem leftZeroTwo_eval (valuation : Nat → Fin 2) (w : Word Nat) :
    leftZeroTwo.semigroup.eval valuation w = valuation w.head := by
  cases w with
  | mk head tail =>
      induction tail with
      | nil => rfl
      | cons y ys ih =>
          simp only [Semigroup.eval, List.foldl_cons]
          exact ih

theorem leftZeroBasis_models : Models leftZeroTwo.semigroup leftZeroBasis := by
  intro e he
  simp only [leftZeroBasis, List.mem_singleton] at he
  subst e
  intro valuation
  rfl

theorem leftZeroDerivesHead (w : Word Nat) :
    Derives leftZeroBasis w (Word.singleton w.head) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil => exact Derives.refl _
      | cons next rest =>
          let suffix : Word Nat := ⟨next, rest⟩
          have hbase : Derives leftZeroBasis natXY natX :=
            Derives.fromBasis (e := leftZeroBasisLaw) <| by
              change leftZeroBasisLaw ∈ [leftZeroBasisLaw]
              exact List.Mem.head []
          have h := Derives.subst hbase
            (instantiateTwo (Word.singleton head) suffix)
          simpa [natXY, natX, instantiateTwo, Word.bind, Word.append,
            Word.singleton, suffix] using h

theorem leftZeroBasis_complete : BasisFor leftZeroTwo.semigroup leftZeroBasis := by
  refine ⟨leftZeroBasis_models, ?_⟩
  intro e hsatisfied
  have hheads : e.lhs.head = e.rhs.head := by
    apply Decidable.byContradiction
    intro hne
    let valuation : Nat → Fin 2 := fun z =>
      if z = e.lhs.head then 0 else 1
    have heval := hsatisfied valuation
    rw [leftZeroTwo_eval, leftZeroTwo_eval] at heval
    simp [valuation, Ne.symm hne] at heval
  exact Derives.trans (leftZeroDerivesHead e.lhs) <| by
    rw [hheads]
    exact Derives.symm (leftZeroDerivesHead e.rhs)

def natY : Word Nat := Word.singleton 1
def rightZeroBasisLaw : Identity Nat := ⟨natXY, natY⟩
def rightZeroBasis : List (Identity Nat) := [rightZeroBasisLaw]

private def swapFirstTwo : Nat → Word Nat
  | 0 => Word.singleton 1
  | 1 => Word.singleton 0
  | n + 2 => Word.singleton (n + 2)

theorem rightZeroBasis_models :
    Models leftZeroTwo.semigroup.opposite rightZeroBasis := by
  intro e he
  simp only [rightZeroBasis, List.mem_singleton] at he
  subst e
  intro valuation
  rfl

theorem reversedLeftAxiomDerivesRight :
    ∀ e : Identity Nat, e ∈ reversedBasis leftZeroBasis →
      Derives rightZeroBasis e.lhs e.rhs := by
  intro e he
  simp only [reversedBasis, leftZeroBasis, List.map_cons, List.map_nil,
    List.mem_singleton] at he
  subst e
  have hbase : Derives rightZeroBasis natXY natY :=
    Derives.fromBasis (e := rightZeroBasisLaw) <| by
      exact List.Mem.head []
  have h := Derives.subst hbase swapFirstTwo
  simpa [leftZeroBasisLaw, rightZeroBasisLaw, natXY, natX, natY,
    Identity.reversed, swapFirstTwo, Word.reverse, Word.reverseAux,
    Word.bind, Word.append, Word.singleton] using h

theorem rightZeroBasis_complete :
    BasisFor leftZeroTwo.semigroup.opposite rightZeroBasis :=
  (leftZeroBasis_complete.oppositeReversed).replace
    rightZeroBasis_models reversedLeftAxiomDerivesRight

end SemigroupBasis.Examples
