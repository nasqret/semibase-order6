import SemigroupBasis.FiniteCertificate

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G1

open SemigroupBasis

/-!
Shared all-variable completeness kernel for group G1 of Fable message 0050.

This file deliberately contains no order-six Cayley table and no member
endpoint.  A concrete table can use `basisForOfInvariantSeparation` after it
proves the two finite-table laws and the global invariant-separation premise.
-/

def xyy : Word Nat := ⟨1, [0, 0]⟩
def yy : Word Nat := ⟨0, [0]⟩
def xyz : Word Nat := ⟨1, [0, 2]⟩
def yyz : Word Nat := ⟨0, [0, 2]⟩

def squareCollapseLaw : Identity Nat := ⟨xyy, yy⟩
def markedCollapseLaw : Identity Nat := ⟨xyz, yyz⟩

/-- The exact candidate basis `{xyy = yy, xyz = yyz}`. -/
def basis : List (Identity Nat) :=
  [squareCollapseLaw, markedCollapseLaw]

/-- The four semantic classes of the G1 relatively free semigroup. -/
inductive Invariant (alpha : Type u) where
  | letter (a : alpha)
  | square (b : alpha)
  | pair (a b : alpha)
  | marked (a b : alpha)
deriving Repr, DecidableEq

/-- Read the G1 class from the final two letters.  The reversed tail makes the
length-one, length-two, and length-at-least-three cases definitionally visible. -/
def invariant [DecidableEq alpha] (word : Word alpha) : Invariant alpha :=
  match word.tail.reverse with
  | [] => .letter word.head
  | final :: [] =>
      if word.head = final then .square final else .pair word.head final
  | final :: penultimate :: _ =>
      if penultimate = final then .square final
      else .marked penultimate final

/-- The canonical words `a`, `aa`, `ab`, and `aab`. -/
def canonical : Invariant alpha → Word alpha
  | .letter a => Word.singleton a
  | .square b => Word.mk b [b]
  | .pair a b => Word.mk a [b]
  | .marked a b => Word.mk a [a, b]

private def instantiate (initial middle final : Word Nat) : Nat → Word Nat
  | 0 => middle
  | 1 => initial
  | 2 => final
  | n + 3 => Word.singleton (n + 3)

/-- One substituted instance of `xyy = yy`. -/
theorem derivesSquareCollapse (initial block : Word Nat) :
    Derives basis
      ((initial ++ block) ++ block)
      (block ++ block) := by
  have base : Derives basis xyy yy :=
    Derives.fromBasis (e := squareCollapseLaw) (List.Mem.head _)
  have substituted := Derives.subst base (instantiate initial block block)
  simpa [basis, squareCollapseLaw, xyy, yy, instantiate, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- One substituted instance of `xyz = yyz`. -/
theorem derivesMarkedCollapse (initial middle final : Word Nat) :
    Derives basis
      ((initial ++ middle) ++ final)
      ((middle ++ middle) ++ final) := by
  have base : Derives basis xyz yyz :=
    Derives.fromBasis (e := markedCollapseLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have substituted := Derives.subst base (instantiate initial middle final)
  simpa [basis, markedCollapseLaw, xyz, yyz, instantiate, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem appendSingleton (head : Nat) (tail : List Nat)
    (final : Nat) :
    Word.mk head tail ++ Word.singleton final =
      Word.mk head (tail ++ [final]) :=
  rfl

private theorem appendTwoSingletons (head : Nat) (tail : List Nat)
    (penultimate final : Nat) :
    (Word.mk head tail ++ Word.singleton penultimate) ++
        Word.singleton final =
      Word.mk head (tail ++ [penultimate, final]) := by
  apply Word.toList_injective
  simp [Word.toList, List.append_assoc]

/-- Every word reaches its G1 canonical word.  In the only non-reflexive case,
the derivation is exactly one substituted basis-law instance. -/
theorem derivesCanonical (word : Word Nat) :
    Derives basis word (canonical (invariant word)) := by
  cases word with
  | mk head tail =>
      cases reversed : tail.reverse with
      | nil =>
          have tailEq : tail = [] := by
            have twice := congrArg List.reverse reversed
            simpa using twice
          subst tail
          exact Derives.refl _
      | cons final rest =>
          cases rest with
          | nil =>
              have tailEq : tail = [final] := by
                have twice := congrArg List.reverse reversed
                simpa using twice
              subst tail
              by_cases equal : head = final
              · subst head
                simpa [invariant, canonical] using
                  (Derives.refl (Word.mk final [final]) :
                    Derives basis (Word.mk final [final])
                      (Word.mk final [final]))
              · simpa [invariant, canonical, equal] using
                  (Derives.refl (Word.mk head [final]) :
                    Derives basis (Word.mk head [final]) (Word.mk head [final]))
          | cons penultimate prefixReverse =>
              have tailEq :
                  tail = prefixReverse.reverse ++ [penultimate, final] := by
                have twice := congrArg List.reverse reversed
                simpa [List.reverse_cons, List.append_assoc] using twice
              rw [tailEq]
              by_cases equal : penultimate = final
              · subst penultimate
                have collapse :=
                  derivesSquareCollapse
                    (Word.mk head prefixReverse.reverse)
                    (Word.singleton final)
                rw [appendTwoSingletons, appendSingleton] at collapse
                simpa [invariant, canonical, List.reverse_append,
                  List.append_assoc] using collapse
              · have collapse :=
                  derivesMarkedCollapse
                    (Word.mk head prefixReverse.reverse)
                    (Word.singleton penultimate)
                    (Word.singleton final)
                rw [appendTwoSingletons, appendTwoSingletons] at collapse
                simpa [invariant, canonical, equal, List.reverse_append,
                  List.append_assoc] using collapse

/-- Equal G1 invariants are sufficient for derivability from the two laws. -/
theorem derivesOfInvariantEq (left right : Word Nat)
    (same : invariant left = invariant right) :
    Derives basis left right := by
  have leftNormal := derivesCanonical left
  have rightNormal := derivesCanonical right
  exact Derives.trans leftNormal <| by
    rw [same]
    exact Derives.symm rightNormal

/-- The exact semantic premise a concrete G1 table must establish. -/
def InvariantSeparation (semigroup : Semigroup carrier) : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy semigroup →
      invariant identity.lhs = invariant identity.rhs

/-- Reusable G1 completeness theorem.  Soundness and semantic separation are
the only table-dependent inputs. -/
theorem basisForOfInvariantSeparation
    (semigroup : Semigroup carrier)
    (models : Models semigroup basis)
    (separates : InvariantSeparation semigroup) :
    BasisFor semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfInvariantEq identity.lhs identity.rhs
    (separates identity valid)

/-! ## Finite-table helper shapes

The first Boolean discharges basis soundness directly.  The second is the
32-canonical-form separation sweep on four variables.  A member wrapper may
prove either Boolean by `decide`; the finite-to-global letter-merging bridge is
kept separate from these executable checks.
-/

def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def checkModels (table : FiniteTable) : Bool :=
  FiniteCertificate.checkModels table basis toFinThree

theorem modelsOfCheckModels (table : FiniteTable)
    (checked : checkModels table = true) :
    Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree checked

/-- All `2 * n^2` formal G1 classes over `Fin n`, with the impossible equal
`pair` and `marked` labels omitted. -/
def finiteInvariants (n : Nat) : List (Invariant (Fin n)) :=
  (List.finRange n).flatMap fun a =>
    [.letter a, .square a] ++
      (List.finRange n).flatMap fun b =>
        if a = b then [] else [.pair a b, .marked a b]

def CanonicalSeparation (table : FiniteTable) (variables : Nat) : Prop :=
  ∀ left, left ∈ finiteInvariants variables →
    ∀ right, right ∈ finiteInvariants variables →
      left ≠ right →
        ∃ valuation : Fin variables → Fin table.order,
          table.semigroup.eval valuation (canonical left) ≠
            table.semigroup.eval valuation (canonical right)

/-- Executable form of four-variable canonical separation. -/
def checkCanonicalSeparationFour (table : FiniteTable) : Bool :=
  (finiteInvariants 4).all fun left =>
    (finiteInvariants 4).all fun right =>
      decide (left = right) ||
        (FiniteTable.assignments 4 table.order).any fun valuation =>
          decide
            (table.semigroup.eval valuation (canonical left) ≠
              table.semigroup.eval valuation (canonical right))

end SemigroupBasis.CoRoots.Order6LeeLiP2G1
