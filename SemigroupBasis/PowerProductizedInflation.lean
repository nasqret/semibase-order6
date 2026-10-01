import SemigroupBasis.EdmundsInflation

namespace SemigroupBasis.PowerProductizedInflation

open SemigroupBasis

def x : Word Nat := Word.singleton 0
def y : Word Nat := Word.singleton 1
def xy : Word Nat := ⟨0, [1]⟩

/-- `power extra word` is the positive power with exponent `extra + 1`. -/
def power : Nat → Word Nat → Word Nat
  | 0, word => word
  | extra + 1, word => power extra word ++ word

def sourcePowerLaw (extra : Nat) : Identity Nat :=
  ⟨x, power extra x⟩

def rightContextLaw (extra : Nat) : Identity Nat :=
  ⟨xy, power extra x ++ y⟩

def productPowerLaw (extra : Nat) : Identity Nat :=
  ⟨xy, power extra xy⟩

def leftContextLaw (extra : Nat) : Identity Nat :=
  ⟨xy, x ++ power extra y⟩

/-- The arbitrary-power Edmunds replacement: three product-sided forms of
the source power law followed by all retained product identities. -/
def basis (extra : Nat) (retained : List (Identity Nat)) :
    List (Identity Nat) :=
  [rightContextLaw extra, productPowerLaw extra, leftContextLaw extra] ++
    retained

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

private theorem bind_append (u v : Word Nat) (substitution : Nat → Word Nat) :
    (u ++ v).bind substitution =
      u.bind substitution ++ v.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

@[simp]
private theorem bind_singleton (letter : Nat)
    (substitution : Nat → Word Nat) :
    (Word.singleton letter).bind substitution = substitution letter := rfl

@[simp]
private theorem bind_mk_nil (letter : Nat)
    (substitution : Nat → Word Nat) :
    (Word.mk letter []).bind substitution = substitution letter := rfl

@[simp]
private theorem power_bind (extra : Nat) (word : Word Nat)
    (substitution : Nat → Word Nat) :
    (power extra word).bind substitution =
      power extra (word.bind substitution) := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      simp [power, bind_append, ih]

private theorem append_isProduct (u v : Word Nat) :
    (u ++ v).tail ≠ [] := by
  simp

theorem power_isProduct
    (extra : Nat) (positive : 0 < extra) (word : Word Nat) :
    (power extra word).tail ≠ [] := by
  cases extra with
  | zero => contradiction
  | succ extra =>
      exact append_isProduct (power extra word) word

private theorem foldl_append_isProduct
    (substitution : Nat → Word Nat) (letters : List Nat)
    (current : Word Nat) (currentProduct : current.tail ≠ []) :
    (letters.foldl (fun value letter => value ++ substitution letter)
      current).tail ≠ [] := by
  induction letters generalizing current with
  | nil => exact currentProduct
  | cons letter rest ih =>
      simp only [List.foldl_cons]
      exact ih (current ++ substitution letter)
        (append_isProduct current (substitution letter))

private theorem bind_isProduct
    (word : Word Nat) (wordProduct : word.tail ≠ [])
    (substitution : Nat → Word Nat) :
    (word.bind substitution).tail ≠ [] := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => contradiction
      | cons next rest =>
          unfold Word.bind
          simp only [List.foldl_cons]
          exact foldl_append_isProduct substitution rest
            (substitution head ++ substitution next)
            (append_isProduct (substitution head) (substitution next))

/-- Replace singleton words by the selected positive power and leave products
unchanged. -/
def productize (extra : Nat) (word : Word Nat) : Word Nat :=
  match word.tail with
  | [] => power extra word
  | _ :: _ => word

@[simp]
theorem productize_of_isProduct
    (extra : Nat) (word : Word Nat) (wordProduct : word.tail ≠ []) :
    productize extra word = word := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => contradiction
      | cons next rest => rfl

private theorem derivesRightContextPower
    (extra : Nat) (retained : List (Identity Nat))
    (u v : Word Nat) :
    Derives (basis extra retained) (u ++ v) (power extra u ++ v) := by
  have base :
      Derives (basis extra retained)
        (rightContextLaw extra).lhs (rightContextLaw extra).rhs :=
    Derives.fromBasis (by simp [basis])
  have instantiated :=
    Derives.subst base (instantiateTwoWords u v)
  have lhs_eq :
      (rightContextLaw extra).lhs.bind (instantiateTwoWords u v) =
        u ++ v := rfl
  have rhs_eq :
      (rightContextLaw extra).rhs.bind (instantiateTwoWords u v) =
        power extra u ++ v := by
    rw [rightContextLaw, bind_append, power_bind]
    rfl
  simpa only [lhs_eq, rhs_eq] using instantiated

private theorem derivesProductPower
    (extra : Nat) (retained : List (Identity Nat))
    (u v : Word Nat) :
    Derives (basis extra retained) (u ++ v) (power extra (u ++ v)) := by
  have base :
      Derives (basis extra retained)
        (productPowerLaw extra).lhs (productPowerLaw extra).rhs :=
    Derives.fromBasis (by simp [basis])
  have instantiated :=
    Derives.subst base (instantiateTwoWords u v)
  have lhs_eq :
      (productPowerLaw extra).lhs.bind (instantiateTwoWords u v) =
        u ++ v := rfl
  have rhs_eq :
      (productPowerLaw extra).rhs.bind (instantiateTwoWords u v) =
        power extra (u ++ v) := by
    rw [productPowerLaw, power_bind]
    rfl
  simpa only [lhs_eq, rhs_eq] using instantiated

private theorem derivesLeftContextPower
    (extra : Nat) (retained : List (Identity Nat))
    (u v : Word Nat) :
    Derives (basis extra retained) (u ++ v) (u ++ power extra v) := by
  have base :
      Derives (basis extra retained)
        (leftContextLaw extra).lhs (leftContextLaw extra).rhs :=
    Derives.fromBasis (by simp [basis])
  have instantiated :=
    Derives.subst base (instantiateTwoWords u v)
  have lhs_eq :
      (leftContextLaw extra).lhs.bind (instantiateTwoWords u v) =
        u ++ v := rfl
  have rhs_eq :
      (leftContextLaw extra).rhs.bind (instantiateTwoWords u v) =
        u ++ power extra v := by
    rw [leftContextLaw, bind_append, power_bind]
    rfl
  simpa only [lhs_eq, rhs_eq] using instantiated

private theorem derivesWholePower
    (extra : Nat) (retained : List (Identity Nat))
    (word : Word Nat) (wordProduct : word.tail ≠ []) :
    Derives (basis extra retained) word (power extra word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => contradiction
      | cons next rest =>
          simpa [Word.singleton, Word.append] using
            derivesProductPower extra retained
              (Word.singleton head) ⟨next, rest⟩

private theorem derivesAppendProductize
    (extra : Nat) (retained : List (Identity Nat))
    (u v : Word Nat) :
    Derives (basis extra retained) (u ++ v) (productize extra u ++ v) := by
  cases u with
  | mk head tail =>
      cases tail with
      | nil =>
          simpa [productize] using
            derivesRightContextPower extra retained (Word.singleton head) v
      | cons next rest =>
          exact Derives.refl _

private theorem derivesPrependProductize
    (extra : Nat) (retained : List (Identity Nat))
    (u v : Word Nat) :
    Derives (basis extra retained) (u ++ v) (u ++ productize extra v) := by
  cases v with
  | mk head tail =>
      cases tail with
      | nil =>
          simpa [productize] using
            derivesLeftContextPower extra retained u (Word.singleton head)
      | cons next rest =>
          exact Derives.refl _

private theorem derivesBindProductize
    (extra : Nat) (positive : 0 < extra)
    (retained : List (Identity Nat))
    (word : Word Nat) (substitution : Nat → Word Nat) :
    Derives (basis extra retained)
      ((productize extra word).bind substitution)
      (productize extra (word.bind substitution)) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          by_cases substitutedProduct : (substitution head).tail = []
          · simpa only [productize, power_bind, bind_mk_nil,
              substitutedProduct] using
              (Derives.refl (power extra (substitution head)) :
                Derives (basis extra retained)
                  (power extra (substitution head))
                  (power extra (substitution head)))
          · have contraction :=
              Derives.symm
                (derivesWholePower extra retained
                  (substitution head) substitutedProduct)
            rw [productize, power_bind, bind_mk_nil]
            change
              Derives (basis extra retained)
                (power extra (substitution head))
                (productize extra (substitution head))
            rw [productize_of_isProduct extra
              (substitution head) substitutedProduct]
            exact contraction
      | cons next rest =>
          have boundProduct :
              ((Word.mk head (next :: rest)).bind substitution).tail ≠ [] :=
            bind_isProduct ⟨head, next :: rest⟩ (by simp) substitution
          change
            Derives (basis extra retained)
              ((Word.mk head (next :: rest)).bind substitution)
              (productize extra
                ((Word.mk head (next :: rest)).bind substitution))
          rw [productize_of_isProduct extra _ boundProduct]
          exact Derives.refl _

theorem sourceModelsTarget
    {A : Type u} {source : Semigroup A}
    (extra : Nat) (retained sourceBasis : List (Identity Nat))
    (sourceMembership : ∀ identity,
      identity ∈ sourceBasis ↔
        identity = sourcePowerLaw extra ∨ identity ∈ retained)
    (sourceBasisProof : BasisFor source sourceBasis) :
    Models source (basis extra retained) := by
  have sourcePowerDerivation :
      Derives sourceBasis x (power extra x) :=
    Derives.fromBasis <|
      (sourceMembership (sourcePowerLaw extra)).2 (Or.inl rfl)
  intro identity member
  simp only [basis, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl | rfl) | retainedMember
  · have derivation :=
      Derives.appendRight sourcePowerDerivation (Word.singleton 1)
    intro valuation
    simpa [rightContextLaw, sourcePowerLaw, xy, x, y,
      Word.append, Word.singleton, Word.append_assoc] using
        Derives.sound sourceBasisProof.1 derivation valuation
  · have derivation :=
      Derives.subst sourcePowerDerivation
        (instantiateTwoWords xy xy)
    have lhs_eq :
        x.bind (instantiateTwoWords xy xy) = xy := rfl
    have rhs_eq :
        (power extra x).bind (instantiateTwoWords xy xy) =
          power extra xy := by
      rw [power_bind]
      rfl
    have productDerivation :
        Derives sourceBasis xy (power extra xy) := by
      simpa only [lhs_eq, rhs_eq] using derivation
    intro valuation
    simpa [productPowerLaw] using
      Derives.sound sourceBasisProof.1 productDerivation valuation
  · have renamed :=
      Derives.subst sourcePowerDerivation
        (instantiateTwoWords (Word.singleton 1) (Word.singleton 1))
    have lhs_eq :
        x.bind
            (instantiateTwoWords (Word.singleton 1) (Word.singleton 1)) =
          Word.singleton 1 := rfl
    have rhs_eq :
        (power extra x).bind
            (instantiateTwoWords (Word.singleton 1) (Word.singleton 1)) =
          power extra (Word.singleton 1) := by
      rw [power_bind]
      rfl
    have renamedDerivation :
        Derives sourceBasis (Word.singleton 1)
          (power extra (Word.singleton 1)) := by
      simpa only [lhs_eq, rhs_eq] using renamed
    have derivation :=
      Derives.prepend (Word.singleton 0) renamedDerivation
    intro valuation
    simpa [leftContextLaw, xy, x, y] using
        Derives.sound sourceBasisProof.1 derivation valuation
  · exact sourceBasisProof.1 identity <|
      (sourceMembership identity).2 (Or.inr retainedMember)

/-- Every source derivation remains derivable after singleton words are
replaced by the selected positive power. -/
theorem derivesProductized
    (extra : Nat) (positive : 0 < extra)
    (retained sourceBasis : List (Identity Nat))
    (sourceMembership : ∀ identity,
      identity ∈ sourceBasis ↔
        identity = sourcePowerLaw extra ∨ identity ∈ retained)
    (retainedProducts : ∀ identity, identity ∈ retained →
      identity.lhs.tail ≠ [] ∧ identity.rhs.tail ≠ [])
    {u v : Word Nat} (derivation : Derives sourceBasis u v) :
    Derives (basis extra retained)
      (productize extra u) (productize extra v) := by
  induction derivation with
  | fromBasis member =>
      rcases (sourceMembership _).1 member with rfl | retainedCase
      ·
        have poweredProduct := power_isProduct extra positive x
        change
          Derives (basis extra retained)
            (productize extra x) (productize extra (power extra x))
        rw [productize_of_isProduct extra _ poweredProduct]
        change
          Derives (basis extra retained)
            (power extra x) (power extra x)
        exact Derives.refl _
      · obtain ⟨lhsProduct, rhsProduct⟩ :=
          retainedProducts _ retainedCase
        rw [productize_of_isProduct extra _ lhsProduct,
          productize_of_isProduct extra _ rhsProduct]
        exact Derives.fromBasis (by simp [basis, retainedCase])
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm ih
  | trans _ _ ihFirst ihSecond =>
      exact Derives.trans ihFirst ihSecond
  | prepend p derivation ih =>
      exact Derives.trans
        (by
          simpa [productize_of_isProduct extra _
              (append_isProduct p _)] using
            derivesPrependProductize extra retained p _)
        (Derives.trans
          (Derives.prepend p ih)
          (by
            simpa [productize_of_isProduct extra _
                (append_isProduct p _)] using
              Derives.symm
                (derivesPrependProductize extra retained p _)))
  | appendRight derivation q ih =>
      exact Derives.trans
        (by
          simpa [productize_of_isProduct extra _
              (append_isProduct _ q)] using
            derivesAppendProductize extra retained _ q)
        (Derives.trans
          (Derives.appendRight ih q)
          (by
            simpa [productize_of_isProduct extra _
                (append_isProduct _ q)] using
              Derives.symm
                (derivesAppendProductize extra retained _ q)))
  | subst derivation substitution ih =>
      exact Derives.trans
        (Derives.symm
          (derivesBindProductize extra positive retained _ substitution)) <|
        Derives.trans (Derives.subst ih substitution)
          (derivesBindProductize extra positive retained _ substitution)

theorem derivesProductIdentity
    (extra : Nat) (positive : 0 < extra)
    (retained sourceBasis : List (Identity Nat))
    (sourceMembership : ∀ identity,
      identity ∈ sourceBasis ↔
        identity = sourcePowerLaw extra ∨ identity ∈ retained)
    (retainedProducts : ∀ identity, identity ∈ retained →
      identity.lhs.tail ≠ [] ∧ identity.rhs.tail ≠ [])
    {u v : Word Nat} (lhsProduct : u.tail ≠ [])
    (rhsProduct : v.tail ≠ [])
    (derivation : Derives sourceBasis u v) :
    Derives (basis extra retained) u v := by
  simpa [productize_of_isProduct extra u lhsProduct,
    productize_of_isProduct extra v rhsProduct] using
      derivesProductized extra positive retained sourceBasis
        sourceMembership retainedProducts derivation

end SemigroupBasis.PowerProductizedInflation

namespace SemigroupBasis.Inflation

open SemigroupBasis

/-- A complete arbitrary-power Edmunds productization theorem. It turns a
source basis consisting of `x = x^(extra+1)` and retained product identities
into a complete basis for every proper product-represented inflation. -/
theorem inheritPowerProductizedBasis
    {A : Type u} {B : Type v}
    {source : Semigroup A} {target : Semigroup B}
    (extra : Nat) (positive : 0 < extra)
    (retained sourceBasis : List (Identity Nat))
    (sourceMembership : ∀ identity,
      identity ∈ sourceBasis ↔
        identity =
          SemigroupBasis.PowerProductizedInflation.sourcePowerLaw extra ∨
        identity ∈ retained)
    (retainedProducts : ∀ identity, identity ∈ retained →
      identity.lhs.tail ≠ [] ∧ identity.rhs.tail ≠ [])
    (inflation : Inflation source target)
    (proper : inflation.Proper)
    (sourceBasisProof : BasisFor source sourceBasis) :
    BasisFor target
      (SemigroupBasis.PowerProductizedInflation.basis extra retained) := by
  have sourceModels :
      Models source
        (SemigroupBasis.PowerProductizedInflation.basis extra retained) :=
    SemigroupBasis.PowerProductizedInflation.sourceModelsTarget
      extra retained sourceBasis sourceMembership sourceBasisProof
  have targetModels :
      Models target
        (SemigroupBasis.PowerProductizedInflation.basis extra retained) := by
    intro identity member
    simp only [SemigroupBasis.PowerProductizedInflation.basis,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl | rfl) | retainedMember
    · exact inflation.pushforwardProductIdentity _ (by simp
          [SemigroupBasis.PowerProductizedInflation.rightContextLaw,
           SemigroupBasis.PowerProductizedInflation.xy])
        (by simp
          [SemigroupBasis.PowerProductizedInflation.rightContextLaw])
        (sourceModels _ (by simp
          [SemigroupBasis.PowerProductizedInflation.basis]))
    · exact inflation.pushforwardProductIdentity _ (by simp
          [SemigroupBasis.PowerProductizedInflation.productPowerLaw,
           SemigroupBasis.PowerProductizedInflation.xy])
        (SemigroupBasis.PowerProductizedInflation.power_isProduct
          extra positive SemigroupBasis.PowerProductizedInflation.xy)
        (sourceModels _ (by simp
          [SemigroupBasis.PowerProductizedInflation.basis]))
    · exact inflation.pushforwardProductIdentity _ (by simp
          [SemigroupBasis.PowerProductizedInflation.leftContextLaw,
           SemigroupBasis.PowerProductizedInflation.xy])
        (by simp
          [SemigroupBasis.PowerProductizedInflation.leftContextLaw])
        (sourceModels _ (by simp
          [SemigroupBasis.PowerProductizedInflation.basis]))
    · obtain ⟨lhsProduct, rhsProduct⟩ :=
        retainedProducts identity retainedMember
      exact inflation.pushforwardProductIdentity identity
        lhsProduct rhsProduct
        (sourceModels identity (by simp
          [SemigroupBasis.PowerProductizedInflation.basis,
           retainedMember]))
  refine ⟨targetModels, ?_⟩
  intro identity valid
  obtain ⟨outside, outsideImage⟩ := proper
  cases identity with
  | mk lhs rhs =>
      cases lhs with
      | mk lhsHead lhsTail =>
          cases lhsTail with
          | nil =>
              cases rhs with
              | mk rhsHead rhsTail =>
                  cases rhsTail with
                  | nil =>
                      have heads : lhsHead = rhsHead := by
                        apply Decidable.byContradiction
                        intro headsNe
                        let inside :=
                          inflation.embedding.toFun
                            (inflation.retract outside)
                        let valuation : Nat → B :=
                          fun letter =>
                            if letter = lhsHead then outside else inside
                        have evaluated := valid valuation
                        change valuation lhsHead = valuation rhsHead at evaluated
                        have rhsNe : rhsHead ≠ lhsHead := Ne.symm headsNe
                        simp [valuation, rhsNe, inside] at evaluated
                        exact outsideImage _ evaluated
                      subst rhsHead
                      exact Derives.refl _
                  | cons rhsNext rhsRest =>
                      let valuation : Nat → B := fun _ => outside
                      have evaluated := valid valuation
                      rw [inflation.eval_represented valuation
                        rhsHead rhsNext rhsRest] at evaluated
                      exact False.elim <| outsideImage _ evaluated
          | cons lhsNext lhsRest =>
              cases rhs with
              | mk rhsHead rhsTail =>
                  cases rhsTail with
                  | nil =>
                      let valuation : Nat → B := fun _ => outside
                      have evaluated := valid valuation
                      rw [inflation.eval_represented valuation
                        lhsHead lhsNext lhsRest] at evaluated
                      exact False.elim <| outsideImage _ evaluated.symm
                  | cons rhsNext rhsRest =>
                      have sourceValid :
                          (Identity.mk
                            (Word.mk lhsHead (lhsNext :: lhsRest))
                            (Word.mk rhsHead (rhsNext :: rhsRest))).SatisfiedBy
                              source :=
                        inflation.embedding.pullback_identity _ valid
                      exact
                        SemigroupBasis.PowerProductizedInflation.derivesProductIdentity
                          extra positive retained sourceBasis
                          sourceMembership retainedProducts
                          (by simp) (by simp)
                          (sourceBasisProof.2 _ sourceValid)

end SemigroupBasis.Inflation
