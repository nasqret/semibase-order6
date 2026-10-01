import SemigroupBasis.CoRoots.S5_804Canonical
import SemigroupBasis.Examples.ConnectedComponentFourNormalize
import SemigroupBasis.Examples.ConnectedComponentFourSemanticComplete
import SemigroupBasis.Transfer

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_804

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Embedded S4_70 component detector -/

/-- The recorded copy `[1,2,4,5]` of `S4_70` inside `S5_804`. -/
def componentEmbedding :
    Embedding connectedComponentFour.semigroup
      Generated.Catalogue.S5_804.table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else
        if value.val = 2 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem valid_s4_70 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_804.table.semigroup) :
    identity.SatisfiedBy connectedComponentFour.semigroup :=
  componentEmbedding.pullback_identity identity valid

/-- The embedded S4_70 detector supplies the ordered supports and unary
repeat flags of all maximal support-connected components. -/
theorem valid_sameBaseComponentSignatures
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_804.table.semigroup) :
    connectedComponentSignaturesWord identity.lhs =
      connectedComponentSignaturesWord identity.rhs := by
  have rootValid := valid_s4_70 identity valid
  have lhsDerivation :=
    connectedComponentFour_derivesCanonical identity.lhs
  have rhsDerivation :=
    connectedComponentFour_derivesCanonical identity.rhs
  have normalizedEval :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender identity.lhs) =
          connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender identity.rhs) := by
    intro valuation
    have lhsSound :=
      lhsDerivation.sound connectedComponentFourBasis_models valuation
    have rhsSound :=
      rhsDerivation.sound connectedComponentFourBasis_models valuation
    exact lhsSound.symm.trans <| (rootValid valuation).trans rhsSound
  exact
    connectedComponentCanonical_eq_of_equalEval
      (connectedComponentFourSignaturesWord_canonical identity.lhs)
      (connectedComponentFourSignaturesWord_canonical identity.rhs)
      (connectedComponentCanonicalRender identity.lhs)
      (connectedComponentCanonicalRender identity.rhs)
      (connectedComponentCanonicalRender_toList identity.lhs)
      (connectedComponentCanonicalRender_toList identity.rhs)
      normalizedEval

/-! ## Exact S5_804 final-variable marker -/

private abbrev table := Generated.Catalogue.S5_804.table

def listStep : Option (Fin 5) → Fin 5 → Option (Fin 5)
  | none, next => some next
  | some current, next => some (table.mul current next)

def evalFrom
    {alpha : Type} (initial : Option (Fin 5))
    (valuation : alpha → Fin 5) (letters : List alpha) :
    Option (Fin 5) :=
  letters.foldl
    (fun current letter => listStep current (valuation letter)) initial

def evalList
    {alpha : Type} (valuation : alpha → Fin 5)
    (letters : List alpha) : Option (Fin 5) :=
  evalFrom none valuation letters

@[simp]
theorem evalFrom_nil
    {alpha : Type} (initial : Option (Fin 5))
    (valuation : alpha → Fin 5) :
    evalFrom initial valuation [] = initial :=
  rfl

@[simp]
theorem evalFrom_cons
    {alpha : Type} (initial : Option (Fin 5))
    (valuation : alpha → Fin 5) (letter : alpha)
    (letters : List alpha) :
    evalFrom initial valuation (letter :: letters) =
      evalFrom (listStep initial (valuation letter)) valuation letters :=
  rfl

theorem evalFrom_append
    {alpha : Type} (initial : Option (Fin 5))
    (valuation : alpha → Fin 5) (left right : List alpha) :
    evalFrom initial valuation (left ++ right) =
      evalFrom (evalFrom initial valuation left) valuation right := by
  simp [evalFrom, List.foldl_append]

theorem evalFrom_some
    {alpha : Type} (initial : Fin 5)
    (valuation : alpha → Fin 5) (letters : List alpha) :
    evalFrom (some initial) valuation letters =
      some
        (letters.foldl
          (fun current letter => table.mul current (valuation letter))
          initial) := by
  induction letters generalizing initial with
  | nil => rfl
  | cons letter letters induction =>
      simp only [evalFrom_cons, listStep]
      exact induction (table.mul initial (valuation letter))

theorem evalList_toList
    {alpha : Type} (valuation : alpha → Fin 5) (word : Word alpha) :
    evalList valuation word.toList =
      some (table.semigroup.eval valuation word) := by
  cases word with
  | mk head tail =>
      simp only [evalList, evalFrom_cons, listStep, Word.toList,
        Semigroup.eval]
      exact evalFrom_some (valuation head) valuation tail

/-- Prefix variables use one-based states 3 and 4; suffix variables use
one-based state 5. -/
def finalCutValuation
    {alpha : Type} [DecidableEq alpha]
    (prefixSupport : List alpha) (tested : alpha) : alpha → Fin 5 :=
  fun letter =>
    if letter = tested then 3
    else if letter ∈ prefixSupport then 2
    else 4

@[simp]
theorem finalCutValuation_tested
    {alpha : Type} [DecidableEq alpha]
    (prefixSupport : List alpha) (tested : alpha) :
    finalCutValuation prefixSupport tested tested = 3 := by
  simp [finalCutValuation]

theorem finalCutValuation_prefix
    {alpha : Type} [DecidableEq alpha]
    {prefixSupport : List alpha} {tested letter : alpha}
    (different : letter ≠ tested) (member : letter ∈ prefixSupport) :
    finalCutValuation prefixSupport tested letter = 2 := by
  simp [finalCutValuation, different, member]

theorem finalCutValuation_suffix
    {alpha : Type} [DecidableEq alpha]
    {prefixSupport : List alpha} {tested letter : alpha}
    (testedMember : tested ∈ prefixSupport)
    (notMember : letter ∉ prefixSupport) :
    finalCutValuation prefixSupport tested letter = 4 := by
  have different : letter ≠ tested := by
    intro equal
    subst letter
    exact notMember testedMember
  simp [finalCutValuation, different, notMember]

private theorem finalCutValuation_prefix_phase
    {alpha : Type} [DecidableEq alpha]
    {prefixSupport : List alpha} {tested letter : alpha}
    (member : letter ∈ prefixSupport) :
    finalCutValuation prefixSupport tested letter = 2 ∨
      finalCutValuation prefixSupport tested letter = 3 := by
  by_cases equal : letter = tested
  · subst letter
    exact Or.inr (finalCutValuation_tested prefixSupport tested)
  · exact Or.inl (finalCutValuation_prefix equal member)

private theorem mul_prefix_phase
    (current next : Fin 5)
    (currentPhase : current = 2 ∨ current = 3)
    (nextPhase : next = 2 ∨ next = 3) :
    table.mul current next = next := by
  rcases currentPhase with rfl | rfl <;>
    rcases nextPhase with rfl | rfl <;> decide

private theorem evalFrom_left_append_final
    {alpha : Type} [DecidableEq alpha]
    (prefixSupport : List alpha) (tested : alpha)
    (current : Fin 5)
    (currentPhase : current = 2 ∨ current = 3) :
    ∀ (body : List alpha) (final : alpha),
      (∀ letter, letter ∈ body → letter ∈ prefixSupport) →
      final ∈ prefixSupport →
      evalFrom (some current) (finalCutValuation prefixSupport tested)
          (body ++ [final]) =
        some (finalCutValuation prefixSupport tested final)
  | [], final, _, finalMember => by
      rw [List.nil_append, evalFrom_cons, evalFrom_nil]
      simp only [listStep]
      rw [mul_prefix_phase current
        (finalCutValuation prefixSupport tested final)
        currentPhase
        (finalCutValuation_prefix_phase finalMember)]
  | letter :: rest, final, supported, finalMember => by
      rw [List.cons_append, evalFrom_cons]
      simp only [listStep]
      have letterMember : letter ∈ prefixSupport :=
        supported letter (by simp)
      have letterPhase :=
        finalCutValuation_prefix_phase (tested := tested) letterMember
      have recursive :=
        evalFrom_left_append_final prefixSupport tested
          (finalCutValuation prefixSupport tested letter) letterPhase
          rest final
          (fun value member => supported value (List.Mem.tail letter member))
          finalMember
      simpa only [mul_prefix_phase current
        (finalCutValuation prefixSupport tested letter)
        currentPhase letterPhase] using recursive

private theorem evalList_left_append_final
    {alpha : Type} [DecidableEq alpha]
    (prefixSupport : List alpha) (tested : alpha)
    (body : List alpha) (final : alpha)
    (supported :
      ∀ letter, letter ∈ body → letter ∈ prefixSupport)
    (finalMember : final ∈ prefixSupport) :
    evalList (finalCutValuation prefixSupport tested)
        (body ++ [final]) =
      some (finalCutValuation prefixSupport tested final) := by
  cases body with
  | nil => rfl
  | cons first rest =>
      rw [List.cons_append]
      change
        evalFrom
            (some (finalCutValuation prefixSupport tested first))
            (finalCutValuation prefixSupport tested) (rest ++ [final]) =
          some (finalCutValuation prefixSupport tested final)
      have firstMember : first ∈ prefixSupport :=
        supported first (by simp)
      exact evalFrom_left_append_final prefixSupport tested
        (finalCutValuation prefixSupport tested first)
        (finalCutValuation_prefix_phase firstMember)
        rest final
        (fun value member => supported value (List.Mem.tail first member))
        finalMember

private theorem evalFrom_zero_suffix
    {alpha : Type} [DecidableEq alpha]
    (prefixSupport : List alpha) (tested : alpha)
    (testedMember : tested ∈ prefixSupport) :
    ∀ letters : List alpha,
      (∀ letter, letter ∈ letters → letter ∉ prefixSupport) →
      evalFrom (some 0) (finalCutValuation prefixSupport tested) letters =
        some 0
  | [], _ => rfl
  | letter :: rest, unsupported => by
      rw [evalFrom_cons,
        finalCutValuation_suffix testedMember
          (unsupported letter (by simp))]
      simp only [listStep]
      rw [show table.mul (0 : Fin 5) (4 : Fin 5) =
        (0 : Fin 5) by decide]
      exact evalFrom_zero_suffix prefixSupport tested testedMember rest
        (fun value member => unsupported value (List.Mem.tail letter member))

private theorem evalFrom_one_suffix
    {alpha : Type} [DecidableEq alpha]
    (prefixSupport : List alpha) (tested : alpha)
    (testedMember : tested ∈ prefixSupport) :
    ∀ letters : List alpha,
      (∀ letter, letter ∈ letters → letter ∉ prefixSupport) →
      evalFrom (some 1) (finalCutValuation prefixSupport tested) letters =
        some 1
  | [], _ => rfl
  | letter :: rest, unsupported => by
      rw [evalFrom_cons,
        finalCutValuation_suffix testedMember
          (unsupported letter (by simp))]
      simp only [listStep]
      rw [show table.mul (1 : Fin 5) (4 : Fin 5) =
        (1 : Fin 5) by decide]
      exact evalFrom_one_suffix prefixSupport tested testedMember rest
        (fun value member => unsupported value (List.Mem.tail letter member))

/-- Exact marker result at a displayed support-disjoint phase boundary. -/
theorem finalCutEvalList
    {alpha : Type} [DecidableEq alpha]
    (prefixSupport : List alpha) (tested : alpha)
    (body : List alpha) (final : alpha) (suffix : List alpha)
    (testedMember : tested ∈ prefixSupport)
    (bodySupported :
      ∀ letter, letter ∈ body → letter ∈ prefixSupport)
    (finalMember : final ∈ prefixSupport)
    (suffixUnsupported :
      ∀ letter, letter ∈ suffix → letter ∉ prefixSupport) :
    evalList (finalCutValuation prefixSupport tested)
        (body ++ [final] ++ suffix) =
      if suffix = [] then
        if final = tested then some 3 else some 2
      else
        if final = tested then some 1 else some 0 := by
  rw [evalList, evalFrom_append]
  change
    evalFrom
        (evalList (finalCutValuation prefixSupport tested)
          (body ++ [final]))
        (finalCutValuation prefixSupport tested) suffix = _
  rw [evalList_left_append_final prefixSupport tested body final
    bodySupported finalMember]
  by_cases finalEq : final = tested
  · subst final
    rw [finalCutValuation_tested]
    cases suffix with
    | nil => simp
    | cons first rest =>
        rw [evalFrom_cons,
          finalCutValuation_suffix testedMember
            (suffixUnsupported first (by simp))]
        simp only [listStep]
        rw [show table.mul (3 : Fin 5) (4 : Fin 5) =
          (1 : Fin 5) by decide]
        rw [evalFrom_one_suffix prefixSupport tested testedMember rest
          (fun value member =>
            suffixUnsupported value (List.Mem.tail first member))]
        simp
  · have finalValue :
        finalCutValuation prefixSupport tested final = 2 :=
      finalCutValuation_prefix finalEq finalMember
    rw [finalValue]
    cases suffix with
    | nil => simp [finalEq]
    | cons first rest =>
        rw [evalFrom_cons,
          finalCutValuation_suffix testedMember
            (suffixUnsupported first (by simp))]
        simp only [listStep]
        rw [show table.mul (2 : Fin 5) (4 : Fin 5) =
          (0 : Fin 5) by decide]
        rw [evalFrom_zero_suffix prefixSupport tested testedMember rest
          (fun value member =>
            suffixUnsupported value (List.Mem.tail first member))]
        simp [finalEq]

/-! ## Canonical signature marker interface -/

def ConnectedCutComponentSignatureValid
    (signature : ConnectedCutComponentSignature) : Prop :=
  connectedComponentSignatureValid signature.base ∧
    signature.final ∈ signature.base.support

def ConnectedCutCanonicalSignatures
    (signatures : List ConnectedCutComponentSignature) : Prop :=
  connectedComponentFourCanonicalSignatures (signatures.map (·.base)) ∧
    ∀ signature, signature ∈ signatures →
      signature.final ∈ signature.base.support

def connectedCutSignatureSupport
    (signatures : List ConnectedCutComponentSignature) : List Nat :=
  signatures.flatMap fun signature => signature.base.support

theorem connectedCutSignaturesWord_canonical (word : Word Nat) :
    ConnectedCutCanonicalSignatures (connectedCutSignaturesWord word) := by
  constructor
  · simpa [connectedCutSignaturesWord, connectedCutSignaturesList,
      connectedCutComponentSignatureOfList, List.map_map] using
      connectedComponentFourSignaturesWord_canonical word
  · intro signature signatureMember
    rw [connectedCutSignaturesWord, connectedCutSignaturesList]
      at signatureMember
    rcases List.mem_map.mp signatureMember with
      ⟨component, componentMember, rfl⟩
    have componentNonempty :=
      connectedComponentDecomposeList_nonempty_components word.toList
        component componentMember
    rcases List.exists_cons_of_ne_nil componentNonempty with
      ⟨head, tail, rfl⟩
    rw [connectedCutComponentSignatureOfList,
      connectedComponentSignatureOfList_support]
    exact
      (connectedComponentSortedSupport_mem_iff
        (componentFinal (head :: tail)) (head :: tail)).2
        (componentFinal_mem head tail)

theorem renderConnectedCutComponentSignature_nonempty
    {signature : ConnectedCutComponentSignature}
    (valid : ConnectedCutComponentSignatureValid signature) :
    renderConnectedCutComponentSignature signature ≠ [] := by
  cases signature with
  | mk base final =>
      cases base with
      | mk support repeatedUnary =>
          cases support with
          | nil => exact False.elim (valid.1.1 rfl)
          | cons first remaining =>
              cases remaining with
              | nil =>
                  cases repeatedUnary <;>
                    simp [renderConnectedCutComponentSignature]
              | cons second rest =>
                  simp [renderConnectedCutComponentSignature]

theorem renderConnectedCutComponentSignature_mem_iff
    {signature : ConnectedCutComponentSignature}
    (valid : ConnectedCutComponentSignatureValid signature)
    (tested : Nat) :
    tested ∈ renderConnectedCutComponentSignature signature ↔
      tested ∈ signature.base.support := by
  cases signature with
  | mk base final =>
      cases base with
      | mk support repeatedUnary =>
          cases support with
          | nil => exact False.elim (valid.1.1 rfl)
          | cons first remaining =>
              cases remaining with
              | nil =>
                  cases repeatedUnary <;>
                    simp [renderConnectedCutComponentSignature]
              | cons second rest =>
                  have supportNodup :
                      (first :: second :: rest).Nodup := valid.1.2.1
                  by_cases equal : tested = final
                  · subst tested
                    simp [renderConnectedCutComponentSignature, valid.2]
                  · simp [renderConnectedCutComponentSignature,
                      supportNodup.mem_erase_iff, equal]

theorem renderConnectedCutComponentSignature_exists_final
    {signature : ConnectedCutComponentSignature}
    (valid : ConnectedCutComponentSignatureValid signature) :
    ∃ body,
      renderConnectedCutComponentSignature signature =
        body ++ [signature.final] := by
  cases signature with
  | mk base final =>
      cases base with
      | mk support repeatedUnary =>
          cases support with
          | nil => exact False.elim (valid.1.1 rfl)
          | cons first remaining =>
              cases remaining with
              | nil =>
                  have finalEq : final = first := by
                    simpa using valid.2
                  subst final
                  cases repeatedUnary with
                  | false =>
                      exact ⟨[], by simp [renderConnectedCutComponentSignature]⟩
                  | true =>
                      exact ⟨[first], by
                        simp [renderConnectedCutComponentSignature]⟩
              | cons second rest =>
                  exact
                    ⟨final :: (first :: second :: rest).erase final,
                      by simp [renderConnectedCutComponentSignature,
                        List.append_assoc]⟩

theorem renderConnectedCutSignatures_append
    (left right : List ConnectedCutComponentSignature) :
    renderConnectedCutSignatures (left ++ right) =
      renderConnectedCutSignatures left ++
        renderConnectedCutSignatures right := by
  simp [renderConnectedCutSignatures, List.flatMap_append]

theorem connectedCutSignatureSupport_append
    (left right : List ConnectedCutComponentSignature) :
    connectedCutSignatureSupport (left ++ right) =
      connectedCutSignatureSupport left ++
        connectedCutSignatureSupport right := by
  simp [connectedCutSignatureSupport, List.flatMap_append]

theorem renderConnectedCutSignatures_mem_iff
    {signatures : List ConnectedCutComponentSignature}
    (valid :
      ∀ signature, signature ∈ signatures →
        ConnectedCutComponentSignatureValid signature)
    (tested : Nat) :
    tested ∈ renderConnectedCutSignatures signatures ↔
      tested ∈ connectedCutSignatureSupport signatures := by
  simp only [renderConnectedCutSignatures, connectedCutSignatureSupport,
    List.mem_flatMap]
  constructor
  · rintro ⟨signature, signatureMember, testedMember⟩
    exact
      ⟨signature, signatureMember,
        (renderConnectedCutComponentSignature_mem_iff
          (valid signature signatureMember) tested).1 testedMember⟩
  · rintro ⟨signature, signatureMember, testedMember⟩
    exact
      ⟨signature, signatureMember,
        (renderConnectedCutComponentSignature_mem_iff
          (valid signature signatureMember) tested).2 testedMember⟩

theorem renderConnectedCutSignatures_nonempty
    {signatures : List ConnectedCutComponentSignature}
    (valid :
      ∀ signature, signature ∈ signatures →
        ConnectedCutComponentSignatureValid signature)
    (nonempty : signatures ≠ []) :
    renderConnectedCutSignatures signatures ≠ [] := by
  rcases List.exists_cons_of_ne_nil nonempty with ⟨first, rest, rfl⟩
  intro renderedEmpty
  have firstNonempty :=
    renderConnectedCutComponentSignature_nonempty
      (valid first (by simp))
  simp only [renderConnectedCutSignatures, List.flatMap_cons]
    at renderedEmpty
  exact firstNonempty (List.append_eq_nil_iff.mp renderedEmpty).1

private theorem connectedCutBlocks_disjoint
    {left right : List ConnectedCutComponentSignature}
    (canonical : ConnectedCutCanonicalSignatures (left ++ right)) :
    ConnectedComponentSupportsDisjoint
      (connectedCutSignatureSupport left)
      (connectedCutSignatureSupport right) := by
  have pairwise :
      (left.map (·.base) ++ right.map (·.base)).Pairwise
        (fun first second =>
          ConnectedComponentSupportsDisjoint
            first.support second.support) := by
    simpa [List.map_append] using canonical.1.2
  have cross := (List.pairwise_append.mp pairwise).2.2
  intro letter leftMember rightMember
  simp only [connectedCutSignatureSupport, List.mem_flatMap]
    at leftMember rightMember
  rcases leftMember with
    ⟨leftSignature, leftSignatureMember, leftSupportMember⟩
  rcases rightMember with
    ⟨rightSignature, rightSignatureMember, rightSupportMember⟩
  exact
    (cross leftSignature.base
      (List.mem_map.mpr ⟨leftSignature, leftSignatureMember, rfl⟩)
      rightSignature.base
      (List.mem_map.mpr ⟨rightSignature, rightSignatureMember, rfl⟩))
      letter leftSupportMember rightSupportMember

/-- The refined marker reads the actual final variable of any displayed
component in a canonical signature list. -/
theorem finalCutMarker_detects
    (before : List ConnectedCutComponentSignature)
    (current : ConnectedCutComponentSignature)
    (after : List ConnectedCutComponentSignature)
    (canonical :
      ConnectedCutCanonicalSignatures (before ++ current :: after))
    (tested : Nat) (testedMember : tested ∈ current.base.support) :
    let prefixSupport :=
      connectedCutSignatureSupport (before ++ [current])
    evalList (finalCutValuation prefixSupport tested)
        (renderConnectedCutSignatures (before ++ current :: after)) =
      if after = [] then
        if current.final = tested then some 3 else some 2
      else
        if current.final = tested then some 1 else some 0 := by
  let prefixSignatures := before ++ [current]
  let prefixSupport := connectedCutSignatureSupport prefixSignatures
  have currentMember : current ∈ before ++ current :: after := by
    simp
  have currentValid : ConnectedCutComponentSignatureValid current :=
    ⟨canonical.1.1 current.base
        (List.mem_map.mpr ⟨current, currentMember, rfl⟩),
      canonical.2 current currentMember⟩
  obtain ⟨currentBody, currentShape⟩ :=
    renderConnectedCutComponentSignature_exists_final currentValid
  let body := renderConnectedCutSignatures before ++ currentBody
  have wholeShape :
      renderConnectedCutSignatures (before ++ current :: after) =
        body ++ [current.final] ++
          renderConnectedCutSignatures after := by
    simp [renderConnectedCutSignatures, List.flatMap_append,
      currentShape, body, List.append_assoc]
  have validAll :
      ∀ signature, signature ∈ before ++ current :: after →
        ConnectedCutComponentSignatureValid signature := by
    intro signature member
    exact
      ⟨canonical.1.1 signature.base
          (List.mem_map.mpr ⟨signature, member, rfl⟩),
        canonical.2 signature member⟩
  have bodySupported :
      ∀ letter, letter ∈ body → letter ∈ prefixSupport := by
    intro letter member
    simp only [body, List.mem_append] at member
    simp only [prefixSupport, prefixSignatures,
      connectedCutSignatureSupport_append, List.mem_append]
    rcases member with beforeMember | currentBodyMember
    · exact Or.inl <|
        (renderConnectedCutSignatures_mem_iff
          (fun signature signatureMember =>
            validAll signature
              (List.mem_append_left (current :: after) signatureMember))
          letter).1 beforeMember
    · apply Or.inr
      simpa [connectedCutSignatureSupport] using
        (renderConnectedCutComponentSignature_mem_iff
          currentValid letter).1 (by
            rw [currentShape]
            exact List.mem_append_left [current.final] currentBodyMember)
  have finalMember : current.final ∈ prefixSupport := by
    simp only [prefixSupport, prefixSignatures,
      connectedCutSignatureSupport_append, List.mem_append]
    exact Or.inr <| by
      simpa [connectedCutSignatureSupport] using currentValid.2
  have suffixUnsupported :
      ∀ letter,
        letter ∈ renderConnectedCutSignatures after →
          letter ∉ prefixSupport := by
    intro letter renderedMember prefixMember
    have afterSupport : letter ∈ connectedCutSignatureSupport after :=
      (renderConnectedCutSignatures_mem_iff
        (fun signature signatureMember =>
          validAll signature <| by
            simpa [List.append_assoc] using
              (List.mem_append_right
                (before ++ [current]) signatureMember))
        letter).1 renderedMember
    have disjoint :=
      connectedCutBlocks_disjoint
        (left := before ++ [current]) (right := after) <| by
          simpa [List.append_assoc] using canonical
    exact disjoint letter prefixMember afterSupport
  have renderedAfterEmpty_iff :
      renderConnectedCutSignatures after = [] ↔ after = [] := by
    constructor
    · intro renderedEmpty
      exact Classical.byContradiction fun afterNonempty =>
        (renderConnectedCutSignatures_nonempty
          (fun signature signatureMember =>
            validAll signature <| by
              simpa [List.append_assoc] using
                (List.mem_append_right
                  (before ++ [current]) signatureMember))
          afterNonempty) renderedEmpty
    · rintro rfl
      rfl
  rw [wholeShape]
  simpa only [renderedAfterEmpty_iff] using
    finalCutEvalList prefixSupport tested body current.final
      (renderConnectedCutSignatures after)
      (by
        simp only [prefixSupport, prefixSignatures,
          connectedCutSignatureSupport_append, List.mem_append]
        exact Or.inr <| by
          simpa [connectedCutSignatureSupport] using testedMember)
      bodySupported finalMember suffixUnsupported

/-! ## Exact signature reconstruction -/

private theorem signatures_eq_aux
    (fullLeft fullRight : List ConnectedCutComponentSignature)
    (leftCanonical : ConnectedCutCanonicalSignatures fullLeft)
    (rightCanonical : ConnectedCutCanonicalSignatures fullRight)
    (equalEval :
      ∀ valuation : Nat → Fin 5,
        evalList valuation (renderConnectedCutSignatures fullLeft) =
          evalList valuation (renderConnectedCutSignatures fullRight)) :
    ∀ (before leftRest rightRest : List ConnectedCutComponentSignature),
      fullLeft = before ++ leftRest →
      fullRight = before ++ rightRest →
      leftRest.map (·.base) = rightRest.map (·.base) →
      leftRest = rightRest := by
  intro before leftRest rightRest
  induction leftRest generalizing before rightRest with
  | nil =>
      intro leftShape rightShape baseEq
      have rightEmpty : rightRest = [] := by
        apply List.eq_nil_of_length_eq_zero
        have lengths := congrArg List.length baseEq
        simp only [List.length_map, List.length_nil] at lengths
        omega
      exact rightEmpty.symm
  | cons current leftTail induction =>
      intro leftShape rightShape baseEq
      cases rightRest with
      | nil => simp at baseEq
      | cons target rightTail =>
          have baseHead : current.base = target.base := by
            simpa using congrArg List.head? baseEq
          have baseTail :
              leftTail.map (·.base) = rightTail.map (·.base) := by
            simpa using congrArg List.tail baseEq
          have currentMember : current ∈ fullLeft := by
            rw [leftShape]
            exact List.mem_append_right before (by simp)
          have targetMember : target ∈ fullRight := by
            rw [rightShape]
            exact List.mem_append_right before (by simp)
          have currentValid :
              ConnectedCutComponentSignatureValid current :=
            ⟨leftCanonical.1.1 current.base
                (List.mem_map.mpr ⟨current, currentMember, rfl⟩),
              leftCanonical.2 current currentMember⟩
          have targetValid :
              ConnectedCutComponentSignatureValid target :=
            ⟨rightCanonical.1.1 target.base
                (List.mem_map.mpr ⟨target, targetMember, rfl⟩),
              rightCanonical.2 target targetMember⟩
          have testedMember : current.final ∈ current.base.support :=
            currentValid.2
          have targetTestedMember : current.final ∈ target.base.support := by
            rwa [← baseHead]
          have leftCanonicalSplit :
              ConnectedCutCanonicalSignatures
                (before ++ current :: leftTail) := by
            rwa [← leftShape]
          have rightCanonicalSplit :
              ConnectedCutCanonicalSignatures
                (before ++ target :: rightTail) := by
            rwa [← rightShape]
          have finalEq : current.final = target.final := by
            let prefixSupport :=
              connectedCutSignatureSupport (before ++ [current])
            let valuation :=
              finalCutValuation prefixSupport current.final
            have evaluations := equalEval valuation
            rw [leftShape, rightShape] at evaluations
            have leftDetected :=
              finalCutMarker_detects before current leftTail
                leftCanonicalSplit current.final testedMember
            have rightDetected :=
              finalCutMarker_detects before target rightTail
                rightCanonicalSplit current.final targetTestedMember
            have leftMarker :
                evalList valuation
                    (renderConnectedCutSignatures
                      (before ++ current :: leftTail)) =
                  if leftTail = [] then some 3 else some 1 := by
              simpa [prefixSupport, valuation] using leftDetected
            have rightMarker :
                evalList valuation
                    (renderConnectedCutSignatures
                      (before ++ target :: rightTail)) =
                  if rightTail = [] then
                    if target.final = current.final then some 3 else some 2
                  else
                    if target.final = current.final then some 1 else some 0 := by
              simpa [prefixSupport, valuation, connectedCutSignatureSupport,
                baseHead] using rightDetected
            by_cases leftTailEmpty : leftTail = []
            · subst leftTail
              have rightTailEmpty : rightTail = [] := by
                apply List.eq_nil_of_length_eq_zero
                have lengths := congrArg List.length baseTail
                simp only [List.length_map, List.length_nil] at lengths
                omega
              subst rightTail
              rw [leftMarker, rightMarker] at evaluations
              simp at evaluations
              exact evaluations.symm
            · have rightTailNonempty : rightTail ≠ [] := by
                intro rightEmpty
                subst rightTail
                apply leftTailEmpty
                apply List.eq_nil_of_length_eq_zero
                have lengths := congrArg List.length baseTail
                simp only [List.length_map, List.length_nil] at lengths
                omega
              rw [leftMarker, rightMarker] at evaluations
              simp [leftTailEmpty, rightTailNonempty] at evaluations
              exact evaluations.symm
          have currentEq : current = target := by
            cases current
            cases target
            simp_all
          subst target
          congr 1
          apply induction (before ++ [current]) rightTail
          · simpa [List.append_assoc] using leftShape
          · simpa [List.append_assoc] using rightShape
          · exact baseTail

theorem connectedCutSignatures_eq_of_base_eq_and_equalEval
    (left right : List ConnectedCutComponentSignature)
    (leftCanonical : ConnectedCutCanonicalSignatures left)
    (rightCanonical : ConnectedCutCanonicalSignatures right)
    (baseEq : left.map (·.base) = right.map (·.base))
    (equalEval :
      ∀ valuation : Nat → Fin 5,
        evalList valuation (renderConnectedCutSignatures left) =
          evalList valuation (renderConnectedCutSignatures right)) :
    left = right := by
  exact signatures_eq_aux left right leftCanonical rightCanonical
    equalEval [] left right (by simp) (by simp) baseEq

/-- Exact table separation: every identity of the catalogue representative
preserves the complete ordered connected-cut signature. -/
theorem valid_sameConnectedCutSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_804.table.semigroup) :
    SameConnectedCutSignature identity.lhs identity.rhs := by
  let leftSignatures := connectedCutSignaturesWord identity.lhs
  let rightSignatures := connectedCutSignaturesWord identity.rhs
  have baseEq :
      leftSignatures.map (·.base) = rightSignatures.map (·.base) := by
    simpa [leftSignatures, rightSignatures, connectedCutSignaturesWord,
      connectedCutSignaturesList, connectedCutComponentSignatureOfList,
      List.map_map] using
        valid_sameBaseComponentSignatures identity valid
  have normalizedEval :
      ∀ valuation : Nat → Fin 5,
        table.semigroup.eval valuation (canonicalRender identity.lhs) =
          table.semigroup.eval valuation (canonicalRender identity.rhs) := by
    intro valuation
    have lhsSound :=
      (derivesCanonical identity.lhs).sound catalogueModels valuation
    have rhsSound :=
      (derivesCanonical identity.rhs).sound catalogueModels valuation
    exact lhsSound.symm.trans <| (valid valuation).trans rhsSound
  have equalList :
      ∀ valuation : Nat → Fin 5,
        evalList valuation (renderConnectedCutSignatures leftSignatures) =
          evalList valuation (renderConnectedCutSignatures rightSignatures) := by
    intro valuation
    have evaluated := normalizedEval valuation
    have leftList := evalList_toList valuation (canonicalRender identity.lhs)
    have rightList := evalList_toList valuation (canonicalRender identity.rhs)
    rw [canonicalRender_toList] at leftList rightList
    have optionEquality := congrArg some evaluated
    have combined := leftList.trans (optionEquality.trans rightList.symm)
    simpa [canonicalRenderList, leftSignatures, rightSignatures] using
      combined
  exact connectedCutSignatures_eq_of_base_eq_and_equalEval
    leftSignatures rightSignatures
    (connectedCutSignaturesWord_canonical identity.lhs)
    (connectedCutSignaturesWord_canonical identity.rhs)
    baseEq equalList

/-- Every derivation from the eight laws preserves the exact signature. -/
theorem derives_sameConnectedCutSignature
    {left right : Word Nat} (derivation : Derives basis left right) :
    SameConnectedCutSignature left right := by
  let identity : Identity Nat := ⟨left, right⟩
  exact valid_sameConnectedCutSignature identity <| fun valuation =>
    derivation.sound catalogueModels valuation

end SemigroupBasis.CoRoots.S5_804
