import SemigroupBasis.Word

namespace SemigroupBasis
namespace FiniteVariableRenaming

/-- A simultaneously normalized pair and the renamings in both directions. -/
structure Result (α : Type u) where
  left : Word Nat
  right : Word Nat
  forward : α → Nat
  inverse : Nat → α

namespace Result

/-- The normalized pair viewed as one left-to-right sequence of variable names. -/
def pattern (result : Result α) : List Nat :=
  result.left.toList ++ result.right.toList

end Result

/--
`RestrictedGrowthFrom next codes final` means that `codes` is a restricted-growth
suffix whose previously available names are `0, ..., next - 1`, and that `final`
is the number of available names after the suffix has been read.
-/
inductive RestrictedGrowthFrom : Nat → List Nat → Nat → Prop
  | nil (next : Nat) : RestrictedGrowthFrom next [] next
  | seen {next final code : Nat} {rest : List Nat} :
      code < next →
        RestrictedGrowthFrom next rest final →
          RestrictedGrowthFrom next (code :: rest) final
  | fresh {next final : Nat} {rest : List Nat} :
      RestrictedGrowthFrom (next + 1) rest final →
        RestrictedGrowthFrom next (next :: rest) final

/-- A restricted-growth sequence starts with no available variable names. -/
def IsRestrictedGrowth (codes : List Nat) : Prop :=
  ∃ final, RestrictedGrowthFrom 0 codes final

private def RestrictedGrowthFrom.append
    {start middle final : Nat} {left right : List Nat}
    (first : RestrictedGrowthFrom start left middle)
    (second : RestrictedGrowthFrom middle right final) :
    RestrictedGrowthFrom start (left ++ right) final :=
  match first with
  | .nil _ => second
  | .seen smaller rest =>
      RestrictedGrowthFrom.seen smaller (rest.append second)
  | .fresh rest =>
      RestrictedGrowthFrom.fresh (rest.append second)

private structure RenameState (α : Type u) where
  next : Nat
  encode : α → Option Nat
  decode : Nat → α
  decode_encode :
    ∀ {letter : α} {code : Nat},
      encode letter = some code → decode code = letter
  encode_lt_next :
    ∀ {letter : α} {code : Nat},
      encode letter = some code → code < next

private def RenameState.forward (state : RenameState α) (letter : α) : Nat :=
  (state.encode letter).getD 0

private theorem RenameState.forward_eq_of_encode
    (state : RenameState α) {letter : α} {code : Nat}
    (encoded : state.encode letter = some code) :
    state.forward letter = code := by
  simp [RenameState.forward, encoded]

private def RenameState.empty (fallback : α) : RenameState α where
  next := 0
  encode := fun _ => none
  decode := fun _ => fallback
  decode_encode := by
    intro letter code impossible
    cases impossible
  encode_lt_next := by
    intro letter code impossible
    cases impossible

private def RenameState.insert [DecidableEq α]
    (state : RenameState α) (fresh : α) : RenameState α where
  next := state.next + 1
  encode := fun letter =>
    if letter = fresh then some state.next else state.encode letter
  decode := fun code =>
    if code = state.next then fresh else state.decode code
  decode_encode := by
    intro letter code encoded
    by_cases isFresh : letter = fresh
    · subst letter
      have codeEq : state.next = code := by
        simpa using encoded
      subst code
      simp
    · simp only [if_neg isFresh] at encoded
      have codeNe : code ≠ state.next :=
        Nat.ne_of_lt (state.encode_lt_next encoded)
      change
        (if code = state.next then fresh else state.decode code) = letter
      rw [if_neg codeNe]
      exact state.decode_encode encoded
  encode_lt_next := by
    intro letter code encoded
    by_cases isFresh : letter = fresh
    · subst letter
      have codeEq : state.next = code := by
        simpa using encoded
      subst code
      exact Nat.lt_succ_self state.next
    · simp only [if_neg isFresh] at encoded
      exact Nat.lt_trans
        (state.encode_lt_next encoded) (Nat.lt_succ_self state.next)

private theorem RenameState.insert_encode_self [DecidableEq α]
    (state : RenameState α) (fresh : α) :
    (state.insert fresh).encode fresh = some state.next := by
  simp [RenameState.insert]

private theorem RenameState.insert_preserves [DecidableEq α]
    (state : RenameState α) {fresh other : α} {code : Nat}
    (freshNotEncoded : state.encode fresh = none)
    (otherEncoded : state.encode other = some code) :
    (state.insert fresh).encode other = some code := by
  by_cases same : other = fresh
  · subst other
    rw [freshNotEncoded] at otherEncoded
    cases otherEncoded
  · change
      (if other = fresh then some state.next else state.encode other) =
        some code
    rw [if_neg same]
    exact otherEncoded

private structure InternResult (initial : RenameState α) (letter : α) where
  code : Nat
  state : RenameState α
  preserves :
    ∀ {other : α} {otherCode : Nat},
      initial.encode other = some otherCode →
        state.encode other = some otherCode
  encoded : state.encode letter = some code
  growth :
    ∀ {rest : List Nat} {final : Nat},
      RestrictedGrowthFrom state.next rest final →
        RestrictedGrowthFrom initial.next (code :: rest) final

private def intern [DecidableEq α]
    (initial : RenameState α) (letter : α) :
    InternResult initial letter :=
  match encoded : initial.encode letter with
  | some code =>
      {
        code := code
        state := initial
        preserves := fun previous => previous
        encoded := encoded
        growth := fun restGrowth =>
          RestrictedGrowthFrom.seen
            (initial.encode_lt_next encoded) restGrowth
      }
  | none =>
      {
        code := initial.next
        state := initial.insert letter
        preserves := fun previous =>
          initial.insert_preserves encoded previous
        encoded := initial.insert_encode_self letter
        growth := fun restGrowth =>
          RestrictedGrowthFrom.fresh restGrowth
      }

private inductive Encodes (state : RenameState α) :
    List α → List Nat → Prop
  | nil : Encodes state [] []
  | cons {letter : α} {code : Nat}
      {letters : List α} {codes : List Nat} :
      state.encode letter = some code →
        Encodes state letters codes →
          Encodes state (letter :: letters) (code :: codes)

private structure ListScanResult
    (initial : RenameState α) (letters : List α) where
  codes : List Nat
  state : RenameState α
  preserves :
    ∀ {letter : α} {code : Nat},
      initial.encode letter = some code → state.encode letter = some code
  encodes : Encodes state letters codes
  growth : RestrictedGrowthFrom initial.next codes state.next

private def scanList [DecidableEq α] :
    (initial : RenameState α) → (letters : List α) →
      ListScanResult initial letters
  | initial, [] =>
      {
        codes := []
        state := initial
        preserves := fun encoded => encoded
        encodes := Encodes.nil
        growth := RestrictedGrowthFrom.nil initial.next
      }
  | initial, letter :: rest =>
      let first := intern initial letter
      let tail := scanList first.state rest
      {
        codes := first.code :: tail.codes
        state := tail.state
        preserves := fun encoded =>
          tail.preserves (first.preserves encoded)
        encodes := Encodes.cons
          (tail.preserves first.encoded) tail.encodes
        growth := first.growth tail.growth
      }

private structure WordScanResult
    (initial : RenameState α) (word : Word α) where
  normalized : Word Nat
  state : RenameState α
  preserves :
    ∀ {letter : α} {code : Nat},
      initial.encode letter = some code → state.encode letter = some code
  encodes : Encodes state word.toList normalized.toList
  growth :
    RestrictedGrowthFrom initial.next normalized.toList state.next

private def scanWord [DecidableEq α]
    (initial : RenameState α) (word : Word α) :
    WordScanResult initial word :=
  let first := intern initial word.head
  let tail := scanList first.state word.tail
  {
    normalized := ⟨first.code, tail.codes⟩
    state := tail.state
    preserves := fun encoded =>
      tail.preserves (first.preserves encoded)
    encodes := Encodes.cons
      (tail.preserves first.encoded) tail.encodes
    growth := first.growth tail.growth
  }

private theorem encodes_mono
    {first second : RenameState α}
    (preserves :
      ∀ {letter : α} {code : Nat},
        first.encode letter = some code → second.encode letter = some code)
    {letters : List α} {codes : List Nat}
    (encoded : Encodes first letters codes) :
    Encodes second letters codes := by
  induction encoded with
  | nil => exact Encodes.nil
  | cons headEncoded restEncoded induction =>
      exact Encodes.cons (preserves headEncoded) induction

private theorem map_decode_eq
    (state : RenameState α) {letters : List α} {codes : List Nat}
    (encoded : Encodes state letters codes) :
    codes.map state.decode = letters := by
  induction encoded with
  | nil => rfl
  | cons headEncoded restEncoded induction =>
      simp only [List.map_cons]
      rw [state.decode_encode headEncoded, induction]

private theorem map_forward_eq
    (state : RenameState α) {letters : List α} {codes : List Nat}
    (encoded : Encodes state letters codes) :
    letters.map state.forward = codes := by
  induction encoded with
  | nil => rfl
  | cons headEncoded restEncoded induction =>
      simp only [List.map_cons]
      rw [state.forward_eq_of_encode headEncoded, induction]

private theorem word_map_decode_eq
    (state : RenameState α) {word : Word α} {normalized : Word Nat}
    (encoded : Encodes state word.toList normalized.toList) :
    normalized.map state.decode = word := by
  apply Word.toList_injective
  change normalized.toList.map state.decode = word.toList
  exact map_decode_eq state encoded

private theorem word_map_forward_eq
    (state : RenameState α) {word : Word α} {normalized : Word Nat}
    (encoded : Encodes state word.toList normalized.toList) :
    word.map state.forward = normalized := by
  apply Word.toList_injective
  change word.toList.map state.forward = normalized.toList
  exact map_forward_eq state encoded

private structure Certified (left right : Word α) where
  result : Result α
  normalizes :
    left.map result.forward = result.left ∧
      right.map result.forward = result.right
  reconstructs :
    result.left.map result.inverse = left ∧
      result.right.map result.inverse = right
  restrictedGrowth : IsRestrictedGrowth result.pattern

private def certified [DecidableEq α]
    (left right : Word α) : Certified left right := by
  let leftScan := scanWord (RenameState.empty left.head) left
  let rightScan := scanWord leftScan.state right
  have leftEncoded := encodes_mono rightScan.preserves leftScan.encodes
  refine {
    result := {
      left := leftScan.normalized
      right := rightScan.normalized
      forward := rightScan.state.forward
      inverse := rightScan.state.decode
    }
    normalizes := ?_
    reconstructs := ?_
    restrictedGrowth := ?_
  }
  · exact ⟨word_map_forward_eq rightScan.state leftEncoded,
      word_map_forward_eq rightScan.state rightScan.encodes⟩
  · exact ⟨word_map_decode_eq rightScan.state leftEncoded,
      word_map_decode_eq rightScan.state rightScan.encodes⟩
  · refine ⟨rightScan.state.next, ?_⟩
    exact RestrictedGrowthFrom.append leftScan.growth rightScan.growth

/--
Rename variables by first occurrence, scanning the left word before the right
word. Unused natural numbers are sent to the left word's head by `inverse`.
-/
def normalize [DecidableEq α] (left right : Word α) : Result α :=
  (certified left right).result

/-- The returned forward renaming simultaneously produces both normalized words. -/
theorem normalize_normalizes [DecidableEq α] (left right : Word α) :
    let result := normalize left right
    left.map result.forward = result.left ∧
      right.map result.forward = result.right := by
  exact (certified left right).normalizes

/-- The returned inverse simultaneously reconstructs both input words. -/
theorem normalize_reconstructs [DecidableEq α] (left right : Word α) :
    let result := normalize left right
    result.left.map result.inverse = left ∧
      result.right.map result.inverse = right := by
  exact (certified left right).reconstructs

/-- The concatenated normalized pair is a restricted-growth sequence. -/
theorem normalize_isRestrictedGrowth [DecidableEq α]
    (left right : Word α) :
    IsRestrictedGrowth (normalize left right).pattern := by
  exact (certified left right).restrictedGrowth

end FiniteVariableRenaming
end SemigroupBasis
