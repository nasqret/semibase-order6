import SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleSwap

set_option maxRecDepth 100000

/-!
The Σ4 normal form of an arbitrary word list and its derivation.

* `iniScan` separates the first occurrences (`ini`) from the remaining
  occurrences (`rest`); inside `w ++ Q` with every letter of `w` recurring in
  `Q`, the first occurrences bubble to the front.
* `lastScan` cuts a word into segments of non-last occurrences, each
  terminated by a last occurrence (the marker).
* `normalForm w = ini w ++ canon (rest w ++ w ++ S₀) ++ z₁ :: renderCanonFactors tail`
  where `lastScan [] w = (S₀, z₁) :: tail`, and `w` derives to it via
  `w → www`, first-occurrence extraction in the first copy, canonicalisation
  of the middle region, and canonicalisation of every segment of the third copy.
-/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleScan

open SemigroupBasis
open Msg0607TripleTables
open Msg0607TripleRules
open Msg0607TripleSwap

/-! ## Moving a letter left across junk -/

/-- Move `x` leftwards across `M` when every letter of `M` occurs in `P` and
`x` and every letter of `M` occur in `Q`. -/
theorem listDerivesMoveLeft (x : Nat) (Q : List Nat) (xQ : x ∈ Q) :
    ∀ (M P : List Nat), (∀ m ∈ M, m ∈ P) → (∀ m ∈ M, m ∈ Q) →
      ListDerives (P ++ M ++ [x] ++ Q) (P ++ [x] ++ M ++ Q)
  | [], P, _, _ => by
      simpa using S5_107.ListDerives.refl (basis := basis) (P ++ [x] ++ Q)
  | m :: M, P, MP, MQ => by
      have ih := listDerivesMoveLeft x Q xQ M (P ++ [m])
        (fun c mem => List.mem_append_left _ (MP c (by simp [mem])))
        (fun c mem => MQ c (by simp [mem]))
      have swapped := listDerivesSwap P (M ++ Q) m x (MP m (by simp))
        (List.mem_append_right _ (MQ m (by simp))) (List.mem_append_right _ xQ)
      have step1 : ListDerives (P ++ (m :: M) ++ [x] ++ Q) (P ++ [m, x] ++ (M ++ Q)) := by
        simpa [List.append_assoc] using ih
      have step2 : ListDerives (P ++ [m, x] ++ (M ++ Q)) (P ++ [x] ++ (m :: M) ++ Q) := by
        simpa [List.append_assoc] using swapped
      exact step1.trans step2

/-! ## First occurrences -/

/-- Scan with the first occurrences seen so far and the collected repeats. -/
def iniScan (seen junk : List Nat) : List Nat → List Nat × List Nat
  | [] => (seen, junk)
  | x :: w => if x ∈ seen then iniScan seen (junk ++ [x]) w else iniScan (seen ++ [x]) junk w

def ini (w : List Nat) : List Nat := (iniScan [] [] w).1

def rest (w : List Nat) : List Nat := (iniScan [] [] w).2

theorem listDerivesIniScan (Q : List Nat) :
    ∀ (w seen junk : List Nat), (∀ m ∈ junk, m ∈ seen) → (∀ c ∈ w, c ∈ Q) → (∀ m ∈ junk, m ∈ Q) →
      ListDerives (seen ++ junk ++ w ++ Q)
        ((iniScan seen junk w).1 ++ (iniScan seen junk w).2 ++ Q)
  | [], seen, junk, _, _, _ => by
      simpa [iniScan] using S5_107.ListDerives.refl (basis := basis) (seen ++ junk ++ Q)
  | x :: w, seen, junk, junkSeen, wQ, junkQ => by
      have xQ : x ∈ Q := wQ x (by simp)
      have wQ' : ∀ c ∈ w, c ∈ Q := fun c mem => wQ c (by simp [mem])
      by_cases mem : x ∈ seen
      · have ih := listDerivesIniScan Q w seen (junk ++ [x])
          (fun m hm => by
            rw [List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | rfl
            · exact junkSeen m hm
            · exact mem)
          wQ'
          (fun m hm => by
            rw [List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | rfl
            · exact junkQ m hm
            · exact xQ)
        simpa [iniScan, mem, List.append_assoc] using ih
      · have move := listDerivesMoveLeft x (w ++ Q) (List.mem_append_right _ xQ) junk seen junkSeen
          (fun m hm => List.mem_append_right _ (junkQ m hm))
        have ih := listDerivesIniScan Q w (seen ++ [x]) junk
          (fun m hm => List.mem_append_left _ (junkSeen m hm)) wQ' junkQ
        have step1 : ListDerives (seen ++ junk ++ (x :: w) ++ Q) ((seen ++ [x]) ++ junk ++ w ++ Q) := by
          simpa [List.append_assoc] using move
        have step2 : ListDerives ((seen ++ [x]) ++ junk ++ w ++ Q)
            ((iniScan seen junk (x :: w)).1 ++ (iniScan seen junk (x :: w)).2 ++ Q) := by
          simpa [iniScan, mem] using ih
        exact step1.trans step2

theorem iniScan_perm :
    ∀ (w seen junk : List Nat),
      ((iniScan seen junk w).1 ++ (iniScan seen junk w).2).Perm (seen ++ junk ++ w)
  | [], seen, junk => by simp [iniScan]
  | x :: w, seen, junk => by
      by_cases mem : x ∈ seen
      · have ih := iniScan_perm w seen (junk ++ [x])
        simpa [iniScan, mem, List.append_assoc] using ih
      · have ih := iniScan_perm w (seen ++ [x]) junk
        simp only [iniScan, mem, if_false]
        refine ih.trans ?_
        have middle : (seen ++ (x :: (junk ++ w))).Perm (seen ++ (junk ++ x :: w)) :=
          List.Perm.append_left seen List.perm_middle.symm
        simpa [List.append_assoc] using middle

theorem mem_iniScan_fst (c : Nat) :
    ∀ (w seen junk : List Nat), c ∈ (iniScan seen junk w).1 ↔ c ∈ seen ∨ c ∈ w
  | [], seen, junk => by simp [iniScan]
  | x :: w, seen, junk => by
      by_cases mem : x ∈ seen
      · have ih := mem_iniScan_fst c w seen (junk ++ [x])
        rw [iniScan, if_pos mem, ih]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (by simp [h])
        · rintro (h | h)
          · exact Or.inl h
          · simp only [List.mem_cons] at h
            rcases h with rfl | h
            · exact Or.inl mem
            · exact Or.inr h
      · have ih := mem_iniScan_fst c w (seen ++ [x]) junk
        rw [iniScan, if_neg mem, ih, List.mem_append, List.mem_singleton, List.mem_cons]
        exact or_assoc

theorem iniScan_fst_nodup :
    ∀ (w seen junk : List Nat), seen.Nodup → (iniScan seen junk w).1.Nodup
  | [], seen, junk, nodup => by simpa [iniScan] using nodup
  | x :: w, seen, junk, nodup => by
      by_cases mem : x ∈ seen
      · rw [iniScan, if_pos mem]
        exact iniScan_fst_nodup w seen (junk ++ [x]) nodup
      · rw [iniScan, if_neg mem]
        apply iniScan_fst_nodup w (seen ++ [x]) junk
        have perm : (seen ++ [x]).Perm (x :: seen) := by
          simp
        exact perm.nodup_iff.mpr (List.nodup_cons.mpr ⟨mem, nodup⟩)

theorem ini_rest_perm (w : List Nat) : (ini w ++ rest w).Perm w := by
  simpa [ini, rest] using iniScan_perm w [] []

theorem mem_ini (c : Nat) (w : List Nat) : c ∈ ini w ↔ c ∈ w := by
  simp [ini, mem_iniScan_fst]

theorem ini_nodup (w : List Nat) : (ini w).Nodup :=
  iniScan_fst_nodup w [] [] List.nodup_nil

theorem mem_rest (c : Nat) (w : List Nat) (mem : c ∈ rest w) : c ∈ w :=
  (ini_rest_perm w).mem_iff.mp (List.mem_append_right _ mem)

theorem count_rest (c : Nat) (w : List Nat) (mem : c ∈ w) : (rest w).count c + 1 = w.count c := by
  have total := (ini_rest_perm w).count_eq c
  rw [List.count_append] at total
  have one : (ini w).count c = 1 := by
    rw [(ini_nodup w).count]
    simp [mem_ini, mem]
  omega

theorem count_rest_of_not_mem (c : Nat) (w : List Nat) (absent : c ∉ w) : (rest w).count c = 0 :=
  List.count_eq_zero.mpr fun mem => absent (mem_rest c w mem)

/-- The first-occurrence list derives to the front of `w ++ Q` when every
letter of `w` recurs in `Q`. -/
theorem listDerivesIni (w Q : List Nat) (wQ : ∀ c ∈ w, c ∈ Q) :
    ListDerives (w ++ Q) (ini w ++ rest w ++ Q) := by
  have step := listDerivesIniScan Q w [] [] (by simp) wQ (by simp)
  simpa [ini, rest] using step

/-! ## Last occurrences -/

/-- Segments of non-last occurrences, each terminated by a last occurrence. -/
def lastScan (current : List Nat) : List Nat → List (List Nat × Nat)
  | [] => []
  | x :: w => if x ∈ w then lastScan (current ++ [x]) w else (current, x) :: lastScan [] w

def renderFactors : List (List Nat × Nat) → List Nat
  | [] => []
  | (block, marker) :: rest => block ++ marker :: renderFactors rest

def renderCanonFactors : List (List Nat × Nat) → List Nat
  | [] => []
  | (block, marker) :: rest => canon block ++ marker :: renderCanonFactors rest

def markers (factors : List (List Nat × Nat)) : List Nat := factors.map fun factor => factor.2

theorem markers_cons (factor : List Nat × Nat) (rest : List (List Nat × Nat)) :
    markers (factor :: rest) = factor.2 :: markers rest := rfl

theorem renderFactors_lastScan :
    ∀ (w current : List Nat), w ≠ [] → renderFactors (lastScan current w) = current ++ w
  | [], _, nonempty => absurd rfl nonempty
  | x :: w, current, _ => by
      by_cases mem : x ∈ w
      · have nonempty : w ≠ [] := fun empty => by simp [empty] at mem
        rw [lastScan, if_pos mem, renderFactors_lastScan w (current ++ [x]) nonempty]
        simp
      · rw [lastScan, if_neg mem]
        cases w with
        | nil => simp [lastScan, renderFactors]
        | cons y w' =>
            rw [renderFactors]
            rw [renderFactors_lastScan (y :: w') [] (by simp)]
            simp

theorem mem_markers_lastScan (c : Nat) :
    ∀ (w current : List Nat), c ∈ markers (lastScan current w) ↔ c ∈ w
  | [], current => by simp [lastScan, markers]
  | x :: w, current => by
      by_cases mem : x ∈ w
      · rw [lastScan, if_pos mem, mem_markers_lastScan c w (current ++ [x])]
        constructor
        · intro h
          exact List.mem_cons_of_mem _ h
        · intro h
          simp only [List.mem_cons] at h
          rcases h with rfl | h
          · exact mem
          · exact h
      · rw [lastScan, if_neg mem, markers_cons]
        simp only [List.mem_cons, mem_markers_lastScan c w []]

theorem markers_lastScan_nodup :
    ∀ (w current : List Nat), (markers (lastScan current w)).Nodup
  | [], current => by simp [lastScan, markers]
  | x :: w, current => by
      by_cases mem : x ∈ w
      · rw [lastScan, if_pos mem]
        exact markers_lastScan_nodup w (current ++ [x])
      · rw [lastScan, if_neg mem, markers_cons]
        refine List.nodup_cons.mpr ⟨?_, markers_lastScan_nodup w []⟩
        rw [mem_markers_lastScan]
        exact mem

theorem lastScan_ne_nil (w current : List Nat) (nonempty : w ≠ []) : lastScan current w ≠ [] := by
  intro empty
  have render := renderFactors_lastScan w current nonempty
  rw [empty] at render
  simp only [renderFactors] at render
  have : (current ++ w).length = 0 := by rw [← render]; rfl
  rw [List.length_append] at this
  cases w with
  | nil => exact nonempty rfl
  | cons _ _ => simp at this

/-- Every block letter recurs as its own marker or a later marker. -/
def Wellformed : List (List Nat × Nat) → Prop
  | [] => True
  | (block, marker) :: rest => (∀ c ∈ block, c = marker ∨ c ∈ markers rest) ∧ Wellformed rest

theorem lastScan_wellformed :
    ∀ (w current : List Nat), (∀ c ∈ current, c ∈ w) → Wellformed (lastScan current w)
  | [], current, _ => by simp [lastScan, Wellformed]
  | x :: w, current, currentW => by
      by_cases mem : x ∈ w
      · rw [lastScan, if_pos mem]
        apply lastScan_wellformed w (current ++ [x])
        intro c hc
        rw [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · have := currentW c hc
          simp only [List.mem_cons] at this
          rcases this with rfl | this
          · exact mem
          · exact this
        · exact mem
      · rw [lastScan, if_neg mem]
        refine ⟨?_, lastScan_wellformed w [] (by simp)⟩
        intro c hc
        have := currentW c hc
        simp only [List.mem_cons] at this
        rcases this with rfl | this
        · exact Or.inl rfl
        · exact Or.inr ((mem_markers_lastScan c w []).mpr this)

theorem marker_mem_renderFactors :
    ∀ (factors : List (List Nat × Nat)) (c : Nat), c ∈ markers factors → c ∈ renderFactors factors
  | [], c, mem => by simp [markers] at mem
  | (block, marker) :: rest, c, mem => by
      rw [markers_cons] at mem
      simp only [List.mem_cons] at mem
      rw [renderFactors]
      rcases mem with rfl | mem
      · simp
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (marker_mem_renderFactors rest c mem))

/-- Canonicalise every segment of a wellformed factor list behind a prefix
containing all its letters. -/
theorem listDerivesCanonFactors :
    ∀ (factors : List (List Nat × Nat)) (L : List Nat), Wellformed factors →
      (∀ c ∈ renderFactors factors, c ∈ L) →
      ListDerives (L ++ renderFactors factors) (L ++ renderCanonFactors factors)
  | [], L, _, _ => by
      simpa [renderFactors, renderCanonFactors] using S5_107.ListDerives.refl (basis := basis) L
  | (block, marker) :: rest, L, wellformed, letters => by
      obtain ⟨blockLater, restWellformed⟩ := wellformed
      have blockBefore : ∀ c ∈ block, c ∈ L := fun c mem =>
        letters c (by rw [renderFactors]; exact List.mem_append_left _ mem)
      have blockAfter : ∀ c ∈ block, c ∈ marker :: renderFactors rest := by
        intro c mem
        rcases blockLater c mem with rfl | later
        · simp
        · exact List.mem_cons_of_mem _ (marker_mem_renderFactors rest c later)
      have step1 := listDerivesCanonRegion L (marker :: renderFactors rest) block.length block
        (Nat.le_refl _) blockBefore blockAfter
      have restLetters : ∀ c ∈ renderFactors rest, c ∈ L ++ canon block ++ [marker] := by
        intro c mem
        apply List.mem_append_left
        apply List.mem_append_left
        exact letters c (by rw [renderFactors]; exact List.mem_append_right _ (List.mem_cons_of_mem _ mem))
      have step2 := listDerivesCanonFactors rest (L ++ canon block ++ [marker]) restWellformed restLetters
      rw [renderFactors, renderCanonFactors]
      refine S5_107.ListDerives.trans (middle := L ++ canon block ++ marker :: renderFactors rest) ?_ ?_
      · simpa [List.append_assoc] using step1
      · simpa [List.append_assoc] using step2

/-! ## The normal form -/

def normalForm (w : List Nat) : List Nat :=
  match lastScan [] w with
  | [] => ini w ++ rest w
  | (first, marker) :: tail => ini w ++ canon (rest w ++ w ++ first) ++ marker :: renderCanonFactors tail

theorem listDerivesTriple (h : Nat) (t : List Nat) :
    ListDerives (h :: t) ((h :: t) ++ (h :: t) ++ (h :: t)) := by
  simpa [Word.toList, Word.append] using S5_107.ListDerives.ofWord (derivesCube ⟨h, t⟩)

/-- Every word list derives to its normal form. -/
theorem listDerivesNormalForm (w : List Nat) : ListDerives w (normalForm w) := by
  cases shape : lastScan [] w with
  | nil =>
      cases w with
      | nil =>
          simp only [normalForm, shape, ini, rest, iniScan, List.append_nil]
          exact S5_107.ListDerives.refl _
      | cons h t => exact absurd shape (lastScan_ne_nil (h :: t) [] (by simp))
  | cons firstFactor tail =>
      rcases firstFactor with ⟨first, marker⟩
      cases w with
      | nil => simp [lastScan] at shape
      | cons h t =>
          have render := renderFactors_lastScan (h :: t) [] (by simp)
          rw [shape, renderFactors, List.nil_append] at render
          -- render : first ++ marker :: renderFactors tail = h :: t
          have wellformed := lastScan_wellformed (h :: t) [] (by simp)
          rw [shape] at wellformed
          obtain ⟨_, tailWellformed⟩ := wellformed
          have inW : ∀ c ∈ first ++ marker :: renderFactors tail, c ∈ h :: t := by
            intro c mem
            rw [render] at mem
            exact mem
          have step0 := listDerivesTriple h t
          have step1 := listDerivesIni (h :: t) ((h :: t) ++ (h :: t))
            (fun c mem => List.mem_append_left _ mem)
          -- middle region
          have middleBefore : ∀ c ∈ rest (h :: t) ++ (h :: t) ++ first, c ∈ ini (h :: t) := by
            intro c mem
            rw [mem_ini]
            simp only [List.mem_append] at mem
            rcases mem with (mem | mem) | mem
            · exact mem_rest c _ mem
            · exact mem
            · exact inW c (List.mem_append_left _ mem)
          have middleAfter : ∀ c ∈ rest (h :: t) ++ (h :: t) ++ first, c ∈ marker :: renderFactors tail := by
            intro c mem
            have inWord : c ∈ h :: t := (mem_ini c _).mp (middleBefore c mem)
            have inMarkers := (mem_markers_lastScan c (h :: t) []).mpr inWord
            rw [shape, markers_cons] at inMarkers
            simp only [List.mem_cons] at inMarkers
            rcases inMarkers with rfl | inMarkers
            · simp
            · exact List.mem_cons_of_mem _ (marker_mem_renderFactors tail c inMarkers)
          have step2 := listDerivesCanonRegion (ini (h :: t)) (marker :: renderFactors tail) _
            (rest (h :: t) ++ (h :: t) ++ first) (Nat.le_refl _) middleBefore middleAfter
          -- fin segments
          have tailLetters : ∀ c ∈ renderFactors tail,
              c ∈ ini (h :: t) ++ canon (rest (h :: t) ++ (h :: t) ++ first) ++ [marker] := by
            intro c mem
            apply List.mem_append_left
            apply List.mem_append_left
            rw [mem_ini]
            exact inW c (List.mem_append_right _ (List.mem_cons_of_mem _ mem))
          have step3 := listDerivesCanonFactors tail
            (ini (h :: t) ++ canon (rest (h :: t) ++ (h :: t) ++ first) ++ [marker]) tailWellformed tailLetters
          have bridge : ini (h :: t) ++ rest (h :: t) ++ ((h :: t) ++ (h :: t)) =
              ini (h :: t) ++ (rest (h :: t) ++ (h :: t) ++ first) ++ (marker :: renderFactors tail) := by
            calc ini (h :: t) ++ rest (h :: t) ++ ((h :: t) ++ (h :: t))
                = ini (h :: t) ++ rest (h :: t) ++
                    ((h :: t) ++ (first ++ marker :: renderFactors tail)) := by rw [render]
              _ = ini (h :: t) ++ (rest (h :: t) ++ (h :: t) ++ first) ++
                    (marker :: renderFactors tail) := by simp [List.append_assoc]
          have step0' : ListDerives (h :: t) ((h :: t) ++ ((h :: t) ++ (h :: t))) := by
            simpa [List.append_assoc] using step0
          have step1' : ListDerives ((h :: t) ++ ((h :: t) ++ (h :: t)))
              (ini (h :: t) ++ (rest (h :: t) ++ (h :: t) ++ first) ++ (marker :: renderFactors tail)) := by
            rw [← bridge]
            exact step1
          have step3' : ListDerives
              (ini (h :: t) ++ canon (rest (h :: t) ++ (h :: t) ++ first) ++ (marker :: renderFactors tail))
              (ini (h :: t) ++ canon (rest (h :: t) ++ (h :: t) ++ first) ++ marker :: renderCanonFactors tail) := by
            simpa [List.append_assoc] using step3
          simp only [normalForm, shape]
          exact step0'.trans (step1'.trans (step2.trans step3'))

end SemigroupBasis.CoRoots.Order6Sunday.Msg0607TripleScan
