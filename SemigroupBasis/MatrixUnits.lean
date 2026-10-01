import SemigroupBasis.Opposite
import SemigroupBasis.Transfer

namespace SemigroupBasis

/-- Matrix units indexed by `I`, with `none` representing zero. -/
abbrev MatrixUnit (I : Type u) := Option (I × I)

namespace MatrixUnit

variable {I : Type u}

/-- The zero matrix unit. -/
def zero : MatrixUnit I := none

/-- The matrix unit with the given row and column coordinates. -/
def ofIndices (row column : I) : MatrixUnit I :=
  some (row, column)

/-- Matrix-unit multiplication: `(i, j) * (k, l)` is `(i, l)` when
`j = k`, and zero otherwise. -/
def mul [DecidableEq I] : MatrixUnit I → MatrixUnit I → MatrixUnit I
  | some (i, j), some (k, l) =>
      if j = k then some (i, l) else none
  | _, _ => none

@[simp]
theorem none_mul [DecidableEq I] (a : MatrixUnit I) :
    mul none a = none := by
  cases a <;> rfl

@[simp]
theorem mul_none [DecidableEq I] (a : MatrixUnit I) :
    mul a none = none := by
  cases a <;> rfl

@[simp]
theorem zero_mul [DecidableEq I] (a : MatrixUnit I) :
    mul (zero : MatrixUnit I) a = zero := by
  simp [zero]

@[simp]
theorem mul_zero [DecidableEq I] (a : MatrixUnit I) :
    mul a (zero : MatrixUnit I) = zero := by
  simp [zero]

@[simp]
theorem ofIndices_mul_ofIndices [DecidableEq I]
    (i j k l : I) :
    mul (ofIndices i j) (ofIndices k l) =
      if j = k then ofIndices i l else zero :=
  rfl

@[simp]
theorem ofIndices_mul_ofIndices_of_eq [DecidableEq I]
    (i j k l : I) (h : j = k) :
    mul (ofIndices i j) (ofIndices k l) = ofIndices i l := by
  simp [h]

@[simp]
theorem ofIndices_mul_ofIndices_of_ne [DecidableEq I]
    (i j k l : I) (h : j ≠ k) :
    mul (ofIndices i j) (ofIndices k l) = zero := by
  simp [h]

theorem mul_assoc [DecidableEq I] (a b c : MatrixUnit I) :
    mul (mul a b) c = mul a (mul b c) := by
  rcases a with _ | ⟨i, j⟩
  · rfl
  rcases b with _ | ⟨k, l⟩
  · rfl
  rcases c with _ | ⟨m, n⟩
  · simp [mul]
  by_cases hjk : j = k <;>
    by_cases hlm : l = m <;>
      simp [mul, hjk, hlm]

/-- The matrix-unit semigroup over `I`. -/
def semigroup [DecidableEq I] : Semigroup (MatrixUnit I) where
  mul := mul
  assoc := mul_assoc

@[simp]
theorem semigroup_mul [DecidableEq I] (a b : MatrixUnit I) :
    (semigroup (I := I)).mul a b = mul a b :=
  rfl

/-- Transpose fixes zero and exchanges the two coordinates. -/
def transpose : MatrixUnit I → MatrixUnit I
  | none => none
  | some (i, j) => some (j, i)

@[simp]
theorem transpose_zero :
    transpose (zero : MatrixUnit I) = zero :=
  rfl

@[simp]
theorem transpose_ofIndices (i j : I) :
    transpose (ofIndices i j) = ofIndices j i :=
  rfl

@[simp]
theorem transpose_transpose (a : MatrixUnit I) :
    transpose (transpose a) = a := by
  rcases a with _ | ⟨i, j⟩ <;> rfl

theorem transpose_injective :
    Function.Injective (transpose (I := I)) := by
  intro a b h
  have h' := congrArg (transpose (I := I)) h
  simpa using h'

theorem transpose_surjective :
    Function.Surjective (transpose (I := I)) := by
  intro a
  exact ⟨transpose a, transpose_transpose a⟩

theorem transpose_bijective :
    Function.Injective (transpose (I := I)) ∧
      Function.Surjective (transpose (I := I)) :=
  ⟨transpose_injective, transpose_surjective⟩

theorem transpose_mul [DecidableEq I] (a b : MatrixUnit I) :
    transpose (mul a b) = mul (transpose b) (transpose a) := by
  rcases a with _ | ⟨i, j⟩
  · rcases b with _ | ⟨k, l⟩ <;> rfl
  rcases b with _ | ⟨k, l⟩
  · rfl
  by_cases h : j = k
  · subst k
    simp only [mul, transpose]
    simp
  · have h' : k ≠ j := by
      intro hkj
      exact h hkj.symm
    simp only [mul, transpose]
    simp [h, h']

/-- Transpose viewed as an injective homomorphism into the opposite
semigroup. Together with `transpose_bijective`, this records the usual
matrix-unit anti-isomorphism. -/
def transposeToOpposite [DecidableEq I] :
    Embedding (semigroup (I := I)) (semigroup (I := I)).opposite where
  toFun := transpose
  map_mul := by
    intro a b
    change transpose (mul a b) = mul (transpose b) (transpose a)
    exact transpose_mul a b
  injective := transpose_injective

/-- The inverse transpose embedding from the opposite semigroup. -/
def transposeFromOpposite [DecidableEq I] :
    Embedding (semigroup (I := I)).opposite (semigroup (I := I)) where
  toFun := transpose
  map_mul := by
    intro a b
    change transpose (mul b a) = mul (transpose a) (transpose b)
    exact transpose_mul b a
  injective := transpose_injective

end MatrixUnit

end SemigroupBasis
