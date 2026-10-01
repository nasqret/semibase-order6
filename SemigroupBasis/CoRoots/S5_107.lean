import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.CoRoots.S5_107

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xyx : Word Nat := w 0 [1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def yxxy : Word Nat := w 1 [0, 0, 1]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xxzyy : Word Nat := w 0 [0, 2, 1, 1]
def xyxzy : Word Nat := w 0 [1, 0, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xyzxy : Word Nat := w 0 [1, 2, 0, 1]
def xyzyx : Word Nat := w 0 [1, 2, 1, 0]
def xzxyy : Word Nat := w 0 [2, 0, 1, 1]
def xzyxy : Word Nat := w 0 [2, 1, 0, 1]
def xzyyx : Word Nat := w 0 [2, 1, 1, 0]
def yxxzy : Word Nat := w 1 [0, 0, 2, 1]
def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
def xzxyx : Word Nat := w 0 [2, 0, 1, 0]
def xxyzz : Word Nat := w 0 [0, 1, 2, 2]
def xxzyz : Word Nat := w 0 [0, 2, 1, 2]
def xyzzx : Word Nat := w 0 [1, 2, 2, 0]

def powerLaw : Identity Nat := ⟨xx, xxx⟩
def leftEndpointLaw : Identity Nat := ⟨xyx, xxyx⟩
def rightEndpointLaw : Identity Nat := ⟨xyx, xyxx⟩
def squareInterleaveLaw : Identity Nat := ⟨xxyy, xyxy⟩
def squareFinalLaw : Identity Nat := ⟨xxyy, xyyx⟩
def squareInitialLaw : Identity Nat := ⟨xxyy, yxxy⟩
def attachmentXXZYYLaw : Identity Nat := ⟨xxyzy, xxzyy⟩
def attachmentXYXZYLaw : Identity Nat := ⟨xxyzy, xyxzy⟩
def attachmentXYYZXLaw : Identity Nat := ⟨xxyzy, xyyzx⟩
def attachmentXYZXYLaw : Identity Nat := ⟨xxyzy, xyzxy⟩
def attachmentXYZYXLaw : Identity Nat := ⟨xxyzy, xyzyx⟩
def attachmentXZXYYLaw : Identity Nat := ⟨xxyzy, xzxyy⟩
def attachmentXZYXYLaw : Identity Nat := ⟨xxyzy, xzyxy⟩
def attachmentXZYYXLaw : Identity Nat := ⟨xxyzy, xzyyx⟩
def attachmentYXXZYLaw : Identity Nat := ⟨xxyzy, yxxzy⟩
def blockSwapLaw : Identity Nat := ⟨xyxzx, xzxyx⟩

/-- The common 16-identity basis proposed for `S5_107`, `S5_108`, and
`S5_109`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftEndpointLaw, rightEndpointLaw,
    squareInterleaveLaw, squareFinalLaw, squareInitialLaw,
    attachmentXXZYYLaw, attachmentXYXZYLaw, attachmentXYYZXLaw,
    attachmentXYZXYLaw, attachmentXYZYXLaw, attachmentXZXYYLaw,
    attachmentXZYXYLaw, attachmentXZYYXLaw, attachmentYXXZYLaw,
    blockSwapLaw]

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisPower :
    Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) <| by
    simp [basis]

private theorem basisLeftEndpoint :
    Derives basis xyx xxyx :=
  Derives.fromBasis (e := leftEndpointLaw) <| by
    simp [basis]

private theorem basisRightEndpoint :
    Derives basis xyx xyxx :=
  Derives.fromBasis (e := rightEndpointLaw) <| by
    simp [basis]

/-- The first Lee-system law `x^4 = x^2`. -/
theorem derivesLeePower :
    Derives basis xxxx xx := by
  have first :=
    Derives.appendRight (Derives.symm basisPower) (Word.singleton 0)
  exact Derives.trans
    (by
      simpa [xxxx, xxx, xx, w, Word.singleton, Word.append,
        Word.append_assoc] using first)
    (Derives.symm basisPower)

/-- The second Lee-system law `x^3 y x = x y x`. -/
theorem derivesLeeLeftContraction :
    Derives basis xxxyx xyx := by
  have first :=
    Derives.prepend (Word.singleton 0)
      (Derives.symm basisLeftEndpoint)
  exact Derives.trans
    (by
      simpa [xxxyx, xxyx, xyx, w, Word.singleton, Word.append,
        Word.append_assoc] using first)
    (Derives.symm basisLeftEndpoint)

/-- The third Lee-system law `x^2 y x = x y x^2`. -/
theorem derivesLeeEndpointTransfer :
    Derives basis xxyx xyxx :=
  Derives.trans (Derives.symm basisLeftEndpoint) basisRightEndpoint

private theorem derivesXxyzzXxzyz :
    Derives basis xxyzz xxzyz := by
  have base :
      Derives basis xxzyy xxyzy :=
    Derives.symm <|
      Derives.fromBasis (e := attachmentXXZYYLaw) <| by
        simp [basis]
  have substituted :=
    Derives.subst base
      (instantiateThreeWords
        (Word.singleton 0) (Word.singleton 2) (Word.singleton 1))
  simpa [attachmentXXZYYLaw, xxyzy, xxzyy, xxyzz, xxzyz, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesXxzyzXyzzx :
    Derives basis xxzyz xyzzx := by
  have base :
      Derives basis xxyzy xzyyx :=
    Derives.fromBasis (e := attachmentXZYYXLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base
      (instantiateThreeWords
        (Word.singleton 0) (Word.singleton 2) (Word.singleton 1))
  simpa [attachmentXZYYXLaw, xxyzy, xzyyx, xxzyz, xyzzx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The fourth Lee-system law `x^2 y z^2 = x y z^2 x`. -/
theorem derivesLeeSquareMove :
    Derives basis xxyzz xyzzx :=
  Derives.trans derivesXxyzzXxzyz derivesXxzyzXyzzx

/-- The fifth Lee-system law is already the final basis law. -/
theorem derivesLeeBlockSwap :
    Derives basis xyxzx xzxyx :=
  Derives.fromBasis (e := blockSwapLaw) <| by
    simp [basis]

/-- Contract four consecutive copies of any nonempty word block to two. -/
theorem derivesFourToTwo (u : Word Nat) :
    Derives basis
      (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have substituted :=
    Derives.subst derivesLeePower
      (instantiateThreeWords u u u)
  simpa [xxxx, xx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Expand two consecutive copies of any nonempty block to four. -/
theorem derivesTwoToFour (u : Word Nat) :
    Derives basis
      (u ++ u) (((u ++ u) ++ u) ++ u) :=
  (derivesFourToTwo u).symm

/-- Contract three consecutive copies of any nonempty word block to two. -/
theorem derivesThreeToTwo (u : Word Nat) :
    Derives basis
      ((u ++ u) ++ u) (u ++ u) := by
  have substituted :=
    Derives.subst (Derives.symm basisPower)
      (instantiateThreeWords u u u)
  simpa [xxx, xx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Expand two consecutive copies of any nonempty block to three. -/
theorem derivesTwoToThree (u : Word Nat) :
    Derives basis
      (u ++ u) ((u ++ u) ++ u) :=
  (derivesThreeToTwo u).symm

/-- Duplicate the left occurrence of a repeated endpoint. -/
theorem derivesLeftEndpointExpansion
    (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      (((u ++ u) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisLeftEndpoint
      (instantiateThreeWords u v v)
  simpa [xyx, xxyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Duplicate the right occurrence of a repeated endpoint. -/
theorem derivesRightEndpointExpansion
    (u v : Word Nat) :
    Derives basis
      ((u ++ v) ++ u)
      (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightEndpoint
      (instantiateThreeWords u v v)
  simpa [xyx, xyxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Contract `u^3 v u` to `u v u`. -/
theorem derivesTripleLeftContraction
    (u v : Word Nat) :
    Derives basis
      ((((u ++ u) ++ u) ++ v) ++ u) ((u ++ v) ++ u) := by
  have substituted :=
    Derives.subst derivesLeeLeftContraction
      (instantiateThreeWords u v v)
  simpa [xxxyx, xyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Move one copy of a repeated endpoint from the left side to the right. -/
theorem derivesEndpointTransfer
    (u v : Word Nat) :
    Derives basis
      (((u ++ u) ++ v) ++ u) ((u ++ v) ++ (u ++ u)) := by
  have substituted :=
    Derives.subst derivesLeeEndpointTransfer
      (instantiateThreeWords u v v)
  simpa [xxyx, xyxx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Move a square block across an arbitrary intervening block. -/
theorem derivesSquareMove
    (u v z : Word Nat) :
    Derives basis
      ((((u ++ u) ++ v) ++ z) ++ z)
      (((u ++ v) ++ (z ++ z)) ++ u) := by
  have substituted :=
    Derives.subst derivesLeeSquareMove
      (instantiateThreeWords u v z)
  simpa [xxyzz, xyzzx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Commute two square blocks. -/
theorem derivesSquareBlockCommutation
    (left right : Word Nat) :
    Derives basis
      ((left ++ left) ++ (right ++ right))
      ((right ++ right) ++ (left ++ left)) := by
  have firstBase :
      Derives basis xxyy xyyx :=
    Derives.fromBasis (e := squareFinalLaw) <| by
      simp [basis]
  have firstSubstituted :=
    Derives.subst firstBase
      (instantiateThreeWords left right right)
  have first :
      Derives basis
        ((left ++ left) ++ (right ++ right))
        (((left ++ right) ++ right) ++ left) := by
    simpa [xxyy, xyyx, w, instantiateThreeWords, Word.bind,
      Word.append, Word.singleton, Word.append_assoc] using
        firstSubstituted
  have secondBase :
      Derives basis xxyy yxxy :=
    Derives.fromBasis (e := squareInitialLaw) <| by
      simp [basis]
  have secondSubstituted :=
    Derives.subst secondBase
      (instantiateThreeWords right left left)
  have second :
      Derives basis
        ((right ++ right) ++ (left ++ left))
        (((left ++ right) ++ right) ++ left) := by
    simpa [xxyy, yxxy, w, instantiateThreeWords, Word.bind,
      Word.append, Word.singleton, Word.append_assoc] using
        secondSubstituted
  exact first.trans second.symm

/-- Swap two blocks separated by repeated copies of an anchor block. -/
theorem derivesAnchoredBlockSwap
    (anchor left right : Word Nat) :
    Derives basis
      ((((anchor ++ left) ++ anchor) ++ right) ++ anchor)
      ((((anchor ++ right) ++ anchor) ++ left) ++ anchor) := by
  have substituted :=
    Derives.subst derivesLeeBlockSwap
      (instantiateThreeWords anchor left right)
  simpa [xyxzx, xzxyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `x²yzy = x²zy²`. -/
theorem derivesAttachmentXXZYY
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ x) ++ z) ++ y) ++ y) := by
  have base :
      Derives basis xxyzy xxzyy :=
    Derives.fromBasis (e := attachmentXXZYYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzy, xxzyy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `x²yzy = xyxzy`. -/
theorem derivesAttachmentXYXZY
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ x) ++ z) ++ y) := by
  have base :
      Derives basis xxyzy xyxzy :=
    Derives.fromBasis (e := attachmentXYXZYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzy, xyxzy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `x²yzy = xy²zx`. -/
theorem derivesAttachmentXYYZX
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ y) ++ z) ++ x) := by
  have base :
      Derives basis xxyzy xyyzx :=
    Derives.fromBasis (e := attachmentXYYZXLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzy, xyyzx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `x²yzy = xyzxy`. -/
theorem derivesAttachmentXYZXY
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ z) ++ x) ++ y) := by
  have base :
      Derives basis xxyzy xyzxy :=
    Derives.fromBasis (e := attachmentXYZXYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzy, xyzxy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `x²yzy = xyzyx`. -/
theorem derivesAttachmentXYZYX
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ z) ++ y) ++ x) := by
  have base :
      Derives basis xxyzy xyzyx :=
    Derives.fromBasis (e := attachmentXYZYXLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzy, xyzyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `x²yzy = xzxy²`. -/
theorem derivesAttachmentXZXYY
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ z) ++ x) ++ y) ++ y) := by
  have base :
      Derives basis xxyzy xzxyy :=
    Derives.fromBasis (e := attachmentXZXYYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzy, xzxyy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `x²yzy = xzyxy`. -/
theorem derivesAttachmentXZYXY
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ z) ++ y) ++ x) ++ y) := by
  have base :
      Derives basis xxyzy xzyxy :=
    Derives.fromBasis (e := attachmentXZYXYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzy, xzyxy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `x²yzy = xzy²x`. -/
theorem derivesAttachmentXZYYX
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ z) ++ y) ++ y) ++ x) := by
  have base :
      Derives basis xxyzy xzyyx :=
    Derives.fromBasis (e := attachmentXZYYXLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzy, xzyyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `x²yzy = yx²zy`. -/
theorem derivesAttachmentYXXZY
    (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((y ++ x) ++ x) ++ z) ++ y) := by
  have base :
      Derives basis xxyzy yxxzy :=
    Derives.fromBasis (e := attachmentYXXZYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzy, yxxzy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Lee's identity system `(8)`, in the order used in the 2013 paper. -/
def leeSystemEight : List (Identity Nat) :=
  [⟨xxxx, xx⟩, ⟨xxxyx, xyx⟩, ⟨xxyx, xyxx⟩,
    ⟨xxyzz, xyzzx⟩, ⟨xyxzx, xzxyx⟩]

/-- Every axiom of Lee's system `(8)` is derivable from the 16-law basis. -/
theorem leeSystemEightAxiomsDerive
    (e : Identity Nat) (member : e ∈ leeSystemEight) :
    Derives basis e.lhs e.rhs := by
  simp only [leeSystemEight, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact derivesLeePower
  · exact derivesLeeLeftContraction
  · exact derivesLeeEndpointTransfer
  · exact derivesLeeSquareMove
  · exact derivesLeeBlockSwap

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun e => e.map toFinThree

private theorem basisRoundTripChecked :
    basis.all (fun e =>
      decide ((e.map toFinThree).map Fin.val = e)) = true := by
  decide

private theorem basisRoundTrip
    (e : Identity Nat) (member : e ∈ basis) :
    (e.map toFinThree).map Fin.val = e := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basisRoundTripChecked) e member

/-- A finite table models the 16 laws once their three-variable images pass
the executable checker. -/
theorem modelsOfFiniteChecks
    (T : FiniteTable)
    (checked : finiteBasis.all T.checkIdentity = true) :
    Models T.semigroup basis := by
  intro e member
  have finiteMember : e.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨e, member, rfl⟩
  have finiteValid :=
    T.checkIdentityNat_sound (e.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basisRoundTrip e member] at finiteValid
  exact finiteValid

end SemigroupBasis.CoRoots.S5_107
