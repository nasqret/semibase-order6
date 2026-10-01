import SemigroupBasis.CoRoots.S5_441

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis

attribute [local simp] w

private def instantiateThreeWords
    (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

/-- Generic substitution instance of `xyx = xxyxx`. -/
theorem derivesXYXToXXYXX (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((x ++ x) ++ y) ++ x) ++ x) := by
  have base :
      Derives basis xyx xxyxx :=
    Derives.fromBasis (e := xyxXXYXXLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xyx, xxyxx, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `xyx = xxyyy`. -/
theorem derivesXYXToXXYYY (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((x ++ x) ++ y) ++ y) ++ y) := by
  have base :
      Derives basis xyx xxyyy :=
    Derives.fromBasis (e := xyxXXYYYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xyx, xxyyy, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `xyx = xyxyy`. -/
theorem derivesXYXToXYXYY (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((x ++ y) ++ x) ++ y) ++ y) := by
  have base :
      Derives basis xyx xyxyy :=
    Derives.fromBasis (e := xyxXYXYYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xyx, xyxyy, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `xyx = xyyxy`. -/
theorem derivesXYXToXYYXY (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((x ++ y) ++ y) ++ x) ++ y) := by
  have base :
      Derives basis xyx xyyxy :=
    Derives.fromBasis (e := xyxXYYXYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xyx, xyyxy, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `xyx = yxxyy`. -/
theorem derivesXYXToYXXYY (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((y ++ x) ++ x) ++ y) ++ y) := by
  have base :
      Derives basis xyx yxxyy :=
    Derives.fromBasis (e := xyxYXXYYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xyx, yxxyy, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `xyx = yxyxy`. -/
theorem derivesXYXToYXYXY (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((y ++ x) ++ y) ++ x) ++ y) := by
  have base :
      Derives basis xyx yxyxy :=
    Derives.fromBasis (e := xyxYXYXYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xyx, yxyxy, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `xyx = yxyyx`. -/
theorem derivesXYXToYXYYX (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((y ++ x) ++ y) ++ y) ++ x) := by
  have base :
      Derives basis xyx yxyyx :=
    Derives.fromBasis (e := xyxYXYYXLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xyx, yxyyx, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `xyx = yyxxy`. -/
theorem derivesXYXToYYXXY (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((y ++ y) ++ x) ++ x) ++ y) := by
  have base :
      Derives basis xyx yyxxy :=
    Derives.fromBasis (e := xyxYYXXYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xyx, yyxxy, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `xyx = yyxyx`. -/
theorem derivesXYXToYYXYX (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((y ++ y) ++ x) ++ y) ++ x) := by
  have base :
      Derives basis xyx yyxyx :=
    Derives.fromBasis (e := xyxYYXYXLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xyx, yyxyx, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `xyx = yyyxx`. -/
theorem derivesXYXToYYYXX (x y : Word Nat) :
    Derives basis
      ((x ++ y) ++ x)
      ((((y ++ y) ++ y) ++ x) ++ x) := by
  have base :
      Derives basis xyx yyyxx :=
    Derives.fromBasis (e := xyxYYYXXLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xyx, yyyxx, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Move one copy of a repeated endpoint from the left side to the right. -/
theorem derivesEndpointTransfer (x y : Word Nat) :
    Derives basis
      (((x ++ x) ++ y) ++ x)
      (((x ++ y) ++ x) ++ x) := by
  have base :
      Derives basis xxyx xyxx :=
    Derives.fromBasis (e := xxyxXYXXLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xxyx, xyxx, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Switch an odd envelope from `x` to `y`. -/
theorem derivesEnvelopeSwitch (x y : Word Nat) :
    Derives basis
      (((x ++ x) ++ y) ++ x)
      (((y ++ x) ++ y) ++ y) := by
  have base :
      Derives basis xxyx yxyy :=
    Derives.fromBasis (e := xxyxYXYYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xxyx, yxyy, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Interleave two adjacent nonempty squares. -/
theorem derivesSquareInterleave (x y : Word Nat) :
    Derives basis
      ((x ++ x) ++ (y ++ y))
      (((x ++ y) ++ x) ++ y) := by
  have base :
      Derives basis xxyy xyxy :=
    Derives.fromBasis (e := xxyyXYXYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xxyy, xyxy, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Move the first square endpoint to the end. -/
theorem derivesSquareFinalSwitch (x y : Word Nat) :
    Derives basis
      ((x ++ x) ++ (y ++ y))
      (((x ++ y) ++ y) ++ x) := by
  have base :
      Derives basis xxyy xyyx :=
    Derives.fromBasis (e := xxyyXYYXLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xxyy, xyyx, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Move the second square endpoint to the beginning. -/
theorem derivesSquareInitialSwitch (x y : Word Nat) :
    Derives basis
      ((x ++ x) ++ (y ++ y))
      (((y ++ x) ++ x) ++ y) := by
  have base :
      Derives basis xxyy yxxy :=
    Derives.fromBasis (e := xxyyYXXYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xxyy, yxxy, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Switch an odd envelope while retaining a nonempty trailing block. -/
theorem derivesExtendedEnvelopeSwitch (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ x)
      ((((y ++ x) ++ y) ++ z) ++ y) := by
  have base :
      Derives basis xxyzx yxyzy :=
    Derives.fromBasis (e := xxyzxYXYZYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzx, yxyzy, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `xxyzy = xyxzy`. -/
theorem derivesAttachmentXYXZY (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ x) ++ z) ++ y) := by
  have base :
      Derives basis xxyzy xyxzy :=
    Derives.fromBasis (e := xxyzyXYXZYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzy, xyxzy, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `xxyzy = xyyzx`. -/
theorem derivesAttachmentXYYZX (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ y) ++ z) ++ x) := by
  have base :
      Derives basis xxyzy xyyzx :=
    Derives.fromBasis (e := xxyzyXYYZXLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzy, xyyzx, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `xxyzy = xzxyy`. -/
theorem derivesAttachmentXZXYY (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ z) ++ x) ++ y) ++ y) := by
  have base :
      Derives basis xxyzy xzxyy :=
    Derives.fromBasis (e := xxyzyXZXYYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzy, xzxyy, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `xxyzy = yxxzy`. -/
theorem derivesAttachmentYXXZY (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((y ++ x) ++ x) ++ z) ++ y) := by
  have base :
      Derives basis xxyzy yxxzy :=
    Derives.fromBasis (e := xxyzyYXXZYLaw) <| by
      simp [basis]
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xxyzy, yxxzy, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

end SemigroupBasis.CoRoots.S5_441
