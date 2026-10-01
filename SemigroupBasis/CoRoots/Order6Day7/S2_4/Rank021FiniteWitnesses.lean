import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank021ShardedFiniteBase

/-!
# Finite displayed-law witnesses for `S2_4 × S5_402op`

Staged family manifest SHA-256: `0541ba14f29867d690fe91ada5b335d7a44bcc9350ca58d95130b05bdb53976c`.
Each derivation selects one member of the exact displayed basis.
Left and right facts reuse the established finite-table proofs.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank021ShardedFiniteBase.FiniteWitnesses

open SemigroupBasis

/-- Finite displayed identity `xxx = xx`. -/
theorem law00_derivation : Derives basis law00.lhs law00.rhs :=
  Derives.fromBasis (e := law00) (by decide)

theorem law00_left_table : law00.SatisfiedBy leftTable.semigroup :=
  left_law00_valid

theorem law00_right_table : law00.SatisfiedBy rightTable.semigroup :=
  right_law00_valid

/-- Finite displayed identity `xxyx = xyx`. -/
theorem law01_derivation : Derives basis law01.lhs law01.rhs :=
  Derives.fromBasis (e := law01) (by decide)

theorem law01_left_table : law01.SatisfiedBy leftTable.semigroup :=
  left_law01_valid

theorem law01_right_table : law01.SatisfiedBy rightTable.semigroup :=
  right_law01_valid

/-- Finite displayed identity `xyxx = xyx`. -/
theorem law02_derivation : Derives basis law02.lhs law02.rhs :=
  Derives.fromBasis (e := law02) (by decide)

theorem law02_left_table : law02.SatisfiedBy leftTable.semigroup :=
  left_law02_valid

theorem law02_right_table : law02.SatisfiedBy rightTable.semigroup :=
  right_law02_valid

/-- Finite displayed identity `hxxkyytzz = hyytxxkzz`. -/
theorem law03_derivation : Derives basis law03.lhs law03.rhs :=
  Derives.fromBasis (e := law03) (by decide)

theorem law03_left_table : law03.SatisfiedBy leftTable.semigroup :=
  left_law03_valid

theorem law03_right_table : law03.SatisfiedBy rightTable.semigroup :=
  right_law03_valid

/-- Finite displayed identity `cabcac = cacabc`. -/
theorem law04_derivation : Derives basis law04.lhs law04.rhs :=
  Derives.fromBasis (e := law04) (by decide)

theorem law04_left_table : law04.SatisfiedBy leftTable.semigroup :=
  left_law04_valid

theorem law04_right_table : law04.SatisfiedBy rightTable.semigroup :=
  right_law04_valid

/-- Finite displayed identity `cacac = caac`. -/
theorem law05_derivation : Derives basis law05.lhs law05.rhs :=
  Derives.fromBasis (e := law05) (by decide)

theorem law05_left_table : law05.SatisfiedBy leftTable.semigroup :=
  left_law05_valid

theorem law05_right_table : law05.SatisfiedBy rightTable.semigroup :=
  right_law05_valid

/-- Finite displayed identity `abba = ababa`. -/
theorem law06_derivation : Derives basis law06.lhs law06.rhs :=
  Derives.fromBasis (e := law06) (by decide)

theorem law06_left_table : law06.SatisfiedBy leftTable.semigroup :=
  left_law06_valid

theorem law06_right_table : law06.SatisfiedBy rightTable.semigroup :=
  right_law06_valid

/-- Finite displayed identity `caabcb = caacbb`. -/
theorem law07_derivation : Derives basis law07.lhs law07.rhs :=
  Derives.fromBasis (e := law07) (by decide)

theorem law07_left_table : law07.SatisfiedBy leftTable.semigroup :=
  left_law07_valid

theorem law07_right_table : law07.SatisfiedBy rightTable.semigroup :=
  right_law07_valid

/-- Finite displayed identity `bacbc = bcbabc`. -/
theorem law08_derivation : Derives basis law08.lhs law08.rhs :=
  Derives.fromBasis (e := law08) (by decide)

theorem law08_left_table : law08.SatisfiedBy leftTable.semigroup :=
  left_law08_valid

theorem law08_right_table : law08.SatisfiedBy rightTable.semigroup :=
  right_law08_valid

/-- Finite displayed identity `aaccb = acacb`. -/
theorem law09_derivation : Derives basis law09.lhs law09.rhs :=
  Derives.fromBasis (e := law09) (by decide)

theorem law09_left_table : law09.SatisfiedBy leftTable.semigroup :=
  left_law09_valid

theorem law09_right_table : law09.SatisfiedBy rightTable.semigroup :=
  right_law09_valid

/-- Finite displayed identity `babacc = bbacac`. -/
theorem law10_derivation : Derives basis law10.lhs law10.rhs :=
  Derives.fromBasis (e := law10) (by decide)

theorem law10_left_table : law10.SatisfiedBy leftTable.semigroup :=
  left_law10_valid

theorem law10_right_table : law10.SatisfiedBy rightTable.semigroup :=
  right_law10_valid

/-- Finite displayed identity `cbbca = cbcbca`. -/
theorem law11_derivation : Derives basis law11.lhs law11.rhs :=
  Derives.fromBasis (e := law11) (by decide)

theorem law11_left_table : law11.SatisfiedBy leftTable.semigroup :=
  left_law11_valid

theorem law11_right_table : law11.SatisfiedBy rightTable.semigroup :=
  right_law11_valid

/-- Finite displayed identity `babcc = bbacc`. -/
theorem law12_derivation : Derives basis law12.lhs law12.rhs :=
  Derives.fromBasis (e := law12) (by decide)

theorem law12_left_table : law12.SatisfiedBy leftTable.semigroup :=
  left_law12_valid

theorem law12_right_table : law12.SatisfiedBy rightTable.semigroup :=
  right_law12_valid

/-- Finite displayed identity `cabcb = ccabb`. -/
theorem law13_derivation : Derives basis law13.lhs law13.rhs :=
  Derives.fromBasis (e := law13) (by decide)

theorem law13_left_table : law13.SatisfiedBy leftTable.semigroup :=
  left_law13_valid

theorem law13_right_table : law13.SatisfiedBy rightTable.semigroup :=
  right_law13_valid

/-- Finite displayed identity `aacbb = abacb`. -/
theorem law14_derivation : Derives basis law14.lhs law14.rhs :=
  Derives.fromBasis (e := law14) (by decide)

theorem law14_left_table : law14.SatisfiedBy leftTable.semigroup :=
  left_law14_valid

theorem law14_right_table : law14.SatisfiedBy rightTable.semigroup :=
  right_law14_valid

/-- Finite displayed identity `abccb = acbcb`. -/
theorem law15_derivation : Derives basis law15.lhs law15.rhs :=
  Derives.fromBasis (e := law15) (by decide)

theorem law15_left_table : law15.SatisfiedBy leftTable.semigroup :=
  left_law15_valid

theorem law15_right_table : law15.SatisfiedBy rightTable.semigroup :=
  right_law15_valid

/-- Finite displayed identity `cbaba = cabba`. -/
theorem law16_derivation : Derives basis law16.lhs law16.rhs :=
  Derives.fromBasis (e := law16) (by decide)

theorem law16_left_table : law16.SatisfiedBy leftTable.semigroup :=
  left_law16_valid

theorem law16_right_table : law16.SatisfiedBy rightTable.semigroup :=
  right_law16_valid

/-- Finite displayed identity `babcb = bcbab`. -/
theorem law17_derivation : Derives basis law17.lhs law17.rhs :=
  Derives.fromBasis (e := law17) (by decide)

theorem law17_left_table : law17.SatisfiedBy leftTable.semigroup :=
  left_law17_valid

theorem law17_right_table : law17.SatisfiedBy rightTable.semigroup :=
  right_law17_valid

/-- Finite displayed identity `babca = bbcaa`. -/
theorem law18_derivation : Derives basis law18.lhs law18.rhs :=
  Derives.fromBasis (e := law18) (by decide)

theorem law18_left_table : law18.SatisfiedBy leftTable.semigroup :=
  left_law18_valid

theorem law18_right_table : law18.SatisfiedBy rightTable.semigroup :=
  right_law18_valid

/-- Finite displayed identity `ccbaa = cacba`. -/
theorem law19_derivation : Derives basis law19.lhs law19.rhs :=
  Derives.fromBasis (e := law19) (by decide)

theorem law19_left_table : law19.SatisfiedBy leftTable.semigroup :=
  left_law19_valid

theorem law19_right_table : law19.SatisfiedBy rightTable.semigroup :=
  right_law19_valid

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank021ShardedFiniteBase.FiniteWitnesses
