import SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415.Profile1415Presentation
import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.Examples.LeftRegularBandThree
import SemigroupBasis.CoRoots.S5_441Invariant
import SemigroupBasis.Subdirect

/-! Exact literal B32 Models and twelve finite semantic maps. Singleton law checks use each law's actual alphabet rank. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415

open SemigroupBasis

abbrev cyclicTable : FiniteTable := Examples.cyclicTwo
abbrev separatorTable : FiniteTable := Generated.Catalogue.S4_69.table
abbrev initialTable : FiniteTable := Examples.leftRegularBandThree

private def toFin1 : Nat → Fin 1
  | _ => 0
private def toFin2 : Nat → Fin 2
  | 0 => 0
  | _ => 1
private def toFin3 : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2
private def toFin4 : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private theorem cyclicLaw00 : law00.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law00] :=
    FiniteCertificate.checkModels_sound cyclicTable [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem cyclicLaw01 : law01.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law01] :=
    FiniteCertificate.checkModels_sound cyclicTable [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem cyclicLaw02 : law02.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law02] :=
    FiniteCertificate.checkModels_sound cyclicTable [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem cyclicLaw03 : law03.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law03] :=
    FiniteCertificate.checkModels_sound cyclicTable [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem cyclicLaw04 : law04.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law04] :=
    FiniteCertificate.checkModels_sound cyclicTable [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem cyclicLaw05 : law05.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law05] :=
    FiniteCertificate.checkModels_sound cyclicTable [law05] toFin2 (by decide)
  exact checked law05 (by decide)

private theorem cyclicLaw06 : law06.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law06] :=
    FiniteCertificate.checkModels_sound cyclicTable [law06] toFin2 (by decide)
  exact checked law06 (by decide)

private theorem cyclicLaw07 : law07.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law07] :=
    FiniteCertificate.checkModels_sound cyclicTable [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem cyclicLaw08 : law08.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law08] :=
    FiniteCertificate.checkModels_sound cyclicTable [law08] toFin2 (by decide)
  exact checked law08 (by decide)

private theorem cyclicLaw09 : law09.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law09] :=
    FiniteCertificate.checkModels_sound cyclicTable [law09] toFin2 (by decide)
  exact checked law09 (by decide)

private theorem cyclicLaw10 : law10.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law10] :=
    FiniteCertificate.checkModels_sound cyclicTable [law10] toFin2 (by decide)
  exact checked law10 (by decide)

private theorem cyclicLaw11 : law11.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law11] :=
    FiniteCertificate.checkModels_sound cyclicTable [law11] toFin2 (by decide)
  exact checked law11 (by decide)

private theorem cyclicLaw12 : law12.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law12] :=
    FiniteCertificate.checkModels_sound cyclicTable [law12] toFin2 (by decide)
  exact checked law12 (by decide)

private theorem cyclicLaw13 : law13.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law13] :=
    FiniteCertificate.checkModels_sound cyclicTable [law13] toFin3 (by decide)
  exact checked law13 (by decide)

private theorem cyclicLaw14 : law14.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law14] :=
    FiniteCertificate.checkModels_sound cyclicTable [law14] toFin3 (by decide)
  exact checked law14 (by decide)

private theorem cyclicLaw15 : law15.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law15] :=
    FiniteCertificate.checkModels_sound cyclicTable [law15] toFin3 (by decide)
  exact checked law15 (by decide)

private theorem cyclicLaw16 : law16.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law16] :=
    FiniteCertificate.checkModels_sound cyclicTable [law16] toFin3 (by decide)
  exact checked law16 (by decide)

private theorem cyclicLaw17 : law17.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law17] :=
    FiniteCertificate.checkModels_sound cyclicTable [law17] toFin3 (by decide)
  exact checked law17 (by decide)

private theorem cyclicLaw18 : law18.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law18] :=
    FiniteCertificate.checkModels_sound cyclicTable [law18] toFin3 (by decide)
  exact checked law18 (by decide)

private theorem cyclicLaw19 : law19.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law19] :=
    FiniteCertificate.checkModels_sound cyclicTable [law19] toFin3 (by decide)
  exact checked law19 (by decide)

private theorem cyclicLaw20 : law20.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law20] :=
    FiniteCertificate.checkModels_sound cyclicTable [law20] toFin3 (by decide)
  exact checked law20 (by decide)

private theorem cyclicLaw21 : law21.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law21] :=
    FiniteCertificate.checkModels_sound cyclicTable [law21] toFin3 (by decide)
  exact checked law21 (by decide)

private theorem cyclicLaw22 : law22.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law22] :=
    FiniteCertificate.checkModels_sound cyclicTable [law22] toFin3 (by decide)
  exact checked law22 (by decide)

private theorem cyclicLaw23 : law23.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law23] :=
    FiniteCertificate.checkModels_sound cyclicTable [law23] toFin3 (by decide)
  exact checked law23 (by decide)

private theorem cyclicLaw24 : law24.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law24] :=
    FiniteCertificate.checkModels_sound cyclicTable [law24] toFin3 (by decide)
  exact checked law24 (by decide)

private theorem cyclicLaw25 : law25.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law25] :=
    FiniteCertificate.checkModels_sound cyclicTable [law25] toFin3 (by decide)
  exact checked law25 (by decide)

private theorem cyclicLaw26 : law26.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law26] :=
    FiniteCertificate.checkModels_sound cyclicTable [law26] toFin3 (by decide)
  exact checked law26 (by decide)

private theorem cyclicLaw27 : law27.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law27] :=
    FiniteCertificate.checkModels_sound cyclicTable [law27] toFin2 (by decide)
  exact checked law27 (by decide)

private theorem cyclicLaw28 : law28.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law28] :=
    FiniteCertificate.checkModels_sound cyclicTable [law28] toFin2 (by decide)
  exact checked law28 (by decide)

private theorem cyclicLaw29 : law29.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law29] :=
    FiniteCertificate.checkModels_sound cyclicTable [law29] toFin2 (by decide)
  exact checked law29 (by decide)

private theorem cyclicLaw30 : law30.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law30] :=
    FiniteCertificate.checkModels_sound cyclicTable [law30] toFin4 (by decide)
  exact checked law30 (by decide)

private theorem cyclicLaw31 : law31.SatisfiedBy cyclicTable.semigroup := by
  have checked : Models cyclicTable.semigroup [law31] :=
    FiniteCertificate.checkModels_sound cyclicTable [law31] toFin4 (by decide)
  exact checked law31 (by decide)

theorem cyclicModels : Models cyclicTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cyclicLaw00
  · exact cyclicLaw01
  · exact cyclicLaw02
  · exact cyclicLaw03
  · exact cyclicLaw04
  · exact cyclicLaw05
  · exact cyclicLaw06
  · exact cyclicLaw07
  · exact cyclicLaw08
  · exact cyclicLaw09
  · exact cyclicLaw10
  · exact cyclicLaw11
  · exact cyclicLaw12
  · exact cyclicLaw13
  · exact cyclicLaw14
  · exact cyclicLaw15
  · exact cyclicLaw16
  · exact cyclicLaw17
  · exact cyclicLaw18
  · exact cyclicLaw19
  · exact cyclicLaw20
  · exact cyclicLaw21
  · exact cyclicLaw22
  · exact cyclicLaw23
  · exact cyclicLaw24
  · exact cyclicLaw25
  · exact cyclicLaw26
  · exact cyclicLaw27
  · exact cyclicLaw28
  · exact cyclicLaw29
  · exact cyclicLaw30
  · exact cyclicLaw31

private theorem separatorLaw00 : law00.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law00] :=
    FiniteCertificate.checkModels_sound separatorTable [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem separatorLaw01 : law01.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law01] :=
    FiniteCertificate.checkModels_sound separatorTable [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem separatorLaw02 : law02.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law02] :=
    FiniteCertificate.checkModels_sound separatorTable [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem separatorLaw03 : law03.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law03] :=
    FiniteCertificate.checkModels_sound separatorTable [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem separatorLaw04 : law04.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law04] :=
    FiniteCertificate.checkModels_sound separatorTable [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem separatorLaw05 : law05.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law05] :=
    FiniteCertificate.checkModels_sound separatorTable [law05] toFin2 (by decide)
  exact checked law05 (by decide)

private theorem separatorLaw06 : law06.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law06] :=
    FiniteCertificate.checkModels_sound separatorTable [law06] toFin2 (by decide)
  exact checked law06 (by decide)

private theorem separatorLaw07 : law07.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law07] :=
    FiniteCertificate.checkModels_sound separatorTable [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem separatorLaw08 : law08.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law08] :=
    FiniteCertificate.checkModels_sound separatorTable [law08] toFin2 (by decide)
  exact checked law08 (by decide)

private theorem separatorLaw09 : law09.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law09] :=
    FiniteCertificate.checkModels_sound separatorTable [law09] toFin2 (by decide)
  exact checked law09 (by decide)

private theorem separatorLaw10 : law10.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law10] :=
    FiniteCertificate.checkModels_sound separatorTable [law10] toFin2 (by decide)
  exact checked law10 (by decide)

private theorem separatorLaw11 : law11.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law11] :=
    FiniteCertificate.checkModels_sound separatorTable [law11] toFin2 (by decide)
  exact checked law11 (by decide)

private theorem separatorLaw12 : law12.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law12] :=
    FiniteCertificate.checkModels_sound separatorTable [law12] toFin2 (by decide)
  exact checked law12 (by decide)

private theorem separatorLaw13 : law13.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law13] :=
    FiniteCertificate.checkModels_sound separatorTable [law13] toFin3 (by decide)
  exact checked law13 (by decide)

private theorem separatorLaw14 : law14.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law14] :=
    FiniteCertificate.checkModels_sound separatorTable [law14] toFin3 (by decide)
  exact checked law14 (by decide)

private theorem separatorLaw15 : law15.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law15] :=
    FiniteCertificate.checkModels_sound separatorTable [law15] toFin3 (by decide)
  exact checked law15 (by decide)

private theorem separatorLaw16 : law16.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law16] :=
    FiniteCertificate.checkModels_sound separatorTable [law16] toFin3 (by decide)
  exact checked law16 (by decide)

private theorem separatorLaw17 : law17.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law17] :=
    FiniteCertificate.checkModels_sound separatorTable [law17] toFin3 (by decide)
  exact checked law17 (by decide)

private theorem separatorLaw18 : law18.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law18] :=
    FiniteCertificate.checkModels_sound separatorTable [law18] toFin3 (by decide)
  exact checked law18 (by decide)

private theorem separatorLaw19 : law19.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law19] :=
    FiniteCertificate.checkModels_sound separatorTable [law19] toFin3 (by decide)
  exact checked law19 (by decide)

private theorem separatorLaw20 : law20.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law20] :=
    FiniteCertificate.checkModels_sound separatorTable [law20] toFin3 (by decide)
  exact checked law20 (by decide)

private theorem separatorLaw21 : law21.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law21] :=
    FiniteCertificate.checkModels_sound separatorTable [law21] toFin3 (by decide)
  exact checked law21 (by decide)

private theorem separatorLaw22 : law22.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law22] :=
    FiniteCertificate.checkModels_sound separatorTable [law22] toFin3 (by decide)
  exact checked law22 (by decide)

private theorem separatorLaw23 : law23.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law23] :=
    FiniteCertificate.checkModels_sound separatorTable [law23] toFin3 (by decide)
  exact checked law23 (by decide)

private theorem separatorLaw24 : law24.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law24] :=
    FiniteCertificate.checkModels_sound separatorTable [law24] toFin3 (by decide)
  exact checked law24 (by decide)

private theorem separatorLaw25 : law25.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law25] :=
    FiniteCertificate.checkModels_sound separatorTable [law25] toFin3 (by decide)
  exact checked law25 (by decide)

private theorem separatorLaw26 : law26.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law26] :=
    FiniteCertificate.checkModels_sound separatorTable [law26] toFin3 (by decide)
  exact checked law26 (by decide)

private theorem separatorLaw27 : law27.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law27] :=
    FiniteCertificate.checkModels_sound separatorTable [law27] toFin2 (by decide)
  exact checked law27 (by decide)

private theorem separatorLaw28 : law28.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law28] :=
    FiniteCertificate.checkModels_sound separatorTable [law28] toFin2 (by decide)
  exact checked law28 (by decide)

private theorem separatorLaw29 : law29.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law29] :=
    FiniteCertificate.checkModels_sound separatorTable [law29] toFin2 (by decide)
  exact checked law29 (by decide)

private theorem separatorLaw30 : law30.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law30] :=
    FiniteCertificate.checkModels_sound separatorTable [law30] toFin4 (by decide)
  exact checked law30 (by decide)

private theorem separatorLaw31 : law31.SatisfiedBy separatorTable.semigroup := by
  have checked : Models separatorTable.semigroup [law31] :=
    FiniteCertificate.checkModels_sound separatorTable [law31] toFin4 (by decide)
  exact checked law31 (by decide)

theorem separatorModels : Models separatorTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact separatorLaw00
  · exact separatorLaw01
  · exact separatorLaw02
  · exact separatorLaw03
  · exact separatorLaw04
  · exact separatorLaw05
  · exact separatorLaw06
  · exact separatorLaw07
  · exact separatorLaw08
  · exact separatorLaw09
  · exact separatorLaw10
  · exact separatorLaw11
  · exact separatorLaw12
  · exact separatorLaw13
  · exact separatorLaw14
  · exact separatorLaw15
  · exact separatorLaw16
  · exact separatorLaw17
  · exact separatorLaw18
  · exact separatorLaw19
  · exact separatorLaw20
  · exact separatorLaw21
  · exact separatorLaw22
  · exact separatorLaw23
  · exact separatorLaw24
  · exact separatorLaw25
  · exact separatorLaw26
  · exact separatorLaw27
  · exact separatorLaw28
  · exact separatorLaw29
  · exact separatorLaw30
  · exact separatorLaw31

private theorem initialLaw00 : law00.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law00] :=
    FiniteCertificate.checkModels_sound initialTable [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem initialLaw01 : law01.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law01] :=
    FiniteCertificate.checkModels_sound initialTable [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem initialLaw02 : law02.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law02] :=
    FiniteCertificate.checkModels_sound initialTable [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem initialLaw03 : law03.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law03] :=
    FiniteCertificate.checkModels_sound initialTable [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem initialLaw04 : law04.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law04] :=
    FiniteCertificate.checkModels_sound initialTable [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem initialLaw05 : law05.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law05] :=
    FiniteCertificate.checkModels_sound initialTable [law05] toFin2 (by decide)
  exact checked law05 (by decide)

private theorem initialLaw06 : law06.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law06] :=
    FiniteCertificate.checkModels_sound initialTable [law06] toFin2 (by decide)
  exact checked law06 (by decide)

private theorem initialLaw07 : law07.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law07] :=
    FiniteCertificate.checkModels_sound initialTable [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem initialLaw08 : law08.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law08] :=
    FiniteCertificate.checkModels_sound initialTable [law08] toFin2 (by decide)
  exact checked law08 (by decide)

private theorem initialLaw09 : law09.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law09] :=
    FiniteCertificate.checkModels_sound initialTable [law09] toFin2 (by decide)
  exact checked law09 (by decide)

private theorem initialLaw10 : law10.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law10] :=
    FiniteCertificate.checkModels_sound initialTable [law10] toFin2 (by decide)
  exact checked law10 (by decide)

private theorem initialLaw11 : law11.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law11] :=
    FiniteCertificate.checkModels_sound initialTable [law11] toFin2 (by decide)
  exact checked law11 (by decide)

private theorem initialLaw12 : law12.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law12] :=
    FiniteCertificate.checkModels_sound initialTable [law12] toFin2 (by decide)
  exact checked law12 (by decide)

private theorem initialLaw13 : law13.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law13] :=
    FiniteCertificate.checkModels_sound initialTable [law13] toFin3 (by decide)
  exact checked law13 (by decide)

private theorem initialLaw14 : law14.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law14] :=
    FiniteCertificate.checkModels_sound initialTable [law14] toFin3 (by decide)
  exact checked law14 (by decide)

private theorem initialLaw15 : law15.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law15] :=
    FiniteCertificate.checkModels_sound initialTable [law15] toFin3 (by decide)
  exact checked law15 (by decide)

private theorem initialLaw16 : law16.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law16] :=
    FiniteCertificate.checkModels_sound initialTable [law16] toFin3 (by decide)
  exact checked law16 (by decide)

private theorem initialLaw17 : law17.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law17] :=
    FiniteCertificate.checkModels_sound initialTable [law17] toFin3 (by decide)
  exact checked law17 (by decide)

private theorem initialLaw18 : law18.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law18] :=
    FiniteCertificate.checkModels_sound initialTable [law18] toFin3 (by decide)
  exact checked law18 (by decide)

private theorem initialLaw19 : law19.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law19] :=
    FiniteCertificate.checkModels_sound initialTable [law19] toFin3 (by decide)
  exact checked law19 (by decide)

private theorem initialLaw20 : law20.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law20] :=
    FiniteCertificate.checkModels_sound initialTable [law20] toFin3 (by decide)
  exact checked law20 (by decide)

private theorem initialLaw21 : law21.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law21] :=
    FiniteCertificate.checkModels_sound initialTable [law21] toFin3 (by decide)
  exact checked law21 (by decide)

private theorem initialLaw22 : law22.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law22] :=
    FiniteCertificate.checkModels_sound initialTable [law22] toFin3 (by decide)
  exact checked law22 (by decide)

private theorem initialLaw23 : law23.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law23] :=
    FiniteCertificate.checkModels_sound initialTable [law23] toFin3 (by decide)
  exact checked law23 (by decide)

private theorem initialLaw24 : law24.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law24] :=
    FiniteCertificate.checkModels_sound initialTable [law24] toFin3 (by decide)
  exact checked law24 (by decide)

private theorem initialLaw25 : law25.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law25] :=
    FiniteCertificate.checkModels_sound initialTable [law25] toFin3 (by decide)
  exact checked law25 (by decide)

private theorem initialLaw26 : law26.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law26] :=
    FiniteCertificate.checkModels_sound initialTable [law26] toFin3 (by decide)
  exact checked law26 (by decide)

private theorem initialLaw27 : law27.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law27] :=
    FiniteCertificate.checkModels_sound initialTable [law27] toFin2 (by decide)
  exact checked law27 (by decide)

private theorem initialLaw28 : law28.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law28] :=
    FiniteCertificate.checkModels_sound initialTable [law28] toFin2 (by decide)
  exact checked law28 (by decide)

private theorem initialLaw29 : law29.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law29] :=
    FiniteCertificate.checkModels_sound initialTable [law29] toFin2 (by decide)
  exact checked law29 (by decide)

private theorem initialLaw30 : law30.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law30] :=
    FiniteCertificate.checkModels_sound initialTable [law30] toFin4 (by decide)
  exact checked law30 (by decide)

private theorem initialLaw31 : law31.SatisfiedBy initialTable.semigroup := by
  have checked : Models initialTable.semigroup [law31] :=
    FiniteCertificate.checkModels_sound initialTable [law31] toFin4 (by decide)
  exact checked law31 (by decide)

theorem initialModels : Models initialTable.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact initialLaw00
  · exact initialLaw01
  · exact initialLaw02
  · exact initialLaw03
  · exact initialLaw04
  · exact initialLaw05
  · exact initialLaw06
  · exact initialLaw07
  · exact initialLaw08
  · exact initialLaw09
  · exact initialLaw10
  · exact initialLaw11
  · exact initialLaw12
  · exact initialLaw13
  · exact initialLaw14
  · exact initialLaw15
  · exact initialLaw16
  · exact initialLaw17
  · exact initialLaw18
  · exact initialLaw19
  · exact initialLaw20
  · exact initialLaw21
  · exact initialLaw22
  · exact initialLaw23
  · exact initialLaw24
  · exact initialLaw25
  · exact initialLaw26
  · exact initialLaw27
  · exact initialLaw28
  · exact initialLaw29
  · exact initialLaw30
  · exact initialLaw31

namespace S6_10967

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 4 else 0) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 3 else if b = 3 then 2 else if b = 4 then 4 else 0) else
  if a = 4 then (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 4 else if b = 3 then 4 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,1,2],[1,2,3,4,5,1],[1,2,4,3,5,1],[5,5,5,5,5,5],[1,1,1,1,1,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

private theorem literalLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem literalLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem literalLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem literalLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem literalLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem literalLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFin2 (by decide)
  exact checked law05 (by decide)

private theorem literalLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFin2 (by decide)
  exact checked law06 (by decide)

private theorem literalLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin2 (by decide)
  exact checked law08 (by decide)

private theorem literalLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFin2 (by decide)
  exact checked law09 (by decide)

private theorem literalLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFin2 (by decide)
  exact checked law10 (by decide)

private theorem literalLaw11 : law11.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law11] :=
    FiniteCertificate.checkModels_sound table [law11] toFin2 (by decide)
  exact checked law11 (by decide)

private theorem literalLaw12 : law12.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law12] :=
    FiniteCertificate.checkModels_sound table [law12] toFin2 (by decide)
  exact checked law12 (by decide)

private theorem literalLaw13 : law13.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law13] :=
    FiniteCertificate.checkModels_sound table [law13] toFin3 (by decide)
  exact checked law13 (by decide)

private theorem literalLaw14 : law14.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law14] :=
    FiniteCertificate.checkModels_sound table [law14] toFin3 (by decide)
  exact checked law14 (by decide)

private theorem literalLaw15 : law15.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law15] :=
    FiniteCertificate.checkModels_sound table [law15] toFin3 (by decide)
  exact checked law15 (by decide)

private theorem literalLaw16 : law16.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law16] :=
    FiniteCertificate.checkModels_sound table [law16] toFin3 (by decide)
  exact checked law16 (by decide)

private theorem literalLaw17 : law17.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law17] :=
    FiniteCertificate.checkModels_sound table [law17] toFin3 (by decide)
  exact checked law17 (by decide)

private theorem literalLaw18 : law18.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law18] :=
    FiniteCertificate.checkModels_sound table [law18] toFin3 (by decide)
  exact checked law18 (by decide)

private theorem literalLaw19 : law19.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law19] :=
    FiniteCertificate.checkModels_sound table [law19] toFin3 (by decide)
  exact checked law19 (by decide)

private theorem literalLaw20 : law20.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law20] :=
    FiniteCertificate.checkModels_sound table [law20] toFin3 (by decide)
  exact checked law20 (by decide)

private theorem literalLaw21 : law21.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law21] :=
    FiniteCertificate.checkModels_sound table [law21] toFin3 (by decide)
  exact checked law21 (by decide)

private theorem literalLaw22 : law22.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law22] :=
    FiniteCertificate.checkModels_sound table [law22] toFin3 (by decide)
  exact checked law22 (by decide)

private theorem literalLaw23 : law23.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law23] :=
    FiniteCertificate.checkModels_sound table [law23] toFin3 (by decide)
  exact checked law23 (by decide)

private theorem literalLaw24 : law24.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law24] :=
    FiniteCertificate.checkModels_sound table [law24] toFin3 (by decide)
  exact checked law24 (by decide)

private theorem literalLaw25 : law25.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law25] :=
    FiniteCertificate.checkModels_sound table [law25] toFin3 (by decide)
  exact checked law25 (by decide)

private theorem literalLaw26 : law26.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law26] :=
    FiniteCertificate.checkModels_sound table [law26] toFin3 (by decide)
  exact checked law26 (by decide)

private theorem literalLaw27 : law27.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law27] :=
    FiniteCertificate.checkModels_sound table [law27] toFin2 (by decide)
  exact checked law27 (by decide)

private theorem literalLaw28 : law28.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law28] :=
    FiniteCertificate.checkModels_sound table [law28] toFin2 (by decide)
  exact checked law28 (by decide)

private theorem literalLaw29 : law29.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law29] :=
    FiniteCertificate.checkModels_sound table [law29] toFin2 (by decide)
  exact checked law29 (by decide)

private theorem literalLaw30 : law30.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law30] :=
    FiniteCertificate.checkModels_sound table [law30] toFin4 (by decide)
  exact checked law30 (by decide)

private theorem literalLaw31 : law31.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law31] :=
    FiniteCertificate.checkModels_sound table [law31] toFin4 (by decide)
  exact checked law31 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08
  · exact literalLaw09
  · exact literalLaw10
  · exact literalLaw11
  · exact literalLaw12
  · exact literalLaw13
  · exact literalLaw14
  · exact literalLaw15
  · exact literalLaw16
  · exact literalLaw17
  · exact literalLaw18
  · exact literalLaw19
  · exact literalLaw20
  · exact literalLaw21
  · exact literalLaw22
  · exact literalLaw23
  · exact literalLaw24
  · exact literalLaw25
  · exact literalLaw26
  · exact literalLaw27
  · exact literalLaw28
  · exact literalLaw29
  · exact literalLaw30
  · exact literalLaw31

theorem models : Models table.semigroup basis := literalModels

def cyclicMap (a : Fin 2) : Fin 6 := if a = 0 then 2 else 3

def cyclicEmbedding : Embedding cyclicTable.semigroup table.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCyclic (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy cyclicTable.semigroup := cyclicEmbedding.pullback_identity identity valid

def initialMap (a : Fin 3) : Fin 6 := if a = 0 then 0 else if a = 1 then 2 else 4

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

def separatorMap (a : Fin 4) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else 5

def separatorEmbedding : Embedding separatorTable.semigroup table.semigroup where
  toFun := separatorMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validSeparator (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy separatorTable.semigroup := separatorEmbedding.pullback_identity identity valid

end S6_10967

namespace S6_10976

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 1) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 4 else 4) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 3 else if b = 3 then 2 else if b = 4 then 4 else 4) else
  if a = 4 then (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 4 else if b = 3 then 4 else if b = 4 then 4 else 4) else
  (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 4 else if b = 3 then 4 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,1,1,1,2],[1,2,3,4,5,5],[1,2,4,3,5,5],[5,5,5,5,5,5],[5,5,5,5,5,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

private theorem literalLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem literalLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem literalLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem literalLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem literalLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem literalLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFin2 (by decide)
  exact checked law05 (by decide)

private theorem literalLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFin2 (by decide)
  exact checked law06 (by decide)

private theorem literalLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin2 (by decide)
  exact checked law08 (by decide)

private theorem literalLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFin2 (by decide)
  exact checked law09 (by decide)

private theorem literalLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFin2 (by decide)
  exact checked law10 (by decide)

private theorem literalLaw11 : law11.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law11] :=
    FiniteCertificate.checkModels_sound table [law11] toFin2 (by decide)
  exact checked law11 (by decide)

private theorem literalLaw12 : law12.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law12] :=
    FiniteCertificate.checkModels_sound table [law12] toFin2 (by decide)
  exact checked law12 (by decide)

private theorem literalLaw13 : law13.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law13] :=
    FiniteCertificate.checkModels_sound table [law13] toFin3 (by decide)
  exact checked law13 (by decide)

private theorem literalLaw14 : law14.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law14] :=
    FiniteCertificate.checkModels_sound table [law14] toFin3 (by decide)
  exact checked law14 (by decide)

private theorem literalLaw15 : law15.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law15] :=
    FiniteCertificate.checkModels_sound table [law15] toFin3 (by decide)
  exact checked law15 (by decide)

private theorem literalLaw16 : law16.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law16] :=
    FiniteCertificate.checkModels_sound table [law16] toFin3 (by decide)
  exact checked law16 (by decide)

private theorem literalLaw17 : law17.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law17] :=
    FiniteCertificate.checkModels_sound table [law17] toFin3 (by decide)
  exact checked law17 (by decide)

private theorem literalLaw18 : law18.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law18] :=
    FiniteCertificate.checkModels_sound table [law18] toFin3 (by decide)
  exact checked law18 (by decide)

private theorem literalLaw19 : law19.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law19] :=
    FiniteCertificate.checkModels_sound table [law19] toFin3 (by decide)
  exact checked law19 (by decide)

private theorem literalLaw20 : law20.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law20] :=
    FiniteCertificate.checkModels_sound table [law20] toFin3 (by decide)
  exact checked law20 (by decide)

private theorem literalLaw21 : law21.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law21] :=
    FiniteCertificate.checkModels_sound table [law21] toFin3 (by decide)
  exact checked law21 (by decide)

private theorem literalLaw22 : law22.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law22] :=
    FiniteCertificate.checkModels_sound table [law22] toFin3 (by decide)
  exact checked law22 (by decide)

private theorem literalLaw23 : law23.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law23] :=
    FiniteCertificate.checkModels_sound table [law23] toFin3 (by decide)
  exact checked law23 (by decide)

private theorem literalLaw24 : law24.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law24] :=
    FiniteCertificate.checkModels_sound table [law24] toFin3 (by decide)
  exact checked law24 (by decide)

private theorem literalLaw25 : law25.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law25] :=
    FiniteCertificate.checkModels_sound table [law25] toFin3 (by decide)
  exact checked law25 (by decide)

private theorem literalLaw26 : law26.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law26] :=
    FiniteCertificate.checkModels_sound table [law26] toFin3 (by decide)
  exact checked law26 (by decide)

private theorem literalLaw27 : law27.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law27] :=
    FiniteCertificate.checkModels_sound table [law27] toFin2 (by decide)
  exact checked law27 (by decide)

private theorem literalLaw28 : law28.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law28] :=
    FiniteCertificate.checkModels_sound table [law28] toFin2 (by decide)
  exact checked law28 (by decide)

private theorem literalLaw29 : law29.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law29] :=
    FiniteCertificate.checkModels_sound table [law29] toFin2 (by decide)
  exact checked law29 (by decide)

private theorem literalLaw30 : law30.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law30] :=
    FiniteCertificate.checkModels_sound table [law30] toFin4 (by decide)
  exact checked law30 (by decide)

private theorem literalLaw31 : law31.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law31] :=
    FiniteCertificate.checkModels_sound table [law31] toFin4 (by decide)
  exact checked law31 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08
  · exact literalLaw09
  · exact literalLaw10
  · exact literalLaw11
  · exact literalLaw12
  · exact literalLaw13
  · exact literalLaw14
  · exact literalLaw15
  · exact literalLaw16
  · exact literalLaw17
  · exact literalLaw18
  · exact literalLaw19
  · exact literalLaw20
  · exact literalLaw21
  · exact literalLaw22
  · exact literalLaw23
  · exact literalLaw24
  · exact literalLaw25
  · exact literalLaw26
  · exact literalLaw27
  · exact literalLaw28
  · exact literalLaw29
  · exact literalLaw30
  · exact literalLaw31

theorem models : Models table.semigroup basis := literalModels

def cyclicMap (a : Fin 2) : Fin 6 := if a = 0 then 2 else 3

def cyclicEmbedding : Embedding cyclicTable.semigroup table.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCyclic (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy cyclicTable.semigroup := cyclicEmbedding.pullback_identity identity valid

def initialMap (a : Fin 3) : Fin 6 := if a = 0 then 0 else if a = 1 then 2 else 4

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

def separatorProjection (a : Fin 6) : Fin 4 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else if a = 3 then 2 else if a = 4 then 0 else 3

def separatorSection (a : Fin 4) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else 5

def separatorSurjection : SplitSurjection table.semigroup separatorTable.semigroup where
  toFun := separatorProjection
  map_mul := by decide
  preimage := separatorSection
  right_inverse := by intro a; exact by decide +revert

theorem validSeparator (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy separatorTable.semigroup := separatorSurjection.pushforwardIdentity identity valid

end S6_10976

namespace S6_11300

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 1 else if b = 3 then 1 else if b = 4 then 0 else 0) else
  if a = 2 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 0 else 0) else
  if a = 3 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 3 else if b = 3 then 2 else if b = 4 then 0 else 0) else
  if a = 4 then (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 4 else 5) else
  (if b = 0 then 5 else if b = 1 then 5 else if b = 2 then 5 else if b = 3 then 5 else if b = 4 then 5 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,2,2,1,1],[1,1,3,4,1,1],[1,1,4,3,1,1],[1,2,1,1,5,6],[6,6,6,6,6,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

private theorem literalLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem literalLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem literalLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem literalLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem literalLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem literalLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFin2 (by decide)
  exact checked law05 (by decide)

private theorem literalLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFin2 (by decide)
  exact checked law06 (by decide)

private theorem literalLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin2 (by decide)
  exact checked law08 (by decide)

private theorem literalLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFin2 (by decide)
  exact checked law09 (by decide)

private theorem literalLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFin2 (by decide)
  exact checked law10 (by decide)

private theorem literalLaw11 : law11.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law11] :=
    FiniteCertificate.checkModels_sound table [law11] toFin2 (by decide)
  exact checked law11 (by decide)

private theorem literalLaw12 : law12.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law12] :=
    FiniteCertificate.checkModels_sound table [law12] toFin2 (by decide)
  exact checked law12 (by decide)

private theorem literalLaw13 : law13.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law13] :=
    FiniteCertificate.checkModels_sound table [law13] toFin3 (by decide)
  exact checked law13 (by decide)

private theorem literalLaw14 : law14.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law14] :=
    FiniteCertificate.checkModels_sound table [law14] toFin3 (by decide)
  exact checked law14 (by decide)

private theorem literalLaw15 : law15.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law15] :=
    FiniteCertificate.checkModels_sound table [law15] toFin3 (by decide)
  exact checked law15 (by decide)

private theorem literalLaw16 : law16.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law16] :=
    FiniteCertificate.checkModels_sound table [law16] toFin3 (by decide)
  exact checked law16 (by decide)

private theorem literalLaw17 : law17.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law17] :=
    FiniteCertificate.checkModels_sound table [law17] toFin3 (by decide)
  exact checked law17 (by decide)

private theorem literalLaw18 : law18.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law18] :=
    FiniteCertificate.checkModels_sound table [law18] toFin3 (by decide)
  exact checked law18 (by decide)

private theorem literalLaw19 : law19.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law19] :=
    FiniteCertificate.checkModels_sound table [law19] toFin3 (by decide)
  exact checked law19 (by decide)

private theorem literalLaw20 : law20.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law20] :=
    FiniteCertificate.checkModels_sound table [law20] toFin3 (by decide)
  exact checked law20 (by decide)

private theorem literalLaw21 : law21.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law21] :=
    FiniteCertificate.checkModels_sound table [law21] toFin3 (by decide)
  exact checked law21 (by decide)

private theorem literalLaw22 : law22.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law22] :=
    FiniteCertificate.checkModels_sound table [law22] toFin3 (by decide)
  exact checked law22 (by decide)

private theorem literalLaw23 : law23.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law23] :=
    FiniteCertificate.checkModels_sound table [law23] toFin3 (by decide)
  exact checked law23 (by decide)

private theorem literalLaw24 : law24.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law24] :=
    FiniteCertificate.checkModels_sound table [law24] toFin3 (by decide)
  exact checked law24 (by decide)

private theorem literalLaw25 : law25.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law25] :=
    FiniteCertificate.checkModels_sound table [law25] toFin3 (by decide)
  exact checked law25 (by decide)

private theorem literalLaw26 : law26.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law26] :=
    FiniteCertificate.checkModels_sound table [law26] toFin3 (by decide)
  exact checked law26 (by decide)

private theorem literalLaw27 : law27.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law27] :=
    FiniteCertificate.checkModels_sound table [law27] toFin2 (by decide)
  exact checked law27 (by decide)

private theorem literalLaw28 : law28.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law28] :=
    FiniteCertificate.checkModels_sound table [law28] toFin2 (by decide)
  exact checked law28 (by decide)

private theorem literalLaw29 : law29.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law29] :=
    FiniteCertificate.checkModels_sound table [law29] toFin2 (by decide)
  exact checked law29 (by decide)

private theorem literalLaw30 : law30.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law30] :=
    FiniteCertificate.checkModels_sound table [law30] toFin4 (by decide)
  exact checked law30 (by decide)

private theorem literalLaw31 : law31.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law31] :=
    FiniteCertificate.checkModels_sound table [law31] toFin4 (by decide)
  exact checked law31 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08
  · exact literalLaw09
  · exact literalLaw10
  · exact literalLaw11
  · exact literalLaw12
  · exact literalLaw13
  · exact literalLaw14
  · exact literalLaw15
  · exact literalLaw16
  · exact literalLaw17
  · exact literalLaw18
  · exact literalLaw19
  · exact literalLaw20
  · exact literalLaw21
  · exact literalLaw22
  · exact literalLaw23
  · exact literalLaw24
  · exact literalLaw25
  · exact literalLaw26
  · exact literalLaw27
  · exact literalLaw28
  · exact literalLaw29
  · exact literalLaw30
  · exact literalLaw31

theorem models : Models table.semigroup basis := literalModels

def cyclicMap (a : Fin 2) : Fin 6 := if a = 0 then 2 else 3

def cyclicEmbedding : Embedding cyclicTable.semigroup table.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCyclic (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy cyclicTable.semigroup := cyclicEmbedding.pullback_identity identity valid

def initialMap (a : Fin 3) : Fin 6 := if a = 0 then 0 else if a = 1 then 4 else 5

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

def separatorMap (a : Fin 4) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 4 else 2

def separatorEmbedding : Embedding separatorTable.semigroup table.semigroup where
  toFun := separatorMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validSeparator (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy separatorTable.semigroup := separatorEmbedding.pullback_identity identity valid

end S6_11300

namespace S6_11412

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 0 else if b = 3 then 0 else if b = 4 then 0 else 0) else
  if a = 1 then (if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 1 else if b = 3 then 1 else if b = 4 then 0 else 0) else
  if a = 2 then (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 2 else if b = 3 then 3 else if b = 4 then 4 else 4) else
  if a = 3 then (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 3 else if b = 3 then 2 else if b = 4 then 4 else 4) else
  if a = 4 then (if b = 0 then 4 else if b = 1 then 4 else if b = 2 then 4 else if b = 3 then 4 else if b = 4 then 4 else 4) else
  (if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 4 else if b = 3 then 4 else if b = 4 then 4 else 5)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def catalogueRows : List (List Nat) := [[1,1,1,1,1,1],[1,1,2,2,1,1],[5,5,3,4,5,5],[5,5,4,3,5,5],[5,5,5,5,5,5],[1,2,5,5,5,6]]

theorem catalogueRows_exact :
    List.ofFn (fun a : Fin 6 => List.ofFn (fun b : Fin 6 => (mul a b).val + 1)) = catalogueRows := by decide

private theorem literalLaw00 : law00.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law00] :=
    FiniteCertificate.checkModels_sound table [law00] toFin1 (by decide)
  exact checked law00 (by decide)

private theorem literalLaw01 : law01.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law01] :=
    FiniteCertificate.checkModels_sound table [law01] toFin2 (by decide)
  exact checked law01 (by decide)

private theorem literalLaw02 : law02.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law02] :=
    FiniteCertificate.checkModels_sound table [law02] toFin2 (by decide)
  exact checked law02 (by decide)

private theorem literalLaw03 : law03.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law03] :=
    FiniteCertificate.checkModels_sound table [law03] toFin2 (by decide)
  exact checked law03 (by decide)

private theorem literalLaw04 : law04.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law04] :=
    FiniteCertificate.checkModels_sound table [law04] toFin2 (by decide)
  exact checked law04 (by decide)

private theorem literalLaw05 : law05.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law05] :=
    FiniteCertificate.checkModels_sound table [law05] toFin2 (by decide)
  exact checked law05 (by decide)

private theorem literalLaw06 : law06.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law06] :=
    FiniteCertificate.checkModels_sound table [law06] toFin2 (by decide)
  exact checked law06 (by decide)

private theorem literalLaw07 : law07.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law07] :=
    FiniteCertificate.checkModels_sound table [law07] toFin2 (by decide)
  exact checked law07 (by decide)

private theorem literalLaw08 : law08.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table [law08] toFin2 (by decide)
  exact checked law08 (by decide)

private theorem literalLaw09 : law09.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law09] :=
    FiniteCertificate.checkModels_sound table [law09] toFin2 (by decide)
  exact checked law09 (by decide)

private theorem literalLaw10 : law10.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law10] :=
    FiniteCertificate.checkModels_sound table [law10] toFin2 (by decide)
  exact checked law10 (by decide)

private theorem literalLaw11 : law11.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law11] :=
    FiniteCertificate.checkModels_sound table [law11] toFin2 (by decide)
  exact checked law11 (by decide)

private theorem literalLaw12 : law12.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law12] :=
    FiniteCertificate.checkModels_sound table [law12] toFin2 (by decide)
  exact checked law12 (by decide)

private theorem literalLaw13 : law13.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law13] :=
    FiniteCertificate.checkModels_sound table [law13] toFin3 (by decide)
  exact checked law13 (by decide)

private theorem literalLaw14 : law14.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law14] :=
    FiniteCertificate.checkModels_sound table [law14] toFin3 (by decide)
  exact checked law14 (by decide)

private theorem literalLaw15 : law15.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law15] :=
    FiniteCertificate.checkModels_sound table [law15] toFin3 (by decide)
  exact checked law15 (by decide)

private theorem literalLaw16 : law16.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law16] :=
    FiniteCertificate.checkModels_sound table [law16] toFin3 (by decide)
  exact checked law16 (by decide)

private theorem literalLaw17 : law17.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law17] :=
    FiniteCertificate.checkModels_sound table [law17] toFin3 (by decide)
  exact checked law17 (by decide)

private theorem literalLaw18 : law18.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law18] :=
    FiniteCertificate.checkModels_sound table [law18] toFin3 (by decide)
  exact checked law18 (by decide)

private theorem literalLaw19 : law19.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law19] :=
    FiniteCertificate.checkModels_sound table [law19] toFin3 (by decide)
  exact checked law19 (by decide)

private theorem literalLaw20 : law20.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law20] :=
    FiniteCertificate.checkModels_sound table [law20] toFin3 (by decide)
  exact checked law20 (by decide)

private theorem literalLaw21 : law21.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law21] :=
    FiniteCertificate.checkModels_sound table [law21] toFin3 (by decide)
  exact checked law21 (by decide)

private theorem literalLaw22 : law22.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law22] :=
    FiniteCertificate.checkModels_sound table [law22] toFin3 (by decide)
  exact checked law22 (by decide)

private theorem literalLaw23 : law23.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law23] :=
    FiniteCertificate.checkModels_sound table [law23] toFin3 (by decide)
  exact checked law23 (by decide)

private theorem literalLaw24 : law24.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law24] :=
    FiniteCertificate.checkModels_sound table [law24] toFin3 (by decide)
  exact checked law24 (by decide)

private theorem literalLaw25 : law25.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law25] :=
    FiniteCertificate.checkModels_sound table [law25] toFin3 (by decide)
  exact checked law25 (by decide)

private theorem literalLaw26 : law26.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law26] :=
    FiniteCertificate.checkModels_sound table [law26] toFin3 (by decide)
  exact checked law26 (by decide)

private theorem literalLaw27 : law27.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law27] :=
    FiniteCertificate.checkModels_sound table [law27] toFin2 (by decide)
  exact checked law27 (by decide)

private theorem literalLaw28 : law28.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law28] :=
    FiniteCertificate.checkModels_sound table [law28] toFin2 (by decide)
  exact checked law28 (by decide)

private theorem literalLaw29 : law29.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law29] :=
    FiniteCertificate.checkModels_sound table [law29] toFin2 (by decide)
  exact checked law29 (by decide)

private theorem literalLaw30 : law30.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law30] :=
    FiniteCertificate.checkModels_sound table [law30] toFin4 (by decide)
  exact checked law30 (by decide)

private theorem literalLaw31 : law31.SatisfiedBy table.semigroup := by
  have checked : Models table.semigroup [law31] :=
    FiniteCertificate.checkModels_sound table [law31] toFin4 (by decide)
  exact checked law31 (by decide)

theorem literalModels : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact literalLaw00
  · exact literalLaw01
  · exact literalLaw02
  · exact literalLaw03
  · exact literalLaw04
  · exact literalLaw05
  · exact literalLaw06
  · exact literalLaw07
  · exact literalLaw08
  · exact literalLaw09
  · exact literalLaw10
  · exact literalLaw11
  · exact literalLaw12
  · exact literalLaw13
  · exact literalLaw14
  · exact literalLaw15
  · exact literalLaw16
  · exact literalLaw17
  · exact literalLaw18
  · exact literalLaw19
  · exact literalLaw20
  · exact literalLaw21
  · exact literalLaw22
  · exact literalLaw23
  · exact literalLaw24
  · exact literalLaw25
  · exact literalLaw26
  · exact literalLaw27
  · exact literalLaw28
  · exact literalLaw29
  · exact literalLaw30
  · exact literalLaw31

theorem models : Models table.semigroup basis := literalModels

def cyclicMap (a : Fin 2) : Fin 6 := if a = 0 then 2 else 3

def cyclicEmbedding : Embedding cyclicTable.semigroup table.semigroup where
  toFun := cyclicMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validCyclic (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy cyclicTable.semigroup := cyclicEmbedding.pullback_identity identity valid

def initialMap (a : Fin 3) : Fin 6 := if a = 0 then 0 else if a = 1 then 5 else 4

def initialEmbedding : Embedding initialTable.semigroup table.semigroup where
  toFun := initialMap
  map_mul := by decide
  injective := by intro a b; exact by decide +revert

theorem validInitial (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy initialTable.semigroup := initialEmbedding.pullback_identity identity valid

def separatorProjection (a : Fin 6) : Fin 4 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 3 else if a = 3 then 3 else if a = 4 then 0 else 2

def separatorSection (a : Fin 4) : Fin 6 := if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 5 else 2

def separatorSurjection : SplitSurjection table.semigroup separatorTable.semigroup where
  toFun := separatorProjection
  map_mul := by decide
  preimage := separatorSection
  right_inverse := by intro a; exact by decide +revert

theorem validSeparator (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy separatorTable.semigroup := separatorSurjection.pushforwardIdentity identity valid

end S6_11412


end SemigroupBasis.CoRoots.Order6Day11.FordLordProfile1415
