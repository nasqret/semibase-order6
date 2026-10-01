import SemigroupBasis.CoRoots.Order6Day14.TwinsA.TwinsAFactors
import SemigroupBasis.CoRoots.Order6Sunday.TwinsAExactTransfers

namespace SemigroupBasis.CoRoots.Order6Day14.TwinsA

open SemigroupBasis

namespace S6_14814

theorem complete :
    BasisFor Order6Sunday.LateFinite.SigmaF137a.S6_14814.table.semigroup basis :=
  anchorBasis

theorem opposite_complete :
    BasisFor Order6Sunday.LateFinite.SigmaF137a.S6_14814.table.semigroup.opposite
      (reversedBasis basis) :=
  complete.oppositeReversed

end S6_14814

namespace S6_11915

theorem complete :
    BasisFor Order6Sunday.LateFinite.SigmaF137c.S6_11915.table.semigroup basis :=
  S6_14814.complete.inheritAlongPowerEmbedding
    Order6Sunday.TwinsAExactTransfers.powerEmbedding11915
    Order6Sunday.TwinTwoLawFinite.A.S6_11915.models

theorem opposite_complete :
    BasisFor Order6Sunday.LateFinite.SigmaF137c.S6_11915.table.semigroup.opposite
      (reversedBasis basis) :=
  complete.oppositeReversed

end S6_11915

namespace S6_14689

theorem complete :
    BasisFor Order6Sunday.LateFinite.SigmaF137c.S6_14689.table.semigroup basis :=
  S6_11915.complete.inheritAlongPowerEmbedding
    Order6Sunday.LateFinite.SigmaF137c.S6_14689.rootIntoPower
    Order6Sunday.TwinTwoLawFinite.A.S6_14689.models

theorem opposite_complete :
    BasisFor Order6Sunday.LateFinite.SigmaF137c.S6_14689.table.semigroup.opposite
      (reversedBasis basis) :=
  complete.oppositeReversed

end S6_14689

namespace S6_14833

theorem complete :
    BasisFor Order6Sunday.LateFinite.SigmaF137b.S6_14833.table.semigroup basis :=
  S6_14814.complete.inheritAlongPowerEmbedding
    Order6Sunday.TwinsAExactTransfers.powerEmbedding14833
    Order6Sunday.TwinTwoLawFinite.A.S6_14833.models

theorem opposite_complete :
    BasisFor Order6Sunday.LateFinite.SigmaF137b.S6_14833.table.semigroup.opposite
      (reversedBasis basis) :=
  complete.oppositeReversed

end S6_14833

namespace S6_14851

theorem complete :
    BasisFor Order6Sunday.LateFinite.SigmaF137c.S6_14851.table.semigroup basis :=
  S6_11915.complete.inheritAlongPowerEmbedding
    Order6Sunday.LateFinite.SigmaF137c.S6_14851.rootIntoPower
    Order6Sunday.TwinTwoLawFinite.A.S6_14851.models

theorem opposite_complete :
    BasisFor Order6Sunday.LateFinite.SigmaF137c.S6_14851.table.semigroup.opposite
      (reversedBasis basis) :=
  complete.oppositeReversed

end S6_14851

namespace S6_14852

theorem complete :
    BasisFor Order6Sunday.LateFinite.SigmaF137c.S6_14852.table.semigroup basis :=
  S6_11915.complete.inheritAlongPowerEmbedding
    Order6Sunday.TwinsAExactTransfers.powerEmbedding14852
    Order6Sunday.TwinTwoLawFinite.A.S6_14852.models

theorem opposite_complete :
    BasisFor Order6Sunday.LateFinite.SigmaF137c.S6_14852.table.semigroup.opposite
      (reversedBasis basis) :=
  complete.oppositeReversed

end S6_14852

end SemigroupBasis.CoRoots.Order6Day14.TwinsA
