import SemiBase

/-! The axioms used by the main theorems. Run with `lake env lean scripts/Axioms.lean`;
`scripts/verify.sh` does this and rejects anything beyond `propext`,
`Classical.choice` and `Quot.sound`. -/

#print axioms SemiBase.order6_classification
#print axioms SemiBase.order6_finitelyBased
#print axioms SemiBase.order6_nonfinitelyBased
#print axioms SemiBase.Catalogue.order6_length
#print axioms SemiBase.Catalogue.order6_ids
