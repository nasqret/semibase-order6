import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards.SourceLabelTransitionProofPart00
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Support.Core
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransition
    (state : Fin 1158)
    (generator : Fin 6) :
    SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.sourceLabel
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.transition state generator) =
      SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7631Representative.sourceSemigroup.mul
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.sourceLabel state)
        (SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.generatorSourceLabel generator) := by
  if hAt576 : state.val < 576 then
    if hAt256 : state.val < 256 then
      if hAt128 : state.val < 128 then
        if hAt64 : state.val < 64 then
          exact sourceLabelTransitionProof0000 state (by omega) (by omega) generator
        else
          exact sourceLabelTransitionProof0001 state (by omega) (by omega) generator
      else
        if hAt192 : state.val < 192 then
          exact sourceLabelTransitionProof0002 state (by omega) (by omega) generator
        else
          exact sourceLabelTransitionProof0003 state (by omega) (by omega) generator
    else
      if hAt384 : state.val < 384 then
        if hAt320 : state.val < 320 then
          exact sourceLabelTransitionProof0004 state (by omega) (by omega) generator
        else
          exact sourceLabelTransitionProof0005 state (by omega) (by omega) generator
      else
        if hAt448 : state.val < 448 then
          exact sourceLabelTransitionProof0006 state (by omega) (by omega) generator
        else
          if hAt512 : state.val < 512 then
            exact sourceLabelTransitionProof0007 state (by omega) (by omega) generator
          else
            exact sourceLabelTransitionProof0008 state (by omega) (by omega) generator
  else
    if hAt896 : state.val < 896 then
      if hAt704 : state.val < 704 then
        if hAt640 : state.val < 640 then
          exact sourceLabelTransitionProof0009 state (by omega) (by omega) generator
        else
          exact sourceLabelTransitionProof0010 state (by omega) (by omega) generator
      else
        if hAt768 : state.val < 768 then
          exact sourceLabelTransitionProof0011 state (by omega) (by omega) generator
        else
          if hAt832 : state.val < 832 then
            exact sourceLabelTransitionProof0012 state (by omega) (by omega) generator
          else
            exact sourceLabelTransitionProof0013 state (by omega) (by omega) generator
    else
      if hAt1024 : state.val < 1024 then
        if hAt960 : state.val < 960 then
          exact sourceLabelTransitionProof0014 state (by omega) (by omega) generator
        else
          exact sourceLabelTransitionProof0015 state (by omega) (by omega) generator
      else
        if hAt1088 : state.val < 1088 then
          exact sourceLabelTransitionProof0016 state (by omega) (by omega) generator
        else
          if hAt1152 : state.val < 1152 then
            exact sourceLabelTransitionProof0017 state (by omega) (by omega) generator
          else
            exact sourceLabelTransitionProof0018 state (by omega) (by omega) generator

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14266.Shards
