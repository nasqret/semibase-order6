import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.SourceLabelTransitionProofPart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Support.Core
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards

set_option maxHeartbeats 2000000 in
theorem sourceLabelTransition
    (state : Fin 1447)
    (generator : Fin 4) :
    SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.sourceLabel
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.transition state generator) =
      SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.Sources.S6_3944.sourceSemigroup.mul
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.sourceLabel state)
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.generatorSourceLabel generator) := by
  if hAt704 : state.val < 704 then
    if hAt320 : state.val < 320 then
      if hAt128 : state.val < 128 then
        if hAt64 : state.val < 64 then
          exact sourceLabelTransitionProof0000 state (by omega) (by omega) generator
        else
          exact sourceLabelTransitionProof0001 state (by omega) (by omega) generator
      else
        if hAt192 : state.val < 192 then
          exact sourceLabelTransitionProof0002 state (by omega) (by omega) generator
        else
          if hAt256 : state.val < 256 then
            exact sourceLabelTransitionProof0003 state (by omega) (by omega) generator
          else
            exact sourceLabelTransitionProof0004 state (by omega) (by omega) generator
    else
      if hAt512 : state.val < 512 then
        if hAt384 : state.val < 384 then
          exact sourceLabelTransitionProof0005 state (by omega) (by omega) generator
        else
          if hAt448 : state.val < 448 then
            exact sourceLabelTransitionProof0006 state (by omega) (by omega) generator
          else
            exact sourceLabelTransitionProof0007 state (by omega) (by omega) generator
      else
        if hAt576 : state.val < 576 then
          exact sourceLabelTransitionProof0008 state (by omega) (by omega) generator
        else
          if hAt640 : state.val < 640 then
            exact sourceLabelTransitionProof0009 state (by omega) (by omega) generator
          else
            exact sourceLabelTransitionProof0010 state (by omega) (by omega) generator
  else
    if hAt1088 : state.val < 1088 then
      if hAt896 : state.val < 896 then
        if hAt768 : state.val < 768 then
          exact sourceLabelTransitionProof0011 state (by omega) (by omega) generator
        else
          if hAt832 : state.val < 832 then
            exact sourceLabelTransitionProof0012 state (by omega) (by omega) generator
          else
            exact sourceLabelTransitionProof0013 state (by omega) (by omega) generator
      else
        if hAt960 : state.val < 960 then
          exact sourceLabelTransitionProof0014 state (by omega) (by omega) generator
        else
          if hAt1024 : state.val < 1024 then
            exact sourceLabelTransitionProof0015 state (by omega) (by omega) generator
          else
            exact sourceLabelTransitionProof0016 state (by omega) (by omega) generator
    else
      if hAt1280 : state.val < 1280 then
        if hAt1152 : state.val < 1152 then
          exact sourceLabelTransitionProof0017 state (by omega) (by omega) generator
        else
          if hAt1216 : state.val < 1216 then
            exact sourceLabelTransitionProof0018 state (by omega) (by omega) generator
          else
            exact sourceLabelTransitionProof0019 state (by omega) (by omega) generator
      else
        if hAt1344 : state.val < 1344 then
          exact sourceLabelTransitionProof0020 state (by omega) (by omega) generator
        else
          if hAt1408 : state.val < 1408 then
            exact sourceLabelTransitionProof0021 state (by omega) (by omega) generator
          else
            exact sourceLabelTransitionProof0022 state (by omega) (by omega) generator

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards
