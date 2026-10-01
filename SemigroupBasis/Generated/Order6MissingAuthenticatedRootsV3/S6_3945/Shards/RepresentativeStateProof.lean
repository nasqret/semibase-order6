import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards.RepresentativeStateProofPart00
import SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Support.Core
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards

set_option maxHeartbeats 2000000 in
theorem representativeState
    (state : Fin 1447)
    : (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.representativeTail state).foldl
        SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.transition
        (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.generatorState
          (SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.representativeHead state)) =
      state := by
  if hAt704 : state.val < 704 then
    if hAt320 : state.val < 320 then
      if hAt128 : state.val < 128 then
        if hAt64 : state.val < 64 then
          exact representativeStateProof0000 state (by omega) (by omega)
        else
          exact representativeStateProof0001 state (by omega) (by omega)
      else
        if hAt192 : state.val < 192 then
          exact representativeStateProof0002 state (by omega) (by omega)
        else
          if hAt256 : state.val < 256 then
            exact representativeStateProof0003 state (by omega) (by omega)
          else
            exact representativeStateProof0004 state (by omega) (by omega)
    else
      if hAt512 : state.val < 512 then
        if hAt384 : state.val < 384 then
          exact representativeStateProof0005 state (by omega) (by omega)
        else
          if hAt448 : state.val < 448 then
            exact representativeStateProof0006 state (by omega) (by omega)
          else
            exact representativeStateProof0007 state (by omega) (by omega)
      else
        if hAt576 : state.val < 576 then
          exact representativeStateProof0008 state (by omega) (by omega)
        else
          if hAt640 : state.val < 640 then
            exact representativeStateProof0009 state (by omega) (by omega)
          else
            exact representativeStateProof0010 state (by omega) (by omega)
  else
    if hAt1088 : state.val < 1088 then
      if hAt896 : state.val < 896 then
        if hAt768 : state.val < 768 then
          exact representativeStateProof0011 state (by omega) (by omega)
        else
          if hAt832 : state.val < 832 then
            exact representativeStateProof0012 state (by omega) (by omega)
          else
            exact representativeStateProof0013 state (by omega) (by omega)
      else
        if hAt960 : state.val < 960 then
          exact representativeStateProof0014 state (by omega) (by omega)
        else
          if hAt1024 : state.val < 1024 then
            exact representativeStateProof0015 state (by omega) (by omega)
          else
            exact representativeStateProof0016 state (by omega) (by omega)
    else
      if hAt1280 : state.val < 1280 then
        if hAt1152 : state.val < 1152 then
          exact representativeStateProof0017 state (by omega) (by omega)
        else
          if hAt1216 : state.val < 1216 then
            exact representativeStateProof0018 state (by omega) (by omega)
          else
            exact representativeStateProof0019 state (by omega) (by omega)
      else
        if hAt1344 : state.val < 1344 then
          exact representativeStateProof0020 state (by omega) (by omega)
        else
          if hAt1408 : state.val < 1408 then
            exact representativeStateProof0021 state (by omega) (by omega)
          else
            exact representativeStateProof0022 state (by omega) (by omega)

end SemigroupBasis.Generated.Order6MissingAuthenticatedRootsV3.S6_3945.Shards
