import SemigroupBasis.CoRoots.S5_441CanonicalGap
import SemigroupBasis.CoRoots.S5_441ParityEnvelopeCombinatorics

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis.Examples

/-- The deterministic reduced interior for a parity envelope with a prescribed
supported endpoint. Every other supported letter occurs once or twice
according to source parity. The endpoint occurs internally exactly when its
source count is odd. -/
def parityEnvelopeCanonicalInterior
    (source : List Nat) (endpoint : Nat) : List Nat :=
  canonicalGapPayload source
      ((connectedComponentSortedSupport source).erase endpoint) ++
    if source.count endpoint % 2 = 0 then [] else [endpoint]

/-- The deterministic parity envelope at a prescribed supported endpoint. -/
def parityEnvelopeCanonical
    (source : List Nat) (endpoint : Nat) : List Nat :=
  parityEnvelopeRender endpoint
    (parityEnvelopeCanonicalInterior source endpoint) []

theorem parityEnvelopeCanonicalInterior_count_endpoint
    (source : List Nat) (endpoint : Nat) :
    (parityEnvelopeCanonicalInterior source endpoint).count endpoint =
      if source.count endpoint % 2 = 0 then 0 else 1 := by
  have supportNodup :=
    connectedComponentSortedSupport_nodup source
  have erasedNodup :
      ((connectedComponentSortedSupport source).erase endpoint).Nodup :=
    supportNodup.erase endpoint
  have endpointAbsent :
      endpoint ∉
        (connectedComponentSortedSupport source).erase endpoint := by
    simp [supportNodup.mem_erase_iff]
  have payloadCount :
      (canonicalGapPayload source
        ((connectedComponentSortedSupport source).erase endpoint)).count
          endpoint = 0 :=
    canonicalGapPayload_count_of_not_mem
      erasedNodup endpointAbsent
  by_cases even : source.count endpoint % 2 = 0
  · simp [parityEnvelopeCanonicalInterior, payloadCount, even]
  · simp [parityEnvelopeCanonicalInterior, payloadCount, even]

theorem parityEnvelopeCanonicalInterior_count_nonendpoint
    {source : List Nat} {endpoint tested : Nat}
    (member : tested ∈ source)
    (different : tested ≠ endpoint) :
    (parityEnvelopeCanonicalInterior source endpoint).count tested =
      if source.count tested % 2 = 0 then 2 else 1 := by
  have supportNodup :=
    connectedComponentSortedSupport_nodup source
  have erasedNodup :
      ((connectedComponentSortedSupport source).erase endpoint).Nodup :=
    supportNodup.erase endpoint
  have testedInSupport :
      tested ∈ connectedComponentSortedSupport source :=
    (connectedComponentSortedSupport_mem_iff tested source).2 member
  have testedInErased :
      tested ∈
        (connectedComponentSortedSupport source).erase endpoint := by
    simpa [supportNodup.mem_erase_iff, different] using testedInSupport
  have payloadCount :
      (canonicalGapPayload source
        ((connectedComponentSortedSupport source).erase endpoint)).count
          tested =
        if source.count tested % 2 = 0 then 2 else 1 :=
    canonicalGapPayload_count_of_mem erasedNodup testedInErased
  by_cases endpointEven : source.count endpoint % 2 = 0
  · simp [parityEnvelopeCanonicalInterior, payloadCount, endpointEven]
  · simp [parityEnvelopeCanonicalInterior, payloadCount, endpointEven,
      Ne.symm different]

theorem parityEnvelopeCanonical_count_endpoint
    (source : List Nat) (endpoint : Nat) :
    (parityEnvelopeCanonical source endpoint).count endpoint =
      if source.count endpoint % 2 = 0 then 2 else 3 := by
  rw [parityEnvelopeCanonical, parityEnvelopeRender,
    List.count_cons_self, List.count_append,
    parityEnvelopeCanonicalInterior_count_endpoint]
  by_cases even : source.count endpoint % 2 = 0
  · simp [even]
  · simp [even]

theorem parityEnvelopeCanonical_count_nonendpoint
    {source : List Nat} {endpoint tested : Nat}
    (member : tested ∈ source)
    (different : tested ≠ endpoint) :
    (parityEnvelopeCanonical source endpoint).count tested =
      if source.count tested % 2 = 0 then 2 else 1 := by
  simp [parityEnvelopeCanonical, parityEnvelopeRender,
    parityEnvelopeCanonicalInterior_count_nonendpoint member different,
    different, Ne.symm different]

/-- A canonical envelope at a supported endpoint has exactly the source
support. -/
theorem parityEnvelopeCanonical_mem_iff
    {source : List Nat} {endpoint : Nat}
    (endpointMember : endpoint ∈ source)
    (tested : Nat) :
    tested ∈ parityEnvelopeCanonical source endpoint ↔
      tested ∈ source := by
  by_cases equal : tested = endpoint
  · subst tested
    simp [parityEnvelopeCanonical, parityEnvelopeRender, endpointMember]
  · have supportNodup :=
      connectedComponentSortedSupport_nodup source
    simp [parityEnvelopeCanonical, parityEnvelopeCanonicalInterior,
      parityEnvelopeRender, canonicalGapPayload_mem_iff,
      supportNodup.mem_erase_iff,
      connectedComponentSortedSupport_mem_iff,
      equal, Ne.symm equal]

/-- Canonicalization at any supported endpoint preserves every source
occurrence parity. -/
theorem parityEnvelopeCanonical_count_mod_two
    {source : List Nat} {endpoint : Nat}
    (endpointMember : endpoint ∈ source)
    (tested : Nat) :
    (parityEnvelopeCanonical source endpoint).count tested % 2 =
      source.count tested % 2 := by
  by_cases equal : tested = endpoint
  · subst tested
    rw [parityEnvelopeCanonical_count_endpoint]
    by_cases even : source.count endpoint % 2 = 0
    · simp [even]
    · have odd : source.count endpoint % 2 = 1 := by
        omega
      simp [even, odd]
  · by_cases member : tested ∈ source
    · rw [parityEnvelopeCanonical_count_nonendpoint member equal]
      by_cases even : source.count tested % 2 = 0
      · simp [even]
      · have odd : source.count tested % 2 = 1 := by
          omega
        simp [even, odd]
    · have canonicalAbsent :
          tested ∉ parityEnvelopeCanonical source endpoint := by
        intro canonicalMember
        exact member <|
          (parityEnvelopeCanonical_mem_iff endpointMember tested).1
            canonicalMember
      rw [List.count_eq_zero.mpr canonicalAbsent,
        List.count_eq_zero.mpr member]

theorem parityEnvelopeCanonicalInterior_endpoint_count_le_one
    (source : List Nat) (endpoint : Nat) :
    (parityEnvelopeCanonicalInterior source endpoint).count endpoint ≤ 1 := by
  rw [parityEnvelopeCanonicalInterior_count_endpoint]
  split <;> omega

theorem parityEnvelopeCanonicalInterior_count_le_two
    (source : List Nat) (endpoint tested : Nat) :
    (parityEnvelopeCanonicalInterior source endpoint).count tested ≤ 2 := by
  by_cases equal : tested = endpoint
  · subst tested
    exact
      Nat.le_trans
        (parityEnvelopeCanonicalInterior_endpoint_count_le_one
          source endpoint)
        (by omega)
  · by_cases member : tested ∈ source
    · rw [
        parityEnvelopeCanonicalInterior_count_nonendpoint member equal
      ]
      split <;> omega
    · have testedAbsentSupport :
          tested ∉ connectedComponentSortedSupport source := by
        simpa [connectedComponentSortedSupport_mem_iff] using member
      have supportNodup :=
        connectedComponentSortedSupport_nodup source
      have testedAbsentErased :
          tested ∉
            (connectedComponentSortedSupport source).erase endpoint := by
        simpa [supportNodup.mem_erase_iff, testedAbsentSupport]
      have erasedNodup :
          ((connectedComponentSortedSupport source).erase endpoint).Nodup :=
        supportNodup.erase endpoint
      have payloadCount :
          (canonicalGapPayload source
            ((connectedComponentSortedSupport source).erase endpoint)).count
              tested = 0 :=
        canonicalGapPayload_count_of_not_mem
          erasedNodup testedAbsentErased
      by_cases endpointEven : source.count endpoint % 2 = 0
      · simp [parityEnvelopeCanonicalInterior, payloadCount, endpointEven]
      · simp [parityEnvelopeCanonicalInterior, payloadCount, endpointEven,
          Ne.symm equal]

/-- Choosing the least supported endpoint recovers `canonicalGap`
definitionally after erasing that endpoint from the sorted support. -/
theorem parityEnvelopeCanonical_eq_canonicalGap
    {source : List Nat} {anchor : Nat} {payloadSupport : List Nat}
    (supportShape :
      connectedComponentSortedSupport source =
        anchor :: payloadSupport) :
    parityEnvelopeCanonical source anchor = canonicalGap source := by
  simp [parityEnvelopeCanonical, parityEnvelopeCanonicalInterior,
    parityEnvelopeRender, canonicalGap, supportShape, List.append_assoc]

end SemigroupBasis.CoRoots.S5_441
