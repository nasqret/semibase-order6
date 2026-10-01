import SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma
import SemigroupBasis.Normalization.OneLocalFordLordSharedReach

/-!
# Displayed systems containing the shared Ford/Lord seven-law basis

Each declaration is one decidable subset check for a distinct displayed
Sigma.  The unrestricted Nat proof remains in
`OneLocalFordLord.SharedReach`; no obligation-specific proof is copied here.
-/

namespace SemigroupBasis.Generated.Order6OneLocalFordLord
namespace SharedSevenLawInstances

open SemigroupBasis.OneLocalFordLord.SharedReach

def sigma_0b1bf8949e267cbb :
    Laws DisplayedSigma.Sigma_0b1bf8949e267cbb.basis :=
  Laws.ofContainsSharedBasis (by decide)

def sigma_1ccaef90de83de0a :
    Laws DisplayedSigma.Sigma_1ccaef90de83de0a.basis :=
  Laws.ofContainsSharedBasis (by decide)

def sigma_898207cd641d13be :
    Laws DisplayedSigma.Sigma_898207cd641d13be.basis :=
  Laws.ofContainsSharedBasis (by decide)

def sigma_9808750adcf41d94 :
    Laws DisplayedSigma.Sigma_9808750adcf41d94.basis :=
  Laws.ofContainsSharedBasis (by decide)

def sigma_ae8f21b57d380dc3 :
    Laws DisplayedSigma.Sigma_ae8f21b57d380dc3.basis :=
  Laws.ofContainsSharedBasis (by decide)

def sigma_bf48e9968fd27f2b :
    Laws DisplayedSigma.Sigma_bf48e9968fd27f2b.basis :=
  Laws.ofContainsSharedBasis (by decide)

def sigma_ce7f74c56f7112a3 :
    Laws DisplayedSigma.Sigma_ce7f74c56f7112a3.basis :=
  Laws.ofContainsSharedBasis (by decide)

def sigma_f42ccd29e813b6b3 :
    Laws DisplayedSigma.Sigma_f42ccd29e813b6b3.basis :=
  Laws.ofContainsSharedBasis (by decide)

end SharedSevenLawInstances
end SemigroupBasis.Generated.Order6OneLocalFordLord
