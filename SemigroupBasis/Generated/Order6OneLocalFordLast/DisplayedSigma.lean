import SemigroupBasis.Equational

/-!
# Exact displayed systems for the order-six Ford/last family

Generated from the pinned v2 workload. Coordinates are
`x=0`, `y=1`, `z=2`, and `w=3`.

DAG SHA-256: `beaf61866b78f3bd7b910b18ce0363500adb50b46742b682862a3f9960b5a5f5`.
Workload SHA-256: `6d63673983ed77e0088718ff5b6ff8ef482f2300c9d0bd4a93b23229989742b6`.
-/

namespace SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

namespace Sigma_086f172522f9551c

def sha256 : String := "086f172522f9551c773861e879d60c365c38d25b5b53d8e7a0949950e755d39c"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 []) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1]) (w 0 [1, 0, 1, 1]),
    Identity.mk (w 0 [0, 1]) (w 0 [1, 1, 0, 1]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 0, 1]) (w 0 [1, 1]),
    Identity.mk (w 0 [0, 1, 0, 2]) (w 0 [1, 2]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2]),
    Identity.mk (w 0 [1, 0, 0, 1]) (w 0 [1, 1]),
    Identity.mk (w 0 [1, 0, 0, 2]) (w 0 [1, 2])
  ]

theorem basis_length : basis.length = 11 := by decide

end Sigma_086f172522f9551c

namespace Sigma_17bbc703ba9dbee0

def sha256 : String := "17bbc703ba9dbee09f4ff3c56333b4a97172eaf70ad46c42d41f38d7f3fb2e36"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1]),
    Identity.mk (w 0 [0, 1, 1, 2]) (w 0 [1, 1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 2 [0, 1, 0, 2]),
    Identity.mk (w 0 [1, 2, 1]) (w 0 [2, 1, 1])
  ]

theorem basis_length : basis.length = 10 := by decide

end Sigma_17bbc703ba9dbee0

namespace Sigma_2c9cb34de943739e

def sha256 : String := "2c9cb34de943739ee70d0046dac67d853ad4d90a244f4ff30c931867808440d9"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0, 0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1]) (w 0 [0, 1]),
    Identity.mk (w 0 [0, 1]) (w 0 [0, 1, 1]),
    Identity.mk (w 0 [0, 1]) (w 1 [0, 1]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [0, 1, 2, 2]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [2, 0, 1, 2]),
    Identity.mk (w 0 [0, 1, 2]) (w 2 [0, 1, 2, 2]),
    Identity.mk (w 0 [1, 1]) (w 0 [1, 1, 1]),
    Identity.mk (w 0 [1, 1, 2]) (w 0 [1, 2])
  ]

theorem basis_length : basis.length = 9 := by decide

end Sigma_2c9cb34de943739e

namespace Sigma_2fbaaa66a46422c3

def sha256 : String := "2fbaaa66a46422c35ece3bc7691c1dcd804d82e3c7459377ebda85e164b80acc"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0, 0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1]) (w 0 [0, 1]),
    Identity.mk (w 0 [0, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1]) (w 0 [1, 1]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 2]),
    Identity.mk (w 0 [1, 0, 2]) (w 0 [1, 2])
  ]

theorem basis_length : basis.length = 7 := by decide

end Sigma_2fbaaa66a46422c3

namespace Sigma_5b78bf5b916fda2a

def sha256 : String := "5b78bf5b916fda2a66d28832afbe8e7c84846b364fbdfdfe6a38808d3c28e071"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 0, 1, 1]) (w 1 [0, 0, 0, 1]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 2, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0])
  ]

theorem basis_length : basis.length = 13 := by decide

end Sigma_5b78bf5b916fda2a

namespace Sigma_628cd88d24637e89

def sha256 : String := "628cd88d24637e898e01418ae94fa7ee514814290a61ec23a2c98d0c735c35d4"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0, 0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 1]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1]),
    Identity.mk (w 0 [1, 1, 2]) (w 0 [2, 1, 1])
  ]

theorem basis_length : basis.length = 4 := by decide

end Sigma_628cd88d24637e89

namespace Sigma_699898150b01acc0

def sha256 : String := "699898150b01acc06e5d00a6cd5c696f8789fa1ff5e2e1615f4b2437bb95b76a"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 1, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 1, 0]),
    Identity.mk (w 0 [1, 0, 2, 1]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 1, 2]) (w 0 [1, 2]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0]),
    Identity.mk (w 0 [1, 2, 1]) (w 0 [1, 2, 1, 2])
  ]

theorem basis_length : basis.length = 13 := by decide

end Sigma_699898150b01acc0

namespace Sigma_6e291332acfa2508

def sha256 : String := "6e291332acfa2508b3130e82c410bffb8176e0e808e1be6758650009f2cc74dd"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0, 0, 0]),
    Identity.mk (w 0 [0, 0, 0, 1]) (w 0 [1]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 1, 1, 1]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 1, 1, 0]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 2, 0])
  ]

theorem basis_length : basis.length = 10 := by decide

end Sigma_6e291332acfa2508

namespace Sigma_6e5b151c213af3dd

def sha256 : String := "6e5b151c213af3dde6039004bd107037438e2d275ec631667aa03023b95b1f20"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 1, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [1, 1, 2]) (w 0 [1, 2])
  ]

theorem basis_length : basis.length = 8 := by decide

end Sigma_6e5b151c213af3dd

namespace Sigma_78b43a0acdd4f5a3

def sha256 : String := "78b43a0acdd4f5a36975560f006e3c33af2bd4204d841b207af1881df1811c82"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1]) (w 0 [1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0]),
    Identity.mk (w 0 [1, 2, 1]) (w 0 [2, 1, 1])
  ]

theorem basis_length : basis.length = 5 := by decide

end Sigma_78b43a0acdd4f5a3

namespace Sigma_799d6f5645f1ae36

def sha256 : String := "799d6f5645f1ae36b4d5bd499508e51dadf1e4283a5810270c32da815caa87d7"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0, 0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1]) (w 0 [0, 1]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 2]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 1]),
    Identity.mk (w 0 [1, 0, 2]) (w 0 [1, 2])
  ]

theorem basis_length : basis.length = 6 := by decide

end Sigma_799d6f5645f1ae36

namespace Sigma_93a811f26898d3d0

def sha256 : String := "93a811f26898d3d0e8de0348e89bb1680364aa6847b60fa3e876547664672300"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 2]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 1]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0])
  ]

theorem basis_length : basis.length = 5 := by decide

end Sigma_93a811f26898d3d0

namespace Sigma_93f39e2d4dde80c3

def sha256 : String := "93f39e2d4dde80c3ebb3efee8d3d3a3f1bb5eb27724be9a84353660c3b63dae0"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [1, 0]) (w 1 [0, 1, 0]),
    Identity.mk (w 0 [1, 0]) (w 1 [1, 0, 0]),
    Identity.mk (w 0 [1, 1, 2]) (w 0 [1, 2]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0]),
    Identity.mk (w 0 [1, 2, 0]) (w 1 [0, 1, 2, 0]),
    Identity.mk (w 0 [1, 2, 0]) (w 1 [1, 0, 2, 0]),
    Identity.mk (w 0 [1, 2, 0]) (w 1 [1, 2, 0, 0]),
    Identity.mk (w 0 [1, 2, 0]) (w 1 [2, 1, 0, 0])
  ]

theorem basis_length : basis.length = 12 := by decide

end Sigma_93f39e2d4dde80c3

namespace Sigma_947d9ea41e9770e5

def sha256 : String := "947d9ea41e9770e5bcbd53753cbc4131b9661e3615e2202b934146f88df9a79b"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0, 0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1]) (w 0 [0, 1]),
    Identity.mk (w 0 [0, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1]) (w 0 [1, 1]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 2]),
    Identity.mk (w 0 [1, 2]) (w 0 [2, 1, 2])
  ]

theorem basis_length : basis.length = 7 := by decide

end Sigma_947d9ea41e9770e5

namespace Sigma_968e763319b37dc8

def sha256 : String := "968e763319b37dc8462836da23c43a4f899cf7bb61405076d7bfc5233742876f"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0]) (w 1 [0, 1]),
    Identity.mk (w 0 [1, 0, 2]) (w 0 [1, 1, 0, 2]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 1, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0]),
    Identity.mk (w 0 [1, 2, 1]) (w 0 [1, 2, 2])
  ]

theorem basis_length : basis.length = 11 := by decide

end Sigma_968e763319b37dc8

namespace Sigma_b38ba0cb580369ae

def sha256 : String := "b38ba0cb580369aeb4009e89a469341dcfc2513653656d0c02cb1f67af008984"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1, 2]) (w 0 [1, 1, 0, 2]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 2, 1]) (w 0 [2, 1, 1])
  ]

theorem basis_length : basis.length = 7 := by decide

end Sigma_b38ba0cb580369ae

namespace Sigma_ba4e34217dcb083d

def sha256 : String := "ba4e34217dcb083d680a3622a00b4ffbf810ca87acc7aa52c909f98a2fc2f769"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 0, 1, 1]) (w 1 [0, 0, 0, 1]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 2 [0, 1, 0, 2]),
    Identity.mk (w 0 [1, 2, 1]) (w 0 [2, 1, 1])
  ]

theorem basis_length : basis.length = 13 := by decide

end Sigma_ba4e34217dcb083d

namespace Sigma_cdd7bcfee1652ef1

def sha256 : String := "cdd7bcfee1652ef1fea22725f108cae810f624abee00d568e7656c9d242c3f1f"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 1, 1, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0]),
    Identity.mk (w 0 [1, 2, 1]) (w 0 [2, 1, 1])
  ]

theorem basis_length : basis.length = 10 := by decide

end Sigma_cdd7bcfee1652ef1

namespace Sigma_de3d4e9ae533e928

def sha256 : String := "de3d4e9ae533e928b1b6c1a2efd488e4172c7df5847570601b316bfcc1fd9032"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 2, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 1, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 0, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 1, 0]),
    Identity.mk (w 0 [1, 1, 1, 2]) (w 0 [1, 2]),
    Identity.mk (w 0 [1, 1, 2, 1]) (w 0 [1, 2, 2, 2])
  ]

theorem basis_length : basis.length = 16 := by decide

end Sigma_de3d4e9ae533e928

namespace Sigma_e90b38ad3e5293c8

def sha256 : String := "e90b38ad3e5293c80e12cbe6de2180b072b5f515600390e1c1bf894ca4e33aca"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 1, 2, 2]) (w 0 [2, 1, 1, 2])
  ]

theorem basis_length : basis.length = 6 := by decide

end Sigma_e90b38ad3e5293c8

namespace Sigma_eb2ae10f901ecada

def sha256 : String := "eb2ae10f901ecada05bb994b6707e13496d11dac819fc219d990b25b4fb703fb"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 2, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 1, 2, 2]) (w 0 [2, 1, 1, 2])
  ]

theorem basis_length : basis.length = 9 := by decide

end Sigma_eb2ae10f901ecada

namespace Sigma_f137c52fe49d8093

def sha256 : String := "f137c52fe49d8093be3d64091708252113574de2ddc5eca5db634c59ec39bd57"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 []) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1]) (w 0 [1, 0, 1, 1]),
    Identity.mk (w 0 [0, 1]) (w 0 [1, 1, 0, 1]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 0, 1]) (w 0 [1, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [1, 0, 0, 1]) (w 0 [1, 1]),
    Identity.mk (w 0 [1, 2]) (w 0 [2, 1, 2, 2]),
    Identity.mk (w 0 [1, 2]) (w 0 [2, 2, 1, 2]),
    Identity.mk (w 0 [1, 2, 1]) (w 0 [2, 1, 1])
  ]

theorem basis_length : basis.length = 11 := by decide

end Sigma_f137c52fe49d8093

namespace Sigma_fa3011392afb2dee

def sha256 : String := "fa3011392afb2dee783b3777df80366eb81775d8472e05acd8e3ea7293938f3d"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 1, 1, 0]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 2]) (w 0 [1, 2, 2, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0])
  ]

theorem basis_length : basis.length = 11 := by decide

end Sigma_fa3011392afb2dee

end SemigroupBasis.Generated.Order6OneLocalFordLast.DisplayedSigma
