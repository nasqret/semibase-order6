import SemigroupBasis.Equational

/-!
# Exact displayed systems for the order-six Ford/Lord family

Generated from the pinned v2 joint-completeness workload.  Variable
coordinates are `x=0`, `y=1`, `z=2`, and `w=3`.

DAG SHA-256: `5d885e74ed0f4fd31f65f4e3c1d348fb274033b352116967a16db7ba63dd7db5`.
Workload SHA-256: `6d63673983ed77e0088718ff5b6ff8ef482f2300c9d0bd4a93b23229989742b6`.
-/

namespace SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

namespace Sigma_01f008d64c8bdb44

def sha256 : String := "01f008d64c8bdb441199e0cafca575a396a4afdf61fefd6ec8d2dd7f5e4e63e3"

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
    Identity.mk (w 0 [0, 1, 2, 0]) (w 0 [1, 0, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0]),
    Identity.mk (w 0 [1, 2, 0, 1]) (w 0 [1, 2, 1, 0]),
    Identity.mk (w 0 [1, 2, 0, 1]) (w 1 [0, 2, 0, 1])
  ]

theorem basis_length : basis.length = 16 := by decide

end Sigma_01f008d64c8bdb44

namespace Sigma_0b1bf8949e267cbb

def sha256 : String := "0b1bf8949e267cbb818a92363668671a54bc852cec5dd98fd48f6d8ea32b989d"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2]),
    Identity.mk (w 0 [1, 1, 2, 2]) (w 0 [2, 1, 1, 2])
  ]

theorem basis_length : basis.length = 8 := by decide

end Sigma_0b1bf8949e267cbb

namespace Sigma_0c28bc28674af3e4

def sha256 : String := "0c28bc28674af3e45192b3f87c7c8c046c741c3e772d24c51bbb891b8f30f5f0"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 1, 1, 0]),
    Identity.mk (w 0 [0, 1, 2, 0]) (w 0 [1, 0, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0]),
    Identity.mk (w 0 [1, 2, 0, 1]) (w 0 [1, 2, 1, 0])
  ]

theorem basis_length : basis.length = 13 := by decide

end Sigma_0c28bc28674af3e4

namespace Sigma_1ccaef90de83de0a

def sha256 : String := "1ccaef90de83de0a2e1aacea90a9067e06355f6223407fe5a03a5986d41d9c42"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1, 2]) (w 0 [1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 0, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 1, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2]),
    Identity.mk (w 0 [1, 1, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [1, 2, 1, 0]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [1, 2, 2, 0])
  ]

theorem basis_length : basis.length = 14 := by decide

end Sigma_1ccaef90de83de0a

namespace Sigma_2788f421bc5802f4

def sha256 : String := "2788f421bc5802f4ab428021363f6d91022992778c60c26d357126cf59b2d45f"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 2]) (w 0 [1, 2]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 1]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [1, 2, 0, 0]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [1, 2, 1, 0])
  ]

theorem basis_length : basis.length = 6 := by decide

end Sigma_2788f421bc5802f4

namespace Sigma_29d21e16b9abee63

def sha256 : String := "29d21e16b9abee63ac4b374fc5837ab7b0c089e7aa33a192ec2b773e952a06ac"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1]) (w 0 [1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 1]) (w 0 [1, 2, 1]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2]),
    Identity.mk (w 0 [1, 2, 1, 2]) (w 0 [1, 2, 2])
  ]

theorem basis_length : basis.length = 7 := by decide

end Sigma_29d21e16b9abee63

namespace Sigma_339231cc161df66a

def sha256 : String := "339231cc161df66ac7fa5ffd934b3ef0b87f2ec93c3d64f3f8f4889f5f43cfc8"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [2, 0, 1, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 1, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 0, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 1, 0]),
    Identity.mk (w 0 [1, 1, 2, 1]) (w 0 [2, 1, 2, 2]),
    Identity.mk (w 0 [1, 1, 2, 2]) (w 0 [2, 1, 1, 2]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0])
  ]

theorem basis_length : basis.length = 17 := by decide

end Sigma_339231cc161df66a

namespace Sigma_3761ee6c224045a2

def sha256 : String := "3761ee6c224045a2e3fab656b09ecd6d6e07763f894f5230cc48992bf6c1e4d6"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1]),
    Identity.mk (w 0 [0, 1, 1, 2]) (w 0 [1, 1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [2, 0, 1, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0])
  ]

theorem basis_length : basis.length = 10 := by decide

end Sigma_3761ee6c224045a2

namespace Sigma_4f48d5dc7526fb97

def sha256 : String := "4f48d5dc7526fb972a5be2370c61e943d80c14d0074e2bbdbc6687330bd66bcd"

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
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [2, 0, 1, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0])
  ]

theorem basis_length : basis.length = 14 := by decide

end Sigma_4f48d5dc7526fb97

namespace Sigma_5979ceb70a193b3f

def sha256 : String := "5979ceb70a193b3fc226941af7f1f1b6ff7466c65e0fe1b460dc2bb55be0e308"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [2, 0, 1, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 1, 2, 2]) (w 0 [2, 1, 1, 2]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0])
  ]

theorem basis_length : basis.length = 10 := by decide

end Sigma_5979ceb70a193b3f

namespace Sigma_5f450af59e61df2f

def sha256 : String := "5f450af59e61df2fc8e14abeb951375022d81acf4b77904231691f3ec9905d6f"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 []) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1]) (w 0 [1, 0, 1, 1]),
    Identity.mk (w 0 [0, 1]) (w 0 [1, 1, 0, 1]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 0, 1]) (w 0 [1, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 2, 0]) (w 0 [1, 0, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [1, 0, 0, 1]) (w 0 [1, 1]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2])
  ]

theorem basis_length : basis.length = 11 := by decide

end Sigma_5f450af59e61df2f

namespace Sigma_80eb7216d34f2e4f

def sha256 : String := "80eb7216d34f2e4f201ded3f4ba8da5c9ff4bbffeb661407e6bfe1ca2153b6f8"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 0, 2]) (w 1 [0, 1, 1, 2]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1]),
    Identity.mk (w 0 [0, 1, 1, 2]) (w 0 [1, 1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [2, 0, 1, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 1, 0]),
    Identity.mk (w 0 [1, 0]) (w 1 [0, 1, 1, 0]),
    Identity.mk (w 0 [1, 0]) (w 1 [1, 0, 1, 0]),
    Identity.mk (w 0 [1, 0]) (w 1 [1, 1, 0, 0]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0])
  ]

theorem basis_length : basis.length = 17 := by decide

end Sigma_80eb7216d34f2e4f

namespace Sigma_898207cd641d13be

def sha256 : String := "898207cd641d13be2a92f4b263b02346432e23664d57ac9c23e791d823ae670b"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 0, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 1, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0])
  ]

theorem basis_length : basis.length = 12 := by decide

end Sigma_898207cd641d13be

namespace Sigma_9808750adcf41d94

def sha256 : String := "9808750adcf41d947a2fdc6474edb2a2609b63c6c949390538ba415d7fada0d8"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1]),
    Identity.mk (w 0 [0, 1, 1, 2]) (w 0 [1, 1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2]),
    Identity.mk (w 0 [1, 2, 0, 1]) (w 1 [0, 2, 0, 1])
  ]

theorem basis_length : basis.length = 11 := by decide

end Sigma_9808750adcf41d94

namespace Sigma_9d96d63ce86e6d2f

def sha256 : String := "9d96d63ce86e6d2f52b1c85daf14a574f73b797c980b1767e0f6e8f851ea9814"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1]) (w 0 [1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 1]) (w 0 [1, 2, 1]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [1, 2, 1, 0]),
    Identity.mk (w 0 [1, 2, 0, 1]) (w 0 [1, 2, 1]),
    Identity.mk (w 0 [1, 2, 0, 2]) (w 0 [1, 2, 2]),
    Identity.mk (w 0 [1, 2, 1, 2]) (w 0 [1, 2, 2])
  ]

theorem basis_length : basis.length = 10 := by decide

end Sigma_9d96d63ce86e6d2f

namespace Sigma_a6866cfa3ad92ae2

def sha256 : String := "a6866cfa3ad92ae26818713730d41cf8335fef4915ab4f5970ba09a51bad5253"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 1 [0, 1, 1, 1]),
    Identity.mk (w 0 [0, 0, 1, 1]) (w 1 [0, 0, 0, 1]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [2, 0, 1, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0])
  ]

theorem basis_length : basis.length = 12 := by decide

end Sigma_a6866cfa3ad92ae2

namespace Sigma_ae8f21b57d380dc3

def sha256 : String := "ae8f21b57d380dc3332a876bf5f58761c79dd35ac2d65356212a9dce2ffa0470"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1, 2]) (w 0 [1, 1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2])
  ]

theorem basis_length : basis.length = 8 := by decide

end Sigma_ae8f21b57d380dc3

namespace Sigma_bf48e9968fd27f2b

def sha256 : String := "bf48e9968fd27f2b614307276ef8f7ab8fc6b10ad7bb62f3c5a2ac11a28ac8b7"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [2, 1, 0, 2]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [2, 1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 2 [0, 1, 0, 2])
  ]

theorem basis_length : basis.length = 14 := by decide

end Sigma_bf48e9968fd27f2b

namespace Sigma_ce7f74c56f7112a3

def sha256 : String := "ce7f74c56f7112a30226eb7fc4fe3b639c7faa6e9e889d78bc3eeca8806726ec"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0]),
    Identity.mk (w 0 [1, 1, 2, 2]) (w 0 [2, 1, 1, 2]),
    Identity.mk (w 0 [1, 2, 0, 1]) (w 0 [1, 2, 1, 0])
  ]

theorem basis_length : basis.length = 11 := by decide

end Sigma_ce7f74c56f7112a3

namespace Sigma_d0d5b02efd41e359

def sha256 : String := "d0d5b02efd41e3590ed13e58b6adae7fddd70d3ec39b12bb6ccd5b5e87fbd43d"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0, 0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1]) (w 0 [0, 1]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0]) (w 1 [0, 1]),
    Identity.mk (w 0 [1, 0, 2]) (w 0 [1, 1, 0, 2]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 1]) (w 0 [1, 1, 1]),
    Identity.mk (w 0 [1, 1, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 2, 0]) (w 0 [2, 1, 0]),
    Identity.mk (w 0 [1, 2, 1]) (w 0 [1, 2, 2, 1])
  ]

theorem basis_length : basis.length = 12 := by decide

end Sigma_d0d5b02efd41e359

namespace Sigma_f42ccd29e813b6b3

def sha256 : String := "f42ccd29e813b6b39d545fb966fdc18595840f3c13a594ec2a124d909e6e8392"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2])
  ]

theorem basis_length : basis.length = 7 := by decide

end Sigma_f42ccd29e813b6b3

namespace Sigma_f92726c4ea660efd

def sha256 : String := "f92726c4ea660efd9180c6910d04ccb32e2dcd67a840db0029c7a255ff4926fb"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 0, 2]) (w 0 [1, 0, 2]),
    Identity.mk (w 0 [0, 1, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [1]) (w 0 [1, 1]),
    Identity.mk (w 0 [1, 0, 2]) (w 0 [1, 2, 0, 2]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0])
  ]

theorem basis_length : basis.length = 8 := by decide

end Sigma_f92726c4ea660efd

namespace Sigma_fbf347965774f83c

def sha256 : String := "fbf347965774f83c810c2db058990bd4f6f9eec9ac661c52ec665b9ac2d25e82"

def basis : List (Identity Nat) :=
  [
    Identity.mk (w 0 [0]) (w 0 [0, 0, 0]),
    Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]),
    Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 2, 0]) (w 0 [1, 0, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 0, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 1, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 1, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 0, 1]),
    Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 1, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0])
  ]

theorem basis_length : basis.length = 18 := by decide

end Sigma_fbf347965774f83c

end SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma
