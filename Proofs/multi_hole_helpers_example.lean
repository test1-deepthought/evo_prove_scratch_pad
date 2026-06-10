import Mathlib

/-- Inlined ChallengeDeps definitions for verification -/
def rootHelper : Nat := 41

namespace Helpers

def preHole : Nat := 100

def postHole : Nat := 1000

structure WithCompanions where
  value : Nat

end Helpers

open Helpers.WithCompanions
open Helpers

namespace Submission
namespace Helpers
def first : Nat := 1
theorem second_eq : first + rootHelper + preHole = first + 141 := rfl
theorem third_eq : postHole + ({ value := 0 } : WithCompanions).value = 1000 := rfl
end Helpers
end Submission