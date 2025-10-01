import Mathlib

namespace Nat

variable {n k r : ℕ}

theorem choose_sub_pos (h : k ≤ n) : 0 < Nat.choose (n - r) (k - r) :=
  Nat.choose_pos (Nat.sub_le_sub_right h r)

theorem choose_sub_ne_zero (h : k ≤ n) : Nat.choose (n - r) (k - r) ≠ 0 :=
  Nat.choose_ne_zero (Nat.sub_le_sub_right h r)

end Nat
