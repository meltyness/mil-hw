import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (max_le_max_left c : a ≤ b → max c a ≤ max c b)
#check (max_le_max_right c : a ≤ b → max a c ≤ max b c)
#check (max_le_max : a ≤ c → b ≤ d → max a b ≤ max c d)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    exact le_max_right b a
    exact le_max_left b a
  repeat
    apply max_le
    exact le_max_right a b
    exact le_max_left a b

theorem nested: min (min a b) c = min a (min b c) := by
  exact min_assoc a b c

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  have h: ∀ x y c : ℝ, min x y ≤ x → min x y + c ≤ x + c := by
    exact fun x y c a ↦ add_le_add_right a c
  . show min a b + c ≤ a + c
    . apply h
      exact min_le_left a b

  have h: ∀ x y c : ℝ, min x y ≤ y → min x y + c ≤ y + c := by
    exact fun x y c a ↦ add_le_add_right a c
  . show min a b + c ≤ b + c
    . apply h
      exact min_le_right a b

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  apply aux
  rw [← add_neg_cancel_right (min a b) (-min (a + c) (b + c))]
  rw [← add_neg_cancel_right (min (a + c) (b + c)) (-min a b)]
  simp
  exact LinearOrder.le_total a b


#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  rw [← sub_add_cancel |a-b| |b|]
  have h: ∀ a b : ℝ, |a| ≤ |a - b| + |b| ↔ |a| - |b| ≤ |a - b| - |b| + |b| := by
    ring_nf
    exact fun a b ↦ Iff.symm neg_add_le_iff_le_add'
  rw [← h]
  show |a| ≤ |a - b| + |b|
  let c := a - b
  have h₂ : a - b = c := rfl
  rw [h₂]
  have h₃ : a = b + c := by
    exact Eq.symm (add_sub_cancel b a)
  rw [h₃, add_comm]
  apply abs_add

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  apply dvd_add
  . rw [← mul_assoc, mul_comm, ← mul_assoc]
    let c := z * y
    have h₁ : z * y = c := rfl
    rw [h₁]
    apply dvd_mul_left
  . apply dvd_mul_left
  . have h₂ : w ∣ w ^ 2 := by
      apply dvd_mul_left
    apply dvd_trans h h₂

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  . rw [@Nat.dvd_gcd_iff]
    constructor
    . exact Nat.gcd_dvd_right m n
    . exact Nat.gcd_dvd_left m n
  . rw [@Nat.dvd_gcd_iff]
    constructor
    . exact Nat.gcd_dvd_right n m
    . exact Nat.gcd_dvd_left n m

end
