import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc]
  nth_rw 2 [add_comm]
  rw [neg_add_cancel, add_comm, zero_add]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b]
  rw [h, ← add_assoc, neg_add_cancel, zero_add]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← neg_add_cancel_left b a]
  rw [add_comm] at h
  rw [h, ← add_assoc,
      add_comm,
      ← add_assoc,
      add_comm b, neg_add_cancel, zero_add]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_left_cancel
  rw [h, add_comm, neg_add_cancel]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← add_neg_cancel_left b a]
  rw [add_comm, add_comm, add_comm, add_assoc, h, add_zero]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [neg_add_cancel]

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : ℝ) : a - a = 0 := by
  apply add_neg_cancel

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

lemma mul_neg_cancel_right (a b : G) : b⁻¹ * b * a = a := by
  rw [inv_mul_cancel, one_mul]

lemma rev_mul_neg_cancel_right (a b : G) : a =  b⁻¹ * b * a := by
  rw [inv_mul_cancel, one_mul]

lemma mul_right_cancel {a b c : G} (h :  a * b = a * c) : b = c := by
  rw [← mul_neg_cancel_right b a, ← mul_neg_cancel_right c a]
  rw [mul_assoc, mul_assoc]
  rw [h]

lemma neg_eq_of_mul_eq_zero_inside {a b : G} (h : a⁻¹ * b = 1) : b = a := by
  apply mul_right_cancel
  rw [h, inv_mul_cancel]

lemma rev_neg_eq_of_mul_eq_zero_inside {a b : G} (h : a⁻¹ * b = 1) : a = b := by
  apply mul_right_cancel
  rw [h, inv_mul_cancel]

-- ✨
lemma mul_neg_cancel_left (a b : G): a * b⁻¹ * b = a := by
  apply neg_eq_of_mul_eq_zero_inside
  rw [mul_assoc, inv_mul_cancel, ← mul_assoc, ← rev_mul_neg_cancel_right 1 a]

lemma mul_left_cancel {a b c : G} (h :  b * a⁻¹ = c * a⁻¹) : b = c := by
  rw [← mul_neg_cancel_left b a, ← mul_neg_cancel_left c a]
  rw [h]

theorem inv_inv {a : G}: a = a⁻¹⁻¹ := by
  apply mul_right_cancel
  rw [mul_neg_cancel_left, mul_neg_cancel_right]

lemma rev_inv {a b : G} (h: a = b⁻¹): a⁻¹ = b := by
  rw [h, ← inv_inv]

lemma mul_inv_cancel_helper (a : G) : 1 = a * a⁻¹ := by
  rw [← mul_neg_cancel_right a a⁻¹]
  apply mul_left_cancel
  rw [one_mul, rev_inv]
  rw [inv_mul_cancel, ← inv_inv, one_mul, mul_neg_cancel_left]
  rw [← inv_inv]

-- to be proved
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  rw [mul_inv_cancel_helper]

-- to be proved
theorem mul_one (a : G) : a * 1 = a := by
 rw [← inv_mul_cancel a, ← mul_assoc]
 rw [mul_neg_cancel_left]

-- to be proved
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
 apply rev_neg_eq_of_mul_eq_zero_inside
 rw [← inv_inv]
 rw [← mul_assoc]
 nth_rw 2 [mul_assoc]
 rw [mul_inv_cancel, mul_one]
 rw [mul_inv_cancel]

end MyGroup

end
