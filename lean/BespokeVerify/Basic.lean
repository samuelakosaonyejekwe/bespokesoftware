import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Verification library

Lemmas that every generated verification file relies on:

* a decidable algebra of physical dimensions, so that dimensional homogeneity of an equation
  is settled by computation in the kernel;
* boundedness and smoothness of the regularised quotient `a * b / (b ^ 2 + ε ^ 2)` that replaces
  any term able to diverge;
* a few bounds used by the model library (exponential relaxation, saturating nonlinearities,
  the Lorentz factor).

The generated files restate these lemmas so that each can be checked on its own.
-/

namespace Bespoke

/-- Physical dimension: exponents of (mass, length, time, current, temperature, amount,
luminous intensity), stored in twelfths so that square and cube roots stay integral. -/
structure Dim where
  m : Int
  l : Int
  t : Int
  i : Int
  th : Int
  n : Int
  j : Int
  deriving DecidableEq, Repr

namespace Dim
def one : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩
def mul (a b : Dim) : Dim := ⟨a.m + b.m, a.l + b.l, a.t + b.t, a.i + b.i, a.th + b.th, a.n + b.n, a.j + b.j⟩
def div (a b : Dim) : Dim := ⟨a.m - b.m, a.l - b.l, a.t - b.t, a.i - b.i, a.th - b.th, a.n - b.n, a.j - b.j⟩
/-- Rational power p/q. -/
def pow (a : Dim) (p q : Int) : Dim := ⟨a.m * p / q, a.l * p / q, a.t * p / q, a.i * p / q, a.th * p / q, a.n * p / q, a.j * p / q⟩

theorem mul_one (a : Dim) : mul a one = a := by cases a; simp [mul, one]
theorem div_self (a : Dim) : div a a = one := by cases a; simp [div, one]
theorem mul_comm (a b : Dim) : mul a b = mul b a := by cases a; cases b; simp [mul, Int.add_comm]
end Dim

/-- The softened denominator never vanishes. -/
theorem soft_den_pos (b ε : ℝ) (hε : 0 < ε) : 0 < b ^ 2 + ε ^ 2 := by positivity

/-- A regularised quotient is bounded by |a| / (2 ε) for every real b: it cannot blow up. -/
theorem soft_recip_bounded (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := by
  have hpos : 0 < b ^ 2 + ε ^ 2 := by positivity
  rw [abs_div, abs_mul, abs_of_pos hpos, div_le_div_iff₀ hpos (by positivity)]
  have h : 2 * ε * |b| ≤ b ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg (|b| - ε), sq_abs b]
  nlinarith [abs_nonneg a, abs_nonneg b]

/-- The regularised reciprocal is infinitely differentiable on the whole real line. -/
theorem soft_recip_smooth (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ⊤ (fun b : ℝ => b / (b ^ 2 + ε ^ 2)) := by
  apply ContDiff.div contDiff_id (by fun_prop)
  intro x; positivity

/-- Away from the singular set the regularised quotient agrees with the original:
the difference is exactly `a * ε ^ 2 / (b * (b ^ 2 + ε ^ 2))`. -/
theorem soft_recip_error (a b ε : ℝ) (hb : b ≠ 0) (hε : 0 < ε) :
    a / b - a * b / (b ^ 2 + ε ^ 2) = a * ε ^ 2 / (b * (b ^ 2 + ε ^ 2)) := by
  have hpos : b ^ 2 + ε ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Exponential relaxation never exceeds its initial amplitude. -/
theorem decay_bounded (x ell : ℝ) (hx : 0 ≤ x) (hl : 0 < ell) : Real.exp (-x / ell) ≤ 1 := by
  rw [Real.exp_le_one_iff]; have := div_nonneg hx hl.le; linarith [neg_div ell x]

/-- Saturating nonlinearity stays strictly inside (-1, 1). -/
theorem tanh_bounded (x : ℝ) : |Real.tanh x| < 1 := by
  rw [abs_lt]; exact ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩

/-- Below light speed the Lorentz factor is well defined. -/
theorem lorentz_pos (v c : ℝ) (hc : 0 < c) (hv : |v| < c) : 0 < 1 - v ^ 2 / c ^ 2 := by
  have h : v ^ 2 < c ^ 2 := by nlinarith [abs_lt.mp hv, sq_abs v, abs_nonneg v]
  have : v ^ 2 / c ^ 2 < 1 := by rw [div_lt_one (by positivity)]; exact h
  linarith

/-- A sum of two bounded quantities is bounded by the sum of the bounds. -/
theorem bounded_add (x y A B : ℝ) (hx : |x| ≤ A) (hy : |y| ≤ B) : |x + y| ≤ A + B :=
  (abs_add_le x y).trans (add_le_add hx hy)

/-- A product of two bounded quantities is bounded by the product of the bounds. -/
theorem bounded_mul (x y A B : ℝ) (hx : |x| ≤ A) (hy : |y| ≤ B) : |x * y| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg y) ((abs_nonneg x).trans hx)

end Bespoke
