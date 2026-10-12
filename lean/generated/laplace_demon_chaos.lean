import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Laplace's demon and the limits of prediction

Machine-checkable statements for this investigation (laplace-demon-chaos).
Dimensional homogeneity is proved by computation. Regularity statements are proved where the
declared domain makes them true, and are otherwise stated with their hypotheses made explicit.
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

/-! ## Dimensions of the symbols -/

def d_length : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩
def d_Delta_tol : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Largest tolerable prediction error [1]
def d_delta_0 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Uncertainty of the initial state [1]
def d_delta_n : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Error after n steps [1]
def d_lambda_L : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Lyapunov exponent per step [1]
def d_lambda_k : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Local stretching rate at step k [1]
def d_n_k : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of steps [1]
def d_r_map : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Logistic-map parameter r [1]
def d_t_star : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Prediction horizon in steps [1]
def d_x_k : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- State at step k [1]
def d_x_next : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- State at the following step [1]

/-! ## 1. Logistic map

    x_next = r_map*x_k*(1 - x_k)
-/
/-- Both sides of "Logistic map" carry the same physical dimension. -/
theorem eq1_map_dim : d_x_next = (Dim.mul (Dim.mul d_r_map d_x_k) Dim.one) := by decide
theorem eq1_map_term1 : Dim.one = d_x_k := by decide

/-! ## 2. Local stretching rate

    lambda_k = ln(abs(r_map*(1 - 2*x_k)))
-/
/-- Both sides of "Local stretching rate" carry the same physical dimension. -/
theorem eq2_loc_dim : d_lambda_k = Dim.one := by decide
theorem eq2_loc_term1 : Dim.one = (Dim.mul Dim.one d_x_k) := by decide
theorem eq2_loc_term2 : (Dim.mul d_r_map Dim.one) = Dim.one := by decide
/-- Domain condition for `abs(r_map * (1 - 2 * x_k))`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_loc_cond1 (r_map x_k : ℝ) (hdom : 0 < abs (r_map * ((1 : ℝ) - (2 : ℝ) * x_k))) : 0 < abs (r_map * ((1 : ℝ) - (2 : ℝ) * x_k)) := hdom

/-! ## 3. Growth of a small error

    delta_n = delta_0*exp(lambda_L*n_k)
-/
/-- Both sides of "Growth of a small error" carry the same physical dimension. -/
theorem eq3_grow_dim : d_delta_n = (Dim.mul d_delta_0 Dim.one) := by decide
theorem eq3_grow_term1 : (Dim.mul d_lambda_L d_n_k) = Dim.one := by decide

/-! ## 4. Prediction horizon

    t_star = ln(Delta_tol/delta_0)/lambda_L
-/
/-- Both sides of "Prediction horizon" carry the same physical dimension. -/
theorem eq4_hor_dim : d_t_star = (Dim.div Dim.one d_lambda_L) := by decide
theorem eq4_hor_term1 : (Dim.div d_Delta_tol d_delta_0) = Dim.one := by decide
/-- The denominator `delta_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_hor_reg1 (delta_0 : ℝ) (hdelta_0 : 0 < delta_0) : delta_0 ≠ 0 := by positivity
/-- The argument `Delta_tol / delta_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_hor_reg2 (Delta_tol delta_0 : ℝ) (hDelta_tol : 0 < Delta_tol) (hdelta_0 : 0 < delta_0) : 0 < Delta_tol / delta_0 := by positivity
/-- The denominator `lambda_L` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_hor_reg3 (lambda_L : ℝ) (hlambda_L : 0 < lambda_L) : lambda_L ≠ 0 := by positivity

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (Chaos Det Exact Pred : Prop) (h1 : Det) (h2 : Chaos) (h3 : ¬Exact) (h4 : (Det ∧ Exact) → Pred) (h5 : (Chaos ∧ (¬Exact)) → (¬Pred)) : Det ∧ (¬Pred) := by tauto

end Bespoke
