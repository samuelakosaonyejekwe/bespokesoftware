import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Hypothetical short-range fifth force of Yukawa form

Machine-checkable statements for this investigation (yukawa-fifth-force).
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
def d_E_med : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Rest energy of the mediating boson [J]
def d_F : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Total force between the bodies [N]
def d_F_N : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Newtonian force [N]
def d_G : Dim := ⟨-12, 36, -24, 0, 0, 0, 0⟩  -- Gravitational constant [m^3/(kg s^2)]
def d_L_arm : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Lever arm of the torsion pendulum [cm]
def d_V : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Interaction potential energy [J]
def d_alpha_Y : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Strength of the new interaction relative to gravity [1]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light [m/s]
def d_dtheta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Anomalous deflection of the pendulum [rad]
def d_hbar : Dim := ⟨12, 24, -12, 0, 0, 0, 0⟩  -- Reduced Planck constant [J s]
def d_kappa_t : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Torsion constant of the fibre [N m]
def d_lambda_Y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Range of the new interaction [mm]
def d_m_1 : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Source (attractor) mass [g]
def d_m_2 : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Test mass on the pendulum [g]
def d_r : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Centre-to-centre separation [mm]

/-! ## 1. Newtonian force

    F_N = G*m_1*m_2/r^2
-/
/-- Both sides of "Newtonian force" carry the same physical dimension. -/
theorem eq1_newton_dim : d_F_N = (Dim.div (Dim.mul (Dim.mul d_G d_m_1) d_m_2) (Dim.pow d_r 2 1)) := by decide
/-- The denominator `r^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_newton_reg1 (r : ℝ) (hr : 0 < r) : r ^ 2 ≠ 0 := by positivity

/-! ## 2. Potential with a Yukawa term

    V = -G*m_1*m_2/r*(1 + alpha_Y*exp(-r/lambda_Y))
-/
/-- Both sides of "Potential with a Yukawa term" carry the same physical dimension. -/
theorem eq2_pot_dim : d_V = (Dim.mul (Dim.div (Dim.mul (Dim.mul d_G d_m_1) d_m_2) d_r) Dim.one) := by decide
theorem eq2_pot_term1 : (Dim.div d_r d_lambda_Y) = Dim.one := by decide
theorem eq2_pot_term2 : Dim.one = (Dim.mul d_alpha_Y Dim.one) := by decide
/-- The denominator `r` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_pot_reg1 (r : ℝ) (hr : 0 < r) : r ≠ 0 := by positivity
/-- The denominator `lambda_Y` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_pot_reg2 (lambda_Y : ℝ) (hlambda_Y : 0 < lambda_Y) : lambda_Y ≠ 0 := by positivity

/-! ## 3. Force with a Yukawa term

    F = G*m_1*m_2/r^2*(1 + alpha_Y*(1 + r/lambda_Y)*exp(-r/lambda_Y))
-/
/-- Both sides of "Force with a Yukawa term" carry the same physical dimension. -/
theorem eq3_force_dim : d_F = (Dim.mul (Dim.div (Dim.mul (Dim.mul d_G d_m_1) d_m_2) (Dim.pow d_r 2 1)) Dim.one) := by decide
theorem eq3_force_term1 : Dim.one = (Dim.div d_r d_lambda_Y) := by decide
theorem eq3_force_term2 : (Dim.div d_r d_lambda_Y) = Dim.one := by decide
theorem eq3_force_term3 : Dim.one = (Dim.mul (Dim.mul d_alpha_Y Dim.one) Dim.one) := by decide
/-- The denominator `r^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_force_reg1 (r : ℝ) (hr : 0 < r) : r ^ 2 ≠ 0 := by positivity
/-- The denominator `lambda_Y` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_force_reg2 (lambda_Y : ℝ) (hlambda_Y : 0 < lambda_Y) : lambda_Y ≠ 0 := by positivity
/-- The denominator `lambda_Y` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_force_reg3 (lambda_Y : ℝ) (hlambda_Y : 0 < lambda_Y) : lambda_Y ≠ 0 := by positivity

/-! ## 4. Rest energy of the mediator

    E_med = hbar*c/lambda_Y
-/
/-- Both sides of "Rest energy of the mediator" carry the same physical dimension. -/
theorem eq4_med_dim : d_E_med = (Dim.div (Dim.mul d_hbar d_c) d_lambda_Y) := by decide
/-- The denominator `lambda_Y` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_med_reg1 (lambda_Y : ℝ) (hlambda_Y : 0 < lambda_Y) : lambda_Y ≠ 0 := by positivity

/-! ## 5. Anomalous deflection of the pendulum

    dtheta = 2*(F - F_N)*L_arm/kappa_t
-/
/-- Both sides of "Anomalous deflection of the pendulum" carry the same physical dimension. -/
theorem eq5_defl_dim : d_dtheta = (Dim.div (Dim.mul (Dim.mul Dim.one d_F) d_L_arm) d_kappa_t) := by decide
theorem eq5_defl_term1 : d_F = d_F_N := by decide
/-- The denominator `kappa_t` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_defl_reg1 (kappa_t : ℝ) (hkappa_t : 0 < kappa_t) : kappa_t ≠ 0 := by positivity

end Bespoke
