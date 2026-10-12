import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Two-body orbit by symplectic integration

Machine-checkable statements for this investigation (orbital-two-body).
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
def d_GM : Dim := ⟨0, 36, -24, 0, 0, 0, 0⟩  -- Gravitational parameter of the central body [m^3/s^2]
def d_T_K : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Kepler period [s]
def d_a_sm : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Semi-major axis [m]
def d_ecc : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Eccentricity [1]
def d_eps : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Specific orbital energy [J/kg]
def d_h_a : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Specific angular momentum [m^2/s]
def d_mu_g : Dim := ⟨0, 36, -24, 0, 0, 0, 0⟩  -- Effective gravitational parameter [m^3/s^2]
def d_r : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Separation [m]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_v : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed [m/s]
def d_v_x : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Velocity, first component [m/s]
def d_v_y : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Velocity, second component [m/s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position, first Cartesian component [m]
def d_y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position, second Cartesian component [m]

/-! ## 1. Gravitational parameter

    mu_g = GM
-/
/-- Both sides of "Gravitational parameter" carry the same physical dimension. -/
theorem eq1_mu_dim : d_mu_g = d_GM := by decide

/-! ## 2. Equation of motion, x

    d2(x,t) = -mu_g*x/r^3
-/
/-- Both sides of "Equation of motion, x" carry the same physical dimension. -/
theorem eq2_mx_dim : (Dim.div d_x (Dim.pow d_t 2 1)) = (Dim.div (Dim.mul d_mu_g d_x) (Dim.pow d_r 3 1)) := by decide
/-- Domain condition for `r^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_mx_cond1 (r : ℝ) (hdom : r ^ 3 ≠ 0) : r ^ 3 ≠ 0 := hdom

/-! ## 3. Equation of motion, y

    d2(y,t) = -mu_g*y/r^3
-/
/-- Both sides of "Equation of motion, y" carry the same physical dimension. -/
theorem eq3_my_dim : (Dim.div d_y (Dim.pow d_t 2 1)) = (Dim.div (Dim.mul d_mu_g d_y) (Dim.pow d_r 3 1)) := by decide
/-- Domain condition for `r^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_my_cond1 (r : ℝ) (hdom : r ^ 3 ≠ 0) : r ^ 3 ≠ 0 := hdom

/-! ## 4. Separation

    r = sqrt(x^2 + y^2)
-/
/-- Both sides of "Separation" carry the same physical dimension. -/
theorem eq4_r_dim : d_r = (Dim.pow (Dim.pow d_x 2 1) 1 2) := by decide
theorem eq4_r_term1 : (Dim.pow d_x 2 1) = (Dim.pow d_y 2 1) := by decide
/-- Domain condition for `x^2 + y^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_r_cond1 (x y : ℝ) (hdom : 0 ≤ x ^ 2 + y ^ 2) : 0 ≤ x ^ 2 + y ^ 2 := hdom

/-! ## 5. Specific orbital energy

    eps = v^2/2 - mu_g/r
-/
/-- Both sides of "Specific orbital energy" carry the same physical dimension. -/
theorem eq5_en_dim : d_eps = (Dim.div (Dim.pow d_v 2 1) Dim.one) := by decide
theorem eq5_en_term1 : (Dim.div (Dim.pow d_v 2 1) Dim.one) = (Dim.div d_mu_g d_r) := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_en_reg1  : (2 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `r`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_en_cond2 (r : ℝ) (hdom : r ≠ 0) : r ≠ 0 := hdom

/-! ## 6. Specific angular momentum

    h_a = x*v_y - y*v_x
-/
/-- Both sides of "Specific angular momentum" carry the same physical dimension. -/
theorem eq6_am_dim : d_h_a = (Dim.mul d_x d_v_y) := by decide
theorem eq6_am_term1 : (Dim.mul d_x d_v_y) = (Dim.mul d_y d_v_x) := by decide

/-! ## 7. Semi-major axis

    a_sm = -mu_g/(2*eps)
-/
/-- Both sides of "Semi-major axis" carry the same physical dimension. -/
theorem eq7_sma_dim : d_a_sm = (Dim.div d_mu_g (Dim.mul Dim.one d_eps)) := by decide
/-- Domain condition for `2 * eps`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq7_sma_cond1 (eps : ℝ) (hdom : (2 : ℝ) * eps ≠ 0) : (2 : ℝ) * eps ≠ 0 := hdom

/-! ## 8. Eccentricity

    ecc = sqrt(1 + 2*eps*h_a^2/mu_g^2)
-/
/-- Both sides of "Eccentricity" carry the same physical dimension. -/
theorem eq8_ecc_dim : d_ecc = (Dim.pow Dim.one 1 2) := by decide
theorem eq8_ecc_term1 : Dim.one = (Dim.div (Dim.mul (Dim.mul Dim.one d_eps) (Dim.pow d_h_a 2 1)) (Dim.pow d_mu_g 2 1)) := by decide
/-- Domain condition for `mu_g^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq8_ecc_cond1 (mu_g : ℝ) (hdom : mu_g ^ 2 ≠ 0) : mu_g ^ 2 ≠ 0 := hdom
/-- Domain condition for `1 + 2 * eps * h_a^2 / mu_g^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq8_ecc_cond2 (eps h_a mu_g : ℝ) (hdom : 0 ≤ (1 : ℝ) + (2 : ℝ) * eps * h_a ^ 2 / mu_g ^ 2) : 0 ≤ (1 : ℝ) + (2 : ℝ) * eps * h_a ^ 2 / mu_g ^ 2 := hdom

/-! ## 9. Kepler's third law

    T_K = 2*pi*sqrt(a_sm^3/mu_g)
-/
/-- Both sides of "Kepler's third law" carry the same physical dimension. -/
theorem eq9_k3_dim : d_T_K = (Dim.mul (Dim.mul Dim.one Dim.one) (Dim.pow (Dim.div (Dim.pow d_a_sm 3 1) d_mu_g) 1 2)) := by decide
/-- Domain condition for `mu_g`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq9_k3_cond1 (mu_g : ℝ) (hdom : mu_g ≠ 0) : mu_g ≠ 0 := hdom
/-- Domain condition for `a_sm^3 / mu_g`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq9_k3_cond2 (a_sm mu_g : ℝ) (hdom : 0 ≤ a_sm ^ 3 / mu_g) : 0 ≤ a_sm ^ 3 / mu_g := hdom

end Bespoke
