import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Projectile motion with air resistance and wind

Machine-checkable statements for this investigation (projectile-drag).
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
def d_A : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Frontal area [m^2]
def d_C_D : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Drag coefficient [1]
def d_d : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Diameter [m]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_m : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass [kg]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Air density at the launch level [kg/m^3]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_v_r : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed relative to the air [m/s]
def d_v_t : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Terminal velocity [m/s]
def d_v_x : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Horizontal velocity [m/s]
def d_v_y : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Vertical velocity [m/s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Horizontal position [m]
def d_y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Height [m]

/-! ## 1. Frontal area

    A = pi*d^2/4
-/
/-- Both sides of "Frontal area" carry the same physical dimension. -/
theorem eq1_area_dim : d_A = (Dim.div (Dim.mul Dim.one (Dim.pow d_d 2 1)) Dim.one) := by decide
/-- The denominator `4` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_area_reg1  : (4 : ℝ) ≠ 0 := by positivity

/-! ## 2. Speed relative to the air

    v_r = sqrt(v_x^2 + v_y^2)
-/
/-- Both sides of "Speed relative to the air" carry the same physical dimension. -/
theorem eq2_vr_dim : d_v_r = (Dim.pow (Dim.pow d_v_x 2 1) 1 2) := by decide
theorem eq2_vr_term1 : (Dim.pow d_v_x 2 1) = (Dim.pow d_v_y 2 1) := by decide
/-- Domain condition for `v_x^2 + v_y^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_vr_cond1 (v_x v_y : ℝ) (hdom : 0 ≤ v_x ^ 2 + v_y ^ 2) : 0 ≤ v_x ^ 2 + v_y ^ 2 := hdom

/-! ## 3. Horizontal momentum

    m*d(v_x,t) = -0.5*rho*C_D*A*v_r*v_x
-/
/-- Both sides of "Horizontal momentum" carry the same physical dimension. -/
theorem eq3_mx_dim : (Dim.mul d_m (Dim.div d_v_x d_t)) = (Dim.mul (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) d_C_D) d_A) d_v_r) d_v_x) := by decide

/-! ## 4. Vertical momentum

    m*d(v_y,t) = -m*g - 0.5*rho*C_D*A*v_r*v_y
-/
/-- Both sides of "Vertical momentum" carry the same physical dimension. -/
theorem eq4_my_dim : (Dim.mul d_m (Dim.div d_v_y d_t)) = (Dim.mul d_m d_g) := by decide
theorem eq4_my_term1 : (Dim.mul d_m d_g) = (Dim.mul (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) d_C_D) d_A) d_v_r) d_v_y) := by decide

/-! ## 5. Kinematics, x

    d(x,t) = v_x
-/
/-- Both sides of "Kinematics, x" carry the same physical dimension. -/
theorem eq5_kx_dim : (Dim.div d_x d_t) = d_v_x := by decide

/-! ## 6. Kinematics, y

    d(y,t) = v_y
-/
/-- Both sides of "Kinematics, y" carry the same physical dimension. -/
theorem eq6_ky_dim : (Dim.div d_y d_t) = d_v_y := by decide

/-! ## 7. Terminal velocity

    v_t = sqrt(2*m*g/(rho*C_D*A))
-/
/-- Both sides of "Terminal velocity" carry the same physical dimension. -/
theorem eq7_vt_dim : d_v_t = (Dim.pow (Dim.div (Dim.mul (Dim.mul Dim.one d_m) d_g) (Dim.mul (Dim.mul d_rho d_C_D) d_A)) 1 2) := by decide
/-- Domain condition for `rho * C_D * A`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_vt_cond1 (rho C_D A : ℝ) (hdom : rho * C_D * A ≠ 0) : rho * C_D * A ≠ 0 := hdom
/-- Domain condition for `2 * m * g / (rho * C_D * A)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_vt_cond2 (m g rho C_D A : ℝ) (hdom : 0 ≤ (2 : ℝ) * m * g / (rho * C_D * A)) : 0 ≤ (2 : ℝ) * m * g / (rho * C_D * A) := hdom

end Bespoke
