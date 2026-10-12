import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Galileo's falling bodies

Machine-checkable statements for this investigation (galileo-falling-bodies).
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
def d_C_D : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Drag coefficient of a sphere [1]
def d_d_b : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Diameter of the body [m]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_h_d : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Height of the drop [m]
def d_m : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass of a falling body [kg]
def d_m_1 : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass of the heavy body [kg]
def d_m_2 : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass of the light body [kg]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Air density [kg/m^3]
def d_rho_b : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Density of the bodies [kg/m^3]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_t_A1 : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Aristotelian fall time of the heavy body [s]
def d_t_A2 : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Aristotelian fall time of the light body [s]
def d_t_f : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time of fall [s]
def d_v : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Downward speed [m/s]
def d_v_t : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Terminal velocity [m/s]
def d_y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Height above the ground [m]

/-! ## 1. Equation of motion of each body

    m*d(v,t) = m*g - 0.5*rho*C_D*A*v^2
-/
/-- Both sides of "Equation of motion of each body" carry the same physical dimension. -/
theorem eq1_mom_dim : (Dim.mul d_m (Dim.div d_v d_t)) = (Dim.mul d_m d_g) := by decide
theorem eq1_mom_term1 : (Dim.mul d_m d_g) = (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) d_C_D) d_A) (Dim.pow d_v 2 1)) := by decide

/-! ## 2. Kinematics

    d(y,t) = -v
-/
/-- Both sides of "Kinematics" carry the same physical dimension. -/
theorem eq2_kin_dim : (Dim.div d_y d_t) = d_v := by decide

/-! ## 3. Mass of a solid sphere

    m = rho_b*pi*d_b^3/6
-/
/-- Both sides of "Mass of a solid sphere" carry the same physical dimension. -/
theorem eq3_mass_dim : d_m = (Dim.div (Dim.mul (Dim.mul d_rho_b Dim.one) (Dim.pow d_d_b 3 1)) Dim.one) := by decide
/-- The denominator `6` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_mass_reg1  : (6 : ℝ) ≠ 0 := by positivity

/-! ## 4. Frontal area

    A = pi*d_b^2/4
-/
/-- Both sides of "Frontal area" carry the same physical dimension. -/
theorem eq4_area_dim : d_A = (Dim.div (Dim.mul Dim.one (Dim.pow d_d_b 2 1)) Dim.one) := by decide
/-- The denominator `4` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_area_reg1  : (4 : ℝ) ≠ 0 := by positivity

/-! ## 5. Terminal velocity

    v_t = sqrt(2*m*g/(rho*C_D*A))
-/
/-- Both sides of "Terminal velocity" carry the same physical dimension. -/
theorem eq5_vt_dim : d_v_t = (Dim.pow (Dim.div (Dim.mul (Dim.mul Dim.one d_m) d_g) (Dim.mul (Dim.mul d_rho d_C_D) d_A)) 1 2) := by decide
/-- Domain condition for `rho * C_D * A`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_vt_cond1 (rho C_D A : ℝ) (hdom : rho * C_D * A ≠ 0) : rho * C_D * A ≠ 0 := hdom
/-- Domain condition for `2 * m * g / (rho * C_D * A)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_vt_cond2 (m g rho C_D A : ℝ) (hdom : 0 ≤ (2 : ℝ) * m * g / (rho * C_D * A)) : 0 ≤ (2 : ℝ) * m * g / (rho * C_D * A) := hdom

/-! ## 6. Time of fall with quadratic drag

    t_f = v_t/g*ln(exp(g*h_d/v_t^2) + sqrt(exp(2*g*h_d/v_t^2) - 1))
-/
/-- Both sides of "Time of fall with quadratic drag" carry the same physical dimension. -/
theorem eq6_tf_dim : d_t_f = (Dim.mul (Dim.div d_v_t d_g) Dim.one) := by decide
theorem eq6_tf_term1 : (Dim.div (Dim.mul d_g d_h_d) (Dim.pow d_v_t 2 1)) = Dim.one := by decide
theorem eq6_tf_term2 : (Dim.div (Dim.mul (Dim.mul Dim.one d_g) d_h_d) (Dim.pow d_v_t 2 1)) = Dim.one := by decide
theorem eq6_tf_term3 : Dim.one = Dim.one := by decide
theorem eq6_tf_term4 : Dim.one = (Dim.pow Dim.one 1 2) := by decide
theorem eq6_tf_term5 : Dim.one = Dim.one := by decide
/-- The denominator `g` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_tf_reg1 (g : ℝ) (hg : 0 < g) : g ≠ 0 := by positivity
/-- Domain condition for `v_t^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_tf_cond2 (v_t : ℝ) (hdom : v_t ^ 2 ≠ 0) : v_t ^ 2 ≠ 0 := hdom
/-- Domain condition for `v_t^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_tf_cond3 (v_t : ℝ) (hdom : v_t ^ 2 ≠ 0) : v_t ^ 2 ≠ 0 := hdom
/-- Domain condition for `exp(2 * g * h_d / v_t^2) - 1`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_tf_cond4 (g h_d v_t : ℝ) (hdom : 0 ≤ Real.exp ((2 : ℝ) * g * h_d / v_t ^ 2) - (1 : ℝ)) : 0 ≤ Real.exp ((2 : ℝ) * g * h_d / v_t ^ 2) - (1 : ℝ) := hdom
/-- Domain condition for `exp(g * h_d / v_t^2) + sqrt(exp(2 * g * h_d / v_t^2) - 1)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_tf_cond5 (g h_d v_t : ℝ) (hdom : 0 < Real.exp (g * h_d / v_t ^ 2) + Real.sqrt (Real.exp ((2 : ℝ) * g * h_d / v_t ^ 2) - (1 : ℝ))) : 0 < Real.exp (g * h_d / v_t ^ 2) + Real.sqrt (Real.exp ((2 : ℝ) * g * h_d / v_t ^ 2) - (1 : ℝ)) := hdom

/-! ## 7. Aristotelian doctrine under test

    t_A2/t_A1 = m_1/m_2
-/
/-- Both sides of "Aristotelian doctrine under test" carry the same physical dimension. -/
theorem eq7_aris_dim : (Dim.div d_t_A2 d_t_A1) = (Dim.div d_m_1 d_m_2) := by decide
/-- Domain condition for `t_A1`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_aris_cond1 (t_A1 : ℝ) (hdom : t_A1 ≠ 0) : t_A1 ≠ 0 := hdom
/-- The denominator `m_2` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_aris_reg2 (m_2 : ℝ) (hm_2 : 0 < m_2) : m_2 ≠ 0 := by positivity

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (A Fst S : Prop) (h1 : A → S) (h2 : A → Fst) (h3 : ¬(S ∧ Fst)) : ¬A := by tauto

end Bespoke
