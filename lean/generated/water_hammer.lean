import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Water hammer on valve closure

Machine-checkable statements for this investigation (water-hammer).
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
def d_D : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Inner diameter [m]
def d_E_p : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Young’s modulus of the pipe [GPa]
def d_K_f : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Bulk modulus of the liquid [GPa]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Pipe length [m]
def d_T_p : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Pipe period 2L/a [s]
def d_a_w : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Wave speed [m/s]
def d_c_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Axial-restraint factor [1]
def d_dp_J : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Joukowsky pressure rise [Pa]
def d_e_w : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Wall thickness [mm]
def d_f_D : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Darcy friction factor [1]
def d_nu : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Poisson’s ratio of the pipe [1]
def d_p : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Pressure [Pa]
def d_p_max : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Peak pressure at the valve [Pa]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Liquid density [kg/m^3]
def d_sigma_h : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Peak hoop stress [Pa]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_v : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Velocity [m/s]
def d_v_0 : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Initial flow velocity [m/s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance from the reservoir [m]

/-! ## 1. Wave speed

    a_w = sqrt((K_f/rho)/(1 + K_f*D*c_1/(E_p*e_w)))
-/
/-- Both sides of "Wave speed" carry the same physical dimension. -/
theorem eq1_aw_dim : d_a_w = (Dim.pow (Dim.div (Dim.div d_K_f d_rho) Dim.one) 1 2) := by decide
theorem eq1_aw_term1 : Dim.one = (Dim.div (Dim.mul (Dim.mul d_K_f d_D) d_c_1) (Dim.mul d_E_p d_e_w)) := by decide
/-- The denominator `rho` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_aw_reg1 (rho : ℝ) (hrho : 0 < rho) : rho ≠ 0 := by positivity
/-- The denominator `E_p * e_w` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_aw_reg2 (E_p e_w : ℝ) (hE_p : 0 < E_p) (he_w : 0 < e_w) : E_p * e_w ≠ 0 := by positivity
/-- Domain condition for `1 + K_f * D * c_1 / (E_p * e_w)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_aw_cond3 (K_f D c_1 E_p e_w : ℝ) (hdom : (1 : ℝ) + K_f * D * c_1 / (E_p * e_w) ≠ 0) : (1 : ℝ) + K_f * D * c_1 / (E_p * e_w) ≠ 0 := hdom
/-- Domain condition for `K_f / rho / (1 + K_f * D * c_1 / (E_p * e_w))`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_aw_cond4 (K_f rho D c_1 E_p e_w : ℝ) (hdom : 0 ≤ K_f / rho / ((1 : ℝ) + K_f * D * c_1 / (E_p * e_w))) : 0 ≤ K_f / rho / ((1 : ℝ) + K_f * D * c_1 / (E_p * e_w)) := hdom

/-! ## 2. Restraint factor

    c_1 = 1 - nu^2
-/
/-- Both sides of "Restraint factor" carry the same physical dimension. -/
theorem eq2_c1_dim : d_c_1 = Dim.one := by decide
theorem eq2_c1_term1 : Dim.one = (Dim.pow d_nu 2 1) := by decide

/-! ## 3. Joukowsky pressure rise

    dp_J = rho*a_w*v_0
-/
/-- Both sides of "Joukowsky pressure rise" carry the same physical dimension. -/
theorem eq3_jouk_dim : d_dp_J = (Dim.mul (Dim.mul d_rho d_a_w) d_v_0) := by decide

/-! ## 4. Continuity

    pd(p,t) = -rho*a_w^2*pd(v,x)
-/
/-- Both sides of "Continuity" carry the same physical dimension. -/
theorem eq4_cont_dim : (Dim.div d_p d_t) = (Dim.mul (Dim.mul d_rho (Dim.pow d_a_w 2 1)) (Dim.div d_v d_x)) := by decide

/-! ## 5. Momentum

    pd(v,t) = -pd(p,x)/rho - f_D*v*abs(v)/(2*D)
-/
/-- Both sides of "Momentum" carry the same physical dimension. -/
theorem eq5_mom_dim : (Dim.div d_v d_t) = (Dim.div (Dim.div d_p d_x) d_rho) := by decide
theorem eq5_mom_term1 : (Dim.div (Dim.div d_p d_x) d_rho) = (Dim.div (Dim.mul (Dim.mul d_f_D d_v) d_v) (Dim.mul Dim.one d_D)) := by decide
/-- The denominator `rho` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_mom_reg1 (rho : ℝ) (hrho : 0 < rho) : rho ≠ 0 := by positivity
/-- The denominator `2 * D` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_mom_reg2 (D : ℝ) (hD : 0 < D) : (2 : ℝ) * D ≠ 0 := by positivity

/-! ## 6. Pipe period

    T_p = 2*L/a_w
-/
/-- Both sides of "Pipe period" carry the same physical dimension. -/
theorem eq6_per_dim : d_T_p = (Dim.div (Dim.mul Dim.one d_L) d_a_w) := by decide
/-- The denominator `a_w` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_per_reg1 (a_w : ℝ) (ha_w : 0 < a_w) : a_w ≠ 0 := by positivity

/-! ## 7. Peak hoop stress

    sigma_h = p_max*D/(2*e_w)
-/
/-- Both sides of "Peak hoop stress" carry the same physical dimension. -/
theorem eq7_hoop_dim : d_sigma_h = (Dim.div (Dim.mul d_p_max d_D) (Dim.mul Dim.one d_e_w)) := by decide
/-- The denominator `2 * e_w` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_hoop_reg1 (e_w : ℝ) (he_w : 0 < e_w) : (2 : ℝ) * e_w ≠ 0 := by positivity

end Bespoke
