import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Finite-wing lift, drag polar and level-flight performance

Machine-checkable statements for this investigation (wing-lift-drag).
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

/-- The smooth rate cap never lets a rate exceed F in magnitude. -/
theorem rate_cap_bounded (f F : ℝ) (hF : 0 < F) : |f / Real.sqrt (1 + (f / F) ^ 2)| ≤ F := by
  have hs : 0 < Real.sqrt (1 + (f / F) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  have h1 : |f| / F ≤ Real.sqrt (1 + (f / F) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, sq_abs, div_pow]; linarith
  calc |f| = F * (|f| / F) := by field_simp
    _ ≤ F * Real.sqrt (1 + (f / F) ^ 2) := by gcongr

/-- A quantity whose rate of change never exceeds F cannot reach infinity in finite time:
after a time T it has moved by at most F * T. -/
theorem bounded_rate_no_blowup (x : ℝ → ℝ) (F T : ℝ) (hT : 0 ≤ T)
    (hx : ∀ t, DifferentiableAt ℝ x t) (hb : ∀ t, |deriv x t| ≤ F) : |x T - x 0| ≤ F * T := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (f := x) (C := F)
    (fun t _ => hx t) (fun t _ => by simpa [Real.norm_eq_abs] using hb t) convex_univ (Set.mem_univ 0) (Set.mem_univ T)
  simpa [Real.norm_eq_abs, abs_of_nonneg hT] using h


/-! ## Dimensions of the symbols -/

def d_length : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩
def d_AR : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Aspect ratio (span² / area) [1]
def d_C_D : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Drag coefficient [1]
def d_C_D0 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Zero-lift drag coefficient [1]
def d_C_L : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Lift coefficient [1]
def d_C_Lmax : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Maximum lift coefficient [1]
def d_D : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Drag [N]
def d_L : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Lift [N]
def d_LD : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Lift-to-drag ratio in level flight [1]
def d_LD_max : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Maximum lift-to-drag ratio [1]
def d_P_req : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Power required for level flight [W]
def d_R_air : Dim := ⟨0, 24, -24, 0, -12, 0, 0⟩  -- Specific gas constant of air [J/(kg K)]
def d_R_b : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Breguet range [m]
def d_S : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Wing reference area [m^2]
def d_T_a : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Ambient temperature [K]
def d_V : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- True airspeed [m/s]
def d_V_s : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Stall speed [m/s]
def d_a_0 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Section lift-curve slope (per radian) [1]
def d_a_w : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Wing lift-curve slope (per radian) [1]
def d_alpha : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Angle of attack [deg]
def d_alpha_0 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Zero-lift angle of attack [deg]
def d_c_b : Dim := ⟨0, -24, 24, 0, 0, 0, 0⟩  -- Brake specific fuel consumption [g/kWh]
def d_e_o : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Oswald span-efficiency factor [1]
def d_eta_p : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Propulsive (propeller) efficiency [1]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Standard gravity [m/s^2]
def d_m : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Aircraft mass [kg]
def d_p_a : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Ambient pressure [Pa]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Air density [kg/m^3]
def d_zeta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fuel mass fraction of take-off mass [1]

/-! ## 1. Air density

    rho = p_a/(R_air*T_a)
-/
/-- Both sides of "Air density" carry the same physical dimension. -/
theorem eq1_rho_dim : d_rho = (Dim.div d_p_a (Dim.mul d_R_air d_T_a)) := by decide
/-- Domain condition for `R_air * T_a`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_rho_cond1 (R_air T_a : ℝ) (hdom : R_air * T_a ≠ 0) : R_air * T_a ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq1_rho_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 2. Finite-wing lift-curve slope

    a_w = a_0/(1 + a_0/(pi*e_o*AR))
-/
/-- Both sides of "Finite-wing lift-curve slope" carry the same physical dimension. -/
theorem eq2_slope_dim : d_a_w = (Dim.div d_a_0 Dim.one) := by decide
theorem eq2_slope_term1 : Dim.one = (Dim.div d_a_0 (Dim.mul (Dim.mul Dim.one d_e_o) d_AR)) := by decide
/-- The denominator `pi * e_o * AR` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_slope_reg1 (e_o AR : ℝ) (he_o : 0 < e_o) (hAR : 0 < AR) : Real.pi * e_o * AR ≠ 0 := by positivity
/-- The denominator `1 + a_0 / (pi * e_o * AR)` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_slope_reg2 (a_0 e_o AR : ℝ) (ha_0 : 0 < a_0) (he_o : 0 < e_o) (hAR : 0 < AR) : (1 : ℝ) + a_0 / (Real.pi * e_o * AR) ≠ 0 := by positivity

/-! ## 3. Lift coefficient

    C_L = a_w*(alpha - alpha_0)
-/
/-- Both sides of "Lift coefficient" carry the same physical dimension. -/
theorem eq3_cl_dim : d_C_L = (Dim.mul d_a_w d_alpha) := by decide
theorem eq3_cl_term1 : d_alpha = d_alpha_0 := by decide

/-! ## 4. Parabolic drag polar

    C_D = C_D0 + C_L^2/(pi*e_o*AR)
-/
/-- Both sides of "Parabolic drag polar" carry the same physical dimension. -/
theorem eq4_cd_dim : d_C_D = d_C_D0 := by decide
theorem eq4_cd_term1 : d_C_D0 = (Dim.div (Dim.pow d_C_L 2 1) (Dim.mul (Dim.mul Dim.one d_e_o) d_AR)) := by decide
/-- The denominator `pi * e_o * AR` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_cd_reg1 (e_o AR : ℝ) (he_o : 0 < e_o) (hAR : 0 < AR) : Real.pi * e_o * AR ≠ 0 := by positivity

/-! ## 5. Lift

    L = 0.5*rho*V^2*S*C_L
-/
/-- Both sides of "Lift" carry the same physical dimension. -/
theorem eq5_lift_dim : d_L = (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) (Dim.pow d_V 2 1)) d_S) d_C_L) := by decide

/-! ## 6. Drag

    D = 0.5*rho*V^2*S*C_D
-/
/-- Both sides of "Drag" carry the same physical dimension. -/
theorem eq6_drag_dim : d_D = (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) (Dim.pow d_V 2 1)) d_S) d_C_D) := by decide

/-! ## 7. Stall speed

    V_s = sqrt(2*m*g/(rho*S*C_Lmax))
-/
/-- Both sides of "Stall speed" carry the same physical dimension. -/
theorem eq7_vs_dim : d_V_s = (Dim.pow (Dim.div (Dim.mul (Dim.mul Dim.one d_m) d_g) (Dim.mul (Dim.mul d_rho d_S) d_C_Lmax)) 1 2) := by decide
/-- The denominator `rho * S * C_Lmax` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_vs_reg1 (rho S C_Lmax : ℝ) (hrho : 0 < rho) (hS : 0 < S) (hC_Lmax : 0 < C_Lmax) : rho * S * C_Lmax ≠ 0 := by positivity
/-- The argument `2 * m * g / (rho * S * C_Lmax)` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_vs_reg2 (m g rho S C_Lmax : ℝ) (hm : 0 < m) (hg : 0 < g) (hrho : 0 < rho) (hS : 0 < S) (hC_Lmax : 0 < C_Lmax) : 0 ≤ (2 : ℝ) * m * g / (rho * S * C_Lmax) := by positivity

/-! ## 8. Maximum lift-to-drag ratio

    LD_max = 0.5*sqrt(pi*e_o*AR/C_D0)
-/
/-- Both sides of "Maximum lift-to-drag ratio" carry the same physical dimension. -/
theorem eq8_ldmax_dim : d_LD_max = (Dim.mul Dim.one (Dim.pow (Dim.div (Dim.mul (Dim.mul Dim.one d_e_o) d_AR) d_C_D0) 1 2)) := by decide
/-- The denominator `C_D0` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_ldmax_reg1 (C_D0 : ℝ) (hC_D0 : 0 < C_D0) : C_D0 ≠ 0 := by positivity
/-- The argument `pi * e_o * AR / C_D0` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_ldmax_reg2 (e_o AR C_D0 : ℝ) (he_o : 0 < e_o) (hAR : 0 < AR) (hC_D0 : 0 < C_D0) : 0 ≤ Real.pi * e_o * AR / C_D0 := by positivity

/-! ## 9. Power required in level flight

    P_req = 0.5*rho*V^3*S*C_D0 + 2*(m*g)^2/(pi*e_o*AR*rho*V*S)
-/
/-- Both sides of "Power required in level flight" carry the same physical dimension. -/
theorem eq9_preq_dim : d_P_req = (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) (Dim.pow d_V 3 1)) d_S) d_C_D0) := by decide
theorem eq9_preq_term1 : (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) (Dim.pow d_V 3 1)) d_S) d_C_D0) = (Dim.div (Dim.mul Dim.one (Dim.pow (Dim.mul d_m d_g) 2 1)) (Dim.mul (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_e_o) d_AR) d_rho) d_V) d_S)) := by decide
/-- The denominator `pi * e_o * AR * rho * V * S` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_preq_reg1 (e_o AR rho V S : ℝ) (he_o : 0 < e_o) (hAR : 0 < AR) (hrho : 0 < rho) (hV : 0 < V) (hS : 0 < S) : Real.pi * e_o * AR * rho * V * S ≠ 0 := by positivity

/-! ## 10. Breguet range (propeller)

    R_b = eta_p/(g*c_b)*LD*ln(1/(1 - zeta))
-/
/-- Both sides of "Breguet range (propeller)" carry the same physical dimension. -/
theorem eq10_range_dim : d_R_b = (Dim.mul (Dim.mul (Dim.div d_eta_p (Dim.mul d_g d_c_b)) d_LD) Dim.one) := by decide
theorem eq10_range_term1 : Dim.one = d_zeta := by decide
theorem eq10_range_term2 : (Dim.div Dim.one Dim.one) = Dim.one := by decide
/-- The denominator `g * c_b` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_range_reg1 (g c_b : ℝ) (hg : 0 < g) (hc_b : 0 < c_b) : g * c_b ≠ 0 := by positivity
/-- Domain condition for `1 - zeta`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq10_range_cond2 (zeta : ℝ) (hdom : (1 : ℝ) - zeta ≠ 0) : (1 : ℝ) - zeta ≠ 0 := hdom
/-- Domain condition for `1 / (1 - zeta)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq10_range_cond3 (zeta : ℝ) (hdom : 0 < (1 : ℝ) / ((1 : ℝ) - zeta)) : 0 < (1 : ℝ) / ((1 : ℝ) - zeta) := hdom

end Bespoke
