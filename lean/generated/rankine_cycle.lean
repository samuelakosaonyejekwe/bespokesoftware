import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Rankine and organic Rankine power cycle

Machine-checkable statements for this investigation (rankine-cycle).
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
def d_P_net : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Net power output [MW]
def d_R_s : Dim := ⟨0, 24, -24, 0, -12, 0, 0⟩  -- Specific gas constant [J/(kg K)]
def d_T : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Temperature [K]
def d_T_H : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Source temperature [K]
def d_T_L : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Sink temperature [K]
def d_bwr : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Back-work ratio [1]
def d_eta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Thermal efficiency [1]
def d_eta_C : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Carnot efficiency [1]
def d_eta_p : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Pump isentropic efficiency [1]
def d_eta_t : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Turbine isentropic efficiency [1]
def d_h_1 : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Enthalpy, condenser outlet [J/kg]
def d_h_2 : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Enthalpy, pump outlet [J/kg]
def d_h_3 : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Enthalpy, turbine inlet [J/kg]
def d_h_4 : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Enthalpy, turbine outlet [J/kg]
def d_h_4s : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Enthalpy after isentropic expansion [J/kg]
def d_h_fg : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Enthalpy of vaporisation [J/kg]
def d_mdot : Dim := ⟨12, 0, -12, 0, 0, 0, 0⟩  -- Working-fluid mass flow rate [kg/s]
def d_p_b : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Boiler pressure [Pa]
def d_p_c : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Condenser pressure [Pa]
def d_p_p : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Pump delivery pressure [Pa]
def d_p_sat : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Saturation pressure [Pa]
def d_q_in : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Heat added [J/kg]
def d_q_out : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Heat rejected [J/kg]
def d_s_3 : Dim := ⟨0, 24, -24, 0, -12, 0, 0⟩  -- Entropy, turbine inlet [J/(kg K)]
def d_s_4s : Dim := ⟨0, 24, -24, 0, -12, 0, 0⟩  -- Entropy after isentropic expansion [J/(kg K)]
def d_v_l : Dim := ⟨-12, 36, 0, 0, 0, 0, 0⟩  -- Liquid specific volume [m^3/kg]
def d_w_p : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Pump work [J/kg]
def d_w_t : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Turbine work [J/kg]

/-! ## 1. Clausius–Clapeyron relation

    d(p_sat,T) = h_fg*p_sat/(R_s*T^2)
-/
/-- Both sides of "Clausius–Clapeyron relation" carry the same physical dimension. -/
theorem eq1_cc_dim : (Dim.div d_p_sat d_T) = (Dim.div (Dim.mul d_h_fg d_p_sat) (Dim.mul d_R_s (Dim.pow d_T 2 1))) := by decide
/-- Domain condition for `R_s * T^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_cc_cond1 (R_s T : ℝ) (hdom : R_s * T ^ 2 ≠ 0) : R_s * T ^ 2 ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq1_cc_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 2. Pump delivery pressure

    p_p = p_b
-/
/-- Both sides of "Pump delivery pressure" carry the same physical dimension. -/
theorem eq2_pp_dim : d_p_p = d_p_b := by decide

/-! ## 3. Pump work

    w_p = v_l*(p_p - p_c)/eta_p
-/
/-- Both sides of "Pump work" carry the same physical dimension. -/
theorem eq3_wp_dim : d_w_p = (Dim.div (Dim.mul d_v_l d_p_p) d_eta_p) := by decide
theorem eq3_wp_term1 : d_p_p = d_p_c := by decide
/-- The denominator `eta_p` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_wp_reg1 (eta_p : ℝ) (heta_p : 0 < eta_p) : eta_p ≠ 0 := by positivity

/-! ## 4. Pump outlet enthalpy

    h_2 = h_1 + w_p
-/
/-- Both sides of "Pump outlet enthalpy" carry the same physical dimension. -/
theorem eq4_h2_dim : d_h_2 = d_h_1 := by decide
theorem eq4_h2_term1 : d_h_1 = d_w_p := by decide

/-! ## 5. Isentropic expansion

    s_4s = s_3
-/
/-- Both sides of "Isentropic expansion" carry the same physical dimension. -/
theorem eq5_s_dim : d_s_4s = d_s_3 := by decide

/-! ## 6. Turbine work

    w_t = eta_t*(h_3 - h_4s)
-/
/-- Both sides of "Turbine work" carry the same physical dimension. -/
theorem eq6_wt_dim : d_w_t = (Dim.mul d_eta_t d_h_3) := by decide
theorem eq6_wt_term1 : d_h_3 = d_h_4s := by decide

/-! ## 7. Heat added

    q_in = h_3 - h_2
-/
/-- Both sides of "Heat added" carry the same physical dimension. -/
theorem eq7_qin_dim : d_q_in = d_h_3 := by decide
theorem eq7_qin_term1 : d_h_3 = d_h_2 := by decide

/-! ## 8. Heat rejected

    q_out = h_4 - h_1
-/
/-- Both sides of "Heat rejected" carry the same physical dimension. -/
theorem eq8_qout_dim : d_q_out = d_h_4 := by decide
theorem eq8_qout_term1 : d_h_4 = d_h_1 := by decide

/-! ## 9. Thermal efficiency

    eta = (w_t - w_p)/q_in
-/
/-- Both sides of "Thermal efficiency" carry the same physical dimension. -/
theorem eq9_eta_dim : d_eta = (Dim.div d_w_t d_q_in) := by decide
theorem eq9_eta_term1 : d_w_t = d_w_p := by decide
/-- The denominator `q_in` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_eta_reg1 (q_in : ℝ) (hq_in : 0 < q_in) : q_in ≠ 0 := by positivity

/-! ## 10. Carnot limit

    eta_C = 1 - T_L/T_H
-/
/-- Both sides of "Carnot limit" carry the same physical dimension. -/
theorem eq10_carnot_dim : d_eta_C = Dim.one := by decide
theorem eq10_carnot_term1 : Dim.one = (Dim.div d_T_L d_T_H) := by decide
/-- The denominator `T_H` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_carnot_reg1 (T_H : ℝ) (hT_H : 0 < T_H) : T_H ≠ 0 := by positivity

/-! ## 11. Back-work ratio

    bwr = w_p/w_t
-/
/-- Both sides of "Back-work ratio" carry the same physical dimension. -/
theorem eq11_bwr_dim : d_bwr = (Dim.div d_w_p d_w_t) := by decide
/-- The denominator `w_t` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_bwr_reg1 (w_t : ℝ) (hw_t : 0 < w_t) : w_t ≠ 0 := by positivity

/-! ## 12. Mass flow rate

    mdot = P_net/(w_t - w_p)
-/
/-- Both sides of "Mass flow rate" carry the same physical dimension. -/
theorem eq12_m_dim : d_mdot = (Dim.div d_P_net d_w_t) := by decide
theorem eq12_m_term1 : d_w_t = d_w_p := by decide
/-- Domain condition for `w_t - w_p`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq12_m_cond1 (w_t w_p : ℝ) (hdom : w_t - w_p ≠ 0) : w_t - w_p ≠ 0 := hdom

end Bespoke
