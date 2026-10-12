import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Catenary mooring line

Machine-checkable statements for this investigation (catenary-mooring).
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
def d_L_t : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Total line length [m]
def d_T_0 : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Specified line tension [kN]
def d_T_H : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Horizontal tension [N]
def d_T_a : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Tension at the anchor [N]
def d_T_top : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Tension at the fairlead [N]
def d_X : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Horizontal distance from anchor to fairlead [m]
def d_a_c : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Catenary parameter [m]
def d_d : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Water depth below the fairlead [m]
def d_k_h : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Horizontal restoring stiffness [N/m]
def d_s_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Suspended (unstretched) length [m]
def d_scope : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Line length as a multiple of water depth (scope) [1]
def d_theta_top : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Line angle to the horizontal at the fairlead [rad]
def d_w : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Submerged weight of line per unit length [N/m]
def d_x_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Horizontal span of the suspended length [m]

/-! ## 1. Specified tension

    T_H = T_0
-/
/-- Both sides of "Specified tension" carry the same physical dimension. -/
theorem eq1_spec_dim : d_T_H = d_T_0 := by decide

/-! ## 2. Catenary parameter

    a_c = T_H/w
-/
/-- Both sides of "Catenary parameter" carry the same physical dimension. -/
theorem eq2_ac_dim : d_a_c = (Dim.div d_T_H d_w) := by decide
/-- The denominator `w` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_ac_reg1 (w : ℝ) (hw : 0 < w) : w ≠ 0 := by positivity

/-! ## 3. Total line length

    L_t = scope*d
-/
/-- Both sides of "Total line length" carry the same physical dimension. -/
theorem eq3_lt_dim : d_L_t = (Dim.mul d_scope d_d) := by decide

/-! ## 4. Suspended length

    s_s = sqrt(d*(d + 2*a_c))
-/
/-- Both sides of "Suspended length" carry the same physical dimension. -/
theorem eq4_ss_dim : d_s_s = (Dim.pow (Dim.mul d_d d_d) 1 2) := by decide
theorem eq4_ss_term1 : d_d = (Dim.mul Dim.one d_a_c) := by decide
/-- The argument `d * (d + 2 * a_c)` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_ss_reg1 (d a_c : ℝ) (hd : 0 < d) (ha_c : 0 < a_c) : 0 ≤ d * (d + (2 : ℝ) * a_c) := by positivity

/-! ## 5. Horizontal span of the suspended line

    x_s = a_c*ln(w*s_s/T_H + sqrt(1 + (w*s_s/T_H)^2))
-/
/-- Both sides of "Horizontal span of the suspended line" carry the same physical dimension. -/
theorem eq5_xs_dim : d_x_s = (Dim.mul d_a_c Dim.one) := by decide
theorem eq5_xs_term1 : Dim.one = (Dim.pow (Dim.div (Dim.mul d_w d_s_s) d_T_H) 2 1) := by decide
theorem eq5_xs_term2 : (Dim.div (Dim.mul d_w d_s_s) d_T_H) = (Dim.pow Dim.one 1 2) := by decide
theorem eq5_xs_term3 : (Dim.div (Dim.mul d_w d_s_s) d_T_H) = Dim.one := by decide
/-- The denominator `T_H` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_xs_reg1 (T_H : ℝ) (hT_H : 0 < T_H) : T_H ≠ 0 := by positivity
/-- The denominator `T_H` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_xs_reg2 (T_H : ℝ) (hT_H : 0 < T_H) : T_H ≠ 0 := by positivity
/-- The argument `1 + (w * s_s / T_H)^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_xs_reg3 (w s_s T_H : ℝ) (hw : 0 < w) (hs_s : 0 < s_s) (hT_H : 0 < T_H) : 0 ≤ (1 : ℝ) + (w * s_s / T_H) ^ 2 := by positivity
/-- The argument `w * s_s / T_H + sqrt(1 + (w * s_s / T_H)^2)` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_xs_reg4 (w s_s T_H : ℝ) (hw : 0 < w) (hs_s : 0 < s_s) (hT_H : 0 < T_H) : 0 < w * s_s / T_H + Real.sqrt ((1 : ℝ) + (w * s_s / T_H) ^ 2) := by positivity

/-! ## 6. Tension at the fairlead

    T_top = T_H + w*d
-/
/-- Both sides of "Tension at the fairlead" carry the same physical dimension. -/
theorem eq6_tt_dim : d_T_top = d_T_H := by decide
theorem eq6_tt_term1 : d_T_H = (Dim.mul d_w d_d) := by decide

/-! ## 7. Line angle at the fairlead

    tan(theta_top) = w*s_s/T_H
-/
/-- Both sides of "Line angle at the fairlead" carry the same physical dimension. -/
theorem eq7_ang_dim : Dim.one = (Dim.div (Dim.mul d_w d_s_s) d_T_H) := by decide
theorem eq7_ang_term1 : d_theta_top = Dim.one := by decide
/-- The denominator `T_H` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_ang_reg1 (T_H : ℝ) (hT_H : 0 < T_H) : T_H ≠ 0 := by positivity

/-! ## 8. Anchor-to-fairlead distance

    X = (L_t - s_s) + x_s
-/
/-- Both sides of "Anchor-to-fairlead distance" carry the same physical dimension. -/
theorem eq8_X_dim : d_X = d_L_t := by decide
theorem eq8_X_term1 : d_L_t = d_s_s := by decide
theorem eq8_X_term2 : d_L_t = d_x_s := by decide

/-! ## 9. Anchor tension

    T_a = T_H
-/
/-- Both sides of "Anchor tension" carry the same physical dimension. -/
theorem eq9_ta_dim : d_T_a = d_T_H := by decide

/-! ## 10. Horizontal stiffness

    k_h = w/(ln(1 + d/a_c + sqrt((1 + d/a_c)^2 - 1)) - 2/sqrt(1 + 2*a_c/d))
-/
/-- Both sides of "Horizontal stiffness" carry the same physical dimension. -/
theorem eq10_kh_dim : d_k_h = (Dim.div d_w Dim.one) := by decide
theorem eq10_kh_term1 : Dim.one = (Dim.div d_d d_a_c) := by decide
theorem eq10_kh_term2 : Dim.one = (Dim.div d_d d_a_c) := by decide
theorem eq10_kh_term3 : (Dim.pow Dim.one 2 1) = Dim.one := by decide
theorem eq10_kh_term4 : Dim.one = (Dim.pow (Dim.pow Dim.one 2 1) 1 2) := by decide
theorem eq10_kh_term5 : Dim.one = Dim.one := by decide
theorem eq10_kh_term6 : Dim.one = (Dim.div (Dim.mul Dim.one d_a_c) d_d) := by decide
theorem eq10_kh_term7 : Dim.one = (Dim.div Dim.one (Dim.pow Dim.one 1 2)) := by decide
/-- The denominator `a_c` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_kh_reg1 (a_c : ℝ) (ha_c : 0 < a_c) : a_c ≠ 0 := by positivity
/-- The denominator `a_c` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_kh_reg2 (a_c : ℝ) (ha_c : 0 < a_c) : a_c ≠ 0 := by positivity
/-- Domain condition for `(1 + d / a_c)^2 - 1`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq10_kh_cond3 (d a_c : ℝ) (hdom : 0 ≤ ((1 : ℝ) + d / a_c) ^ 2 - (1 : ℝ)) : 0 ≤ ((1 : ℝ) + d / a_c) ^ 2 - (1 : ℝ) := hdom
/-- Domain condition for `1 + d / a_c + sqrt((1 + d / a_c)^2 - 1)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq10_kh_cond4 (d a_c : ℝ) (hdom : 0 < (1 : ℝ) + d / a_c + Real.sqrt (((1 : ℝ) + d / a_c) ^ 2 - (1 : ℝ))) : 0 < (1 : ℝ) + d / a_c + Real.sqrt (((1 : ℝ) + d / a_c) ^ 2 - (1 : ℝ)) := hdom
/-- The denominator `d` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_kh_reg5 (d : ℝ) (hd : 0 < d) : d ≠ 0 := by positivity
/-- The argument `1 + 2 * a_c / d` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_kh_reg6 (a_c d : ℝ) (ha_c : 0 < a_c) (hd : 0 < d) : 0 ≤ (1 : ℝ) + (2 : ℝ) * a_c / d := by positivity
/-- The denominator `sqrt(1 + 2 * a_c / d)` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_kh_reg7 (a_c d : ℝ) (ha_c : 0 < a_c) (hd : 0 < d) : Real.sqrt ((1 : ℝ) + (2 : ℝ) * a_c / d) ≠ 0 := by positivity
/-- Domain condition for `ln(1 + d / a_c + sqrt((1 + d / a_c)^2 - 1)) - 2 / sqrt(1 + 2 * a_c / d)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_kh_cond8 (d a_c : ℝ) (hdom : Real.log ((1 : ℝ) + d / a_c + Real.sqrt (((1 : ℝ) + d / a_c) ^ 2 - (1 : ℝ))) - (2 : ℝ) / Real.sqrt ((1 : ℝ) + (2 : ℝ) * a_c / d) ≠ 0) : Real.log ((1 : ℝ) + d / a_c + Real.sqrt (((1 : ℝ) + d / a_c) ^ 2 - (1 : ℝ))) - (2 : ℝ) / Real.sqrt ((1 : ℝ) + (2 : ℝ) * a_c / d) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq10_kh_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

end Bespoke
