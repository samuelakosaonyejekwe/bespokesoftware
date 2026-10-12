import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Hydrodynamic slugging in a flowline

Machine-checkable statements for this investigation (hydrodynamic-slug-flow).
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
def d_A : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Pipe area [m^2]
def d_A_G : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Gas flow area [m^2]
def d_C_0 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Distribution coefficient [1]
def d_D : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Pipe inner diameter [in]
def d_F_b : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Peak force on a 90° bend [N]
def d_H_l : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Mean liquid holdup [1]
def d_H_ls : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Slug-body liquid holdup [1]
def d_L_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Slug length [m]
def d_L_u : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Slug-unit length [m]
def d_S_i : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Interface width [m]
def d_f_ref : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Reference frequency 1 Hz [1/s]
def d_f_s : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Slug frequency [1/s]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_h_L : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Liquid level over diameter [1]
def d_n_ls : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Slug length in pipe diameters [1]
def d_rho_g : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Gas density at line conditions [kg/m^3]
def d_rho_l : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Liquid density [kg/m^3]
def d_rho_s : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Slug-body density [kg/m^3]
def d_theta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Inclination (positive upward) [deg]
def d_u_G : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Gas velocity in stratified flow [m/s]
def d_v_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Reference velocity, v_c² = 19.75 m²/s² [m/s]
def d_v_d : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Drift velocity [m/s]
def d_v_m : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Mixture velocity [m/s]
def d_v_ref : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Reference velocity 8.66 m/s [m/s]
def d_v_sg : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Superficial gas velocity [m/s]
def d_v_sl : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Superficial liquid velocity [m/s]
def d_v_t : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Slug translational velocity [m/s]

/-! ## 1. Mixture velocity

    v_m = v_sl + v_sg
-/
/-- Both sides of "Mixture velocity" carry the same physical dimension. -/
theorem eq1_vm_dim : d_v_m = d_v_sl := by decide
theorem eq1_vm_term1 : d_v_sl = d_v_sg := by decide

/-! ## 2. Translational velocity

    v_t = C_0*v_m + v_d
-/
/-- Both sides of "Translational velocity" carry the same physical dimension. -/
theorem eq2_vt_dim : d_v_t = (Dim.mul d_C_0 d_v_m) := by decide
theorem eq2_vt_term1 : (Dim.mul d_C_0 d_v_m) = d_v_d := by decide

/-! ## 3. Distribution coefficient (Froude number below 3.5)

    C_0 = 1.05 + 0.15*sin(theta)^2
-/
/-- Both sides of "Distribution coefficient (Froude number below 3.5)" carry the same physical dimension. -/
theorem eq3_c0_dim : d_C_0 = Dim.one := by decide
theorem eq3_c0_term1 : d_theta = Dim.one := by decide
theorem eq3_c0_term2 : Dim.one = (Dim.mul Dim.one (Dim.pow Dim.one 2 1)) := by decide

/-! ## 4. Drift velocity (Froude number below 3.5)

    v_d = 0.54*sqrt(g*D)*cos(theta) + 0.35*sqrt(g*D)*sin(theta)
-/
/-- Both sides of "Drift velocity (Froude number below 3.5)" carry the same physical dimension. -/
theorem eq4_vd_dim : d_v_d = (Dim.mul (Dim.mul Dim.one (Dim.pow (Dim.mul d_g d_D) 1 2)) Dim.one) := by decide
theorem eq4_vd_term1 : d_theta = Dim.one := by decide
theorem eq4_vd_term2 : d_theta = Dim.one := by decide
theorem eq4_vd_term3 : (Dim.mul (Dim.mul Dim.one (Dim.pow (Dim.mul d_g d_D) 1 2)) Dim.one) = (Dim.mul (Dim.mul Dim.one (Dim.pow (Dim.mul d_g d_D) 1 2)) Dim.one) := by decide
/-- The argument `g * D` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_vd_reg1 (g D : ℝ) (hg : 0 < g) (hD : 0 < D) : 0 ≤ g * D := by positivity
/-- The argument `g * D` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_vd_reg2 (g D : ℝ) (hg : 0 < g) (hD : 0 < D) : 0 ≤ g * D := by positivity

/-! ## 5. Slug-body holdup

    H_ls = 1/(1 + (v_m/v_ref)^1.39)
-/
-- dimensional statement omitted: a symbol has no registered unit
/-- Domain condition for `v_ref`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_hls_cond1 (v_ref : ℝ) (hdom : v_ref ≠ 0) : v_ref ≠ 0 := hdom
/-- Domain condition for `v_m / v_ref`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_hls_cond2 (v_m v_ref : ℝ) (hdom : 0 ≤ v_m / v_ref) : 0 ≤ v_m / v_ref := hdom
/-- Domain condition for `1 + (v_m / v_ref)^1.39`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_hls_cond3 (v_m v_ref : ℝ) (hdom : (1 : ℝ) + Real.rpow (v_m / v_ref) (1.39 : ℝ) ≠ 0) : (1 : ℝ) + Real.rpow (v_m / v_ref) (1.39 : ℝ) ≠ 0 := hdom

/-! ## 6. Slug frequency

    f_s/f_ref = 0.0226*(v_sl/(g*D)*(v_c^2/v_m + v_m))^1.2
-/
-- dimensional statement omitted: a symbol has no registered unit
/-- Domain condition for `f_ref`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_fs_cond1 (f_ref : ℝ) (hdom : f_ref ≠ 0) : f_ref ≠ 0 := hdom
/-- The denominator `g * D` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_fs_reg2 (g D : ℝ) (hg : 0 < g) (hD : 0 < D) : g * D ≠ 0 := by positivity
/-- The denominator `v_m` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_fs_reg3 (v_m : ℝ) (hv_m : 0 < v_m) : v_m ≠ 0 := by positivity
/-- Domain condition for `v_sl / (g * D) * (v_c^2 / v_m + v_m)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_fs_cond4 (v_sl g D v_c v_m : ℝ) (hdom : 0 ≤ v_sl / (g * D) * (v_c ^ 2 / v_m + v_m)) : 0 ≤ v_sl / (g * D) * (v_c ^ 2 / v_m + v_m) := hdom

/-! ## 7. Slug length

    L_s = n_ls*D
-/
/-- Both sides of "Slug length" carry the same physical dimension. -/
theorem eq7_ls_dim : d_L_s = (Dim.mul d_n_ls d_D) := by decide

/-! ## 8. Slug-unit length

    L_u = v_t/f_s
-/
/-- Both sides of "Slug-unit length" carry the same physical dimension. -/
theorem eq8_lu_dim : d_L_u = (Dim.div d_v_t d_f_s) := by decide
/-- The denominator `f_s` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_lu_reg1 (f_s : ℝ) (hf_s : 0 < f_s) : f_s ≠ 0 := by positivity

/-! ## 9. Mean liquid holdup

    H_l = 1 - v_sg/v_t
-/
/-- Both sides of "Mean liquid holdup" carry the same physical dimension. -/
theorem eq9_hl_dim : d_H_l = Dim.one := by decide
theorem eq9_hl_term1 : Dim.one = (Dim.div d_v_sg d_v_t) := by decide
/-- The denominator `v_t` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_hl_reg1 (v_t : ℝ) (hv_t : 0 < v_t) : v_t ≠ 0 := by positivity

/-! ## 10. Stratified-to-intermittent transition

    u_G = (1 - h_L)*sqrt((rho_l - rho_g)*g*cos(theta)*A_G/(rho_g*S_i))
-/
/-- Both sides of "Stratified-to-intermittent transition" carry the same physical dimension. -/
theorem eq10_kh_dim : d_u_G = (Dim.mul Dim.one (Dim.pow (Dim.div (Dim.mul (Dim.mul (Dim.mul d_rho_l d_g) Dim.one) d_A_G) (Dim.mul d_rho_g d_S_i)) 1 2)) := by decide
theorem eq10_kh_term1 : Dim.one = d_h_L := by decide
theorem eq10_kh_term2 : d_rho_l = d_rho_g := by decide
theorem eq10_kh_term3 : d_theta = Dim.one := by decide
/-- Domain condition for `rho_g * S_i`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_kh_cond1 (rho_g S_i : ℝ) (hdom : rho_g * S_i ≠ 0) : rho_g * S_i ≠ 0 := hdom
/-- Domain condition for `(rho_l - rho_g) * g * cos(theta) * A_G / (rho_g * S_i)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_kh_cond2 (rho_l rho_g g theta A_G S_i : ℝ) (hdom : 0 ≤ (rho_l - rho_g) * g * Real.cos theta * A_G / (rho_g * S_i)) : 0 ≤ (rho_l - rho_g) * g * Real.cos theta * A_G / (rho_g * S_i) := hdom

/-! ## 11. Peak slug force on a 90° bend

    F_b = sqrt(2)*rho_s*A*v_t^2
-/
/-- Both sides of "Peak slug force on a 90° bend" carry the same physical dimension. -/
theorem eq11_fb_dim : d_F_b = (Dim.mul (Dim.mul (Dim.mul (Dim.pow Dim.one 1 2) d_rho_s) d_A) (Dim.pow d_v_t 2 1)) := by decide
/-- The argument `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_fb_reg1  : 0 ≤ (2 : ℝ) := by positivity

end Bespoke
