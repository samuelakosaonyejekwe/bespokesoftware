import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Skin depth, plane-wave attenuation and shielding effectiveness

Machine-checkable statements for this investigation (skin-depth-plane-wave).
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
def d_A_dB : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Absorption loss [1]
def d_B_dB : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Re-reflection correction [1]
def d_E_0 : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Incident field amplitude [V/m]
def d_E_t : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Transmitted field amplitude [V/m]
def d_E_y : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Electric field of the wave [V/m]
def d_R_dB : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Reflection loss [1]
def d_R_s : Dim := ⟨12, 24, -36, -24, 0, 0, 0⟩  -- Surface resistance [ohm]
def d_SE : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Shielding effectiveness [1]
def d_Z_w : Dim := ⟨12, 24, -36, -24, 0, 0, 0⟩  -- Wave impedance of the incident field [ohm]
def d_alpha : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Attenuation constant [1/m]
def d_delta_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Skin depth [m]
def d_eps_0 : Dim := ⟨-12, -36, 48, 24, 0, 0, 0⟩  -- Vacuum permittivity [F/m]
def d_eta_m : Dim := ⟨12, 24, -36, -24, 0, 0, 0⟩  -- Magnitude of the intrinsic impedance [ohm]
def d_f_d : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Frequency [MHz]
def d_mu_0 : Dim := ⟨12, 12, -24, -24, 0, 0, 0⟩  -- Vacuum permeability [H/m]
def d_mu_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Relative permeability [1]
def d_omega : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Angular frequency [1/s]
def d_sigma_e : Dim := ⟨-12, -36, 36, 24, 0, 0, 0⟩  -- Conductivity of the medium [S/m]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_t_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Sheet thickness [mm]
def d_z : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Depth into the medium [m]

/-! ## 1. Angular frequency

    omega = 2*pi*f_d
-/
/-- Both sides of "Angular frequency" carry the same physical dimension. -/
theorem eq1_w_dim : d_omega = (Dim.mul (Dim.mul Dim.one Dim.one) d_f_d) := by decide

/-! ## 2. Field equation in the medium

    pd2(E_y,z) = mu_0*mu_r*sigma_e*pd(E_y,t)
-/
/-- Both sides of "Field equation in the medium" carry the same physical dimension. -/
theorem eq2_wave_dim : (Dim.div d_E_y (Dim.pow d_z 2 1)) = (Dim.mul (Dim.mul (Dim.mul d_mu_0 d_mu_r) d_sigma_e) (Dim.div d_E_y d_t)) := by decide

/-! ## 3. Skin depth

    delta_s = sqrt(2/(omega*mu_0*mu_r*sigma_e))
-/
/-- Both sides of "Skin depth" carry the same physical dimension. -/
theorem eq3_delta_dim : d_delta_s = (Dim.pow (Dim.div Dim.one (Dim.mul (Dim.mul (Dim.mul d_omega d_mu_0) d_mu_r) d_sigma_e)) 1 2) := by decide
/-- Domain condition for `omega * mu_0 * mu_r * sigma_e`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_delta_cond1 (omega mu_0 mu_r sigma_e : ℝ) (hdom : omega * mu_0 * mu_r * sigma_e ≠ 0) : omega * mu_0 * mu_r * sigma_e ≠ 0 := hdom
/-- Domain condition for `2 / (omega * mu_0 * mu_r * sigma_e)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_delta_cond2 (omega mu_0 mu_r sigma_e : ℝ) (hdom : 0 ≤ (2 : ℝ) / (omega * mu_0 * mu_r * sigma_e)) : 0 ≤ (2 : ℝ) / (omega * mu_0 * mu_r * sigma_e) := hdom

/-! ## 4. Attenuation constant

    alpha = 1/delta_s
-/
/-- Both sides of "Attenuation constant" carry the same physical dimension. -/
theorem eq4_alpha_dim : d_alpha = (Dim.div Dim.one d_delta_s) := by decide
/-- The denominator `delta_s` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_alpha_reg1 (delta_s : ℝ) (hdelta_s : 0 < delta_s) : delta_s ≠ 0 := by positivity

/-! ## 5. Intrinsic impedance magnitude

    eta_m = sqrt(omega*mu_0*mu_r/sigma_e)
-/
/-- Both sides of "Intrinsic impedance magnitude" carry the same physical dimension. -/
theorem eq5_eta_dim : d_eta_m = (Dim.pow (Dim.div (Dim.mul (Dim.mul d_omega d_mu_0) d_mu_r) d_sigma_e) 1 2) := by decide
/-- The denominator `sigma_e` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_eta_reg1 (sigma_e : ℝ) (hsigma_e : 0 < sigma_e) : sigma_e ≠ 0 := by positivity
/-- Domain condition for `omega * mu_0 * mu_r / sigma_e`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_eta_cond2 (omega mu_0 mu_r sigma_e : ℝ) (hdom : 0 ≤ omega * mu_0 * mu_r / sigma_e) : 0 ≤ omega * mu_0 * mu_r / sigma_e := hdom

/-! ## 6. Surface resistance

    R_s = 1/(sigma_e*delta_s)
-/
/-- Both sides of "Surface resistance" carry the same physical dimension. -/
theorem eq6_rs_dim : d_R_s = (Dim.div Dim.one (Dim.mul d_sigma_e d_delta_s)) := by decide
/-- The denominator `sigma_e * delta_s` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_rs_reg1 (sigma_e delta_s : ℝ) (hsigma_e : 0 < sigma_e) (hdelta_s : 0 < delta_s) : sigma_e * delta_s ≠ 0 := by positivity

/-! ## 7. Wave impedance of a plane wave

    Z_w = sqrt(mu_0/eps_0)
-/
/-- Both sides of "Wave impedance of a plane wave" carry the same physical dimension. -/
theorem eq7_zw_dim : d_Z_w = (Dim.pow (Dim.div d_mu_0 d_eps_0) 1 2) := by decide
/-- The denominator `eps_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_zw_reg1 (eps_0 : ℝ) (heps_0 : 0 < eps_0) : eps_0 ≠ 0 := by positivity
/-- The argument `mu_0 / eps_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_zw_reg2 (mu_0 eps_0 : ℝ) (hmu_0 : 0 < mu_0) (heps_0 : 0 < eps_0) : 0 ≤ mu_0 / eps_0 := by positivity

/-! ## 8. Absorption loss

    A_dB = 8.686*t_s*alpha
-/
/-- Both sides of "Absorption loss" carry the same physical dimension. -/
theorem eq8_adb_dim : d_A_dB = (Dim.mul (Dim.mul Dim.one d_t_s) d_alpha) := by decide

/-! ## 9. Reflection loss

    R_dB = 20*log10((Z_w^2 + 2*Z_w*R_s + eta_m^2)/(4*Z_w*eta_m))
-/
/-- Both sides of "Reflection loss" carry the same physical dimension. -/
theorem eq9_rdb_dim : d_R_dB = (Dim.mul Dim.one Dim.one) := by decide
theorem eq9_rdb_term1 : (Dim.pow d_Z_w 2 1) = (Dim.mul (Dim.mul Dim.one d_Z_w) d_R_s) := by decide
theorem eq9_rdb_term2 : (Dim.pow d_Z_w 2 1) = (Dim.pow d_eta_m 2 1) := by decide
theorem eq9_rdb_term3 : (Dim.div (Dim.pow d_Z_w 2 1) (Dim.mul (Dim.mul Dim.one d_Z_w) d_eta_m)) = Dim.one := by decide
/-- The denominator `4 * Z_w * eta_m` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_rdb_reg1 (Z_w eta_m : ℝ) (hZ_w : 0 < Z_w) (heta_m : 0 < eta_m) : (4 : ℝ) * Z_w * eta_m ≠ 0 := by positivity
/-- The argument `(Z_w^2 + 2 * Z_w * R_s + eta_m^2) / (4 * Z_w * eta_m)` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_rdb_reg2 (Z_w R_s eta_m : ℝ) (hZ_w : 0 < Z_w) (hR_s : 0 < R_s) (heta_m : 0 < eta_m) : 0 < (Z_w ^ 2 + (2 : ℝ) * Z_w * R_s + eta_m ^ 2) / ((4 : ℝ) * Z_w * eta_m) := by positivity

/-! ## 10. Re-reflection correction

    B_dB = 20*log10(abs(1 - ((Z_w - eta_m)/(Z_w + eta_m))^2*exp(-2*t_s*alpha)))
-/
/-- Both sides of "Re-reflection correction" carry the same physical dimension. -/
theorem eq10_bdb_dim : d_B_dB = (Dim.mul Dim.one Dim.one) := by decide
theorem eq10_bdb_term1 : d_Z_w = d_eta_m := by decide
theorem eq10_bdb_term2 : d_Z_w = d_eta_m := by decide
theorem eq10_bdb_term3 : (Dim.mul (Dim.mul Dim.one d_t_s) d_alpha) = Dim.one := by decide
theorem eq10_bdb_term4 : Dim.one = (Dim.mul (Dim.pow (Dim.div d_Z_w d_Z_w) 2 1) Dim.one) := by decide
theorem eq10_bdb_term5 : Dim.one = Dim.one := by decide
/-- The denominator `Z_w + eta_m` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_bdb_reg1 (Z_w eta_m : ℝ) (hZ_w : 0 < Z_w) (heta_m : 0 < eta_m) : Z_w + eta_m ≠ 0 := by positivity
/-- Domain condition for `abs(1 - ((Z_w - eta_m) / (Z_w + eta_m))^2 * exp(-2 * t_s * alpha))`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_bdb_cond2 (Z_w eta_m t_s alpha : ℝ) (hdom : 0 < abs ((1 : ℝ) - ((Z_w - eta_m) / (Z_w + eta_m)) ^ 2 * Real.exp (-(2 : ℝ) * t_s * alpha))) : 0 < abs ((1 : ℝ) - ((Z_w - eta_m) / (Z_w + eta_m)) ^ 2 * Real.exp (-(2 : ℝ) * t_s * alpha)) := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq10_bdb_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 11. Shielding effectiveness

    SE = A_dB + R_dB + B_dB
-/
/-- Both sides of "Shielding effectiveness" carry the same physical dimension. -/
theorem eq11_se_dim : d_SE = d_A_dB := by decide
theorem eq11_se_term1 : d_A_dB = d_R_dB := by decide
theorem eq11_se_term2 : d_A_dB = d_B_dB := by decide

/-! ## 12. Transmitted field

    E_t = E_0*10^(-SE/20)
-/
/-- Both sides of "Transmitted field" carry the same physical dimension. -/
theorem eq12_et_dim : d_E_t = (Dim.mul d_E_0 Dim.one) := by decide
/-- The denominator `20` stays away from its singular set whenever the quantities are positive. -/
theorem eq12_et_reg1  : (20 : ℝ) ≠ 0 := by positivity

end Bespoke
