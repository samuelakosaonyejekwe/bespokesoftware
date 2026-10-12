import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Acoustic radiation pressure and standing-wave levitation

Machine-checkable statements for this investigation (acoustic-radiation-pressure).
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
def d_A_t : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Target area for the plane-wave case [cm^2]
def d_E_ac : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Energy density of the standing wave [J/m^3]
def d_E_t : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Energy density of the travelling wave [J/m^3]
def d_F_max : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Peak radiation force on the sphere [N]
def d_F_t : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Radiation force on the target [N]
def d_M_lev : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Levitation margin [1]
def d_Phi_c : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Acoustic contrast factor [1]
def d_U_g : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Gor'kov potential [J]
def d_W_p : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Net weight of the sphere [N]
def d_c_s : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of sound in the medium [m/s]
def d_d_p : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Sphere diameter [mm]
def d_f_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Monopole (compressibility) coefficient [1]
def d_f_2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Dipole (density) coefficient [1]
def d_f_a : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Frequency [kHz]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_k_w : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Wavenumber [1/m]
def d_p_a : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Acoustic pressure amplitude [Pa]
def d_p_rad : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Radiation pressure [Pa]
def d_rho_0 : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Density of the medium [kg/m^3]
def d_rho_p : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Sphere density [kg/m^3]
def d_z : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position along the standing wave, from a pressure antinode [m]

/-! ## 1. Wavenumber

    k_w = 2*pi*f_a/c_s
-/
/-- Both sides of "Wavenumber" carry the same physical dimension. -/
theorem eq1_k_dim : d_k_w = (Dim.div (Dim.mul (Dim.mul Dim.one Dim.one) d_f_a) d_c_s) := by decide
/-- The denominator `c_s` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_k_reg1 (c_s : ℝ) (hc_s : 0 < c_s) : c_s ≠ 0 := by positivity

/-! ## 2. Energy density of a travelling plane wave

    E_t = p_a^2/(2*rho_0*c_s^2)
-/
/-- Both sides of "Energy density of a travelling plane wave" carry the same physical dimension. -/
theorem eq2_et_dim : d_E_t = (Dim.div (Dim.pow d_p_a 2 1) (Dim.mul (Dim.mul Dim.one d_rho_0) (Dim.pow d_c_s 2 1))) := by decide
/-- The denominator `2 * rho_0 * c_s^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_et_reg1 (rho_0 c_s : ℝ) (hrho_0 : 0 < rho_0) (hc_s : 0 < c_s) : (2 : ℝ) * rho_0 * c_s ^ 2 ≠ 0 := by positivity

/-! ## 3. Radiation pressure on an absorber

    p_rad = E_t
-/
/-- Both sides of "Radiation pressure on an absorber" carry the same physical dimension. -/
theorem eq3_prad_dim : d_p_rad = d_E_t := by decide

/-! ## 4. Force on the target

    F_t = p_rad*A_t
-/
/-- Both sides of "Force on the target" carry the same physical dimension. -/
theorem eq4_ft_dim : d_F_t = (Dim.mul d_p_rad d_A_t) := by decide

/-! ## 5. Energy density of the standing wave

    E_ac = p_a^2/(4*rho_0*c_s^2)
-/
/-- Both sides of "Energy density of the standing wave" carry the same physical dimension. -/
theorem eq5_eac_dim : d_E_ac = (Dim.div (Dim.pow d_p_a 2 1) (Dim.mul (Dim.mul Dim.one d_rho_0) (Dim.pow d_c_s 2 1))) := by decide
/-- The denominator `4 * rho_0 * c_s^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_eac_reg1 (rho_0 c_s : ℝ) (hrho_0 : 0 < rho_0) (hc_s : 0 < c_s) : (4 : ℝ) * rho_0 * c_s ^ 2 ≠ 0 := by positivity

/-! ## 6. Monopole coefficient

    f_1 = 1
-/
/-- Both sides of "Monopole coefficient" carry the same physical dimension. -/
theorem eq6_f1_dim : d_f_1 = Dim.one := by decide

/-! ## 7. Dipole coefficient

    f_2 = 2*(rho_p - rho_0)/(2*rho_p + rho_0)
-/
/-- Both sides of "Dipole coefficient" carry the same physical dimension. -/
theorem eq7_f2_dim : d_f_2 = (Dim.div (Dim.mul Dim.one d_rho_p) (Dim.mul Dim.one d_rho_p)) := by decide
theorem eq7_f2_term1 : d_rho_p = d_rho_0 := by decide
theorem eq7_f2_term2 : (Dim.mul Dim.one d_rho_p) = d_rho_0 := by decide
/-- The denominator `2 * rho_p + rho_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_f2_reg1 (rho_p rho_0 : ℝ) (hrho_p : 0 < rho_p) (hrho_0 : 0 < rho_0) : (2 : ℝ) * rho_p + rho_0 ≠ 0 := by positivity

/-! ## 8. Acoustic contrast factor

    Phi_c = f_1/3 + f_2/2
-/
/-- Both sides of "Acoustic contrast factor" carry the same physical dimension. -/
theorem eq8_phi_dim : d_Phi_c = (Dim.div d_f_1 Dim.one) := by decide
theorem eq8_phi_term1 : (Dim.div d_f_1 Dim.one) = (Dim.div d_f_2 Dim.one) := by decide
/-- The denominator `3` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_phi_reg1  : (3 : ℝ) ≠ 0 := by positivity
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_phi_reg2  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 9. Gor'kov potential

    U_g = pi*d_p^3/6*E_ac*(f_1*cos(k_w*z)^2 - 3/2*f_2*sin(k_w*z)^2)
-/
/-- Both sides of "Gor'kov potential" carry the same physical dimension. -/
theorem eq9_gor_dim : d_U_g = (Dim.mul (Dim.mul (Dim.div (Dim.mul Dim.one (Dim.pow d_d_p 3 1)) Dim.one) d_E_ac) (Dim.mul d_f_1 (Dim.pow Dim.one 2 1))) := by decide
theorem eq9_gor_term1 : (Dim.mul d_k_w d_z) = Dim.one := by decide
theorem eq9_gor_term2 : (Dim.mul d_k_w d_z) = Dim.one := by decide
theorem eq9_gor_term3 : (Dim.mul d_f_1 (Dim.pow Dim.one 2 1)) = (Dim.mul (Dim.mul (Dim.div Dim.one Dim.one) d_f_2) (Dim.pow Dim.one 2 1)) := by decide
/-- The denominator `6` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_gor_reg1  : (6 : ℝ) ≠ 0 := by positivity
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_gor_reg2  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 10. Peak force on the sphere

    F_max = pi*d_p^3/2*k_w*E_ac*Phi_c
-/
/-- Both sides of "Peak force on the sphere" carry the same physical dimension. -/
theorem eq10_fmax_dim : d_F_max = (Dim.mul (Dim.mul (Dim.mul (Dim.div (Dim.mul Dim.one (Dim.pow d_d_p 3 1)) Dim.one) d_k_w) d_E_ac) d_Phi_c) := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_fmax_reg1  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 11. Net weight of the sphere

    W_p = pi*d_p^3/6*(rho_p - rho_0)*g
-/
/-- Both sides of "Net weight of the sphere" carry the same physical dimension. -/
theorem eq11_wp_dim : d_W_p = (Dim.mul (Dim.mul (Dim.div (Dim.mul Dim.one (Dim.pow d_d_p 3 1)) Dim.one) d_rho_p) d_g) := by decide
theorem eq11_wp_term1 : d_rho_p = d_rho_0 := by decide
/-- The denominator `6` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_wp_reg1  : (6 : ℝ) ≠ 0 := by positivity

/-! ## 12. Levitation margin

    M_lev = F_max/W_p
-/
/-- Both sides of "Levitation margin" carry the same physical dimension. -/
theorem eq12_mlev_dim : d_M_lev = (Dim.div d_F_max d_W_p) := by decide
/-- The denominator `W_p` stays away from its singular set whenever the quantities are positive. -/
theorem eq12_mlev_reg1 (W_p : ℝ) (hW_p : 0 < W_p) : W_p ≠ 0 := by positivity

end Bespoke
