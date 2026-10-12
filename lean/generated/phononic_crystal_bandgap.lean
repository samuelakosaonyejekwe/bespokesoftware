import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Band gap of a one-dimensional phononic crystal

Machine-checkable statements for this investigation (phononic-crystal-bandgap).
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
def d_N_c : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of cells in the finite stack [1]
def d_T_g : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Power transmission inside the gap [1]
def d_Z_1 : Dim := ⟨12, -24, -12, 0, 0, 0, 0⟩  -- Acoustic impedance of layer 1 [Pa s/m]
def d_Z_2 : Dim := ⟨12, -24, -12, 0, 0, 0, 0⟩  -- Acoustic impedance of layer 2 [Pa s/m]
def d_Z_e : Dim := ⟨12, -24, -12, 0, 0, 0, 0⟩  -- Impedance of the end media [Pa s/m]
def d_a_c : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Cell length [m]
def d_alpha_B : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Bloch attenuation per cell [1]
def d_c_1 : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Longitudinal wave speed in layer 1 [m/s]
def d_c_2 : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Longitudinal wave speed in layer 2 [m/s]
def d_c_a : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Wave speed used in layer 1 [m/s]
def d_c_b : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Wave speed used in layer 2 [m/s]
def d_c_eff : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Long-wavelength effective speed [m/s]
def d_d_1 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Thickness of layer 1 [mm]
def d_d_2 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Thickness of layer 2 [mm]
def d_f : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Frequency [Hz]
def d_f_B : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Bragg frequency [Hz]
def d_k_1 : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Wavenumber in layer 1 [1/m]
def d_k_2 : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Wavenumber in layer 2 [1/m]
def d_q_B : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Bloch wavenumber [1/m]
def d_rho_1 : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Density of layer 1 [kg/m^3]
def d_rho_2 : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Density of layer 2 [kg/m^3]

/-! ## 1. Wave speed in layer 1

    c_a = c_1
-/
/-- Both sides of "Wave speed in layer 1" carry the same physical dimension. -/
theorem eq1_ca_dim : d_c_a = d_c_1 := by decide

/-! ## 2. Wave speed in layer 2

    c_b = c_2
-/
/-- Both sides of "Wave speed in layer 2" carry the same physical dimension. -/
theorem eq2_cb_dim : d_c_b = d_c_2 := by decide

/-! ## 3. Wavenumber in layer 1

    k_1 = 2*pi*f/c_a
-/
/-- Both sides of "Wavenumber in layer 1" carry the same physical dimension. -/
theorem eq3_k1_dim : d_k_1 = (Dim.div (Dim.mul (Dim.mul Dim.one Dim.one) d_f) d_c_a) := by decide
/-- Domain condition for `c_a`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_k1_cond1 (c_a : ℝ) (hdom : c_a ≠ 0) : c_a ≠ 0 := hdom

/-! ## 4. Wavenumber in layer 2

    k_2 = 2*pi*f/c_b
-/
/-- Both sides of "Wavenumber in layer 2" carry the same physical dimension. -/
theorem eq4_k2_dim : d_k_2 = (Dim.div (Dim.mul (Dim.mul Dim.one Dim.one) d_f) d_c_b) := by decide
/-- Domain condition for `c_b`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_k2_cond1 (c_b : ℝ) (hdom : c_b ≠ 0) : c_b ≠ 0 := hdom

/-! ## 5. Acoustic impedance of layer 1

    Z_1 = rho_1*c_a
-/
/-- Both sides of "Acoustic impedance of layer 1" carry the same physical dimension. -/
theorem eq5_z1_dim : d_Z_1 = (Dim.mul d_rho_1 d_c_a) := by decide

/-! ## 6. Acoustic impedance of layer 2

    Z_2 = rho_2*c_b
-/
/-- Both sides of "Acoustic impedance of layer 2" carry the same physical dimension. -/
theorem eq6_z2_dim : d_Z_2 = (Dim.mul d_rho_2 d_c_b) := by decide

/-! ## 7. Cell length

    a_c = d_1 + d_2
-/
/-- Both sides of "Cell length" carry the same physical dimension. -/
theorem eq7_ac_dim : d_a_c = d_d_1 := by decide
theorem eq7_ac_term1 : d_d_1 = d_d_2 := by decide

/-! ## 8. Bloch dispersion relation

    cos(q_B*a_c) = cos(k_1*d_1)*cos(k_2*d_2) - (Z_1/Z_2 + Z_2/Z_1)/2*sin(k_1*d_1)*sin(k_2*d_2)
-/
/-- Both sides of "Bloch dispersion relation" carry the same physical dimension. -/
theorem eq8_bloch_dim : Dim.one = (Dim.mul Dim.one Dim.one) := by decide
theorem eq8_bloch_term1 : (Dim.mul d_q_B d_a_c) = Dim.one := by decide
theorem eq8_bloch_term2 : (Dim.mul d_k_1 d_d_1) = Dim.one := by decide
theorem eq8_bloch_term3 : (Dim.mul d_k_2 d_d_2) = Dim.one := by decide
theorem eq8_bloch_term4 : (Dim.div d_Z_1 d_Z_2) = (Dim.div d_Z_2 d_Z_1) := by decide
theorem eq8_bloch_term5 : (Dim.mul d_k_1 d_d_1) = Dim.one := by decide
theorem eq8_bloch_term6 : (Dim.mul d_k_2 d_d_2) = Dim.one := by decide
theorem eq8_bloch_term7 : (Dim.mul Dim.one Dim.one) = (Dim.mul (Dim.mul (Dim.div (Dim.div d_Z_1 d_Z_2) Dim.one) Dim.one) Dim.one) := by decide
/-- The denominator `Z_2` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_bloch_reg1 (Z_2 : ℝ) (hZ_2 : 0 < Z_2) : Z_2 ≠ 0 := by positivity
/-- The denominator `Z_1` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_bloch_reg2 (Z_1 : ℝ) (hZ_1 : 0 < Z_1) : Z_1 ≠ 0 := by positivity
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_bloch_reg3  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 9. Bragg frequency

    f_B = 1/(2*(d_1/c_a + d_2/c_b))
-/
/-- Both sides of "Bragg frequency" carry the same physical dimension. -/
theorem eq9_fb_dim : d_f_B = (Dim.div Dim.one (Dim.mul Dim.one (Dim.div d_d_1 d_c_a))) := by decide
theorem eq9_fb_term1 : (Dim.div d_d_1 d_c_a) = (Dim.div d_d_2 d_c_b) := by decide
/-- Domain condition for `c_a`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq9_fb_cond1 (c_a : ℝ) (hdom : c_a ≠ 0) : c_a ≠ 0 := hdom
/-- Domain condition for `c_b`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq9_fb_cond2 (c_b : ℝ) (hdom : c_b ≠ 0) : c_b ≠ 0 := hdom
/-- Domain condition for `2 * (d_1 / c_a + d_2 / c_b)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq9_fb_cond3 (d_1 c_a d_2 c_b : ℝ) (hdom : (2 : ℝ) * (d_1 / c_a + d_2 / c_b) ≠ 0) : (2 : ℝ) * (d_1 / c_a + d_2 / c_b) ≠ 0 := hdom

/-! ## 10. Long-wavelength effective speed

    c_eff = a_c/sqrt((d_1/c_a)^2 + (d_2/c_b)^2 + (Z_1/Z_2 + Z_2/Z_1)*d_1*d_2/(c_a*c_b))
-/
/-- Both sides of "Long-wavelength effective speed" carry the same physical dimension. -/
theorem eq10_ceff_dim : d_c_eff = (Dim.div d_a_c (Dim.pow (Dim.pow (Dim.div d_d_1 d_c_a) 2 1) 1 2)) := by decide
theorem eq10_ceff_term1 : (Dim.pow (Dim.div d_d_1 d_c_a) 2 1) = (Dim.pow (Dim.div d_d_2 d_c_b) 2 1) := by decide
theorem eq10_ceff_term2 : (Dim.div d_Z_1 d_Z_2) = (Dim.div d_Z_2 d_Z_1) := by decide
theorem eq10_ceff_term3 : (Dim.pow (Dim.div d_d_1 d_c_a) 2 1) = (Dim.div (Dim.mul (Dim.mul (Dim.div d_Z_1 d_Z_2) d_d_1) d_d_2) (Dim.mul d_c_a d_c_b)) := by decide
/-- Domain condition for `c_a`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_ceff_cond1 (c_a : ℝ) (hdom : c_a ≠ 0) : c_a ≠ 0 := hdom
/-- Domain condition for `c_b`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_ceff_cond2 (c_b : ℝ) (hdom : c_b ≠ 0) : c_b ≠ 0 := hdom
/-- The denominator `Z_2` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_ceff_reg3 (Z_2 : ℝ) (hZ_2 : 0 < Z_2) : Z_2 ≠ 0 := by positivity
/-- The denominator `Z_1` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_ceff_reg4 (Z_1 : ℝ) (hZ_1 : 0 < Z_1) : Z_1 ≠ 0 := by positivity
/-- Domain condition for `c_a * c_b`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_ceff_cond5 (c_a c_b : ℝ) (hdom : c_a * c_b ≠ 0) : c_a * c_b ≠ 0 := hdom
/-- Domain condition for `(d_1 / c_a)^2 + (d_2 / c_b)^2 + (Z_1 / Z_2 + Z_2 / Z_1) * d_1 * d_2 / (c_a * c_b)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_ceff_cond6 (d_1 c_a d_2 c_b Z_1 Z_2 : ℝ) (hdom : 0 ≤ (d_1 / c_a) ^ 2 + (d_2 / c_b) ^ 2 + (Z_1 / Z_2 + Z_2 / Z_1) * d_1 * d_2 / (c_a * c_b)) : 0 ≤ (d_1 / c_a) ^ 2 + (d_2 / c_b) ^ 2 + (Z_1 / Z_2 + Z_2 / Z_1) * d_1 * d_2 / (c_a * c_b) := hdom
/-- Domain condition for `sqrt((d_1 / c_a)^2 + (d_2 / c_b)^2 + (Z_1 / Z_2 + Z_2 / Z_1) * d_1 * d_2 / (c_a * c_b))`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_ceff_cond7 (d_1 c_a d_2 c_b Z_1 Z_2 : ℝ) (hdom : Real.sqrt ((d_1 / c_a) ^ 2 + (d_2 / c_b) ^ 2 + (Z_1 / Z_2 + Z_2 / Z_1) * d_1 * d_2 / (c_a * c_b)) ≠ 0) : Real.sqrt ((d_1 / c_a) ^ 2 + (d_2 / c_b) ^ 2 + (Z_1 / Z_2 + Z_2 / Z_1) * d_1 * d_2 / (c_a * c_b)) ≠ 0 := hdom

/-! ## 11. End media

    Z_e = Z_1
-/
/-- Both sides of "End media" carry the same physical dimension. -/
theorem eq11_ze_dim : d_Z_e = d_Z_1 := by decide

/-! ## 12. Transmission of a finite stack inside the gap

    T_g = exp(-2*N_c*alpha_B)
-/
/-- Both sides of "Transmission of a finite stack inside the gap" carry the same physical dimension. -/
theorem eq12_tg_dim : d_T_g = Dim.one := by decide
theorem eq12_tg_term1 : (Dim.mul (Dim.mul Dim.one d_N_c) d_alpha_B) = Dim.one := by decide

end Bespoke
