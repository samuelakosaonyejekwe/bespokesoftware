import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Expansion history of a Friedmann universe

Machine-checkable statements for this investigation (frw-cosmology).
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
def d_D_A : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Angular-diameter distance [m]
def d_D_C : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Comoving distance [m]
def d_D_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Luminosity distance [m]
def d_D_M : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Transverse comoving distance [m]
def d_G : Dim := ⟨-12, 36, -24, 0, 0, 0, 0⟩  -- Gravitational constant [m^3/(kg s^2)]
def d_H : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Hubble rate [1/s]
def d_H_0 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Hubble constant [km/s/Mpc]
def d_Omega_L : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Dark-energy density parameter (used when the universe is not assumed flat) [1]
def d_Omega_m : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Matter density parameter [1]
def d_Omega_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Radiation density parameter (photons and relativistic neutrinos) [1]
def d_a_s : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Scale factor (1 today) [1]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light [m/s]
def d_q_0 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Deceleration parameter [1]
def d_rho_c : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Critical density [kg/m^3]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Cosmic time [s]
def d_t_0 : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Age of the universe [s]
def d_z : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Redshift of interest [1]

/-! ## 1. Friedmann equation

    (d(a_s,t)/a_s)^2 = H_0^2*(Omega_r/a_s^4 + Omega_m/a_s^3 + Omega_L)
-/
/-- Both sides of "Friedmann equation" carry the same physical dimension. -/
theorem eq1_fried_dim : (Dim.pow (Dim.div (Dim.div d_a_s d_t) d_a_s) 2 1) = (Dim.mul (Dim.pow d_H_0 2 1) (Dim.div d_Omega_r (Dim.pow d_a_s 4 1))) := by decide
theorem eq1_fried_term1 : (Dim.div d_Omega_r (Dim.pow d_a_s 4 1)) = (Dim.div d_Omega_m (Dim.pow d_a_s 3 1)) := by decide
theorem eq1_fried_term2 : (Dim.div d_Omega_r (Dim.pow d_a_s 4 1)) = d_Omega_L := by decide
/-- Domain condition for `a_s`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_fried_cond1 (a_s : ℝ) (hdom : a_s ≠ 0) : a_s ≠ 0 := hdom
/-- Domain condition for `a_s^4`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_fried_cond2 (a_s : ℝ) (hdom : a_s ^ 4 ≠ 0) : a_s ^ 4 ≠ 0 := hdom
/-- Domain condition for `a_s^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_fried_cond3 (a_s : ℝ) (hdom : a_s ^ 3 ≠ 0) : a_s ^ 3 ≠ 0 := hdom

/-! ## 2. Hubble rate

    H = d(a_s,t)/a_s
-/
/-- Both sides of "Hubble rate" carry the same physical dimension. -/
theorem eq2_hub_dim : d_H = (Dim.div (Dim.div d_a_s d_t) d_a_s) := by decide
/-- Domain condition for `a_s`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_hub_cond1 (a_s : ℝ) (hdom : a_s ≠ 0) : a_s ≠ 0 := hdom

/-! ## 3. Flatness

    Omega_L = 1 - Omega_m - Omega_r
-/
/-- Both sides of "Flatness" carry the same physical dimension. -/
theorem eq3_close_dim : d_Omega_L = Dim.one := by decide
theorem eq3_close_term1 : Dim.one = d_Omega_m := by decide
theorem eq3_close_term2 : Dim.one = d_Omega_r := by decide

/-! ## 4. Redshift

    1 + z = 1/a_s
-/
/-- Both sides of "Redshift" carry the same physical dimension. -/
theorem eq4_z_dim : Dim.one = (Dim.div Dim.one d_a_s) := by decide
theorem eq4_z_term1 : Dim.one = d_z := by decide
/-- Domain condition for `a_s`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_z_cond1 (a_s : ℝ) (hdom : a_s ≠ 0) : a_s ≠ 0 := hdom

/-! ## 5. Age of the universe

    t_0 = int(1/(a_s*H), a_s)
-/
/-- Both sides of "Age of the universe" carry the same physical dimension. -/
theorem eq5_age_dim : d_t_0 = (Dim.mul (Dim.div Dim.one (Dim.mul d_a_s d_H)) d_a_s) := by decide
/-- Domain condition for `a_s * H`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_age_cond1 (a_s H : ℝ) (hdom : a_s * H ≠ 0) : a_s * H ≠ 0 := hdom

/-! ## 6. Comoving distance

    D_C = c*int(1/H, z)
-/
/-- Both sides of "Comoving distance" carry the same physical dimension. -/
theorem eq6_dc_dim : d_D_C = (Dim.mul d_c (Dim.mul (Dim.div Dim.one d_H) d_z)) := by decide
/-- Domain condition for `H`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_dc_cond1 (H : ℝ) (hdom : H ≠ 0) : H ≠ 0 := hdom

/-! ## 7. Luminosity distance

    D_L = (1 + z)*D_M
-/
/-- Both sides of "Luminosity distance" carry the same physical dimension. -/
theorem eq7_dl_dim : d_D_L = (Dim.mul Dim.one d_D_M) := by decide
theorem eq7_dl_term1 : Dim.one = d_z := by decide

/-! ## 8. Angular-diameter distance

    D_A = D_M/(1 + z)
-/
/-- Both sides of "Angular-diameter distance" carry the same physical dimension. -/
theorem eq8_da_dim : d_D_A = (Dim.div d_D_M Dim.one) := by decide
theorem eq8_da_term1 : Dim.one = d_z := by decide
/-- The denominator `1 + z` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_da_reg1 (z : ℝ) (hz : 0 < z) : (1 : ℝ) + z ≠ 0 := by positivity

/-! ## 9. Deceleration parameter today

    q_0 = Omega_r + Omega_m/2 + -Omega_L
-/
/-- Both sides of "Deceleration parameter today" carry the same physical dimension. -/
theorem eq9_q_dim : d_q_0 = d_Omega_r := by decide
theorem eq9_q_term1 : d_Omega_r = (Dim.div d_Omega_m Dim.one) := by decide
theorem eq9_q_term2 : d_Omega_r = d_Omega_L := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_q_reg1  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 10. Critical density

    rho_c = 3*H_0^2/(8*pi*G)
-/
/-- Both sides of "Critical density" carry the same physical dimension. -/
theorem eq10_rhoc_dim : d_rho_c = (Dim.div (Dim.mul Dim.one (Dim.pow d_H_0 2 1)) (Dim.mul (Dim.mul Dim.one Dim.one) d_G)) := by decide
/-- The denominator `8 * pi * G` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_rhoc_reg1 (G : ℝ) (hG : 0 < G) : (8 : ℝ) * Real.pi * G ≠ 0 := by positivity

end Bespoke
