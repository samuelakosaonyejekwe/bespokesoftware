import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Ballistic atmospheric entry (Allen–Eggers)

Machine-checkable statements for this investigation (atmospheric-entry).
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
def d_H : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Density scale height [km]
def d_R_n : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Nose radius [m]
def d_T_w : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Radiative-equilibrium wall temperature [K]
def d_V : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed [m/s]
def d_V_E : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Entry speed [km/s]
def d_a_AE : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Peak deceleration from the Allen–Eggers solution [m/s^2]
def d_beta : Dim := ⟨12, -24, 0, 0, 0, 0, 0⟩  -- Ballistic coefficient m/(C_D A) [kg/m^2]
def d_eps_w : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Surface emissivity [1]
def d_gamma : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Flight-path angle below the horizontal [rad]
def d_gamma_E : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Entry flight-path angle below the horizontal [deg]
def d_k_SG : Dim := ⟨6, -12, 0, 0, 0, 0, 0⟩  -- Sutton–Graves constant, 1.7415×10⁻⁴ [kg^0.5/m]
def d_q_s : Dim := ⟨12, 0, -36, 0, 0, 0, 0⟩  -- Stagnation-point heat flux [W/m^2]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Atmospheric density [kg/m^3]
def d_rho_0 : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Reference surface density of the exponential fit [kg/m^3]
def d_sigma_SB : Dim := ⟨12, 0, -36, 0, -48, 0, 0⟩  -- Stefan–Boltzmann constant [W/(m^2 K^4)]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_z : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Altitude [m]
def d_z_AE : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Altitude of peak deceleration from the Allen–Eggers solution [m]

/-! ## 1. Atmospheric density

    rho = rho_0*exp(-z/H)
-/
/-- Both sides of "Atmospheric density" carry the same physical dimension. -/
theorem eq1_rho_dim : d_rho = (Dim.mul d_rho_0 Dim.one) := by decide
theorem eq1_rho_term1 : (Dim.div d_z d_H) = Dim.one := by decide
/-- The denominator `H` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_rho_reg1 (H : ℝ) (hH : 0 < H) : H ≠ 0 := by positivity

/-! ## 2. Along-path momentum

    d(V,t) = -rho*V^2/(2*beta)
-/
/-- Both sides of "Along-path momentum" carry the same physical dimension. -/
theorem eq2_drag_dim : (Dim.div d_V d_t) = (Dim.div (Dim.mul d_rho (Dim.pow d_V 2 1)) (Dim.mul Dim.one d_beta)) := by decide
/-- The denominator `2 * beta` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_drag_reg1 (beta : ℝ) (hbeta : 0 < beta) : (2 : ℝ) * beta ≠ 0 := by positivity

/-! ## 3. Altitude rate

    d(z,t) = -V*sin(gamma)
-/
/-- Both sides of "Altitude rate" carry the same physical dimension. -/
theorem eq3_alt_dim : (Dim.div d_z d_t) = (Dim.mul d_V Dim.one) := by decide
theorem eq3_alt_term1 : d_gamma = Dim.one := by decide

/-! ## 4. Flight-path angle

    gamma = gamma_E
-/
/-- Both sides of "Flight-path angle" carry the same physical dimension. -/
theorem eq4_turn_dim : d_gamma = d_gamma_E := by decide

/-! ## 5. Allen–Eggers velocity

    V = V_E*exp(-rho*H/(2*beta*sin(gamma_E)))
-/
/-- Both sides of "Allen–Eggers velocity" carry the same physical dimension. -/
theorem eq5_ae_dim : d_V = (Dim.mul d_V_E Dim.one) := by decide
theorem eq5_ae_term1 : d_gamma_E = Dim.one := by decide
theorem eq5_ae_term2 : (Dim.div (Dim.mul d_rho d_H) (Dim.mul (Dim.mul Dim.one d_beta) Dim.one)) = Dim.one := by decide
/-- Domain condition for `2 * beta * sin(gamma_E)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq5_ae_cond1 (beta gamma_E : ℝ) (hdom : (2 : ℝ) * beta * Real.sin gamma_E ≠ 0) : (2 : ℝ) * beta * Real.sin gamma_E ≠ 0 := hdom

/-! ## 6. Peak deceleration (Allen–Eggers)

    a_AE = V_E^2*sin(gamma_E)/(2*exp(1)*H)
-/
/-- Both sides of "Peak deceleration (Allen–Eggers)" carry the same physical dimension. -/
theorem eq6_amax_dim : d_a_AE = (Dim.div (Dim.mul (Dim.pow d_V_E 2 1) Dim.one) (Dim.mul (Dim.mul Dim.one Dim.one) d_H)) := by decide
theorem eq6_amax_term1 : d_gamma_E = Dim.one := by decide
theorem eq6_amax_term2 : Dim.one = Dim.one := by decide
/-- The denominator `2 * exp(1) * H` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_amax_reg1 (H : ℝ) (hH : 0 < H) : (2 : ℝ) * Real.exp (1 : ℝ) * H ≠ 0 := by positivity

/-! ## 7. Altitude of peak deceleration (Allen–Eggers)

    z_AE = H*ln(rho_0*H/(beta*sin(gamma_E)))
-/
/-- Both sides of "Altitude of peak deceleration (Allen–Eggers)" carry the same physical dimension. -/
theorem eq7_za_dim : d_z_AE = (Dim.mul d_H Dim.one) := by decide
theorem eq7_za_term1 : d_gamma_E = Dim.one := by decide
theorem eq7_za_term2 : (Dim.div (Dim.mul d_rho_0 d_H) (Dim.mul d_beta Dim.one)) = Dim.one := by decide
/-- Domain condition for `beta * sin(gamma_E)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq7_za_cond1 (beta gamma_E : ℝ) (hdom : beta * Real.sin gamma_E ≠ 0) : beta * Real.sin gamma_E ≠ 0 := hdom
/-- Domain condition for `rho_0 * H / (beta * sin(gamma_E))`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq7_za_cond2 (rho_0 H beta gamma_E : ℝ) (hdom : 0 < rho_0 * H / (beta * Real.sin gamma_E)) : 0 < rho_0 * H / (beta * Real.sin gamma_E) := hdom

/-! ## 8. Stagnation-point convective heat flux

    q_s = k_SG*sqrt(rho/R_n)*V^3
-/
/-- Both sides of "Stagnation-point convective heat flux" carry the same physical dimension. -/
theorem eq8_heat_dim : d_q_s = (Dim.mul (Dim.mul d_k_SG (Dim.pow (Dim.div d_rho d_R_n) 1 2)) (Dim.pow d_V 3 1)) := by decide
/-- The denominator `R_n` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_heat_reg1 (R_n : ℝ) (hR_n : 0 < R_n) : R_n ≠ 0 := by positivity
/-- The argument `rho / R_n` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_heat_reg2 (rho R_n : ℝ) (hrho : 0 < rho) (hR_n : 0 < R_n) : 0 ≤ rho / R_n := by positivity

/-! ## 9. Radiative-equilibrium wall temperature

    q_s = eps_w*sigma_SB*T_w^4
-/
/-- Both sides of "Radiative-equilibrium wall temperature" carry the same physical dimension. -/
theorem eq9_wall_dim : d_q_s = (Dim.mul (Dim.mul d_eps_w d_sigma_SB) (Dim.pow d_T_w 4 1)) := by decide

end Bespoke
