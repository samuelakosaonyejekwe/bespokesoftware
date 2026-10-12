import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Brine outfall: inclined dense jet and far-field plume

Machine-checkable statements for this investigation (brine-discharge-plume).
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
def d_D_x : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Longitudinal dispersion coefficient [m^2/s]
def d_F : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Densimetric Froude number [1]
def d_K_y : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Lateral turbulent diffusivity at the source scale [m^2/s]
def d_M : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Laterally integrated salinity excess [m]
def d_Q_b : Dim := ⟨0, 36, -12, 0, 0, 0, 0⟩  -- Total brine flow [m^3/s]
def d_S_i : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Impact-point dilution [1]
def d_S_n : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Near-field dilution [1]
def d_U_a : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Ambient current speed [m/s]
def d_b : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Initial plume width [m]
def d_d : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Port diameter [m]
def d_dS : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Centre-line salinity excess [1]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_g_r : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Reduced gravity [m/s^2]
def d_n_p : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of ports [1]
def d_rho_a : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Ambient density [kg/m^3]
def d_rho_b : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Brine density [kg/m^3]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_u_j : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Jet exit velocity [m/s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance down-current [m]
def d_x_i : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Impact-point distance [m]
def d_x_n : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Return-point (end of near field) distance [m]
def d_y_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Thickness of the bottom layer [m]
def d_y_t : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Terminal rise height [m]

/-! ## 1. Reduced gravity

    g_r = g*(rho_b - rho_a)/rho_a
-/
/-- Both sides of "Reduced gravity" carry the same physical dimension. -/
theorem eq1_gr_dim : d_g_r = (Dim.div (Dim.mul d_g d_rho_b) d_rho_a) := by decide
theorem eq1_gr_term1 : d_rho_b = d_rho_a := by decide
/-- The denominator `rho_a` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_gr_reg1 (rho_a : ℝ) (hrho_a : 0 < rho_a) : rho_a ≠ 0 := by positivity

/-! ## 2. Jet exit velocity

    u_j = Q_b/(n_p*pi*d^2/4)
-/
/-- Both sides of "Jet exit velocity" carry the same physical dimension. -/
theorem eq2_uj_dim : d_u_j = (Dim.div d_Q_b (Dim.div (Dim.mul (Dim.mul d_n_p Dim.one) (Dim.pow d_d 2 1)) Dim.one)) := by decide
/-- The denominator `4` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_uj_reg1  : (4 : ℝ) ≠ 0 := by positivity
/-- The denominator `n_p * pi * d^2 / 4` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_uj_reg2 (n_p d : ℝ) (hn_p : 0 < n_p) (hd : 0 < d) : n_p * Real.pi * d ^ 2 / (4 : ℝ) ≠ 0 := by positivity

/-! ## 3. Densimetric Froude number

    F = u_j/sqrt(g_r*d)
-/
/-- Both sides of "Densimetric Froude number" carry the same physical dimension. -/
theorem eq3_fr_dim : d_F = (Dim.div d_u_j (Dim.pow (Dim.mul d_g_r d_d) 1 2)) := by decide
/-- The argument `g_r * d` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_fr_reg1 (g_r d : ℝ) (hg_r : 0 < g_r) (hd : 0 < d) : 0 ≤ g_r * d := by positivity
/-- The denominator `sqrt(g_r * d)` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_fr_reg2 (g_r d : ℝ) (hg_r : 0 < g_r) (hd : 0 < d) : Real.sqrt (g_r * d) ≠ 0 := by positivity

/-! ## 4. Terminal rise height

    y_t = 2.2*d*F
-/
/-- Both sides of "Terminal rise height" carry the same physical dimension. -/
theorem eq4_yt_dim : d_y_t = (Dim.mul (Dim.mul Dim.one d_d) d_F) := by decide

/-! ## 5. Impact-point distance

    x_i = 2.4*d*F
-/
/-- Both sides of "Impact-point distance" carry the same physical dimension. -/
theorem eq5_xi_dim : d_x_i = (Dim.mul (Dim.mul Dim.one d_d) d_F) := by decide

/-! ## 6. Impact-point dilution

    S_i = 1.6*F
-/
/-- Both sides of "Impact-point dilution" carry the same physical dimension. -/
theorem eq6_si_dim : d_S_i = (Dim.mul Dim.one d_F) := by decide

/-! ## 7. Return-point distance

    x_n = 9*d*F
-/
/-- Both sides of "Return-point distance" carry the same physical dimension. -/
theorem eq7_xn_dim : d_x_n = (Dim.mul (Dim.mul Dim.one d_d) d_F) := by decide

/-! ## 8. Near-field dilution

    S_n = 2.6*F
-/
/-- Both sides of "Near-field dilution" carry the same physical dimension. -/
theorem eq8_sn_dim : d_S_n = (Dim.mul Dim.one d_F) := by decide

/-! ## 9. Bottom-layer thickness

    y_L = 0.7*d*F
-/
/-- Both sides of "Bottom-layer thickness" carry the same physical dimension. -/
theorem eq9_yl_dim : d_y_L = (Dim.mul (Dim.mul Dim.one d_d) d_F) := by decide

/-! ## 10. Far-field transport of the laterally integrated excess

    pd(M,t) + U_a*pd(M,x) = D_x*pd2(M,x)
-/
/-- Both sides of "Far-field transport of the laterally integrated excess" carry the same physical dimension. -/
theorem eq10_ade_dim : (Dim.div d_M d_t) = (Dim.mul d_D_x (Dim.div d_M (Dim.pow d_x 2 1))) := by decide
theorem eq10_ade_term1 : (Dim.div d_M d_t) = (Dim.mul d_U_a (Dim.div d_M d_x)) := by decide

/-! ## 11. Centre-line excess with lateral diffusion

    dS = M/b*erf(b/(4*sqrt(K_y*x/U_a)))
-/
/-- Both sides of "Centre-line excess with lateral diffusion" carry the same physical dimension. -/
theorem eq11_lat_dim : d_dS = (Dim.mul (Dim.div d_M d_b) Dim.one) := by decide
theorem eq11_lat_term1 : (Dim.div d_b (Dim.mul Dim.one (Dim.pow (Dim.div (Dim.mul d_K_y d_x) d_U_a) 1 2))) = Dim.one := by decide
/-- The denominator `b` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_lat_reg1 (b : ℝ) (hb : 0 < b) : b ≠ 0 := by positivity
/-- The denominator `U_a` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_lat_reg2 (U_a : ℝ) (hU_a : 0 < U_a) : U_a ≠ 0 := by positivity
/-- Domain condition for `K_y * x / U_a`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq11_lat_cond3 (K_y x U_a : ℝ) (hdom : 0 ≤ K_y * x / U_a) : 0 ≤ K_y * x / U_a := hdom
/-- Domain condition for `4 * sqrt(K_y * x / U_a)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq11_lat_cond4 (K_y x U_a : ℝ) (hdom : (4 : ℝ) * Real.sqrt (K_y * x / U_a) ≠ 0) : (4 : ℝ) * Real.sqrt (K_y * x / U_a) ≠ 0 := hdom

end Bespoke
