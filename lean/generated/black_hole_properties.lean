import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Black-hole properties, Hawking radiation and the central singularity

Machine-checkable statements for this investigation (black-hole-properties).
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
def d_A_h : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Horizon area [m^2]
def d_G : Dim := ⟨-12, 36, -24, 0, 0, 0, 0⟩  -- Gravitational constant [m^3/(kg s^2)]
def d_K : Dim := ⟨0, -48, 0, 0, 0, 0, 0⟩  -- Kretschmann curvature scalar [1/m^4]
def d_L_b : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Length of the infalling body [m]
def d_M : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Black-hole mass [Msun]
def d_P_H : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Hawking luminosity [W]
def d_S_BH : Dim := ⟨12, 24, -24, 0, -12, 0, 0⟩  -- Bekenstein–Hawking entropy [J/K]
def d_T_H : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Hawking temperature [K]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light [m/s]
def d_da : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Tidal acceleration across the body [m/s^2]
def d_hbar : Dim := ⟨12, 24, -12, 0, 0, 0, 0⟩  -- Reduced Planck constant [J s]
def d_k_B : Dim := ⟨12, 24, -24, 0, -12, 0, 0⟩  -- Boltzmann constant [J/K]
def d_kappa : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Surface gravity [m/s^2]
def d_r : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Radial coordinate [m]
def d_r_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Schwarzschild radius [m]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_t_ev : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Evaporation time [s]

/-! ## 1. Schwarzschild radius

    r_s = 2*G*M/c^2
-/
/-- Both sides of "Schwarzschild radius" carry the same physical dimension. -/
theorem eq1_rs_dim : d_r_s = (Dim.div (Dim.mul (Dim.mul Dim.one d_G) d_M) (Dim.pow d_c 2 1)) := by decide
/-- The denominator `c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_rs_reg1 (c : ℝ) (hc : 0 < c) : c ^ 2 ≠ 0 := by positivity

/-! ## 2. Horizon area

    A_h = 4*pi*r_s^2
-/
/-- Both sides of "Horizon area" carry the same physical dimension. -/
theorem eq2_area_dim : d_A_h = (Dim.mul (Dim.mul Dim.one Dim.one) (Dim.pow d_r_s 2 1)) := by decide

/-! ## 3. Surface gravity

    kappa = c^4/(4*G*M)
-/
/-- Both sides of "Surface gravity" carry the same physical dimension. -/
theorem eq3_kap_dim : d_kappa = (Dim.div (Dim.pow d_c 4 1) (Dim.mul (Dim.mul Dim.one d_G) d_M)) := by decide
/-- The denominator `4 * G * M` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_kap_reg1 (G M : ℝ) (hG : 0 < G) (hM : 0 < M) : (4 : ℝ) * G * M ≠ 0 := by positivity

/-! ## 4. Tidal acceleration across a body

    da = 2*G*M*L_b/r^3
-/
/-- Both sides of "Tidal acceleration across a body" carry the same physical dimension. -/
theorem eq4_tide_dim : d_da = (Dim.div (Dim.mul (Dim.mul (Dim.mul Dim.one d_G) d_M) d_L_b) (Dim.pow d_r 3 1)) := by decide
/-- Domain condition for `r^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_tide_cond1 (r : ℝ) (hdom : r ^ 3 ≠ 0) : r ^ 3 ≠ 0 := hdom

/-! ## 5. Kretschmann scalar

    K = 48*G^2*M^2/(c^4*r^6)
-/
/-- Both sides of "Kretschmann scalar" carry the same physical dimension. -/
theorem eq5_K_dim : d_K = (Dim.div (Dim.mul (Dim.mul Dim.one (Dim.pow d_G 2 1)) (Dim.pow d_M 2 1)) (Dim.mul (Dim.pow d_c 4 1) (Dim.pow d_r 6 1))) := by decide
/-- Domain condition for `c^4 * r^6`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_K_cond1 (c r : ℝ) (hdom : c ^ 4 * r ^ 6 ≠ 0) : c ^ 4 * r ^ 6 ≠ 0 := hdom

/-! ## 6. Hawking temperature

    T_H = hbar*c^3/(8*pi*G*M*k_B)
-/
/-- Both sides of "Hawking temperature" carry the same physical dimension. -/
theorem eq6_TH_dim : d_T_H = (Dim.div (Dim.mul d_hbar (Dim.pow d_c 3 1)) (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_G) d_M) d_k_B)) := by decide
/-- The denominator `8 * pi * G * M * k_B` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_TH_reg1 (G M k_B : ℝ) (hG : 0 < G) (hM : 0 < M) (hk_B : 0 < k_B) : (8 : ℝ) * Real.pi * G * M * k_B ≠ 0 := by positivity

/-! ## 7. Bekenstein–Hawking entropy

    S_BH = k_B*c^3*A_h/(4*G*hbar)
-/
/-- Both sides of "Bekenstein–Hawking entropy" carry the same physical dimension. -/
theorem eq7_S_dim : d_S_BH = (Dim.div (Dim.mul (Dim.mul d_k_B (Dim.pow d_c 3 1)) d_A_h) (Dim.mul (Dim.mul Dim.one d_G) d_hbar)) := by decide
/-- The denominator `4 * G * hbar` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_S_reg1 (G hbar : ℝ) (hG : 0 < G) (hhbar : 0 < hbar) : (4 : ℝ) * G * hbar ≠ 0 := by positivity

/-! ## 8. Hawking luminosity

    P_H = hbar*c^6/(15360*pi*G^2*M^2)
-/
/-- Both sides of "Hawking luminosity" carry the same physical dimension. -/
theorem eq8_P_dim : d_P_H = (Dim.div (Dim.mul d_hbar (Dim.pow d_c 6 1)) (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) (Dim.pow d_G 2 1)) (Dim.pow d_M 2 1))) := by decide
/-- The denominator `15360 * pi * G^2 * M^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_P_reg1 (G M : ℝ) (hG : 0 < G) (hM : 0 < M) : (15360 : ℝ) * Real.pi * G ^ 2 * M ^ 2 ≠ 0 := by positivity

/-! ## 9. Mass loss

    c^2*d(M,t) = -P_H
-/
/-- Both sides of "Mass loss" carry the same physical dimension. -/
theorem eq9_ev_dim : (Dim.mul (Dim.pow d_c 2 1) (Dim.div d_M d_t)) = d_P_H := by decide

/-! ## 10. Evaporation time

    t_ev = 5120*pi*G^2*M^3/(hbar*c^4)
-/
/-- Both sides of "Evaporation time" carry the same physical dimension. -/
theorem eq10_tev_dim : d_t_ev = (Dim.div (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) (Dim.pow d_G 2 1)) (Dim.pow d_M 3 1)) (Dim.mul d_hbar (Dim.pow d_c 4 1))) := by decide
/-- The denominator `hbar * c^4` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_tev_reg1 (hbar c : ℝ) (hhbar : 0 < hbar) (hc : 0 < c) : hbar * c ^ 4 ≠ 0 := by positivity

end Bespoke
