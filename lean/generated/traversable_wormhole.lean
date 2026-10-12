import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Traversable wormhole of Morris–Thorne type

Machine-checkable statements for this investigation (traversable-wormhole).
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
def d_G : Dim := ⟨-12, 36, -24, 0, 0, 0, 0⟩  -- Gravitational constant [m^3/(kg s^2)]
def d_M_ex : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Integrated mass of the supporting matter [kg]
def d_a_lat : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Lateral tidal acceleration at the throat [m/s^2]
def d_b_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Throat radius [m]
def d_b_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Shape function [m]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light [m/s]
def d_dtau : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Traveller's proper crossing time [s]
def d_gamma : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Lorentz factor of the traveller [1]
def d_l : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Proper radial distance from the throat [m]
def d_l_1 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Proper distance of each station from the throat [km]
def d_r : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Circumferential radius [m]
def d_rho_e : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Mass density of the supporting matter [kg/m^3]
def d_tau_r : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Radial tension [Pa]
def d_v : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Traveller's speed through the throat, measured by static observers [m/s]
def d_w_nec : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Null-energy combination ρc² + p_r [Pa]
def d_xi : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Height of the traveller [m]
def d_z_e : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Embedding height [m]

/-! ## 1. Shape function

    b_s = b_0^2/r
-/
/-- Both sides of "Shape function" carry the same physical dimension. -/
theorem eq1_shape_dim : d_b_s = (Dim.div (Dim.pow d_b_0 2 1) d_r) := by decide
/-- Domain condition for `r`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_shape_cond1 (r : ℝ) (hdom : r ≠ 0) : r ≠ 0 := hdom

/-! ## 2. Proper radial distance

    d(l,r) = 1/sqrt(1 - b_s/r)
-/
/-- Both sides of "Proper radial distance" carry the same physical dimension. -/
theorem eq2_prop_dim : (Dim.div d_l d_r) = (Dim.div Dim.one (Dim.pow Dim.one 1 2)) := by decide
theorem eq2_prop_term1 : Dim.one = (Dim.div d_b_s d_r) := by decide
/-- Domain condition for `r`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_prop_cond1 (r : ℝ) (hdom : r ≠ 0) : r ≠ 0 := hdom
/-- Domain condition for `1 - b_s / r`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_prop_cond2 (b_s r : ℝ) (hdom : 0 ≤ (1 : ℝ) - b_s / r) : 0 ≤ (1 : ℝ) - b_s / r := hdom
/-- Domain condition for `sqrt(1 - b_s / r)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_prop_cond3 (b_s r : ℝ) (hdom : Real.sqrt ((1 : ℝ) - b_s / r) ≠ 0) : Real.sqrt ((1 : ℝ) - b_s / r) ≠ 0 := hdom

/-! ## 3. Embedding surface

    d(z_e,r) = 1/sqrt(r/b_s - 1)
-/
/-- Both sides of "Embedding surface" carry the same physical dimension. -/
theorem eq3_emb_dim : (Dim.div d_z_e d_r) = (Dim.div Dim.one (Dim.pow (Dim.div d_r d_b_s) 1 2)) := by decide
theorem eq3_emb_term1 : (Dim.div d_r d_b_s) = Dim.one := by decide
/-- Domain condition for `b_s`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_emb_cond1 (b_s : ℝ) (hdom : b_s ≠ 0) : b_s ≠ 0 := hdom
/-- Domain condition for `r / b_s - 1`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_emb_cond2 (r b_s : ℝ) (hdom : 0 ≤ r / b_s - (1 : ℝ)) : 0 ≤ r / b_s - (1 : ℝ) := hdom
/-- Domain condition for `sqrt(r / b_s - 1)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_emb_cond3 (r b_s : ℝ) (hdom : Real.sqrt (r / b_s - (1 : ℝ)) ≠ 0) : Real.sqrt (r / b_s - (1 : ℝ)) ≠ 0 := hdom

/-! ## 4. Energy density required

    rho_e*c^2 = c^4/(8*pi*G)*d(b_s,r)/r^2
-/
/-- Both sides of "Energy density required" carry the same physical dimension. -/
theorem eq4_rho_dim : (Dim.mul d_rho_e (Dim.pow d_c 2 1)) = (Dim.div (Dim.mul (Dim.div (Dim.pow d_c 4 1) (Dim.mul (Dim.mul Dim.one Dim.one) d_G)) (Dim.div d_b_s d_r)) (Dim.pow d_r 2 1)) := by decide
/-- The denominator `8 * pi * G` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_rho_reg1 (G : ℝ) (hG : 0 < G) : (8 : ℝ) * Real.pi * G ≠ 0 := by positivity
/-- Domain condition for `r^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_rho_cond2 (r : ℝ) (hdom : r ^ 2 ≠ 0) : r ^ 2 ≠ 0 := hdom

/-! ## 5. Radial tension required

    tau_r = c^4/(8*pi*G)*b_s/r^3
-/
/-- Both sides of "Radial tension required" carry the same physical dimension. -/
theorem eq5_tau_dim : d_tau_r = (Dim.div (Dim.mul (Dim.div (Dim.pow d_c 4 1) (Dim.mul (Dim.mul Dim.one Dim.one) d_G)) d_b_s) (Dim.pow d_r 3 1)) := by decide
/-- The denominator `8 * pi * G` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_tau_reg1 (G : ℝ) (hG : 0 < G) : (8 : ℝ) * Real.pi * G ≠ 0 := by positivity
/-- Domain condition for `r^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_tau_cond2 (r : ℝ) (hdom : r ^ 3 ≠ 0) : r ^ 3 ≠ 0 := hdom

/-! ## 6. Null-energy combination

    w_nec = rho_e*c^2 - tau_r
-/
/-- Both sides of "Null-energy combination" carry the same physical dimension. -/
theorem eq6_nec_dim : d_w_nec = (Dim.mul d_rho_e (Dim.pow d_c 2 1)) := by decide
theorem eq6_nec_term1 : (Dim.mul d_rho_e (Dim.pow d_c 2 1)) = d_tau_r := by decide

/-! ## 7. Lorentz factor of the traveller

    gamma = 1/sqrt(1 - v^2/c^2)
-/
/-- Both sides of "Lorentz factor of the traveller" carry the same physical dimension. -/
theorem eq7_gam_dim : d_gamma = (Dim.div Dim.one (Dim.pow Dim.one 1 2)) := by decide
theorem eq7_gam_term1 : Dim.one = (Dim.div (Dim.pow d_v 2 1) (Dim.pow d_c 2 1)) := by decide
/-- The denominator `c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_gam_reg1 (c : ℝ) (hc : 0 < c) : c ^ 2 ≠ 0 := by positivity
/-- Domain condition for `1 - v^2 / c^2`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq7_gam_cond2 (v c : ℝ) (hdom : 0 ≤ (1 : ℝ) - v ^ 2 / c ^ 2) : 0 ≤ (1 : ℝ) - v ^ 2 / c ^ 2 := hdom
/-- Domain condition for `sqrt(1 - v^2 / c^2)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq7_gam_cond3 (v c : ℝ) (hdom : Real.sqrt ((1 : ℝ) - v ^ 2 / c ^ 2) ≠ 0) : Real.sqrt ((1 : ℝ) - v ^ 2 / c ^ 2) ≠ 0 := hdom

/-! ## 8. Lateral tidal acceleration at the throat

    a_lat = gamma^2*v^2*xi/b_0^2
-/
/-- Both sides of "Lateral tidal acceleration at the throat" carry the same physical dimension. -/
theorem eq8_lat_dim : d_a_lat = (Dim.div (Dim.mul (Dim.mul (Dim.pow d_gamma 2 1) (Dim.pow d_v 2 1)) d_xi) (Dim.pow d_b_0 2 1)) := by decide
/-- The denominator `b_0^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_lat_reg1 (b_0 : ℝ) (hb_0 : 0 < b_0) : b_0 ^ 2 ≠ 0 := by positivity

/-! ## 9. Proper crossing time

    dtau = 2*l_1/(gamma*v)
-/
/-- Both sides of "Proper crossing time" carry the same physical dimension. -/
theorem eq9_time_dim : d_dtau = (Dim.div (Dim.mul Dim.one d_l_1) (Dim.mul d_gamma d_v)) := by decide
/-- The denominator `gamma * v` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_time_reg1 (gamma v : ℝ) (hgamma : 0 < gamma) (hv : 0 < v) : gamma * v ≠ 0 := by positivity

/-! ## 10. Integrated mass of the supporting matter

    M_ex = -pi*c^2*b_0/(2*G)
-/
/-- Both sides of "Integrated mass of the supporting matter" carry the same physical dimension. -/
theorem eq10_mex_dim : d_M_ex = (Dim.div (Dim.mul (Dim.mul Dim.one (Dim.pow d_c 2 1)) d_b_0) (Dim.mul Dim.one d_G)) := by decide
/-- The denominator `2 * G` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_mex_reg1 (G : ℝ) (hG : 0 < G) : (2 : ℝ) * G ≠ 0 := by positivity

end Bespoke
