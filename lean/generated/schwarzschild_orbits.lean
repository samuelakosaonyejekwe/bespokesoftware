import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Orbits and light deflection in Schwarzschild spacetime

Machine-checkable statements for this investigation (schwarzschild-orbits).
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
def d_M : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Central mass [Msun]
def d_V_eff : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Effective potential per unit mass [J/kg]
def d_a : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Semi-major axis of the orbit [AU]
def d_b : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Impact parameter of the light ray [km]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light [m/s]
def d_delta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Deflection angle of light [rad]
def d_dphi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Perihelion advance per orbit [rad]
def d_e' : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Orbital eccentricity [1]
def d_h_L : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Specific angular momentum [m^2/s]
def d_phi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Orbital angle [rad]
def d_r : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Radial coordinate [m]
def d_r_isco : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Innermost stable circular orbit [m]
def d_r_ph : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Photon-sphere radius [m]
def d_r_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Schwarzschild radius [m]
def d_u : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Inverse radius 1/r [1/m]

/-! ## 1. Orbit equation

    d2(u,phi) + u = G*M/h_L^2 + 3*G*M*u^2/c^2
-/
/-- Both sides of "Orbit equation" carry the same physical dimension. -/
theorem eq1_orbit_dim : (Dim.div d_u (Dim.pow d_phi 2 1)) = (Dim.div (Dim.mul d_G d_M) (Dim.pow d_h_L 2 1)) := by decide
theorem eq1_orbit_term1 : (Dim.div d_u (Dim.pow d_phi 2 1)) = d_u := by decide
theorem eq1_orbit_term2 : (Dim.div (Dim.mul d_G d_M) (Dim.pow d_h_L 2 1)) = (Dim.div (Dim.mul (Dim.mul (Dim.mul Dim.one d_G) d_M) (Dim.pow d_u 2 1)) (Dim.pow d_c 2 1)) := by decide
/-- The denominator `h_L^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_orbit_reg1 (h_L : ℝ) (hh_L : 0 < h_L) : h_L ^ 2 ≠ 0 := by positivity
/-- The denominator `c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_orbit_reg2 (c : ℝ) (hc : 0 < c) : c ^ 2 ≠ 0 := by positivity

/-! ## 2. Effective potential

    V_eff = -G*M/r + h_L^2/(2*r^2) - G*M*h_L^2/(c^2*r^3)
-/
/-- Both sides of "Effective potential" carry the same physical dimension. -/
theorem eq2_veff_dim : d_V_eff = (Dim.div (Dim.mul d_G d_M) d_r) := by decide
theorem eq2_veff_term1 : (Dim.div (Dim.mul d_G d_M) d_r) = (Dim.div (Dim.pow d_h_L 2 1) (Dim.mul Dim.one (Dim.pow d_r 2 1))) := by decide
theorem eq2_veff_term2 : (Dim.div (Dim.mul d_G d_M) d_r) = (Dim.div (Dim.mul (Dim.mul d_G d_M) (Dim.pow d_h_L 2 1)) (Dim.mul (Dim.pow d_c 2 1) (Dim.pow d_r 3 1))) := by decide
/-- Domain condition for `r`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_veff_cond1 (r : ℝ) (hdom : r ≠ 0) : r ≠ 0 := hdom
/-- Domain condition for `2 * r^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_veff_cond2 (r : ℝ) (hdom : (2 : ℝ) * r ^ 2 ≠ 0) : (2 : ℝ) * r ^ 2 ≠ 0 := hdom
/-- Domain condition for `c^2 * r^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_veff_cond3 (c r : ℝ) (hdom : c ^ 2 * r ^ 3 ≠ 0) : c ^ 2 * r ^ 3 ≠ 0 := hdom

/-! ## 3. Perihelion advance per orbit

    dphi = 6*pi*G*M/(c^2*a*(1 - e^2))
-/
/-- Both sides of "Perihelion advance per orbit" carry the same physical dimension. -/
theorem eq3_prec_dim : d_dphi = (Dim.div (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_G) d_M) (Dim.mul (Dim.mul (Dim.pow d_c 2 1) d_a) Dim.one)) := by decide
theorem eq3_prec_term1 : Dim.one = (Dim.pow d_e' 2 1) := by decide
/-- Domain condition for `c^2 * a * (1 - e^2)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq3_prec_cond1 (c a e' : ℝ) (hdom : c ^ 2 * a * ((1 : ℝ) - e' ^ 2) ≠ 0) : c ^ 2 * a * ((1 : ℝ) - e' ^ 2) ≠ 0 := hdom

/-! ## 4. Light-ray equation

    d2(u,phi) + u = 3*G*M*u^2/c^2
-/
/-- Both sides of "Light-ray equation" carry the same physical dimension. -/
theorem eq4_null_dim : (Dim.div d_u (Dim.pow d_phi 2 1)) = (Dim.div (Dim.mul (Dim.mul (Dim.mul Dim.one d_G) d_M) (Dim.pow d_u 2 1)) (Dim.pow d_c 2 1)) := by decide
theorem eq4_null_term1 : (Dim.div d_u (Dim.pow d_phi 2 1)) = d_u := by decide
/-- The denominator `c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_null_reg1 (c : ℝ) (hc : 0 < c) : c ^ 2 ≠ 0 := by positivity

/-! ## 5. Deflection of light

    delta = 4*G*M/(c^2*b)
-/
/-- Both sides of "Deflection of light" carry the same physical dimension. -/
theorem eq5_defl_dim : d_delta = (Dim.div (Dim.mul (Dim.mul Dim.one d_G) d_M) (Dim.mul (Dim.pow d_c 2 1) d_b)) := by decide
/-- The denominator `c^2 * b` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_defl_reg1 (c b : ℝ) (hc : 0 < c) (hb : 0 < b) : c ^ 2 * b ≠ 0 := by positivity

/-! ## 6. Schwarzschild radius

    r_s = 2*G*M/c^2
-/
/-- Both sides of "Schwarzschild radius" carry the same physical dimension. -/
theorem eq6_rs_dim : d_r_s = (Dim.div (Dim.mul (Dim.mul Dim.one d_G) d_M) (Dim.pow d_c 2 1)) := by decide
/-- The denominator `c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_rs_reg1 (c : ℝ) (hc : 0 < c) : c ^ 2 ≠ 0 := by positivity

/-! ## 7. Innermost stable circular orbit

    r_isco = 6*G*M/c^2
-/
/-- Both sides of "Innermost stable circular orbit" carry the same physical dimension. -/
theorem eq7_isco_dim : d_r_isco = (Dim.div (Dim.mul (Dim.mul Dim.one d_G) d_M) (Dim.pow d_c 2 1)) := by decide
/-- The denominator `c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_isco_reg1 (c : ℝ) (hc : 0 < c) : c ^ 2 ≠ 0 := by positivity

/-! ## 8. Photon sphere

    r_ph = 3*G*M/c^2
-/
/-- Both sides of "Photon sphere" carry the same physical dimension. -/
theorem eq8_rph_dim : d_r_ph = (Dim.div (Dim.mul (Dim.mul Dim.one d_G) d_M) (Dim.pow d_c 2 1)) := by decide
/-- The denominator `c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_rph_reg1 (c : ℝ) (hc : 0 < c) : c ^ 2 ≠ 0 := by positivity

end Bespoke
