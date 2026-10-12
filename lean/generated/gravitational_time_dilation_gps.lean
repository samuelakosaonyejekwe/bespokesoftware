import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Relativistic clock offsets in satellite navigation

Machine-checkable statements for this investigation (gravitational-time-dilation-gps).
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
def d_GM : Dim := ⟨0, 36, -24, 0, 0, 0, 0⟩  -- Gravitational parameter of the planet [m^3/s^2]
def d_Phi : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Newtonian potential (negative) [J/kg]
def d_R_E : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Equatorial radius of the planet [km]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light [m/s]
def d_dt : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Accumulated clock offset [s]
def d_dx : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Ranging error [m]
def d_h : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Satellite altitude above the equatorial radius [km]
def d_r : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Orbital radius [m]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Coordinate time [s]
def d_t_el : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Elapsed time without correction [d]
def d_tau : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Proper time of a clock [s]
def d_u : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Clock speed [m/s]
def d_v_g : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Ground-clock speed [m/s]
def d_v_s : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Satellite speed [m/s]
def d_x_gr : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fractional rate offset, gravitational [1]
def d_x_net : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Net fractional rate offset [1]
def d_x_sr : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fractional rate offset, velocity [1]

/-! ## 1. Clock rate in a weak field

    d(tau,t) = 1 + Phi/c^2 - u^2/(2*c^2)
-/
/-- Both sides of "Clock rate in a weak field" carry the same physical dimension. -/
theorem eq1_rate_dim : (Dim.div d_tau d_t) = Dim.one := by decide
theorem eq1_rate_term1 : Dim.one = (Dim.div d_Phi (Dim.pow d_c 2 1)) := by decide
theorem eq1_rate_term2 : Dim.one = (Dim.div (Dim.pow d_u 2 1) (Dim.mul Dim.one (Dim.pow d_c 2 1))) := by decide
/-- The denominator `c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_rate_reg1 (c : ℝ) (hc : 0 < c) : c ^ 2 ≠ 0 := by positivity
/-- The denominator `2 * c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_rate_reg2 (c : ℝ) (hc : 0 < c) : (2 : ℝ) * c ^ 2 ≠ 0 := by positivity

/-! ## 2. Orbital radius

    r = R_E + h
-/
/-- Both sides of "Orbital radius" carry the same physical dimension. -/
theorem eq2_rad_dim : d_r = d_R_E := by decide
theorem eq2_rad_term1 : d_R_E = d_h := by decide

/-! ## 3. Circular orbital speed

    v_s = sqrt(GM/r)
-/
/-- Both sides of "Circular orbital speed" carry the same physical dimension. -/
theorem eq3_vs_dim : d_v_s = (Dim.pow (Dim.div d_GM d_r) 1 2) := by decide
/-- The denominator `r` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_vs_reg1 (r : ℝ) (hr : 0 < r) : r ≠ 0 := by positivity
/-- The argument `GM / r` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_vs_reg2 (GM r : ℝ) (hGM : 0 < GM) (hr : 0 < r) : 0 ≤ GM / r := by positivity

/-! ## 4. Gravitational offset

    x_gr = GM/c^2*(1/R_E - 1/r)
-/
/-- Both sides of "Gravitational offset" carry the same physical dimension. -/
theorem eq4_gr_dim : d_x_gr = (Dim.mul (Dim.div d_GM (Dim.pow d_c 2 1)) (Dim.div Dim.one d_R_E)) := by decide
theorem eq4_gr_term1 : (Dim.div Dim.one d_R_E) = (Dim.div Dim.one d_r) := by decide
/-- The denominator `c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_gr_reg1 (c : ℝ) (hc : 0 < c) : c ^ 2 ≠ 0 := by positivity
/-- The denominator `R_E` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_gr_reg2 (R_E : ℝ) (hR_E : 0 < R_E) : R_E ≠ 0 := by positivity
/-- The denominator `r` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_gr_reg3 (r : ℝ) (hr : 0 < r) : r ≠ 0 := by positivity

/-! ## 5. Velocity offset

    x_sr = -(v_s^2 - v_g^2)/(2*c^2)
-/
/-- Both sides of "Velocity offset" carry the same physical dimension. -/
theorem eq5_sr_dim : d_x_sr = (Dim.div (Dim.pow d_v_s 2 1) (Dim.mul Dim.one (Dim.pow d_c 2 1))) := by decide
theorem eq5_sr_term1 : (Dim.pow d_v_s 2 1) = (Dim.pow d_v_g 2 1) := by decide
/-- The denominator `2 * c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_sr_reg1 (c : ℝ) (hc : 0 < c) : (2 : ℝ) * c ^ 2 ≠ 0 := by positivity

/-! ## 6. Net fractional offset

    x_net = x_gr + x_sr
-/
/-- Both sides of "Net fractional offset" carry the same physical dimension. -/
theorem eq6_net_dim : d_x_net = d_x_gr := by decide
theorem eq6_net_term1 : d_x_gr = d_x_sr := by decide

/-! ## 7. Accumulated time offset

    dt = x_net*t_el
-/
/-- Both sides of "Accumulated time offset" carry the same physical dimension. -/
theorem eq7_acc_dim : d_dt = (Dim.mul d_x_net d_t_el) := by decide

/-! ## 8. Ranging error

    dx = c*dt
-/
/-- Both sides of "Ranging error" carry the same physical dimension. -/
theorem eq8_rng_dim : d_dx = (Dim.mul d_c d_dt) := by decide

end Bespoke
