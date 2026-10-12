import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Hohmann and bi-elliptic orbit transfers

Machine-checkable statements for this investigation (hohmann-transfer).
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
def d_GM : Dim := ⟨0, 36, -24, 0, 0, 0, 0⟩  -- Gravitational parameter of the central body [m^3/s^2]
def d_I_sp : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Specific impulse [s]
def d_a_o : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Semi-major axis of the orbit [m]
def d_a_t : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Semi-major axis of the transfer ellipse [m]
def d_dv_1 : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- First velocity increment [m/s]
def d_dv_2 : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Second velocity increment [m/s]
def d_dv_tot : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Total velocity increment [m/s]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Standard gravity [m/s^2]
def d_m_0 : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Spacecraft mass before the transfer [kg]
def d_m_p : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Propellant mass [kg]
def d_r : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Orbital radius [m]
def d_r_1 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Initial orbit radius (from the body centre) [km]
def d_r_2 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Final orbit radius (from the body centre) [km]
def d_t_f : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time of flight [s]
def d_v : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Orbital speed [m/s]
def d_v_c1 : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Circular speed at the initial radius [m/s]
def d_v_c2 : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Circular speed at the final radius [m/s]
def d_v_d : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed in the initial orbit at departure [m/s]
def d_v_ta : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Transfer-orbit speed at the final radius [m/s]
def d_v_tp : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Transfer-orbit speed at the initial radius [m/s]

/-! ## 1. Vis-viva equation

    v^2 = GM*(2/r - 1/a_o)
-/
/-- Both sides of "Vis-viva equation" carry the same physical dimension. -/
theorem eq1_vv_dim : (Dim.pow d_v 2 1) = (Dim.mul d_GM (Dim.div Dim.one d_r)) := by decide
theorem eq1_vv_term1 : (Dim.div Dim.one d_r) = (Dim.div Dim.one d_a_o) := by decide
/-- Domain condition for `r`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_vv_cond1 (r : ℝ) (hdom : r ≠ 0) : r ≠ 0 := hdom
/-- Domain condition for `a_o`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_vv_cond2 (a_o : ℝ) (hdom : a_o ≠ 0) : a_o ≠ 0 := hdom

/-! ## 2. Circular speed, initial orbit

    v_c1 = sqrt(GM/r_1)
-/
/-- Both sides of "Circular speed, initial orbit" carry the same physical dimension. -/
theorem eq2_vc1_dim : d_v_c1 = (Dim.pow (Dim.div d_GM d_r_1) 1 2) := by decide
/-- The denominator `r_1` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_vc1_reg1 (r_1 : ℝ) (hr_1 : 0 < r_1) : r_1 ≠ 0 := by positivity
/-- The argument `GM / r_1` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_vc1_reg2 (GM r_1 : ℝ) (hGM : 0 < GM) (hr_1 : 0 < r_1) : 0 ≤ GM / r_1 := by positivity

/-! ## 3. Circular speed, final orbit

    v_c2 = sqrt(GM/r_2)
-/
/-- Both sides of "Circular speed, final orbit" carry the same physical dimension. -/
theorem eq3_vc2_dim : d_v_c2 = (Dim.pow (Dim.div d_GM d_r_2) 1 2) := by decide
/-- The denominator `r_2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_vc2_reg1 (r_2 : ℝ) (hr_2 : 0 < r_2) : r_2 ≠ 0 := by positivity
/-- The argument `GM / r_2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_vc2_reg2 (GM r_2 : ℝ) (hGM : 0 < GM) (hr_2 : 0 < r_2) : 0 ≤ GM / r_2 := by positivity

/-! ## 4. Departure speed

    v_d = v_c1
-/
/-- Both sides of "Departure speed" carry the same physical dimension. -/
theorem eq4_vd_dim : d_v_d = d_v_c1 := by decide

/-! ## 5. Transfer semi-major axis

    a_t = (r_1 + r_2)/2
-/
/-- Both sides of "Transfer semi-major axis" carry the same physical dimension. -/
theorem eq5_at'_dim : d_a_t = (Dim.div d_r_1 Dim.one) := by decide
theorem eq5_at'_term1 : d_r_1 = d_r_2 := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_at'_reg1  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 6. Transfer speed at the initial radius

    v_tp = sqrt(GM*(2/r_1 - 1/a_t))
-/
/-- Both sides of "Transfer speed at the initial radius" carry the same physical dimension. -/
theorem eq6_vtp_dim : d_v_tp = (Dim.pow (Dim.mul d_GM (Dim.div Dim.one d_r_1)) 1 2) := by decide
theorem eq6_vtp_term1 : (Dim.div Dim.one d_r_1) = (Dim.div Dim.one d_a_t) := by decide
/-- The denominator `r_1` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_vtp_reg1 (r_1 : ℝ) (hr_1 : 0 < r_1) : r_1 ≠ 0 := by positivity
/-- The denominator `a_t` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_vtp_reg2 (a_t : ℝ) (ha_t : 0 < a_t) : a_t ≠ 0 := by positivity
/-- Domain condition for `GM * (2 / r_1 - 1 / a_t)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_vtp_cond3 (GM r_1 a_t : ℝ) (hdom : 0 ≤ GM * ((2 : ℝ) / r_1 - (1 : ℝ) / a_t)) : 0 ≤ GM * ((2 : ℝ) / r_1 - (1 : ℝ) / a_t) := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq6_vtp_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 7. Transfer speed at the final radius

    v_ta = sqrt(GM*(2/r_2 - 1/a_t))
-/
/-- Both sides of "Transfer speed at the final radius" carry the same physical dimension. -/
theorem eq7_vta_dim : d_v_ta = (Dim.pow (Dim.mul d_GM (Dim.div Dim.one d_r_2)) 1 2) := by decide
theorem eq7_vta_term1 : (Dim.div Dim.one d_r_2) = (Dim.div Dim.one d_a_t) := by decide
/-- The denominator `r_2` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_vta_reg1 (r_2 : ℝ) (hr_2 : 0 < r_2) : r_2 ≠ 0 := by positivity
/-- The denominator `a_t` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_vta_reg2 (a_t : ℝ) (ha_t : 0 < a_t) : a_t ≠ 0 := by positivity
/-- Domain condition for `GM * (2 / r_2 - 1 / a_t)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_vta_cond3 (GM r_2 a_t : ℝ) (hdom : 0 ≤ GM * ((2 : ℝ) / r_2 - (1 : ℝ) / a_t)) : 0 ≤ GM * ((2 : ℝ) / r_2 - (1 : ℝ) / a_t) := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq7_vta_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 8. First impulse

    dv_1 = abs(v_tp - v_d)
-/
/-- Both sides of "First impulse" carry the same physical dimension. -/
theorem eq8_dv1_dim : d_dv_1 = d_v_tp := by decide
theorem eq8_dv1_term1 : d_v_tp = d_v_d := by decide

/-! ## 9. Second impulse

    dv_2 = abs(v_c2 - v_ta)
-/
/-- Both sides of "Second impulse" carry the same physical dimension. -/
theorem eq9_dv2_dim : d_dv_2 = d_v_c2 := by decide
theorem eq9_dv2_term1 : d_v_c2 = d_v_ta := by decide

/-! ## 10. Total velocity increment

    dv_tot = dv_1 + dv_2
-/
/-- Both sides of "Total velocity increment" carry the same physical dimension. -/
theorem eq10_dvt_dim : d_dv_tot = d_dv_1 := by decide
theorem eq10_dvt_term1 : d_dv_1 = d_dv_2 := by decide

/-! ## 11. Time of flight

    t_f = pi*sqrt(a_t^3/GM)
-/
/-- Both sides of "Time of flight" carry the same physical dimension. -/
theorem eq11_tf_dim : d_t_f = (Dim.mul Dim.one (Dim.pow (Dim.div (Dim.pow d_a_t 3 1) d_GM) 1 2)) := by decide
/-- The denominator `GM` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_tf_reg1 (GM : ℝ) (hGM : 0 < GM) : GM ≠ 0 := by positivity
/-- The argument `a_t^3 / GM` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_tf_reg2 (a_t GM : ℝ) (ha_t : 0 < a_t) (hGM : 0 < GM) : 0 ≤ a_t ^ 3 / GM := by positivity

/-! ## 12. Propellant mass

    m_p = m_0*(1 - exp(-dv_tot/(g*I_sp)))
-/
/-- Both sides of "Propellant mass" carry the same physical dimension. -/
theorem eq12_mp_dim : d_m_p = (Dim.mul d_m_0 Dim.one) := by decide
theorem eq12_mp_term1 : (Dim.div d_dv_tot (Dim.mul d_g d_I_sp)) = Dim.one := by decide
theorem eq12_mp_term2 : Dim.one = Dim.one := by decide
/-- The denominator `g * I_sp` stays away from its singular set whenever the quantities are positive. -/
theorem eq12_mp_reg1 (g I_sp : ℝ) (hg : 0 < g) (hI_sp : 0 < I_sp) : g * I_sp ≠ 0 := by positivity

end Bespoke
