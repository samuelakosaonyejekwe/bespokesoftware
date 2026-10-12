import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Vertical rocket ascent with drag and gravity

Machine-checkable statements for this investigation (rocket-ascent).
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
def d_A_ref : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Frontal area [m^2]
def d_C_D : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Drag coefficient (frontal-area basis) [1]
def d_D : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Drag [N]
def d_F : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Thrust [N]
def d_F_v : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Vacuum thrust [N]
def d_H : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Atmospheric scale height [km]
def d_I_sp : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Specific impulse (vacuum) [s]
def d_R_p : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Planet radius [km]
def d_TW : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Thrust-to-weight ratio at lift-off [1]
def d_dv_id : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Ideal velocity increment [m/s]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Standard gravity [m/s^2]
def d_g_h : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Local gravitational acceleration [m/s^2]
def d_g_s : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Surface gravitational acceleration [m/s^2]
def d_m : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Vehicle mass [kg]
def d_m_0 : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Lift-off mass [kg]
def d_m_f : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Burnout mass [kg]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Air density [kg/m^3]
def d_rho_0 : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Air density at the launch site [kg/m^3]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_v : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Vertical velocity [m/s]
def d_z : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Altitude [m]
def d_zeta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Propellant mass fraction [1]

/-! ## 1. Vacuum thrust

    F_v = TW*m_0*g_s
-/
/-- Both sides of "Vacuum thrust" carry the same physical dimension. -/
theorem eq1_fv_dim : d_F_v = (Dim.mul (Dim.mul d_TW d_m_0) d_g_s) := by decide

/-! ## 2. Propellant consumption

    d(m,t) = -F_v/(g*I_sp)
-/
/-- Both sides of "Propellant consumption" carry the same physical dimension. -/
theorem eq2_mass_dim : (Dim.div d_m d_t) = (Dim.div d_F_v (Dim.mul d_g d_I_sp)) := by decide
/-- The denominator `g * I_sp` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_mass_reg1 (g I_sp : ℝ) (hg : 0 < g) (hI_sp : 0 < I_sp) : g * I_sp ≠ 0 := by positivity

/-! ## 3. Burnout mass

    m_f = m_0*(1 - zeta)
-/
/-- Both sides of "Burnout mass" carry the same physical dimension. -/
theorem eq3_mf_dim : d_m_f = (Dim.mul d_m_0 Dim.one) := by decide
theorem eq3_mf_term1 : Dim.one = d_zeta := by decide

/-! ## 4. Ideal velocity increment

    dv_id = g*I_sp*ln(m_0/m_f)
-/
/-- Both sides of "Ideal velocity increment" carry the same physical dimension. -/
theorem eq4_tsi_dim : d_dv_id = (Dim.mul (Dim.mul d_g d_I_sp) Dim.one) := by decide
theorem eq4_tsi_term1 : (Dim.div d_m_0 d_m_f) = Dim.one := by decide
/-- The denominator `m_f` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_tsi_reg1 (m_f : ℝ) (hm_f : 0 < m_f) : m_f ≠ 0 := by positivity
/-- The argument `m_0 / m_f` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_tsi_reg2 (m_0 m_f : ℝ) (hm_0 : 0 < m_0) (hm_f : 0 < m_f) : 0 < m_0 / m_f := by positivity

/-! ## 5. Equation of motion

    m*d(v,t) = F - D - m*g_h
-/
/-- Both sides of "Equation of motion" carry the same physical dimension. -/
theorem eq5_mom_dim : (Dim.mul d_m (Dim.div d_v d_t)) = d_F := by decide
theorem eq5_mom_term1 : d_F = d_D := by decide
theorem eq5_mom_term2 : d_F = (Dim.mul d_m d_g_h) := by decide

/-! ## 6. Kinematics

    d(z,t) = v
-/
/-- Both sides of "Kinematics" carry the same physical dimension. -/
theorem eq6_kin_dim : (Dim.div d_z d_t) = d_v := by decide

/-! ## 7. Thrust

    F = F_v
-/
/-- Both sides of "Thrust" carry the same physical dimension. -/
theorem eq7_thr_dim : d_F = d_F_v := by decide

/-! ## 8. Drag

    D = 0.5*rho*v*abs(v)*C_D*A_ref
-/
/-- Both sides of "Drag" carry the same physical dimension. -/
theorem eq8_drag_dim : d_D = (Dim.mul (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) d_v) d_v) d_C_D) d_A_ref) := by decide

/-! ## 9. Air density

    rho = rho_0*exp(-z/H)
-/
/-- Both sides of "Air density" carry the same physical dimension. -/
theorem eq9_rho_dim : d_rho = (Dim.mul d_rho_0 Dim.one) := by decide
theorem eq9_rho_term1 : (Dim.div d_z d_H) = Dim.one := by decide
/-- The denominator `H` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_rho_reg1 (H : ℝ) (hH : 0 < H) : H ≠ 0 := by positivity

/-! ## 10. Local gravity

    g_h = g_s*(R_p/(R_p + z))^2
-/
/-- Both sides of "Local gravity" carry the same physical dimension. -/
theorem eq10_grav_dim : d_g_h = (Dim.mul d_g_s (Dim.pow (Dim.div d_R_p d_R_p) 2 1)) := by decide
theorem eq10_grav_term1 : d_R_p = d_z := by decide
/-- Domain condition for `R_p + z`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_grav_cond1 (R_p z : ℝ) (hdom : R_p + z ≠ 0) : R_p + z ≠ 0 := hdom

end Bespoke
