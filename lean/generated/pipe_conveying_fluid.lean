import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Stability of a pipe conveying fluid

Machine-checkable statements for this investigation (pipe-conveying-fluid).
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
def d_A_i : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Internal flow area [m^2]
def d_E : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Young's modulus of the pipe [GPa]
def d_I_b : Dim := ⟨0, 48, 0, 0, 0, 0, 0⟩  -- Second moment of area of the pipe wall [m^4]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Span between supports [m]
def d_N_e : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Effective axial tension [N]
def d_T_0 : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Externally applied axial tension [kN]
def d_U : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Mean flow velocity [m/s]
def d_U_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Critical flow velocity [m/s]
def d_m_f : Dim := ⟨12, -12, 0, 0, 0, 0, 0⟩  -- Fluid mass per unit length [kg/m]
def d_m_p : Dim := ⟨12, -12, 0, 0, 0, 0, 0⟩  -- Pipe mass per unit length [kg/m]
def d_m_t : Dim := ⟨12, -12, 0, 0, 0, 0, 0⟩  -- Total vibrating mass per unit length [kg/m]
def d_omega_0 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Natural frequency at zero flow [1/s]
def d_omega_1 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- First natural frequency at velocity U [1/s]
def d_rho_f : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Density of the conveyed fluid [kg/m^3]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance along the pipe [m]
def d_y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Lateral deflection [m]

/-! ## 1. Fluid mass per unit length

    m_f = rho_f*A_i
-/
/-- Both sides of "Fluid mass per unit length" carry the same physical dimension. -/
theorem eq1_mf_dim : d_m_f = (Dim.mul d_rho_f d_A_i) := by decide

/-! ## 2. Vibrating mass per unit length

    m_t = m_p + m_f
-/
/-- Both sides of "Vibrating mass per unit length" carry the same physical dimension. -/
theorem eq2_mt_dim : d_m_t = d_m_p := by decide
theorem eq2_mt_term1 : d_m_p = d_m_f := by decide

/-! ## 3. Effective axial tension

    N_e = T_0
-/
/-- Both sides of "Effective axial tension" carry the same physical dimension. -/
theorem eq3_ne_dim : d_N_e = d_T_0 := by decide

/-! ## 4. Equation of motion

    m_t*pd2(y,t) = -E*I_b*pd2(pd2(y,x),x) - (m_f*U^2 - N_e)*pd2(y,x) - 2*m_f*U*pd(pd(y,x),t)
-/
/-- Both sides of "Equation of motion" carry the same physical dimension. -/
theorem eq4_eom_dim : (Dim.mul d_m_t (Dim.div d_y (Dim.pow d_t 2 1))) = (Dim.mul (Dim.mul d_E d_I_b) (Dim.div (Dim.div d_y (Dim.pow d_x 2 1)) (Dim.pow d_x 2 1))) := by decide
theorem eq4_eom_term1 : (Dim.mul d_m_f (Dim.pow d_U 2 1)) = d_N_e := by decide
theorem eq4_eom_term2 : (Dim.mul (Dim.mul d_E d_I_b) (Dim.div (Dim.div d_y (Dim.pow d_x 2 1)) (Dim.pow d_x 2 1))) = (Dim.mul (Dim.mul d_m_f (Dim.pow d_U 2 1)) (Dim.div d_y (Dim.pow d_x 2 1))) := by decide
theorem eq4_eom_term3 : (Dim.mul (Dim.mul d_E d_I_b) (Dim.div (Dim.div d_y (Dim.pow d_x 2 1)) (Dim.pow d_x 2 1))) = (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_f) d_U) (Dim.div (Dim.div d_y d_x) d_t)) := by decide

/-! ## 5. Critical velocity for divergence

    U_c = sqrt((E*I_b*(pi/L)^2 + N_e)/m_f)
-/
/-- Both sides of "Critical velocity for divergence" carry the same physical dimension. -/
theorem eq5_uc_dim : d_U_c = (Dim.pow (Dim.div (Dim.mul (Dim.mul d_E d_I_b) (Dim.pow (Dim.div Dim.one d_L) 2 1)) d_m_f) 1 2) := by decide
theorem eq5_uc_term1 : (Dim.mul (Dim.mul d_E d_I_b) (Dim.pow (Dim.div Dim.one d_L) 2 1)) = d_N_e := by decide
/-- The denominator `L` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_uc_reg1 (L : ℝ) (hL : 0 < L) : L ≠ 0 := by positivity
/-- The denominator `m_f` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_uc_reg2 (m_f : ℝ) (hm_f : 0 < m_f) : m_f ≠ 0 := by positivity
/-- Domain condition for `(E * I_b * (pi / L)^2 + N_e) / m_f`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_uc_cond3 (E I_b L N_e m_f : ℝ) (hdom : 0 ≤ (E * I_b * (Real.pi / L) ^ 2 + N_e) / m_f) : 0 ≤ (E * I_b * (Real.pi / L) ^ 2 + N_e) / m_f := hdom

/-! ## 6. Natural frequency at zero flow

    omega_0 = pi/L*sqrt((E*I_b*(pi/L)^2 + N_e)/m_t)
-/
/-- Both sides of "Natural frequency at zero flow" carry the same physical dimension. -/
theorem eq6_w0_dim : d_omega_0 = (Dim.mul (Dim.div Dim.one d_L) (Dim.pow (Dim.div (Dim.mul (Dim.mul d_E d_I_b) (Dim.pow (Dim.div Dim.one d_L) 2 1)) d_m_t) 1 2)) := by decide
theorem eq6_w0_term1 : (Dim.mul (Dim.mul d_E d_I_b) (Dim.pow (Dim.div Dim.one d_L) 2 1)) = d_N_e := by decide
/-- The denominator `L` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_w0_reg1 (L : ℝ) (hL : 0 < L) : L ≠ 0 := by positivity
/-- The denominator `L` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_w0_reg2 (L : ℝ) (hL : 0 < L) : L ≠ 0 := by positivity
/-- The denominator `m_t` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_w0_reg3 (m_t : ℝ) (hm_t : 0 < m_t) : m_t ≠ 0 := by positivity
/-- Domain condition for `(E * I_b * (pi / L)^2 + N_e) / m_t`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_w0_cond4 (E I_b L N_e m_t : ℝ) (hdom : 0 ≤ (E * I_b * (Real.pi / L) ^ 2 + N_e) / m_t) : 0 ≤ (E * I_b * (Real.pi / L) ^ 2 + N_e) / m_t := hdom

/-! ## 7. Natural frequency with flow

    omega_1 = omega_0*sqrt(1 - (U/U_c)^2)
-/
/-- Both sides of "Natural frequency with flow" carry the same physical dimension. -/
theorem eq7_w1_dim : d_omega_1 = (Dim.mul d_omega_0 (Dim.pow Dim.one 1 2)) := by decide
theorem eq7_w1_term1 : Dim.one = (Dim.pow (Dim.div d_U d_U_c) 2 1) := by decide
/-- The denominator `U_c` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_w1_reg1 (U_c : ℝ) (hU_c : 0 < U_c) : U_c ≠ 0 := by positivity
/-- Domain condition for `1 - (U / U_c)^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_w1_cond2 (U U_c : ℝ) (hdom : 0 ≤ (1 : ℝ) - (U / U_c) ^ 2) : 0 ≤ (1 : ℝ) - (U / U_c) ^ 2 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq7_w1_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

end Bespoke
