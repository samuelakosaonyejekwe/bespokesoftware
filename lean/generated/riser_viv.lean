import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Vortex-induced vibration of a tensioned riser

Machine-checkable statements for this investigation (riser-viv).
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
def d_A_c : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Wake coupling parameter A [1]
def d_A_y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Displacement amplitude at the antinode [m]
def d_C_Ds : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Sectional drag coefficient in the fluid-damping term [1]
def d_C_L0 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Lift coefficient of the fixed cylinder [1]
def d_C_a : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Added-mass coefficient [1]
def d_D : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Outer (hydrodynamic) diameter [m]
def d_E : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Young's modulus [GPa]
def d_I_b : Dim := ⟨0, 48, 0, 0, 0, 0, 0⟩  -- Second moment of area [m^4]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Riser length between supports [m]
def d_Omega_f : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Shedding angular frequency [1/s]
def d_St : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Strouhal number [1]
def d_T_e : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Effective tension [N]
def d_T_top : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Effective top tension [kN]
def d_U : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Current speed normal to the riser [m/s]
def d_U_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Reduced velocity [1]
def d_eps_w : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Van der Pol parameter ε [1]
def d_f_n : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Natural frequency of mode n [1/s]
def d_f_s : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Vortex-shedding frequency [1/s]
def d_gamma_f : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Stall parameter [1]
def d_m_s : Dim := ⟨12, -12, 0, 0, 0, 0, 0⟩  -- Structural mass per unit length including contents [kg/m]
def d_m_t : Dim := ⟨12, -12, 0, 0, 0, 0, 0⟩  -- Total mass per unit length including added mass [kg/m]
def d_n_m : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Mode number [1]
def d_omega_n : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Natural angular frequency [1/s]
def d_q : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Wake variable (reduced lift) [1]
def d_r_t : Dim := ⟨12, -12, -12, 0, 0, 0, 0⟩  -- Total damping per unit length [kg/(m s)]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Sea-water density [kg/m^3]
def d_sigma_a : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Bending-stress amplitude [Pa]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Cross-flow displacement [m]
def d_y_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Limit-cycle amplitude of the oscillator pair [m]
def d_zeta_s : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Structural damping ratio [1]

/-! ## 1. Strouhal relation

    f_s = St*U/D
-/
/-- Both sides of "Strouhal relation" carry the same physical dimension. -/
theorem eq1_fs_dim : d_f_s = (Dim.div (Dim.mul d_St d_U) d_D) := by decide
/-- The denominator `D` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_fs_reg1 (D : ℝ) (hD : 0 < D) : D ≠ 0 := by positivity

/-! ## 2. Shedding angular frequency

    Omega_f = 2*pi*f_s
-/
/-- Both sides of "Shedding angular frequency" carry the same physical dimension. -/
theorem eq2_of_dim : d_Omega_f = (Dim.mul (Dim.mul Dim.one Dim.one) d_f_s) := by decide

/-! ## 3. Mass per unit length

    m_t = m_s + C_a*rho*pi*D^2/4
-/
/-- Both sides of "Mass per unit length" carry the same physical dimension. -/
theorem eq3_mt_dim : d_m_t = d_m_s := by decide
theorem eq3_mt_term1 : d_m_s = (Dim.div (Dim.mul (Dim.mul (Dim.mul d_C_a d_rho) Dim.one) (Dim.pow d_D 2 1)) Dim.one) := by decide
/-- The denominator `4` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_mt_reg1  : (4 : ℝ) ≠ 0 := by positivity

/-! ## 4. Effective tension

    T_e = T_top
-/
/-- Both sides of "Effective tension" carry the same physical dimension. -/
theorem eq4_te_dim : d_T_e = d_T_top := by decide

/-! ## 5. Tensioned-beam natural frequency

    f_n = n_m/(2*L)*sqrt(T_e/m_t + n_m^2*pi^2*E*I_b/(m_t*L^2))
-/
/-- Both sides of "Tensioned-beam natural frequency" carry the same physical dimension. -/
theorem eq5_fn_dim : d_f_n = (Dim.mul (Dim.div d_n_m (Dim.mul Dim.one d_L)) (Dim.pow (Dim.div d_T_e d_m_t) 1 2)) := by decide
theorem eq5_fn_term1 : (Dim.div d_T_e d_m_t) = (Dim.div (Dim.mul (Dim.mul (Dim.mul (Dim.pow d_n_m 2 1) (Dim.pow Dim.one 2 1)) d_E) d_I_b) (Dim.mul d_m_t (Dim.pow d_L 2 1))) := by decide
/-- The denominator `2 * L` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_fn_reg1 (L : ℝ) (hL : 0 < L) : (2 : ℝ) * L ≠ 0 := by positivity
/-- Domain condition for `m_t`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_fn_cond2 (m_t : ℝ) (hdom : m_t ≠ 0) : m_t ≠ 0 := hdom
/-- Domain condition for `m_t * L^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_fn_cond3 (m_t L : ℝ) (hdom : m_t * L ^ 2 ≠ 0) : m_t * L ^ 2 ≠ 0 := hdom
/-- Domain condition for `T_e / m_t + n_m^2 * pi^2 * E * I_b / (m_t * L^2)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_fn_cond4 (T_e m_t n_m E I_b L : ℝ) (hdom : 0 ≤ T_e / m_t + n_m ^ 2 * Real.pi ^ 2 * E * I_b / (m_t * L ^ 2)) : 0 ≤ T_e / m_t + n_m ^ 2 * Real.pi ^ 2 * E * I_b / (m_t * L ^ 2) := hdom

/-! ## 6. Natural angular frequency

    omega_n = 2*pi*f_n
-/
/-- Both sides of "Natural angular frequency" carry the same physical dimension. -/
theorem eq6_on_dim : d_omega_n = (Dim.mul (Dim.mul Dim.one Dim.one) d_f_n) := by decide

/-! ## 7. Reduced velocity

    U_r = U/(f_n*D)
-/
/-- Both sides of "Reduced velocity" carry the same physical dimension. -/
theorem eq7_ur_dim : d_U_r = (Dim.div d_U (Dim.mul d_f_n d_D)) := by decide
/-- The denominator `f_n * D` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_ur_reg1 (f_n D : ℝ) (hf_n : 0 < f_n) (hD : 0 < D) : f_n * D ≠ 0 := by positivity

/-! ## 8. Stall parameter

    gamma_f = C_Ds/(4*pi*St)
-/
/-- Both sides of "Stall parameter" carry the same physical dimension. -/
theorem eq8_gam_dim : d_gamma_f = (Dim.div d_C_Ds (Dim.mul (Dim.mul Dim.one Dim.one) d_St)) := by decide
/-- The denominator `4 * pi * St` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_gam_reg1 (St : ℝ) (hSt : 0 < St) : (4 : ℝ) * Real.pi * St ≠ 0 := by positivity

/-! ## 9. Damping per unit length

    r_t = 2*zeta_s*m_t*omega_n + gamma_f*Omega_f*rho*D^2
-/
/-- Both sides of "Damping per unit length" carry the same physical dimension. -/
theorem eq9_rt_dim : d_r_t = (Dim.mul (Dim.mul (Dim.mul Dim.one d_zeta_s) d_m_t) d_omega_n) := by decide
theorem eq9_rt_term1 : (Dim.mul (Dim.mul (Dim.mul Dim.one d_zeta_s) d_m_t) d_omega_n) = (Dim.mul (Dim.mul (Dim.mul d_gamma_f d_Omega_f) d_rho) (Dim.pow d_D 2 1)) := by decide

/-! ## 10. Structural oscillator

    m_t*d2(y,t) + r_t*d(y,t) + m_t*omega_n^2*y = 0.25*rho*U^2*D*C_L0*q
-/
/-- Both sides of "Structural oscillator" carry the same physical dimension. -/
theorem eq10_str_dim : (Dim.mul d_m_t (Dim.div d_y (Dim.pow d_t 2 1))) = (Dim.mul (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) (Dim.pow d_U 2 1)) d_D) d_C_L0) d_q) := by decide
theorem eq10_str_term1 : (Dim.mul d_m_t (Dim.div d_y (Dim.pow d_t 2 1))) = (Dim.mul d_r_t (Dim.div d_y d_t)) := by decide
theorem eq10_str_term2 : (Dim.mul d_m_t (Dim.div d_y (Dim.pow d_t 2 1))) = (Dim.mul (Dim.mul d_m_t (Dim.pow d_omega_n 2 1)) d_y) := by decide

/-! ## 11. Wake oscillator

    d2(q,t) + eps_w*Omega_f*(q^2 - 1)*d(q,t) + Omega_f^2*q = A_c/D*d2(y,t)
-/
/-- Both sides of "Wake oscillator" carry the same physical dimension. -/
theorem eq11_wake_dim : (Dim.div d_q (Dim.pow d_t 2 1)) = (Dim.mul (Dim.div d_A_c d_D) (Dim.div d_y (Dim.pow d_t 2 1))) := by decide
theorem eq11_wake_term1 : (Dim.pow d_q 2 1) = Dim.one := by decide
theorem eq11_wake_term2 : (Dim.div d_q (Dim.pow d_t 2 1)) = (Dim.mul (Dim.mul (Dim.mul d_eps_w d_Omega_f) (Dim.pow d_q 2 1)) (Dim.div d_q d_t)) := by decide
theorem eq11_wake_term3 : (Dim.div d_q (Dim.pow d_t 2 1)) = (Dim.mul (Dim.pow d_Omega_f 2 1) d_q) := by decide
/-- The denominator `D` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_wake_reg1 (D : ℝ) (hD : 0 < D) : D ≠ 0 := by positivity

/-! ## 12. Modal amplitude

    A_y = y_0
-/
/-- Both sides of "Modal amplitude" carry the same physical dimension. -/
theorem eq12_amp_dim : d_A_y = d_y_0 := by decide

/-! ## 13. Bending-stress amplitude

    sigma_a = E*D/2*(n_m*pi/L)^2*A_y
-/
/-- Both sides of "Bending-stress amplitude" carry the same physical dimension. -/
theorem eq13_sig_dim : d_sigma_a = (Dim.mul (Dim.mul (Dim.div (Dim.mul d_E d_D) Dim.one) (Dim.pow (Dim.div (Dim.mul d_n_m Dim.one) d_L) 2 1)) d_A_y) := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq13_sig_reg1  : (2 : ℝ) ≠ 0 := by positivity
/-- The denominator `L` stays away from its singular set whenever the quantities are positive. -/
theorem eq13_sig_reg2 (L : ℝ) (hL : 0 < L) : L ≠ 0 := by positivity

end Bespoke
