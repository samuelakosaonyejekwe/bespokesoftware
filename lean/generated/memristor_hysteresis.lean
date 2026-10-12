import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Memristor: pinched current–voltage hysteresis

Machine-checkable statements for this investigation (memristor-hysteresis).
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
def d_D_f : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Film thickness [nm]
def d_F_w : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Window function [1]
def d_M_r : Dim := ⟨12, 24, -36, -24, 0, 0, 0⟩  -- Memristance [ohm]
def d_Q_D : Dim := ⟨0, 0, 12, 12, 0, 0, 0⟩  -- Charge to move the boundary across the film [C]
def d_R_off : Dim := ⟨12, 24, -36, -24, 0, 0, 0⟩  -- Resistance when fully undoped [kohm]
def d_R_on : Dim := ⟨12, 24, -36, -24, 0, 0, 0⟩  -- Resistance when fully doped [ohm]
def d_V_0 : Dim := ⟨12, 24, -36, -12, 0, 0, 0⟩  -- Drive voltage amplitude [V]
def d_f_c : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Characteristic switching frequency [Hz]
def d_f_d : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Drive frequency [Hz]
def d_i_m : Dim := ⟨0, 0, 0, 12, 0, 0, 0⟩  -- Current [A]
def d_mu_v : Dim := ⟨-12, 0, 24, 12, 0, 0, 0⟩  -- Dopant (ion) mobility [m^2/(V s)]
def d_p_w : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Window exponent [1]
def d_phi_D : Dim := ⟨12, 24, -24, -12, 0, 0, 0⟩  -- Flux to switch fully [V s]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_v_m : Dim := ⟨12, 24, -36, -12, 0, 0, 0⟩  -- Applied voltage [V]
def d_x_w : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- State variable w/D [1]

/-! ## 1. State-dependent Ohm's law

    v_m = M_r*i_m
-/
/-- Both sides of "State-dependent Ohm's law" carry the same physical dimension. -/
theorem eq1_ohm_dim : d_v_m = (Dim.mul d_M_r d_i_m) := by decide

/-! ## 2. Memristance of the two-region film

    M_r = R_on*x_w + R_off*(1 - x_w)
-/
/-- Both sides of "Memristance of the two-region film" carry the same physical dimension. -/
theorem eq2_mem_dim : d_M_r = (Dim.mul d_R_on d_x_w) := by decide
theorem eq2_mem_term1 : Dim.one = d_x_w := by decide
theorem eq2_mem_term2 : (Dim.mul d_R_on d_x_w) = (Dim.mul d_R_off Dim.one) := by decide

/-! ## 3. Drift of the doped-region boundary

    d(x_w,t) = mu_v*R_on/D_f^2*i_m*F_w
-/
/-- Both sides of "Drift of the doped-region boundary" carry the same physical dimension. -/
theorem eq3_state_dim : (Dim.div d_x_w d_t) = (Dim.mul (Dim.mul (Dim.div (Dim.mul d_mu_v d_R_on) (Dim.pow d_D_f 2 1)) d_i_m) d_F_w) := by decide
/-- The denominator `D_f^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_state_reg1 (D_f : ℝ) (hD_f : 0 < D_f) : D_f ^ 2 ≠ 0 := by positivity

/-! ## 4. Window function

    F_w = 1 - (2*x_w - 1)^(2*p_w)
-/
/-- Both sides of "Window function" carry the same physical dimension. -/
theorem eq4_win_dim : d_F_w = Dim.one := by decide
theorem eq4_win_term1 : (Dim.mul Dim.one d_x_w) = Dim.one := by decide
theorem eq4_win_term2 : Dim.one = Dim.one := by decide

/-! ## 5. Applied voltage

    v_m = V_0*sin(2*pi*f_d*t)
-/
/-- Both sides of "Applied voltage" carry the same physical dimension. -/
theorem eq5_drive_dim : d_v_m = (Dim.mul d_V_0 Dim.one) := by decide
theorem eq5_drive_term1 : (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_d) d_t) = Dim.one := by decide

/-! ## 6. Charge to cross the film

    Q_D = D_f^2/(mu_v*R_on)
-/
/-- Both sides of "Charge to cross the film" carry the same physical dimension. -/
theorem eq6_qd_dim : d_Q_D = (Dim.div (Dim.pow d_D_f 2 1) (Dim.mul d_mu_v d_R_on)) := by decide
/-- The denominator `mu_v * R_on` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_qd_reg1 (mu_v R_on : ℝ) (hmu_v : 0 < mu_v) (hR_on : 0 < R_on) : mu_v * R_on ≠ 0 := by positivity

/-! ## 7. Flux to switch fully

    phi_D = Q_D*(R_on + R_off)/2
-/
/-- Both sides of "Flux to switch fully" carry the same physical dimension. -/
theorem eq7_phid_dim : d_phi_D = (Dim.div (Dim.mul d_Q_D d_R_on) Dim.one) := by decide
theorem eq7_phid_term1 : d_R_on = d_R_off := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_phid_reg1  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 8. Characteristic frequency

    f_c = V_0/(pi*phi_D)
-/
/-- Both sides of "Characteristic frequency" carry the same physical dimension. -/
theorem eq8_fc_dim : d_f_c = (Dim.div d_V_0 (Dim.mul Dim.one d_phi_D)) := by decide
/-- The denominator `pi * phi_D` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_fc_reg1 (phi_D : ℝ) (hphi_D : 0 < phi_D) : Real.pi * phi_D ≠ 0 := by positivity

end Bespoke
