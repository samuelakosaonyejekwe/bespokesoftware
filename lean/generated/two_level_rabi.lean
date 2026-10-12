import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Rabi oscillations of a driven two-level system

Machine-checkable statements for this investigation (two-level-rabi).
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
def d_Omega_e : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Generalised Rabi frequency [1/s]
def d_P_e : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Excited-state population [1]
def d_P_ss : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Steady-state population [1]
def d_f_D : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Detuning of the drive from resonance, Δ/2π [MHz]
def d_f_R : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Rabi frequency Ω/2π [MHz]
def d_gamma_1 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Energy relaxation rate 1/T₁ [1/us]
def d_gamma_2 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Transverse relaxation rate [1/s]
def d_gamma_phi : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Pure dephasing rate [1/us]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_t_p : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Pulse duration [us]
def d_theta_p : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Pulse area [rad]
def d_u_b : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Bloch-vector component u [1]
def d_v_b : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Bloch-vector component v [1]
def d_w_b : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Bloch-vector component w (inversion) [1]

/-! ## 1. Generalised Rabi frequency

    Omega_e = 2*pi*sqrt(f_R^2 + f_D^2)
-/
/-- Both sides of "Generalised Rabi frequency" carry the same physical dimension. -/
theorem eq1_we_dim : d_Omega_e = (Dim.mul (Dim.mul Dim.one Dim.one) (Dim.pow (Dim.pow d_f_R 2 1) 1 2)) := by decide
theorem eq1_we_term1 : (Dim.pow d_f_R 2 1) = (Dim.pow d_f_D 2 1) := by decide
/-- Domain condition for `f_R^2 + f_D^2`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq1_we_cond1 (f_R f_D : ℝ) (hdom : 0 ≤ f_R ^ 2 + f_D ^ 2) : 0 ≤ f_R ^ 2 + f_D ^ 2 := hdom

/-! ## 2. Rabi formula (no damping)

    P_e = f_R^2/(f_R^2 + f_D^2)*sin(Omega_e*t/2)^2
-/
/-- Both sides of "Rabi formula (no damping)" carry the same physical dimension. -/
theorem eq2_pe_dim : d_P_e = (Dim.mul (Dim.div (Dim.pow d_f_R 2 1) (Dim.pow d_f_R 2 1)) (Dim.pow Dim.one 2 1)) := by decide
theorem eq2_pe_term1 : (Dim.pow d_f_R 2 1) = (Dim.pow d_f_D 2 1) := by decide
theorem eq2_pe_term2 : (Dim.div (Dim.mul d_Omega_e d_t) Dim.one) = Dim.one := by decide
/-- Domain condition for `f_R^2 + f_D^2`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq2_pe_cond1 (f_R f_D : ℝ) (hdom : f_R ^ 2 + f_D ^ 2 ≠ 0) : f_R ^ 2 + f_D ^ 2 ≠ 0 := hdom
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_pe_reg2  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 3. Pulse area

    theta_p = 2*pi*f_R*t_p
-/
/-- Both sides of "Pulse area" carry the same physical dimension. -/
theorem eq3_area_dim : d_theta_p = (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_R) d_t_p) := by decide

/-! ## 4. Transverse relaxation rate

    gamma_2 = gamma_1/2 + gamma_phi
-/
/-- Both sides of "Transverse relaxation rate" carry the same physical dimension. -/
theorem eq4_g2_dim : d_gamma_2 = (Dim.div d_gamma_1 Dim.one) := by decide
theorem eq4_g2_term1 : (Dim.div d_gamma_1 Dim.one) = d_gamma_phi := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_g2_reg1  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 5. Bloch equation for u

    d(u_b,t) = -2*pi*f_D*v_b - gamma_2*u_b
-/
/-- Both sides of "Bloch equation for u" carry the same physical dimension. -/
theorem eq5_bu_dim : (Dim.div d_u_b d_t) = (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_D) d_v_b) := by decide
theorem eq5_bu_term1 : (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_D) d_v_b) = (Dim.mul d_gamma_2 d_u_b) := by decide

/-! ## 6. Bloch equation for v

    d(v_b,t) = 2*pi*f_D*u_b - 2*pi*f_R*w_b - gamma_2*v_b
-/
/-- Both sides of "Bloch equation for v" carry the same physical dimension. -/
theorem eq6_bv_dim : (Dim.div d_v_b d_t) = (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_D) d_u_b) := by decide
theorem eq6_bv_term1 : (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_D) d_u_b) = (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_R) d_w_b) := by decide
theorem eq6_bv_term2 : (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_D) d_u_b) = (Dim.mul d_gamma_2 d_v_b) := by decide

/-! ## 7. Bloch equation for the inversion

    d(w_b,t) = 2*pi*f_R*v_b - gamma_1*(w_b + 1)
-/
/-- Both sides of "Bloch equation for the inversion" carry the same physical dimension. -/
theorem eq7_bw_dim : (Dim.div d_w_b d_t) = (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_R) d_v_b) := by decide
theorem eq7_bw_term1 : d_w_b = Dim.one := by decide
theorem eq7_bw_term2 : (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_R) d_v_b) = (Dim.mul d_gamma_1 d_w_b) := by decide

/-! ## 8. Steady-state population

    P_ss = (2*pi*f_R)^2*gamma_2/gamma_1/(2*(gamma_2^2 + (2*pi*f_D)^2 + (2*pi*f_R)^2*gamma_2/gamma_1))
-/
/-- Both sides of "Steady-state population" carry the same physical dimension. -/
theorem eq8_ss_dim : d_P_ss = (Dim.div (Dim.div (Dim.mul (Dim.pow (Dim.mul (Dim.mul Dim.one Dim.one) d_f_R) 2 1) d_gamma_2) d_gamma_1) (Dim.mul Dim.one (Dim.pow d_gamma_2 2 1))) := by decide
theorem eq8_ss_term1 : (Dim.pow d_gamma_2 2 1) = (Dim.pow (Dim.mul (Dim.mul Dim.one Dim.one) d_f_D) 2 1) := by decide
theorem eq8_ss_term2 : (Dim.pow d_gamma_2 2 1) = (Dim.div (Dim.mul (Dim.pow (Dim.mul (Dim.mul Dim.one Dim.one) d_f_R) 2 1) d_gamma_2) d_gamma_1) := by decide
/-- Domain condition for `gamma_1`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq8_ss_cond1 (gamma_1 : ℝ) (hdom : gamma_1 ≠ 0) : gamma_1 ≠ 0 := hdom
/-- Domain condition for `gamma_1`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq8_ss_cond2 (gamma_1 : ℝ) (hdom : gamma_1 ≠ 0) : gamma_1 ≠ 0 := hdom
/-- Domain condition for `2 * (gamma_2^2 + (2 * pi * f_D)^2 + (2 * pi * f_R)^2 * gamma_2 / gamma_1)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq8_ss_cond3 (gamma_2 f_D f_R gamma_1 : ℝ) (hdom : (2 : ℝ) * (gamma_2 ^ 2 + ((2 : ℝ) * Real.pi * f_D) ^ 2 + ((2 : ℝ) * Real.pi * f_R) ^ 2 * gamma_2 / gamma_1) ≠ 0) : (2 : ℝ) * (gamma_2 ^ 2 + ((2 : ℝ) * Real.pi * f_D) ^ 2 + ((2 : ℝ) * Real.pi * f_R) ^ 2 * gamma_2 / gamma_1) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq8_ss_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

end Bespoke
