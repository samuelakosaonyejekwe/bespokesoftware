import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Piezo-driven Helmholtz synthetic-jet actuator

Machine-checkable statements for this investigation (helmholtz-synthetic-jet).
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
def d_A_o : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Orifice area [m^2]
def d_D_c : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Cavity (diaphragm) diameter [mm]
def d_F_j : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Jet-formation parameter Re/S² [1]
def d_H_c : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Cavity depth [mm]
def d_L_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Stroke length [m]
def d_L_eff : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Effective neck length [m]
def d_P_e : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Electrical power [W]
def d_P_f : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Fluidic power [W]
def d_Q_d : Dim := ⟨0, 36, -12, 0, 0, 0, 0⟩  -- Diaphragm volume-velocity amplitude [m^3/s]
def d_Re_j : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Jet Reynolds number [1]
def d_S_t : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Stokes number [1]
def d_T_j : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Time-mean thrust [N]
def d_U_o : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Orifice velocity amplitude [m/s]
def d_V_c : Dim := ⟨0, 36, 0, 0, 0, 0, 0⟩  -- Cavity volume [m^3]
def d_c_s : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of sound [m/s]
def d_dV : Dim := ⟨0, 36, 0, 0, 0, 0, 0⟩  -- Volume displaced by the diaphragm [m^3]
def d_d_o : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Orifice diameter [mm]
def d_delta_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Diaphragm centre displacement amplitude [um]
def d_eta_e : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Electrical-to-fluidic efficiency [%]
def d_f_H : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Helmholtz frequency [Hz]
def d_f_d : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Drive frequency [Hz]
def d_l_o : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Orifice (neck) length [mm]
def d_nu : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Kinematic viscosity [m^2/s]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Fluid density [kg/m^3]

/-! ## 1. Orifice area

    A_o = pi*d_o^2/4
-/
/-- Both sides of "Orifice area" carry the same physical dimension. -/
theorem eq1_ao_dim : d_A_o = (Dim.div (Dim.mul Dim.one (Dim.pow d_d_o 2 1)) Dim.one) := by decide
/-- The denominator `4` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_ao_reg1  : (4 : ℝ) ≠ 0 := by positivity

/-! ## 2. Cavity volume

    V_c = pi*D_c^2/4*H_c
-/
/-- Both sides of "Cavity volume" carry the same physical dimension. -/
theorem eq2_vc_dim : d_V_c = (Dim.mul (Dim.div (Dim.mul Dim.one (Dim.pow d_D_c 2 1)) Dim.one) d_H_c) := by decide
/-- The denominator `4` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_vc_reg1  : (4 : ℝ) ≠ 0 := by positivity

/-! ## 3. Effective neck length

    L_eff = l_o + 0.85*d_o
-/
/-- Both sides of "Effective neck length" carry the same physical dimension. -/
theorem eq3_leff_dim : d_L_eff = d_l_o := by decide
theorem eq3_leff_term1 : d_l_o = (Dim.mul Dim.one d_d_o) := by decide

/-! ## 4. Helmholtz frequency

    f_H = c_s/(2*pi)*sqrt(A_o/(V_c*L_eff))
-/
/-- Both sides of "Helmholtz frequency" carry the same physical dimension. -/
theorem eq4_fh_dim : d_f_H = (Dim.mul (Dim.div d_c_s (Dim.mul Dim.one Dim.one)) (Dim.pow (Dim.div d_A_o (Dim.mul d_V_c d_L_eff)) 1 2)) := by decide
/-- The denominator `2 * pi` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_fh_reg1  : (2 : ℝ) * Real.pi ≠ 0 := by positivity
/-- The denominator `V_c * L_eff` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_fh_reg2 (V_c L_eff : ℝ) (hV_c : 0 < V_c) (hL_eff : 0 < L_eff) : V_c * L_eff ≠ 0 := by positivity
/-- Domain condition for `A_o / (V_c * L_eff)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_fh_cond3 (A_o V_c L_eff : ℝ) (hdom : 0 ≤ A_o / (V_c * L_eff)) : 0 ≤ A_o / (V_c * L_eff) := hdom

/-! ## 5. Volume displaced, clamped plate

    dV = pi*D_c^2*delta_0/12
-/
/-- Both sides of "Volume displaced, clamped plate" carry the same physical dimension. -/
theorem eq5_dv_dim : d_dV = (Dim.div (Dim.mul (Dim.mul Dim.one (Dim.pow d_D_c 2 1)) d_delta_0) Dim.one) := by decide
/-- The denominator `12` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_dv_reg1  : (12 : ℝ) ≠ 0 := by positivity

/-! ## 6. Diaphragm volume velocity

    Q_d = 2*pi*f_d*dV
-/
/-- Both sides of "Diaphragm volume velocity" carry the same physical dimension. -/
theorem eq6_qd_dim : d_Q_d = (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_d) d_dV) := by decide

/-! ## 7. Orifice velocity amplitude

    U_o = Q_d/A_o
-/
/-- Both sides of "Orifice velocity amplitude" carry the same physical dimension. -/
theorem eq7_uo_dim : d_U_o = (Dim.div d_Q_d d_A_o) := by decide
/-- Domain condition for `A_o`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_uo_cond1 (A_o : ℝ) (hdom : A_o ≠ 0) : A_o ≠ 0 := hdom

/-! ## 8. Stroke length

    L_0 = U_o/(pi*f_d)
-/
/-- Both sides of "Stroke length" carry the same physical dimension. -/
theorem eq8_l0_dim : d_L_0 = (Dim.div d_U_o (Dim.mul Dim.one d_f_d)) := by decide
/-- The denominator `pi * f_d` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_l0_reg1 (f_d : ℝ) (hf_d : 0 < f_d) : Real.pi * f_d ≠ 0 := by positivity

/-! ## 9. Jet Reynolds number

    Re_j = 2*U_o*d_o/(pi*nu)
-/
/-- Both sides of "Jet Reynolds number" carry the same physical dimension. -/
theorem eq9_re_dim : d_Re_j = (Dim.div (Dim.mul (Dim.mul Dim.one d_U_o) d_d_o) (Dim.mul Dim.one d_nu)) := by decide
/-- The denominator `pi * nu` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_re_reg1 (nu : ℝ) (hnu : 0 < nu) : Real.pi * nu ≠ 0 := by positivity

/-! ## 10. Stokes number

    S_t = sqrt(2*pi*f_d*d_o^2/nu)
-/
/-- Both sides of "Stokes number" carry the same physical dimension. -/
theorem eq10_st_dim : d_S_t = (Dim.pow (Dim.div (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_d) (Dim.pow d_d_o 2 1)) d_nu) 1 2) := by decide
/-- The denominator `nu` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_st_reg1 (nu : ℝ) (hnu : 0 < nu) : nu ≠ 0 := by positivity
/-- The argument `2 * pi * f_d * d_o^2 / nu` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_st_reg2 (f_d d_o nu : ℝ) (hf_d : 0 < f_d) (hd_o : 0 < d_o) (hnu : 0 < nu) : 0 ≤ (2 : ℝ) * Real.pi * f_d * d_o ^ 2 / nu := by positivity

/-! ## 11. Jet-formation parameter

    F_j = Re_j/S_t^2
-/
/-- Both sides of "Jet-formation parameter" carry the same physical dimension. -/
theorem eq11_fj_dim : d_F_j = (Dim.div d_Re_j (Dim.pow d_S_t 2 1)) := by decide
/-- The denominator `S_t^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_fj_reg1 (S_t : ℝ) (hS_t : 0 < S_t) : S_t ^ 2 ≠ 0 := by positivity

/-! ## 12. Time-mean thrust

    T_j = rho*A_o*U_o^2/4
-/
/-- Both sides of "Time-mean thrust" carry the same physical dimension. -/
theorem eq12_thr_dim : d_T_j = (Dim.div (Dim.mul (Dim.mul d_rho d_A_o) (Dim.pow d_U_o 2 1)) Dim.one) := by decide
/-- The denominator `4` stays away from its singular set whenever the quantities are positive. -/
theorem eq12_thr_reg1  : (4 : ℝ) ≠ 0 := by positivity

/-! ## 13. Fluidic power

    P_f = rho*A_o*U_o^3/(3*pi)
-/
/-- Both sides of "Fluidic power" carry the same physical dimension. -/
theorem eq13_pf_dim : d_P_f = (Dim.div (Dim.mul (Dim.mul d_rho d_A_o) (Dim.pow d_U_o 3 1)) (Dim.mul Dim.one Dim.one)) := by decide
/-- The denominator `3 * pi` stays away from its singular set whenever the quantities are positive. -/
theorem eq13_pf_reg1  : (3 : ℝ) * Real.pi ≠ 0 := by positivity

/-! ## 14. Electrical power

    P_e = P_f/eta_e
-/
/-- Both sides of "Electrical power" carry the same physical dimension. -/
theorem eq14_pe_dim : d_P_e = (Dim.div d_P_f d_eta_e) := by decide
/-- The denominator `eta_e` stays away from its singular set whenever the quantities are positive. -/
theorem eq14_pe_reg1 (eta_e : ℝ) (heta_e : 0 < eta_e) : eta_e ≠ 0 := by positivity

end Bespoke
