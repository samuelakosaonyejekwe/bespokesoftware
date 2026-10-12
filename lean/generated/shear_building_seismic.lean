import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Shear building under ground motion

Machine-checkable statements for this investigation (shear-building-seismic).
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
def d_Delta_1 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Drift of the first storey [m]
def d_Delta_i : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Drift of storey i [m]
def d_Gamma_n : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Modal participation factor [1]
def d_K_m : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Stiffness matrix entry [N/m]
def d_L_n : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Modal excitation factor φᵀM1 [kg]
def d_M_m : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass matrix entry [kg]
def d_M_n : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Modal mass φᵀMφ [kg]
def d_V_b : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Base shear [N]
def d_a_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Peak ground acceleration [g0]
def d_a_gt : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Ground acceleration [m/s^2]
def d_f_g : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Frequency of the ground motion [Hz]
def d_k_s : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Lateral stiffness of each storey [MN/m]
def d_m_s : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass of each floor [t]
def d_n_s : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of storeys [1]
def d_omega_1 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Fundamental angular frequency [1/s]
def d_omega_n : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Natural angular frequency of mode n [1/s]
def d_phi_n : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Mode shape n [1]
def d_q_n : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Modal coordinate [m]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_u_i : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Displacement of floor i relative to the ground [m]
def d_u_im : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Displacement of the floor below [m]
def d_zeta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Damping ratio [1]
def d_zeta_n : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Damping ratio of mode n [1]

/-! ## 1. Free-vibration eigenproblem

    K_m*phi_n = omega_n^2*M_m*phi_n
-/
/-- Both sides of "Free-vibration eigenproblem" carry the same physical dimension. -/
theorem eq1_eig_dim : (Dim.mul d_K_m d_phi_n) = (Dim.mul (Dim.mul (Dim.pow d_omega_n 2 1) d_M_m) d_phi_n) := by decide

/-! ## 2. Fundamental frequency of a uniform shear building

    omega_1 = 2*sqrt(k_s/m_s)*sin(pi/(2*(2*n_s + 1)))
-/
/-- Both sides of "Fundamental frequency of a uniform shear building" carry the same physical dimension. -/
theorem eq2_w1_dim : d_omega_1 = (Dim.mul (Dim.mul Dim.one (Dim.pow (Dim.div d_k_s d_m_s) 1 2)) Dim.one) := by decide
theorem eq2_w1_term1 : (Dim.mul Dim.one d_n_s) = Dim.one := by decide
theorem eq2_w1_term2 : (Dim.div Dim.one (Dim.mul Dim.one (Dim.mul Dim.one d_n_s))) = Dim.one := by decide
/-- The denominator `m_s` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_w1_reg1 (m_s : ℝ) (hm_s : 0 < m_s) : m_s ≠ 0 := by positivity
/-- The argument `k_s / m_s` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_w1_reg2 (k_s m_s : ℝ) (hk_s : 0 < k_s) (hm_s : 0 < m_s) : 0 ≤ k_s / m_s := by positivity
/-- The denominator `2 * (2 * n_s + 1)` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_w1_reg3 (n_s : ℝ) (hn_s : 0 < n_s) : (2 : ℝ) * ((2 : ℝ) * n_s + (1 : ℝ)) ≠ 0 := by positivity

/-! ## 3. Participation factor

    Gamma_n = L_n/M_n
-/
/-- Both sides of "Participation factor" carry the same physical dimension. -/
theorem eq3_gam_dim : d_Gamma_n = (Dim.div d_L_n d_M_n) := by decide
/-- Domain condition for `M_n`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_gam_cond1 (M_n : ℝ) (hdom : M_n ≠ 0) : M_n ≠ 0 := hdom

/-! ## 4. Modal damping

    zeta_n = zeta
-/
/-- Both sides of "Modal damping" carry the same physical dimension. -/
theorem eq4_zn_dim : d_zeta_n = d_zeta := by decide

/-! ## 5. Ground acceleration

    a_gt = a_g*sin(2*pi*f_g*t)
-/
/-- Both sides of "Ground acceleration" carry the same physical dimension. -/
theorem eq5_ag_dim : d_a_gt = (Dim.mul d_a_g Dim.one) := by decide
theorem eq5_ag_term1 : (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_g) d_t) = Dim.one := by decide

/-! ## 6. Modal equation of motion

    d2(q_n,t) + 2*zeta_n*omega_n*d(q_n,t) + omega_n^2*q_n = -Gamma_n*a_gt
-/
/-- Both sides of "Modal equation of motion" carry the same physical dimension. -/
theorem eq6_modal_dim : (Dim.div d_q_n (Dim.pow d_t 2 1)) = (Dim.mul d_Gamma_n d_a_gt) := by decide
theorem eq6_modal_term1 : (Dim.div d_q_n (Dim.pow d_t 2 1)) = (Dim.mul (Dim.mul (Dim.mul Dim.one d_zeta_n) d_omega_n) (Dim.div d_q_n d_t)) := by decide
theorem eq6_modal_term2 : (Dim.div d_q_n (Dim.pow d_t 2 1)) = (Dim.mul (Dim.pow d_omega_n 2 1) d_q_n) := by decide

/-! ## 7. Modal superposition (summed over all modes n)

    u_i = phi_n*q_n
-/
/-- Both sides of "Modal superposition (summed over all modes n)" carry the same physical dimension. -/
theorem eq7_sup_dim : d_u_i = (Dim.mul d_phi_n d_q_n) := by decide

/-! ## 8. Storey drift

    Delta_i = u_i - u_im
-/
/-- Both sides of "Storey drift" carry the same physical dimension. -/
theorem eq8_dr_dim : d_Delta_i = d_u_i := by decide
theorem eq8_dr_term1 : d_u_i = d_u_im := by decide

/-! ## 9. Base shear

    V_b = k_s*Delta_1
-/
/-- Both sides of "Base shear" carry the same physical dimension. -/
theorem eq9_vb_dim : d_V_b = (Dim.mul d_k_s d_Delta_1) := by decide

end Bespoke
