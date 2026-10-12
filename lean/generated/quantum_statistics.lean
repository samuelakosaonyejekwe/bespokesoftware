import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Quantum statistics of ideal gases

Machine-checkable statements for this investigation (quantum-statistics).
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
def d_E_F : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Fermi energy [J]
def d_E_s : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Single-particle energy [J]
def d_T_F : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Fermi temperature [K]
def d_T_b : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Temperature of the Bose gas [uK]
def d_T_c : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Bose–Einstein condensation temperature [K]
def d_T_x : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Temperature [K]
def d_f_0 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Condensate fraction [1]
def d_f_BE : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Bose–Einstein occupation [1]
def d_f_FD : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fermi–Dirac occupation [1]
def d_f_MB : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Maxwell–Boltzmann occupation [1]
def d_hbar : Dim := ⟨12, 24, -12, 0, 0, 0, 0⟩  -- Reduced Planck constant [J s]
def d_k_B : Dim := ⟨12, 24, -24, 0, -12, 0, 0⟩  -- Boltzmann constant [J/K]
def d_lambda_T : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Thermal de Broglie wavelength [m]
def d_m_b : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass of a boson [u]
def d_m_e : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Electron mass [kg]
def d_m_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Mass of a fermion in electron masses [1]
def d_mu_c : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Chemical potential [J]
def d_n_b : Dim := ⟨0, -36, 0, 0, 0, 0, 0⟩  -- Number density of the Bose gas [1/cm^3]
def d_n_f : Dim := ⟨0, -36, 0, 0, 0, 0, 0⟩  -- Number density of the Fermi gas [1/m^3]
def d_zeta_32 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Riemann zeta function at 3/2 [1]

/-! ## 1. Bose–Einstein distribution

    f_BE = 1/(exp((E_s - mu_c)/(k_B*T_x)) - 1)
-/
/-- Both sides of "Bose–Einstein distribution" carry the same physical dimension. -/
theorem eq1_be_dim : d_f_BE = (Dim.div Dim.one Dim.one) := by decide
theorem eq1_be_term1 : d_E_s = d_mu_c := by decide
theorem eq1_be_term2 : (Dim.div d_E_s (Dim.mul d_k_B d_T_x)) = Dim.one := by decide
theorem eq1_be_term3 : Dim.one = Dim.one := by decide
/-- Domain condition for `k_B * T_x`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_be_cond1 (k_B T_x : ℝ) (hdom : k_B * T_x ≠ 0) : k_B * T_x ≠ 0 := hdom
/-- Domain condition for `exp((E_s - mu_c) / (k_B * T_x)) - 1`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_be_cond2 (E_s mu_c k_B T_x : ℝ) (hdom : Real.exp ((E_s - mu_c) / (k_B * T_x)) - (1 : ℝ) ≠ 0) : Real.exp ((E_s - mu_c) / (k_B * T_x)) - (1 : ℝ) ≠ 0 := hdom

/-! ## 2. Fermi–Dirac distribution

    f_FD = 1/(exp((E_s - mu_c)/(k_B*T_x)) + 1)
-/
/-- Both sides of "Fermi–Dirac distribution" carry the same physical dimension. -/
theorem eq2_fd_dim : d_f_FD = (Dim.div Dim.one Dim.one) := by decide
theorem eq2_fd_term1 : d_E_s = d_mu_c := by decide
theorem eq2_fd_term2 : (Dim.div d_E_s (Dim.mul d_k_B d_T_x)) = Dim.one := by decide
theorem eq2_fd_term3 : Dim.one = Dim.one := by decide
/-- Domain condition for `k_B * T_x`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_fd_cond1 (k_B T_x : ℝ) (hdom : k_B * T_x ≠ 0) : k_B * T_x ≠ 0 := hdom
/-- Domain condition for `exp((E_s - mu_c) / (k_B * T_x)) + 1`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_fd_cond2 (E_s mu_c k_B T_x : ℝ) (hdom : Real.exp ((E_s - mu_c) / (k_B * T_x)) + (1 : ℝ) ≠ 0) : Real.exp ((E_s - mu_c) / (k_B * T_x)) + (1 : ℝ) ≠ 0 := hdom

/-! ## 3. Maxwell–Boltzmann distribution

    f_MB = exp(-(E_s - mu_c)/(k_B*T_x))
-/
/-- Both sides of "Maxwell–Boltzmann distribution" carry the same physical dimension. -/
theorem eq3_mb_dim : d_f_MB = Dim.one := by decide
theorem eq3_mb_term1 : d_E_s = d_mu_c := by decide
theorem eq3_mb_term2 : (Dim.div d_E_s (Dim.mul d_k_B d_T_x)) = Dim.one := by decide
/-- Domain condition for `k_B * T_x`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_mb_cond1 (k_B T_x : ℝ) (hdom : k_B * T_x ≠ 0) : k_B * T_x ≠ 0 := hdom

/-! ## 4. Thermal de Broglie wavelength of the bosons

    lambda_T = sqrt(2*pi*hbar^2/(m_b*k_B*T_b))
-/
/-- Both sides of "Thermal de Broglie wavelength of the bosons" carry the same physical dimension. -/
theorem eq4_lam_dim : d_lambda_T = (Dim.pow (Dim.div (Dim.mul (Dim.mul Dim.one Dim.one) (Dim.pow d_hbar 2 1)) (Dim.mul (Dim.mul d_m_b d_k_B) d_T_b)) 1 2) := by decide
/-- The denominator `m_b * k_B * T_b` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_lam_reg1 (m_b k_B T_b : ℝ) (hm_b : 0 < m_b) (hk_B : 0 < k_B) (hT_b : 0 < T_b) : m_b * k_B * T_b ≠ 0 := by positivity
/-- The argument `2 * pi * hbar^2 / (m_b * k_B * T_b)` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_lam_reg2 (hbar m_b k_B T_b : ℝ) (hhbar : 0 < hbar) (hm_b : 0 < m_b) (hk_B : 0 < k_B) (hT_b : 0 < T_b) : 0 ≤ (2 : ℝ) * Real.pi * hbar ^ 2 / (m_b * k_B * T_b) := by positivity

/-! ## 5. Condensation temperature of a uniform gas

    T_c = 2*pi*hbar^2/(m_b*k_B)*(n_b/zeta_32)^(2/3)
-/
/-- Both sides of "Condensation temperature of a uniform gas" carry the same physical dimension. -/
theorem eq5_tc_dim : d_T_c = (Dim.mul (Dim.div (Dim.mul (Dim.mul Dim.one Dim.one) (Dim.pow d_hbar 2 1)) (Dim.mul d_m_b d_k_B)) (Dim.pow (Dim.div d_n_b d_zeta_32) 2 3)) := by decide
/-- The denominator `m_b * k_B` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_tc_reg1 (m_b k_B : ℝ) (hm_b : 0 < m_b) (hk_B : 0 < k_B) : m_b * k_B ≠ 0 := by positivity
/-- Domain condition for `zeta_32`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_tc_cond2 (zeta_32 : ℝ) (hdom : zeta_32 ≠ 0) : zeta_32 ≠ 0 := hdom
/-- The denominator `3` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_tc_reg3  : (3 : ℝ) ≠ 0 := by positivity

/-! ## 6. Condensate fraction

    f_0 = 1 - (T_b/T_c)^(3/2)
-/
/-- Both sides of "Condensate fraction" carry the same physical dimension. -/
theorem eq6_f0_dim : d_f_0 = Dim.one := by decide
theorem eq6_f0_term1 : Dim.one = (Dim.pow (Dim.div d_T_b d_T_c) 3 2) := by decide
/-- The denominator `T_c` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_f0_reg1 (T_c : ℝ) (hT_c : 0 < T_c) : T_c ≠ 0 := by positivity
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_f0_reg2  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 7. Fermi energy

    E_F = hbar^2/(2*m_r*m_e)*(3*pi^2*n_f)^(2/3)
-/
/-- Both sides of "Fermi energy" carry the same physical dimension. -/
theorem eq7_ef_dim : d_E_F = (Dim.mul (Dim.div (Dim.pow d_hbar 2 1) (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e)) (Dim.pow (Dim.mul (Dim.mul Dim.one (Dim.pow Dim.one 2 1)) d_n_f) 2 3)) := by decide
/-- The denominator `2 * m_r * m_e` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_ef_reg1 (m_r m_e : ℝ) (hm_r : 0 < m_r) (hm_e : 0 < m_e) : (2 : ℝ) * m_r * m_e ≠ 0 := by positivity
/-- The denominator `3` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_ef_reg2  : (3 : ℝ) ≠ 0 := by positivity

/-! ## 8. Fermi temperature

    T_F = E_F/k_B
-/
/-- Both sides of "Fermi temperature" carry the same physical dimension. -/
theorem eq8_tf_dim : d_T_F = (Dim.div d_E_F d_k_B) := by decide
/-- The denominator `k_B` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_tf_reg1 (k_B : ℝ) (hk_B : 0 < k_B) : k_B ≠ 0 := by positivity

end Bespoke
