import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A world with different constants of nature

Machine-checkable statements for this investigation (varying-constants-world).
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
def d_E_R : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Hydrogen binding energy [J]
def d_G : Dim := ⟨-12, 36, -24, 0, 0, 0, 0⟩  -- Newtonian constant of gravitation [m^3/(kg s^2)]
def d_M_Ch : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Chandrasekhar mass [kg]
def d_M_sun : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Solar mass, as a fixed number of kilograms [kg]
def d_Z_max : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Largest stable nuclear charge (heuristic) [1]
def d_a_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Bohr radius [m]
def d_alpha : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fine-structure constant [1]
def d_alpha_G : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Gravitational coupling of two protons [1]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light in vacuum [m/s]
def d_e_c : Dim := ⟨0, 0, 12, 12, 0, 0, 0⟩  -- Elementary charge [C]
def d_eps_0 : Dim := ⟨-12, -36, 48, 24, 0, 0, 0⟩  -- Vacuum permittivity [F/m]
def d_hbar : Dim := ⟨12, 24, -12, 0, 0, 0, 0⟩  -- Reduced Planck constant [J s]
def d_k_Ch : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Numerical factor in the Chandrasekhar mass [1]
def d_l_P : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Planck length [m]
def d_lambda_C : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Compton wavelength [m]
def d_m_P : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Planck mass [kg]
def d_m_e : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Electron mass [kg]
def d_m_p : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Proton mass [kg]
def d_r_S : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Schwarzschild radius of a solar mass [m]
def d_t_P : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Planck time [s]

/-! ## 1. Fine-structure constant

    alpha = e_c^2/(4*pi*eps_0*hbar*c)
-/
/-- Both sides of "Fine-structure constant" carry the same physical dimension. -/
theorem eq1_alpha_dim : d_alpha = (Dim.div (Dim.pow d_e_c 2 1) (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_eps_0) d_hbar) d_c)) := by decide
/-- The denominator `4 * pi * eps_0 * hbar * c` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_alpha_reg1 (eps_0 hbar c : ℝ) (heps_0 : 0 < eps_0) (hhbar : 0 < hbar) (hc : 0 < c) : (4 : ℝ) * Real.pi * eps_0 * hbar * c ≠ 0 := by positivity

/-! ## 2. Bohr radius

    a_0 = 4*pi*eps_0*hbar^2/(m_e*e_c^2)
-/
/-- Both sides of "Bohr radius" carry the same physical dimension. -/
theorem eq2_a0_dim : d_a_0 = (Dim.div (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_eps_0) (Dim.pow d_hbar 2 1)) (Dim.mul d_m_e (Dim.pow d_e_c 2 1))) := by decide
/-- The denominator `m_e * e_c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_a0_reg1 (m_e e_c : ℝ) (hm_e : 0 < m_e) (he_c : 0 < e_c) : m_e * e_c ^ 2 ≠ 0 := by positivity

/-! ## 3. Hydrogen binding energy

    E_R = m_e*c^2*alpha^2/2
-/
/-- Both sides of "Hydrogen binding energy" carry the same physical dimension. -/
theorem eq3_ER_dim : d_E_R = (Dim.div (Dim.mul (Dim.mul d_m_e (Dim.pow d_c 2 1)) (Dim.pow d_alpha 2 1)) Dim.one) := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_ER_reg1  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 4. Compton wavelength

    lambda_C = 2*pi*hbar/(m_e*c)
-/
/-- Both sides of "Compton wavelength" carry the same physical dimension. -/
theorem eq4_lc_dim : d_lambda_C = (Dim.div (Dim.mul (Dim.mul Dim.one Dim.one) d_hbar) (Dim.mul d_m_e d_c)) := by decide
/-- The denominator `m_e * c` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_lc_reg1 (m_e c : ℝ) (hm_e : 0 < m_e) (hc : 0 < c) : m_e * c ≠ 0 := by positivity

/-! ## 5. Planck length

    l_P = sqrt(hbar*G/c^3)
-/
/-- Both sides of "Planck length" carry the same physical dimension. -/
theorem eq5_lp_dim : d_l_P = (Dim.pow (Dim.div (Dim.mul d_hbar d_G) (Dim.pow d_c 3 1)) 1 2) := by decide
/-- The denominator `c^3` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_lp_reg1 (c : ℝ) (hc : 0 < c) : c ^ 3 ≠ 0 := by positivity
/-- The argument `hbar * G / c^3` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_lp_reg2 (hbar G c : ℝ) (hhbar : 0 < hbar) (hG : 0 < G) (hc : 0 < c) : 0 ≤ hbar * G / c ^ 3 := by positivity

/-! ## 6. Planck time

    t_P = sqrt(hbar*G/c^5)
-/
/-- Both sides of "Planck time" carry the same physical dimension. -/
theorem eq6_tp_dim : d_t_P = (Dim.pow (Dim.div (Dim.mul d_hbar d_G) (Dim.pow d_c 5 1)) 1 2) := by decide
/-- The denominator `c^5` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_tp_reg1 (c : ℝ) (hc : 0 < c) : c ^ 5 ≠ 0 := by positivity
/-- The argument `hbar * G / c^5` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_tp_reg2 (hbar G c : ℝ) (hhbar : 0 < hbar) (hG : 0 < G) (hc : 0 < c) : 0 ≤ hbar * G / c ^ 5 := by positivity

/-! ## 7. Planck mass

    m_P = sqrt(hbar*c/G)
-/
/-- Both sides of "Planck mass" carry the same physical dimension. -/
theorem eq7_mp_dim : d_m_P = (Dim.pow (Dim.div (Dim.mul d_hbar d_c) d_G) 1 2) := by decide
/-- The denominator `G` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_mp_reg1 (G : ℝ) (hG : 0 < G) : G ≠ 0 := by positivity
/-- The argument `hbar * c / G` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_mp_reg2 (hbar c G : ℝ) (hhbar : 0 < hbar) (hc : 0 < c) (hG : 0 < G) : 0 ≤ hbar * c / G := by positivity

/-! ## 8. Gravitational coupling

    alpha_G = G*m_p^2/(hbar*c)
-/
/-- Both sides of "Gravitational coupling" carry the same physical dimension. -/
theorem eq8_ag_dim : d_alpha_G = (Dim.div (Dim.mul d_G (Dim.pow d_m_p 2 1)) (Dim.mul d_hbar d_c)) := by decide
/-- The denominator `hbar * c` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_ag_reg1 (hbar c : ℝ) (hhbar : 0 < hbar) (hc : 0 < c) : hbar * c ≠ 0 := by positivity

/-! ## 9. Chandrasekhar mass

    M_Ch = k_Ch*(hbar*c/G)^(3/2)/m_p^2
-/
/-- Both sides of "Chandrasekhar mass" carry the same physical dimension. -/
theorem eq9_mch_dim : d_M_Ch = (Dim.div (Dim.mul d_k_Ch (Dim.pow (Dim.div (Dim.mul d_hbar d_c) d_G) 3 2)) (Dim.pow d_m_p 2 1)) := by decide
/-- The denominator `G` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_mch_reg1 (G : ℝ) (hG : 0 < G) : G ≠ 0 := by positivity
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_mch_reg2  : (2 : ℝ) ≠ 0 := by positivity
/-- The denominator `m_p^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_mch_reg3 (m_p : ℝ) (hm_p : 0 < m_p) : m_p ^ 2 ≠ 0 := by positivity

/-! ## 10. Schwarzschild radius of a solar mass

    r_S = 2*G*M_sun/c^2
-/
/-- Both sides of "Schwarzschild radius of a solar mass" carry the same physical dimension. -/
theorem eq10_rs_dim : d_r_S = (Dim.div (Dim.mul (Dim.mul Dim.one d_G) d_M_sun) (Dim.pow d_c 2 1)) := by decide
/-- The denominator `c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_rs_reg1 (c : ℝ) (hc : 0 < c) : c ^ 2 ≠ 0 := by positivity

/-! ## 11. Largest stable nuclear charge

    Z_max = 1/alpha
-/
/-- Both sides of "Largest stable nuclear charge" carry the same physical dimension. -/
theorem eq11_zmax_dim : d_Z_max = (Dim.div Dim.one d_alpha) := by decide
/-- The denominator `alpha` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_zmax_reg1 (alpha : ℝ) (halpha : 0 < alpha) : alpha ≠ 0 := by positivity

end Bespoke
