import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Schrödinger's cat and environmental decoherence

Machine-checkable statements for this investigation (schrodinger-cat-decoherence).
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
def d_Gamma : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Decoherence rate [1/s]
def d_Lambda_a : Dim := ⟨0, -24, -12, 0, 0, 0, 0⟩  -- Localisation rate from gas collisions [1/(m^2 s)]
def d_Lambda_p : Dim := ⟨0, -24, -12, 0, 0, 0, 0⟩  -- Localisation rate from thermal photons [1/(m^2 s)]
def d_T : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Temperature of gas and radiation [K]
def d_a : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Radius of the object [um]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light [m/s]
def d_dx : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Separation between the two branches of the superposition [nm]
def d_hbar : Dim := ⟨12, 24, -12, 0, 0, 0, 0⟩  -- Reduced Planck constant [J s]
def d_k_B : Dim := ⟨12, 24, -24, 0, -12, 0, 0⟩  -- Boltzmann constant [J/K]
def d_l_c : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Coherence length of the scattering environment [m]
def d_m_g : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass of a gas molecule [u]
def d_n_g : Dim := ⟨0, -36, 0, 0, 0, 0, 0⟩  -- Number density of the gas [1/m^3]
def d_p : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Gas pressure [Pa]
def d_rho_c : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Off-diagonal element of the density matrix [1]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_tau_D : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Decoherence time [s]
def d_zeta_9 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Riemann zeta function at 9 [1]

/-! ## 1. Decay of the interference term

    d(rho_c,t) = -Gamma*rho_c
-/
/-- Both sides of "Decay of the interference term" carry the same physical dimension. -/
theorem eq1_rho_dim : (Dim.div d_rho_c d_t) = (Dim.mul d_Gamma d_rho_c) := by decide

/-! ## 2. Gas number density

    n_g = p/(k_B*T)
-/
/-- Both sides of "Gas number density" carry the same physical dimension. -/
theorem eq2_ng_dim : d_n_g = (Dim.div d_p (Dim.mul d_k_B d_T)) := by decide
/-- The denominator `k_B * T` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_ng_reg1 (k_B T : ℝ) (hk_B : 0 < k_B) (hT : 0 < T) : k_B * T ≠ 0 := by positivity

/-! ## 3. Localisation rate from gas collisions

    Lambda_a = 8/(3*hbar^2)*n_g*sqrt(2*pi*m_g)*a^2*(k_B*T)^(3/2)
-/
/-- Both sides of "Localisation rate from gas collisions" carry the same physical dimension. -/
theorem eq3_la_dim : d_Lambda_a = (Dim.mul (Dim.mul (Dim.mul (Dim.mul (Dim.div Dim.one (Dim.mul Dim.one (Dim.pow d_hbar 2 1))) d_n_g) (Dim.pow (Dim.mul (Dim.mul Dim.one Dim.one) d_m_g) 1 2)) (Dim.pow d_a 2 1)) (Dim.pow (Dim.mul d_k_B d_T) 3 2)) := by decide
/-- The denominator `3 * hbar^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_la_reg1 (hbar : ℝ) (hhbar : 0 < hbar) : (3 : ℝ) * hbar ^ 2 ≠ 0 := by positivity
/-- The argument `2 * pi * m_g` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_la_reg2 (m_g : ℝ) (hm_g : 0 < m_g) : 0 ≤ (2 : ℝ) * Real.pi * m_g := by positivity
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_la_reg3  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 4. Localisation rate from thermal photons

    Lambda_p = 8*40320*zeta_9*c*a^6/(9*pi)*(k_B*T/(hbar*c))^9
-/
/-- Both sides of "Localisation rate from thermal photons" carry the same physical dimension. -/
theorem eq4_lp_dim : d_Lambda_p = (Dim.mul (Dim.div (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_zeta_9) d_c) (Dim.pow d_a 6 1)) (Dim.mul Dim.one Dim.one)) (Dim.pow (Dim.div (Dim.mul d_k_B d_T) (Dim.mul d_hbar d_c)) 9 1)) := by decide
/-- The denominator `9 * pi` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_lp_reg1  : (9 : ℝ) * Real.pi ≠ 0 := by positivity
/-- The denominator `hbar * c` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_lp_reg2 (hbar c : ℝ) (hhbar : 0 < hbar) (hc : 0 < c) : hbar * c ≠ 0 := by positivity

/-! ## 5. Decoherence rate with saturation

    Gamma = (Lambda_a + Lambda_p)*dx^2/(1 + dx^2/l_c^2)
-/
/-- Both sides of "Decoherence rate with saturation" carry the same physical dimension. -/
theorem eq5_gam_dim : d_Gamma = (Dim.div (Dim.mul d_Lambda_a (Dim.pow d_dx 2 1)) Dim.one) := by decide
theorem eq5_gam_term1 : d_Lambda_a = d_Lambda_p := by decide
theorem eq5_gam_term2 : Dim.one = (Dim.div (Dim.pow d_dx 2 1) (Dim.pow d_l_c 2 1)) := by decide
/-- Domain condition for `l_c^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_gam_cond1 (l_c : ℝ) (hdom : l_c ^ 2 ≠ 0) : l_c ^ 2 ≠ 0 := hdom
/-- Domain condition for `1 + dx^2 / l_c^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_gam_cond2 (dx l_c : ℝ) (hdom : (1 : ℝ) + dx ^ 2 / l_c ^ 2 ≠ 0) : (1 : ℝ) + dx ^ 2 / l_c ^ 2 ≠ 0 := hdom

/-! ## 6. Decoherence time

    tau_D = 1/Gamma
-/
/-- Both sides of "Decoherence time" carry the same physical dimension. -/
theorem eq6_tau_dim : d_tau_D = (Dim.div Dim.one d_Gamma) := by decide
/-- The denominator `Gamma` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_tau_reg1 (Gamma : ℝ) (hGamma : 0 < Gamma) : Gamma ≠ 0 := by positivity

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (C D M O U : Prop) (h1 : U → D) (h2 : D → M) (h3 : (M ∧ C) → O) (h4 : U) : M ∧ (C → O) := by tauto

end Bespoke
