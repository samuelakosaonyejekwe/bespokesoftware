import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Quantum harmonic oscillator

Machine-checkable statements for this investigation (harmonic-oscillator-quantum).
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
def d_E_n : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Energy of level n [J]
def d_alpha_c : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Coherent-state amplitude |α| [1]
def d_dp : Dim := ⟨12, 12, -12, 0, 0, 0, 0⟩  -- Momentum uncertainty [kg m/s]
def d_dx : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position uncertainty [m]
def d_f : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Oscillation frequency [THz]
def d_hbar : Dim := ⟨12, 24, -12, 0, 0, 0, 0⟩  -- Reduced Planck constant [J s]
def d_m : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Oscillating mass [u]
def d_n : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Quantum number of the level examined [1]
def d_omega : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Angular frequency [1/s]
def d_psi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Wavefunction (arbitrary normalisation) [1]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position [m]
def d_x_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Oscillator length [m]
def d_x_c : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Centre of the coherent state [m]

/-! ## 1. Angular frequency

    omega = 2*pi*f
-/
/-- Both sides of "Angular frequency" carry the same physical dimension. -/
theorem eq1_om_dim : d_omega = (Dim.mul (Dim.mul Dim.one Dim.one) d_f) := by decide

/-! ## 2. Schrödinger equation

    -hbar^2/(2*m)*d2(psi,x) + m*omega^2*x^2/2*psi = E_n*psi
-/
/-- Both sides of "Schrödinger equation" carry the same physical dimension. -/
theorem eq2_tise_dim : (Dim.mul (Dim.div (Dim.pow d_hbar 2 1) (Dim.mul Dim.one d_m)) (Dim.div d_psi (Dim.pow d_x 2 1))) = (Dim.mul d_E_n d_psi) := by decide
theorem eq2_tise_term1 : (Dim.mul (Dim.div (Dim.pow d_hbar 2 1) (Dim.mul Dim.one d_m)) (Dim.div d_psi (Dim.pow d_x 2 1))) = (Dim.mul (Dim.div (Dim.mul (Dim.mul d_m (Dim.pow d_omega 2 1)) (Dim.pow d_x 2 1)) Dim.one) d_psi) := by decide
/-- The denominator `2 * m` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_tise_reg1 (m : ℝ) (hm : 0 < m) : (2 : ℝ) * m ≠ 0 := by positivity
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_tise_reg2  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 3. Oscillator length

    x_0 = sqrt(hbar/(m*omega))
-/
/-- Both sides of "Oscillator length" carry the same physical dimension. -/
theorem eq3_x0_dim : d_x_0 = (Dim.pow (Dim.div d_hbar (Dim.mul d_m d_omega)) 1 2) := by decide
/-- The denominator `m * omega` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_x0_reg1 (m omega : ℝ) (hm : 0 < m) (homega : 0 < omega) : m * omega ≠ 0 := by positivity
/-- The argument `hbar / (m * omega)` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_x0_reg2 (hbar m omega : ℝ) (hhbar : 0 < hbar) (hm : 0 < m) (homega : 0 < omega) : 0 ≤ hbar / (m * omega) := by positivity

/-! ## 4. Energy levels

    E_n = hbar*omega*(n + 1/2)
-/
/-- Both sides of "Energy levels" carry the same physical dimension. -/
theorem eq4_En_dim : d_E_n = (Dim.mul (Dim.mul d_hbar d_omega) d_n) := by decide
theorem eq4_En_term1 : d_n = (Dim.div Dim.one Dim.one) := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_En_reg1  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 5. Uncertainty product of level n

    dx*dp = hbar*(n + 1/2)
-/
/-- Both sides of "Uncertainty product of level n" carry the same physical dimension. -/
theorem eq5_unc_dim : (Dim.mul d_dx d_dp) = (Dim.mul d_hbar d_n) := by decide
theorem eq5_unc_term1 : d_n = (Dim.div Dim.one Dim.one) := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_unc_reg1  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 6. Centre of a coherent state

    x_c = sqrt(2)*alpha_c*x_0*cos(omega*t)
-/
/-- Both sides of "Centre of a coherent state" carry the same physical dimension. -/
theorem eq6_coh_dim : d_x_c = (Dim.mul (Dim.mul (Dim.mul (Dim.pow Dim.one 1 2) d_alpha_c) d_x_0) Dim.one) := by decide
theorem eq6_coh_term1 : (Dim.mul d_omega d_t) = Dim.one := by decide
/-- The argument `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_coh_reg1  : 0 ≤ (2 : ℝ) := by positivity

end Bespoke
