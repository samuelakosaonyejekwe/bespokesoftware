import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Two-body collision with restitution

Machine-checkable statements for this investigation (collision-1d-2d).
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
def d_J : Dim := ⟨12, 12, -12, 0, 0, 0, 0⟩  -- Impulse [N s]
def d_dE : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Kinetic energy dissipated [J]
def d_e_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Coefficient of restitution [1]
def d_m_1 : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass of body 1 [kg]
def d_m_2 : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass of body 2 [kg]
def d_m_red : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Reduced mass [kg]
def d_u_1 : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Velocity of body 1 before impact [m/s]
def d_u_1n : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Normal velocity of body 1 before impact [m/s]
def d_u_2 : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Velocity of body 2 before impact [m/s]
def d_u_2n : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Normal velocity of body 2 before impact [m/s]
def d_v_1n : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Normal velocity of body 1 after impact [m/s]
def d_v_2n : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Normal velocity of body 2 after impact [m/s]
def d_v_n : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Closing speed along the line of centres [m/s]

/-! ## 1. Closing speed

    v_n = abs(u_1 - u_2)
-/
/-- Both sides of "Closing speed" carry the same physical dimension. -/
theorem eq1_vn_dim : d_v_n = d_u_1 := by decide
theorem eq1_vn_term1 : d_u_1 = d_u_2 := by decide

/-! ## 2. Conservation of momentum

    m_1*v_1n + m_2*v_2n = m_1*u_1n + m_2*u_2n
-/
/-- Both sides of "Conservation of momentum" carry the same physical dimension. -/
theorem eq2_mom_dim : (Dim.mul d_m_1 d_v_1n) = (Dim.mul d_m_1 d_u_1n) := by decide
theorem eq2_mom_term1 : (Dim.mul d_m_1 d_v_1n) = (Dim.mul d_m_2 d_v_2n) := by decide
theorem eq2_mom_term2 : (Dim.mul d_m_1 d_u_1n) = (Dim.mul d_m_2 d_u_2n) := by decide

/-! ## 3. Law of restitution

    v_2n - v_1n = e_r*(u_1n - u_2n)
-/
/-- Both sides of "Law of restitution" carry the same physical dimension. -/
theorem eq3_rest_dim : d_v_2n = (Dim.mul d_e_r d_u_1n) := by decide
theorem eq3_rest_term1 : d_v_2n = d_v_1n := by decide
theorem eq3_rest_term2 : d_u_1n = d_u_2n := by decide

/-! ## 4. Reduced mass

    m_red = m_1*m_2/(m_1 + m_2)
-/
/-- Both sides of "Reduced mass" carry the same physical dimension. -/
theorem eq4_mred_dim : d_m_red = (Dim.div (Dim.mul d_m_1 d_m_2) d_m_1) := by decide
theorem eq4_mred_term1 : d_m_1 = d_m_2 := by decide
/-- The denominator `m_1 + m_2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_mred_reg1 (m_1 m_2 : ℝ) (hm_1 : 0 < m_1) (hm_2 : 0 < m_2) : m_1 + m_2 ≠ 0 := by positivity

/-! ## 5. Impulse

    J = (1 + e_r)*m_red*v_n
-/
/-- Both sides of "Impulse" carry the same physical dimension. -/
theorem eq5_imp_dim : d_J = (Dim.mul (Dim.mul Dim.one d_m_red) d_v_n) := by decide
theorem eq5_imp_term1 : Dim.one = d_e_r := by decide

/-! ## 6. Kinetic energy dissipated

    dE = 0.5*m_red*(1 - e_r^2)*v_n^2
-/
/-- Both sides of "Kinetic energy dissipated" carry the same physical dimension. -/
theorem eq6_loss_dim : d_dE = (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_red) Dim.one) (Dim.pow d_v_n 2 1)) := by decide
theorem eq6_loss_term1 : Dim.one = (Dim.pow d_e_r 2 1) := by decide

end Bespoke
