import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Time-reversal focusing of a wave pulse

Machine-checkable statements for this investigation (time-reversal-focusing).
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
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Length of the medium [m]
def d_c_w : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Wave speed [m/s]
def d_c_x : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Local wave speed [m/s]
def d_q_f : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Refocused amplitude over emitted amplitude [1]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_u : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Wave displacement [m]
def d_u_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Initial displacement [m]
def d_u_TR : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Displacement imposed at a sensor during replay [m]
def d_u_a : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Emitted amplitude [m]
def d_u_rec : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Displacement recorded at that sensor [m]
def d_w_p : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Pulse width (standard deviation) as a fraction of the length [1]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position [m]
def d_x_s : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Source position as a fraction of the length [1]

/-! ## 1. Wave equation

    pd2(u,t) = c_x^2*pd2(u,x)
-/
/-- Both sides of "Wave equation" carry the same physical dimension. -/
theorem eq1_wave_dim : (Dim.div d_u (Dim.pow d_t 2 1)) = (Dim.mul (Dim.pow d_c_x 2 1) (Dim.div d_u (Dim.pow d_x 2 1))) := by decide

/-! ## 2. Wave speed

    c_x = c_w
-/
/-- Both sides of "Wave speed" carry the same physical dimension. -/
theorem eq2_cx_dim : d_c_x = d_c_w := by decide

/-! ## 3. Emitted pulse

    u_0 = u_a*exp(-(x - x_s*L)^2/(2*(w_p*L)^2))
-/
/-- Both sides of "Emitted pulse" carry the same physical dimension. -/
theorem eq3_ic_dim : d_u_0 = (Dim.mul d_u_a Dim.one) := by decide
theorem eq3_ic_term1 : d_x = (Dim.mul d_x_s d_L) := by decide
theorem eq3_ic_term2 : (Dim.div (Dim.pow d_x 2 1) (Dim.mul Dim.one (Dim.pow (Dim.mul d_w_p d_L) 2 1))) = Dim.one := by decide
/-- The denominator `2 * (w_p * L)^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_ic_reg1 (w_p L : ℝ) (hw_p : 0 < w_p) (hL : 0 < L) : (2 : ℝ) * (w_p * L) ^ 2 ≠ 0 := by positivity

/-! ## 4. Replay at a sensor

    u_TR = u_rec
-/
/-- Both sides of "Replay at a sensor" carry the same physical dimension. -/
theorem eq4_tr_dim : d_u_TR = d_u_rec := by decide

/-! ## 5. Expected refocused amplitude

    q_f = 1
-/
/-- Both sides of "Expected refocused amplitude" carry the same physical dimension. -/
theorem eq5_qf_dim : d_q_f = Dim.one := by decide

end Bespoke
