import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Doppler shift and beats

Machine-checkable statements for this investigation (doppler-and-beats).
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
def d_c_s : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Wave speed in the medium [m/s]
def d_f_0 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Emitted frequency [Hz]
def d_f_beat : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Beat frequency [Hz]
def d_f_obs : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Received frequency [Hz]
def d_lambda_f : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Wavelength ahead of the source [m]
def d_u_s : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Radial component of the source velocity [m/s]
def d_v_o : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Observer speed toward the source [m/s]
def d_v_s : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Source speed toward the observer [m/s]

/-! ## 1. Radial source speed

    u_s = v_s
-/
/-- Both sides of "Radial source speed" carry the same physical dimension. -/
theorem eq1_us_dim : d_u_s = d_v_s := by decide

/-! ## 2. Doppler shift in a medium

    f_obs = f_0*(c_s + v_o)/(c_s - u_s)
-/
/-- Both sides of "Doppler shift in a medium" carry the same physical dimension. -/
theorem eq2_dop_dim : d_f_obs = (Dim.div (Dim.mul d_f_0 d_c_s) d_c_s) := by decide
theorem eq2_dop_term1 : d_c_s = d_v_o := by decide
theorem eq2_dop_term2 : d_c_s = d_u_s := by decide
/-- Domain condition for `c_s - u_s`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_dop_cond1 (c_s u_s : ℝ) (hdom : c_s - u_s ≠ 0) : c_s - u_s ≠ 0 := hdom

/-! ## 3. Wavelength ahead of the source

    lambda_f = (c_s - u_s)/f_0
-/
/-- Both sides of "Wavelength ahead of the source" carry the same physical dimension. -/
theorem eq3_lam_dim : d_lambda_f = (Dim.div d_c_s d_f_0) := by decide
theorem eq3_lam_term1 : d_c_s = d_u_s := by decide
/-- The denominator `f_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_lam_reg1 (f_0 : ℝ) (hf_0 : 0 < f_0) : f_0 ≠ 0 := by positivity

/-! ## 4. Beat frequency against the emitted tone

    f_beat = abs(f_obs - f_0)
-/
/-- Both sides of "Beat frequency against the emitted tone" carry the same physical dimension. -/
theorem eq4_beat_dim : d_f_beat = d_f_obs := by decide
theorem eq4_beat_term1 : d_f_obs = d_f_0 := by decide

end Bespoke
