import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

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

/-- The smooth rate cap never lets a rate exceed F in magnitude. -/
theorem rate_cap_bounded (f F : ℝ) (hF : 0 < F) : |f / Real.sqrt (1 + (f / F) ^ 2)| ≤ F := by
  have hs : 0 < Real.sqrt (1 + (f / F) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  have h1 : |f| / F ≤ Real.sqrt (1 + (f / F) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, sq_abs, div_pow]; linarith
  calc |f| = F * (|f| / F) := by field_simp
    _ ≤ F * Real.sqrt (1 + (f / F) ^ 2) := by gcongr

/-- A quantity whose rate of change never exceeds F cannot reach infinity in finite time:
after a time T it has moved by at most F * T. -/
theorem bounded_rate_no_blowup (x : ℝ → ℝ) (F T : ℝ) (hT : 0 ≤ T)
    (hx : ∀ t, DifferentiableAt ℝ x t) (hb : ∀ t, |deriv x t| ≤ F) : |x T - x 0| ≤ F * T := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (f := x) (C := F)
    (fun t _ => hx t) (fun t _ => by simpa [Real.norm_eq_abs] using hb t) convex_univ (Set.mem_univ 0) (Set.mem_univ T)
  simpa [Real.norm_eq_abs, abs_of_nonneg hT] using h


/-! ## Dimensions of the symbols -/

def d_length : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Length of the medium [m]
def d_c_w : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Wave speed [m/s]
def d_c_x : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Local wave speed [m/s]
def d_q_pred : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Expected refocused amplitude ratio from the loss estimate [1]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_u : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Wave displacement [m]
def d_u_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Initial displacement [m]
def d_u_TR : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Displacement imposed at a sensor during replay [m]
def d_u_a : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Emitted amplitude [m]
def d_u_rec : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Displacement recorded at that sensor [m]
def d_w_m : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fade weight of the mirror: 1, falling smoothly to 0 over the last 0.2 L/c of the record [1]
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

    u_TR = w_m*u_rec
-/
/-- Both sides of "Replay at a sensor" carry the same physical dimension. -/
theorem eq4_tr_dim : d_u_TR = (Dim.mul d_w_m d_u_rec) := by decide

/-! ## 5. Expected refocused amplitude

    q_pred = 1
-/
/-- Both sides of "Expected refocused amplitude" carry the same physical dimension. -/
theorem eq5_qf_dim : d_q_pred = Dim.one := by decide

end Bespoke
