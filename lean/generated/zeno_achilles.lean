import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Zeno's paradox of Achilles and the tortoise

Machine-checkable statements for this investigation (zeno-achilles).
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
def d_d_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Head start of the tortoise [m]
def d_k_i : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Stage index [1]
def d_n_st : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Stages of Zeno's construction to evaluate [1]
def d_r_v : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Speed ratio [1]
def d_t_c : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Catch-up time [s]
def d_t_n : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Elapsed time after n stages [s]
def d_tau_k : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Duration of stage k [s]
def d_v_A : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of Achilles [m/s]
def d_v_T : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of the tortoise [m/s]
def d_x_c : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Catch-up position [m]

/-! ## 1. Speed ratio

    r_v = v_T/v_A
-/
/-- Both sides of "Speed ratio" carry the same physical dimension. -/
theorem eq1_ratio_dim : d_r_v = (Dim.div d_v_T d_v_A) := by decide
/-- The denominator `v_A` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_ratio_reg1 (v_A : ℝ) (hv_A : 0 < v_A) : v_A ≠ 0 := by positivity

/-! ## 2. Duration of stage k

    tau_k = d_0*r_v^k_i/v_A
-/
/-- Both sides of "Duration of stage k" carry the same physical dimension. -/
theorem eq2_stage_dim : d_tau_k = (Dim.div (Dim.mul d_d_0 Dim.one) d_v_A) := by decide
/-- The denominator `v_A` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_stage_reg1 (v_A : ℝ) (hv_A : 0 < v_A) : v_A ≠ 0 := by positivity

/-! ## 3. Elapsed time after n stages

    t_n = d_0*(1 - r_v^n_st)/(v_A*(1 - r_v))
-/
/-- Both sides of "Elapsed time after n stages" carry the same physical dimension. -/
theorem eq3_part_dim : d_t_n = (Dim.div (Dim.mul d_d_0 Dim.one) (Dim.mul d_v_A Dim.one)) := by decide
theorem eq3_part_term1 : Dim.one = Dim.one := by decide
theorem eq3_part_term2 : Dim.one = d_r_v := by decide
/-- Domain condition for `v_A * (1 - r_v)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_part_cond1 (v_A r_v : ℝ) (hdom : v_A * ((1 : ℝ) - r_v) ≠ 0) : v_A * ((1 : ℝ) - r_v) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq3_part_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 4. Catch-up time (limit of the partial sums)

    t_c = d_0/(v_A - v_T)
-/
/-- Both sides of "Catch-up time (limit of the partial sums)" carry the same physical dimension. -/
theorem eq4_lim_dim : d_t_c = (Dim.div d_d_0 d_v_A) := by decide
theorem eq4_lim_term1 : d_v_A = d_v_T := by decide
/-- Domain condition for `v_A - v_T`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_lim_cond1 (v_A v_T : ℝ) (hdom : v_A - v_T ≠ 0) : v_A - v_T ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq4_lim_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 5. Catch-up position

    x_c = v_A*t_c
-/
/-- Both sides of "Catch-up position" carry the same physical dimension. -/
theorem eq5_xc_dim : d_x_c = (Dim.mul d_v_A d_t_c) := by decide

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (Catch Conv Inf NoSuper : Prop) (h1 : Inf) (h2 : Conv) (h3 : Conv → Catch) (h4 : (Inf ∧ NoSuper) → (¬Catch)) : ¬NoSuper := by tauto

end Bespoke
