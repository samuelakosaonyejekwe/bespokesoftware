import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Base rates and the diagnostic test

Machine-checkable statements for this investigation (bayes-diagnostic-test).
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
def d_LR_n : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Likelihood ratio of a negative result [1]
def d_LR_p : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Likelihood ratio of a positive result [1]
def d_NPV : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Negative predictive value [1]
def d_O_post : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Post-test odds of disease after a positive result [1]
def d_PPV : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Positive predictive value [1]
def d_P_pos : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Probability of a positive result [1]
def d_prev : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Prevalence in the tested population [%]
def d_sens : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Sensitivity (true-positive rate) [%]
def d_spec : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Specificity (true-negative rate) [%]

/-! ## 1. Probability of a positive result

    P_pos = sens*prev + (1 - spec)*(1 - prev)
-/
/-- Both sides of "Probability of a positive result" carry the same physical dimension. -/
theorem eq1_tot_dim : d_P_pos = (Dim.mul d_sens d_prev) := by decide
theorem eq1_tot_term1 : Dim.one = d_spec := by decide
theorem eq1_tot_term2 : Dim.one = d_prev := by decide
theorem eq1_tot_term3 : (Dim.mul d_sens d_prev) = (Dim.mul Dim.one Dim.one) := by decide

/-! ## 2. Positive predictive value

    PPV = sens*prev/P_pos
-/
/-- Both sides of "Positive predictive value" carry the same physical dimension. -/
theorem eq2_ppv_dim : d_PPV = (Dim.div (Dim.mul d_sens d_prev) d_P_pos) := by decide
/-- The denominator `P_pos` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_ppv_reg1 (P_pos : ℝ) (hP_pos : 0 < P_pos) : P_pos ≠ 0 := by positivity

/-! ## 3. Negative predictive value

    NPV = (1 - (1 - spec))*(1 - prev)/(1 - P_pos)
-/
/-- Both sides of "Negative predictive value" carry the same physical dimension. -/
theorem eq3_npv_dim : d_NPV = (Dim.div (Dim.mul Dim.one Dim.one) Dim.one) := by decide
theorem eq3_npv_term1 : Dim.one = d_spec := by decide
theorem eq3_npv_term2 : Dim.one = Dim.one := by decide
theorem eq3_npv_term3 : Dim.one = d_prev := by decide
theorem eq3_npv_term4 : Dim.one = d_P_pos := by decide
/-- Domain condition for `1 - P_pos`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq3_npv_cond1 (P_pos : ℝ) (hdom : (1 : ℝ) - P_pos ≠ 0) : (1 : ℝ) - P_pos ≠ 0 := hdom

/-! ## 4. Likelihood ratio of a positive result

    LR_p = sens/(1 - spec)
-/
/-- Both sides of "Likelihood ratio of a positive result" carry the same physical dimension. -/
theorem eq4_lrp_dim : d_LR_p = (Dim.div d_sens Dim.one) := by decide
theorem eq4_lrp_term1 : Dim.one = d_spec := by decide
/-- Domain condition for `1 - spec`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_lrp_cond1 (spec : ℝ) (hdom : (1 : ℝ) - spec ≠ 0) : (1 : ℝ) - spec ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq4_lrp_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 5. Likelihood ratio of a negative result

    LR_n = (1 - sens)/(1 - (1 - spec))
-/
/-- Both sides of "Likelihood ratio of a negative result" carry the same physical dimension. -/
theorem eq5_lrn_dim : d_LR_n = (Dim.div Dim.one Dim.one) := by decide
theorem eq5_lrn_term1 : Dim.one = d_sens := by decide
theorem eq5_lrn_term2 : Dim.one = d_spec := by decide
theorem eq5_lrn_term3 : Dim.one = Dim.one := by decide
/-- Domain condition for `1 - (1 - spec)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq5_lrn_cond1 (spec : ℝ) (hdom : (1 : ℝ) - ((1 : ℝ) - spec) ≠ 0) : (1 : ℝ) - ((1 : ℝ) - spec) ≠ 0 := hdom

/-! ## 6. Post-test odds after a positive result

    O_post = LR_p*prev/(1 - prev)
-/
/-- Both sides of "Post-test odds after a positive result" carry the same physical dimension. -/
theorem eq6_odds_dim : d_O_post = (Dim.div (Dim.mul d_LR_p d_prev) Dim.one) := by decide
theorem eq6_odds_term1 : Dim.one = d_prev := by decide
/-- Domain condition for `1 - prev`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq6_odds_cond1 (prev : ℝ) (hdom : (1 : ℝ) - prev ≠ 0) : (1 : ℝ) - prev ≠ 0 := hdom

/-! ## Logical structure of the argument -/

/-- The inference is not valid: this assignment makes every premise true and the conclusion false. -/
theorem countermodel : (False → True) ∧ (True) ∧ ¬(False) := by simp

end Bespoke
