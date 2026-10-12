import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The Monty Hall problem

Machine-checkable statements for this investigation (monty-hall).
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
def d_A_sw : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Advantage ratio of switching [1]
def d_P_st : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Probability of winning by staying [1]
def d_P_sw : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Probability of winning by switching to one remaining door [1]
def d_k_open : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Doors opened by the host [1]
def d_n_d : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of doors [1]
def d_n_trials : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Simulated games [1]
def d_sigma_mc : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Standard error of the simulated frequency [1]

/-! ## 1. Winning by staying

    P_st = 1/n_d
-/
/-- Both sides of "Winning by staying" carry the same physical dimension. -/
theorem eq1_stay_dim : d_P_st = (Dim.div Dim.one d_n_d) := by decide
/-- The denominator `n_d` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_stay_reg1 (n_d : ℝ) (hn_d : 0 < n_d) : n_d ≠ 0 := by positivity

/-! ## 2. Winning by switching to one of the remaining doors

    P_sw = (n_d - 1)/(n_d*(n_d - k_open - 1))
-/
/-- Both sides of "Winning by switching to one of the remaining doors" carry the same physical dimension. -/
theorem eq2_switch_dim : d_P_sw = (Dim.div d_n_d (Dim.mul d_n_d d_n_d)) := by decide
theorem eq2_switch_term1 : d_n_d = Dim.one := by decide
theorem eq2_switch_term2 : d_n_d = d_k_open := by decide
theorem eq2_switch_term3 : d_n_d = Dim.one := by decide
/-- Domain condition for `n_d * (n_d - k_open - 1)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_switch_cond1 (n_d k_open : ℝ) (hdom : n_d * (n_d - k_open - (1 : ℝ)) ≠ 0) : n_d * (n_d - k_open - (1 : ℝ)) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq2_switch_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 3. Advantage of switching

    A_sw = P_sw/P_st
-/
/-- Both sides of "Advantage of switching" carry the same physical dimension. -/
theorem eq3_adv_dim : d_A_sw = (Dim.div d_P_sw d_P_st) := by decide
/-- The denominator `P_st` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_adv_reg1 (P_st : ℝ) (hP_st : 0 < P_st) : P_st ≠ 0 := by positivity

/-! ## 4. Standard error of a simulated frequency

    sigma_mc = sqrt(P_sw*(1 - P_sw)/n_trials)
-/
/-- Both sides of "Standard error of a simulated frequency" carry the same physical dimension. -/
theorem eq4_se_dim : d_sigma_mc = (Dim.pow (Dim.div (Dim.mul d_P_sw Dim.one) d_n_trials) 1 2) := by decide
theorem eq4_se_term1 : Dim.one = d_P_sw := by decide
/-- The denominator `n_trials` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_se_reg1 (n_trials : ℝ) (hn_trials : 0 < n_trials) : n_trials ≠ 0 := by positivity
/-- Domain condition for `P_sw * (1 - P_sw) / n_trials`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_se_cond2 (P_sw n_trials : ℝ) (hdom : 0 ≤ P_sw * ((1 : ℝ) - P_sw) / n_trials) : 0 ≤ P_sw * ((1 : ℝ) - P_sw) / n_trials := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq4_se_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (FirstCar HostGoat StayWins SwitchWins : Prop) (h1 : HostGoat) (h2 : FirstCar → StayWins) (h3 : ((¬FirstCar) ∧ HostGoat) → SwitchWins) (h4 : StayWins ↔ (¬SwitchWins)) : SwitchWins ↔ (¬FirstCar) := by tauto

end Bespoke
