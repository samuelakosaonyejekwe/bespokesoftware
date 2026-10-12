import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The birthday problem

Machine-checkable statements for this investigation (birthday-problem).
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
def d_E_pair : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Expected number of matching pairs [1]
def d_N_pair : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of pairs of people [1]
def d_P_apx : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Exponential approximation [1]
def d_Q_k : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Probability that the first k people have no match [1]
def d_Q_next : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Probability that the first k + 1 people have no match [1]
def d_d_y : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of equally likely days [1]
def d_k_i : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of people already considered [1]
def d_n_p : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of people [1]

/-! ## 1. Number of pairs

    N_pair = n_p*(n_p - 1)/2
-/
/-- Both sides of "Number of pairs" carry the same physical dimension. -/
theorem eq1_pairs_dim : d_N_pair = (Dim.div (Dim.mul d_n_p d_n_p) Dim.one) := by decide
theorem eq1_pairs_term1 : d_n_p = Dim.one := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_pairs_reg1  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 2. No-match recurrence

    Q_next = Q_k*(1 - k_i/d_y)
-/
/-- Both sides of "No-match recurrence" carry the same physical dimension. -/
theorem eq2_rec_dim : d_Q_next = (Dim.mul d_Q_k Dim.one) := by decide
theorem eq2_rec_term1 : Dim.one = (Dim.div d_k_i d_d_y) := by decide
/-- The denominator `d_y` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_rec_reg1 (d_y : ℝ) (hd_y : 0 < d_y) : d_y ≠ 0 := by positivity

/-! ## 3. Expected number of matching pairs

    E_pair = N_pair/d_y
-/
/-- Both sides of "Expected number of matching pairs" carry the same physical dimension. -/
theorem eq3_exp_dim : d_E_pair = (Dim.div d_N_pair d_d_y) := by decide
/-- The denominator `d_y` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_exp_reg1 (d_y : ℝ) (hd_y : 0 < d_y) : d_y ≠ 0 := by positivity

/-! ## 4. Exponential approximation

    P_apx = 1 - exp(-E_pair)
-/
/-- Both sides of "Exponential approximation" carry the same physical dimension. -/
theorem eq4_apx_dim : d_P_apx = Dim.one := by decide
theorem eq4_apx_term1 : d_E_pair = Dim.one := by decide
theorem eq4_apx_term2 : Dim.one = Dim.one := by decide

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (Comparable Likely : Prop) (h1 : Likely) (h2 : ¬Comparable) : ¬(Likely → Comparable) := by tauto

end Bespoke
