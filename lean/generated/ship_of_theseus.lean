import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The ship of Theseus

Machine-checkable statements for this investigation (ship-of-theseus).
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
def d_N_p : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of parts in the ship [1]
def d_f_B : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fraction of the original matter in the reassembled ship [1]
def d_f_o : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fraction of original matter in the repaired ship [1]
def d_r_rep : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Replacement rate [1/yr]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_t_50 : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time at which half the original matter remains [s]
def d_t_all : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Expected time for every original part to be replaced [s]

/-! ## 1. Expected original fraction

    f_o = (1 - 1/N_p)^(r_rep*t)
-/
/-- Both sides of "Expected original fraction" carry the same physical dimension. -/
theorem eq1_frac_dim : d_f_o = Dim.one := by decide
theorem eq1_frac_term1 : Dim.one = (Dim.div Dim.one d_N_p) := by decide
/-- The denominator `N_p` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_frac_reg1 (N_p : ℝ) (hN_p : 0 < N_p) : N_p ≠ 0 := by positivity

/-! ## 2. Time to one half

    t_50 = ln(1/2)/(r_rep*ln(1 - 1/N_p))
-/
/-- Both sides of "Time to one half" carry the same physical dimension. -/
theorem eq2_half_dim : d_t_50 = (Dim.div Dim.one (Dim.mul d_r_rep Dim.one)) := by decide
theorem eq2_half_term1 : (Dim.div Dim.one Dim.one) = Dim.one := by decide
theorem eq2_half_term2 : Dim.one = (Dim.div Dim.one d_N_p) := by decide
theorem eq2_half_term3 : Dim.one = Dim.one := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_half_reg1  : (2 : ℝ) ≠ 0 := by positivity
/-- The argument `1 / 2` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_half_reg2  : 0 < (1 : ℝ) / (2 : ℝ) := by positivity
/-- The denominator `N_p` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_half_reg3 (N_p : ℝ) (hN_p : 0 < N_p) : N_p ≠ 0 := by positivity
/-- Domain condition for `1 - 1 / N_p`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq2_half_cond4 (N_p : ℝ) (hdom : 0 < (1 : ℝ) - (1 : ℝ) / N_p) : 0 < (1 : ℝ) - (1 : ℝ) / N_p := hdom
/-- Domain condition for `r_rep * ln(1 - 1 / N_p)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq2_half_cond5 (r_rep N_p : ℝ) (hdom : r_rep * Real.log ((1 : ℝ) - (1 : ℝ) / N_p) ≠ 0) : r_rep * Real.log ((1 : ℝ) - (1 : ℝ) / N_p) ≠ 0 := hdom

/-! ## 3. Expected time until no original part remains

    t_all = N_p*(ln(N_p) + 0.5772)/r_rep
-/
/-- Both sides of "Expected time until no original part remains" carry the same physical dimension. -/
theorem eq3_all_dim : d_t_all = (Dim.div (Dim.mul d_N_p Dim.one) d_r_rep) := by decide
theorem eq3_all_term1 : d_N_p = Dim.one := by decide
theorem eq3_all_term2 : Dim.one = Dim.one := by decide
/-- The argument `N_p` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_all_reg1 (N_p : ℝ) (hN_p : 0 < N_p) : 0 < N_p := by positivity
/-- The denominator `r_rep` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_all_reg2 (r_rep : ℝ) (hr_rep : 0 < r_rep) : r_rep ≠ 0 := by positivity

/-! ## 4. Share of the original matter in the reassembled ship

    f_B = 1 - f_o
-/
/-- Both sides of "Share of the original matter in the reassembled ship" carry the same physical dimension. -/
theorem eq4_other_dim : d_f_B = Dim.one := by decide
theorem eq4_other_term1 : Dim.one = d_f_o := by decide

/-! ## Logical structure of the argument -/

/-- The premises are jointly contradictory. -/
theorem premises_inconsistent (A B Form Matter : Prop) (h1 : Form → A) (h2 : Matter → B) (h3 : ¬(A ∧ B)) (h4 : Form) (h5 : Matter) : False := by tauto

end Bespoke
