import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The sorites paradox of the heap

Machine-checkable statements for this investigation (sorites-heap).
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
def d_I_k : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Truth value of the conditional at n grains [1]
def d_h_n : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Degree to which n grains make a heap [1]
def d_n_k : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of grains [1]
def d_n_mid : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of grains at which "heap" is half true (or at which the sharp boundary lies) [1]
def d_v_k : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Truth derived so far for the current number of grains [1]
def d_v_next : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Truth derived for one grain fewer [1]

/-! ## 1. Two-valued heap predicate

    h_n = heaviside(n_k - n_mid)
-/
/-- Both sides of "Two-valued heap predicate" carry the same physical dimension. -/
theorem eq1_heap_dim : d_h_n = Dim.one := by decide
theorem eq1_heap_term1 : d_n_k = d_n_mid := by decide

/-! ## 2. Truth of each inductive conditional

    I_k = 1
-/
/-- Both sides of "Truth of each inductive conditional" carry the same physical dimension. -/
theorem eq2_imp_dim : d_I_k = Dim.one := by decide

/-! ## 3. Truth passed on by modus ponens

    v_next = max(0, v_k + I_k - 1)
-/
/-- Both sides of "Truth passed on by modus ponens" carry the same physical dimension. -/
theorem eq3_mp_dim : d_v_next = d_v_k := by decide
theorem eq3_mp_term1 : d_v_k = d_I_k := by decide
theorem eq3_mp_term2 : d_v_k = Dim.one := by decide

/-! ## Logical structure of the argument -/

/-- The premises are jointly contradictory. -/
theorem premises_inconsistent (H1 H10 H100 H1000 H10000 : Prop) (h1 : H10000) (h2 : H10000 → H1000) (h3 : H1000 → H100) (h4 : H100 → H10) (h5 : H10 → H1) (h6 : ¬H1) : False := by tauto

end Bespoke
