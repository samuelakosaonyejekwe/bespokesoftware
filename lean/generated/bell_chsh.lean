import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Bell test: the CHSH inequality

Machine-checkable statements for this investigation (bell-chsh).
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
def d_E_11 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Correlation for settings a₁, b₁ [1]
def d_E_12 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Correlation for settings a₁, b₂ [1]
def d_E_21 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Correlation for settings a₂, b₁ [1]
def d_E_22 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Correlation for settings a₂, b₂ [1]
def d_E_c : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Correlation of the two outcomes [1]
def d_S : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- CHSH parameter [1]
def d_S_L : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Bound for local-realist theories [1]
def d_S_T : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Tsirelson bound [1]
def d_theta_ab : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Angle between the analysers [rad]

/-! ## 1. Quantum correlation

    E_c = -cos(theta_ab)
-/
/-- Both sides of "Quantum correlation" carry the same physical dimension. -/
theorem eq1_corr_dim : d_E_c = Dim.one := by decide
theorem eq1_corr_term1 : d_theta_ab = Dim.one := by decide

/-! ## 2. CHSH combination

    S = E_11 - E_12 + E_21 + E_22
-/
/-- Both sides of "CHSH combination" carry the same physical dimension. -/
theorem eq2_chsh_dim : d_S = d_E_11 := by decide
theorem eq2_chsh_term1 : d_E_11 = d_E_12 := by decide
theorem eq2_chsh_term2 : d_E_11 = d_E_21 := by decide
theorem eq2_chsh_term3 : d_E_11 = d_E_22 := by decide

/-! ## 3. Local-realist bound

    S_L = 2
-/
/-- Both sides of "Local-realist bound" carry the same physical dimension. -/
theorem eq3_local_dim : d_S_L = Dim.one := by decide

/-! ## 4. Tsirelson bound

    S_T = 2*sqrt(2)
-/
/-- Both sides of "Tsirelson bound" carry the same physical dimension. -/
theorem eq4_tsir_dim : d_S_T = (Dim.mul Dim.one (Dim.pow Dim.one 1 2)) := by decide
/-- The argument `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_tsir_reg1  : 0 ≤ (2 : ℝ) := by positivity

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (B F L R : Prop) (h1 : ((L ∧ R) ∧ F) → B) (h2 : ¬B) : ¬((L ∧ R) ∧ F) := by tauto

end Bespoke
