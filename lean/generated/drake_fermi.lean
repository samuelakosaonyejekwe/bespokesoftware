import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The Drake equation and the Fermi question

Machine-checkable statements for this investigation (drake-fermi).
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
def d_L_civ : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time for which a civilisation remains detectable [yr]
def d_N_civ : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of detectable civilisations in the Galaxy [1]
def d_R_star : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Rate of star formation in the Galaxy [1/yr]
def d_f_c : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fraction of those that develop detectable technology [1]
def d_f_i : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fraction of those on which intelligence evolves [1]
def d_f_l : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fraction of habitable planets on which life arises [1]
def d_f_p : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fraction of stars with planets [1]
def d_n_e : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Habitable planets per planetary system [1]

/-! ## 1. Drake equation

    N_civ = R_star*f_p*n_e*f_l*f_i*f_c*L_civ
-/
/-- Both sides of "Drake equation" carry the same physical dimension. -/
theorem eq1_drake_dim : d_N_civ = (Dim.mul (Dim.mul (Dim.mul (Dim.mul (Dim.mul (Dim.mul d_R_star d_f_p) d_n_e) d_f_l) d_f_i) d_f_c) d_L_civ) := by decide

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (Here Many Observed Spread : Prop) (h1 : (Many ∧ Spread) → Here) (h2 : Here → Observed) (h3 : ¬Observed) : ¬(Many ∧ Spread) := by tauto

end Bespoke
