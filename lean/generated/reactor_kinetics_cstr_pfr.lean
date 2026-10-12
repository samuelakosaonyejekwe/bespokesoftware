import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Conversion in stirred-tank and plug-flow reactors

Machine-checkable statements for this investigation (reactor-kinetics-cstr-pfr).
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
def d_A_f : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Frequency factor (first-order equivalent at feed concentration) [1/s]
def d_Da : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Damköhler number [1]
def d_E_a : Dim := ⟨12, 24, -24, 0, 0, -12, 0⟩  -- Activation energy [kJ/mol]
def d_R_u : Dim := ⟨12, 24, -24, 0, -12, -12, 0⟩  -- Molar gas constant [J/(mol K)]
def d_T : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Reactor temperature [K]
def d_T_0 : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Feed temperature [°C]
def d_X : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Conversion [1]
def d_X_cstr : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Conversion in the stirred tank [1]
def d_k : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Rate constant [1/s]
def d_r_X : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Rate of conversion [1/s]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Space-time coordinate [s]
def d_tau : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Space time V/v₀ [s]

/-! ## 1. Arrhenius law

    k = A_f*exp(-E_a/(R_u*T))
-/
/-- Both sides of "Arrhenius law" carry the same physical dimension. -/
theorem eq1_arr_dim : d_k = (Dim.mul d_A_f Dim.one) := by decide
theorem eq1_arr_term1 : (Dim.div d_E_a (Dim.mul d_R_u d_T)) = Dim.one := by decide
/-- Domain condition for `R_u * T`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_arr_cond1 (R_u T : ℝ) (hdom : R_u * T ≠ 0) : R_u * T ≠ 0 := hdom

/-! ## 2. Rate of conversion

    r_X = k*(1 - X)
-/
/-- Both sides of "Rate of conversion" carry the same physical dimension. -/
theorem eq2_rate_dim : d_r_X = (Dim.mul d_k Dim.one) := by decide
theorem eq2_rate_term1 : Dim.one = d_X := by decide

/-! ## 3. Plug-flow design equation

    d(X,t) = r_X
-/
/-- Both sides of "Plug-flow design equation" carry the same physical dimension. -/
theorem eq3_pfr_dim : (Dim.div d_X d_t) = d_r_X := by decide

/-! ## 4. Stirred-tank design equation

    X_cstr = tau*r_X
-/
/-- Both sides of "Stirred-tank design equation" carry the same physical dimension. -/
theorem eq4_cstr_dim : d_X_cstr = (Dim.mul d_tau d_r_X) := by decide

/-! ## 5. Energy balance

    T = T_0
-/
/-- Both sides of "Energy balance" carry the same physical dimension. -/
theorem eq5_en_dim : d_T = d_T_0 := by decide

/-! ## 6. Damköhler number

    Da = k*tau
-/
/-- Both sides of "Damköhler number" carry the same physical dimension. -/
theorem eq6_da_dim : d_Da = (Dim.mul d_k d_tau) := by decide

end Bespoke
