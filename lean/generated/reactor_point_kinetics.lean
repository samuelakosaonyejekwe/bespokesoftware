import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Reactor point kinetics after a reactivity step

Machine-checkable statements for this investigation (reactor-point-kinetics).
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
def d_C : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Precursor concentration (same normalisation) [1]
def d_Lambda_g : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Prompt-neutron generation time [s]
def d_T_pa : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Approximate stable period [s]
def d_beta_d : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Delayed-neutron fraction [1]
def d_lambda_d : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Effective precursor decay constant [1/s]
def d_n : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Neutron population relative to its initial value [1]
def d_n_pj : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Population after the prompt jump [1]
def d_rho_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Reactivity inserted [1]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]

/-! ## 1. Neutron balance

    d(n,t) = (rho_r - beta_d)/Lambda_g*n + lambda_d*C
-/
/-- Both sides of "Neutron balance" carry the same physical dimension. -/
theorem eq1_n_dim : (Dim.div d_n d_t) = (Dim.mul (Dim.div d_rho_r d_Lambda_g) d_n) := by decide
theorem eq1_n_term1 : d_rho_r = d_beta_d := by decide
theorem eq1_n_term2 : (Dim.mul (Dim.div d_rho_r d_Lambda_g) d_n) = (Dim.mul d_lambda_d d_C) := by decide
/-- The denominator `Lambda_g` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_n_reg1 (Lambda_g : ℝ) (hLambda_g : 0 < Lambda_g) : Lambda_g ≠ 0 := by positivity

/-! ## 2. Precursor balance

    d(C,t) = beta_d/Lambda_g*n - lambda_d*C
-/
/-- Both sides of "Precursor balance" carry the same physical dimension. -/
theorem eq2_c_dim : (Dim.div d_C d_t) = (Dim.mul (Dim.div d_beta_d d_Lambda_g) d_n) := by decide
theorem eq2_c_term1 : (Dim.mul (Dim.div d_beta_d d_Lambda_g) d_n) = (Dim.mul d_lambda_d d_C) := by decide
/-- The denominator `Lambda_g` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_c_reg1 (Lambda_g : ℝ) (hLambda_g : 0 < Lambda_g) : Lambda_g ≠ 0 := by positivity

/-! ## 3. Prompt jump

    n_pj = beta_d/(beta_d - rho_r)
-/
/-- Both sides of "Prompt jump" carry the same physical dimension. -/
theorem eq3_pj_dim : d_n_pj = (Dim.div d_beta_d d_beta_d) := by decide
theorem eq3_pj_term1 : d_beta_d = d_rho_r := by decide
/-- Domain condition for `beta_d - rho_r`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_pj_cond1 (beta_d rho_r : ℝ) (hdom : beta_d - rho_r ≠ 0) : beta_d - rho_r ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq3_pj_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 4. Stable period, small-reactivity approximation

    T_pa = (beta_d - rho_r)/(lambda_d*rho_r)
-/
/-- Both sides of "Stable period, small-reactivity approximation" carry the same physical dimension. -/
theorem eq4_per_dim : d_T_pa = (Dim.div d_beta_d (Dim.mul d_lambda_d d_rho_r)) := by decide
theorem eq4_per_term1 : d_beta_d = d_rho_r := by decide
/-- Domain condition for `lambda_d * rho_r`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_per_cond1 (lambda_d rho_r : ℝ) (hdom : lambda_d * rho_r ≠ 0) : lambda_d * rho_r ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq4_per_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

end Bespoke
