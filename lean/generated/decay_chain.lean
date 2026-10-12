import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Radioactive decay chain

Machine-checkable statements for this investigation (decay-chain).
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
def d_N_0 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Initial number of parent nuclei [1]
def d_N_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Parent nuclei [1]
def d_N_2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Daughter nuclei [1]
def d_N_20 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Daughter nuclei at the start [1]
def d_N_3 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Granddaughter nuclei [1]
def d_T_1 : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Half-life of the parent [d]
def d_T_2 : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Half-life of the daughter [h]
def d_T_3 : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Half-life of the granddaughter [yr]
def d_f_b : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Branching fraction of parent to daughter [1]
def d_lambda_1 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Parent decay constant [1/s]
def d_lambda_2 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Daughter decay constant [1/s]
def d_lambda_3 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Granddaughter decay constant [1/s]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_t_max : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time of maximum daughter activity [s]

/-! ## 1. Parent decay

    d(N_1,t) = -lambda_1*N_1
-/
/-- Both sides of "Parent decay" carry the same physical dimension. -/
theorem eq1_p_dim : (Dim.div d_N_1 d_t) = (Dim.mul d_lambda_1 d_N_1) := by decide

/-! ## 2. Daughter balance

    d(N_2,t) = f_b*lambda_1*N_1 - lambda_2*N_2
-/
/-- Both sides of "Daughter balance" carry the same physical dimension. -/
theorem eq2_d_dim : (Dim.div d_N_2 d_t) = (Dim.mul (Dim.mul d_f_b d_lambda_1) d_N_1) := by decide
theorem eq2_d_term1 : (Dim.mul (Dim.mul d_f_b d_lambda_1) d_N_1) = (Dim.mul d_lambda_2 d_N_2) := by decide

/-! ## 3. Granddaughter balance

    d(N_3,t) = lambda_2*N_2 - lambda_3*N_3
-/
/-- Both sides of "Granddaughter balance" carry the same physical dimension. -/
theorem eq3_g_dim : (Dim.div d_N_3 d_t) = (Dim.mul d_lambda_2 d_N_2) := by decide
theorem eq3_g_term1 : (Dim.mul d_lambda_2 d_N_2) = (Dim.mul d_lambda_3 d_N_3) := by decide

/-! ## 4. Decay constant of the parent

    lambda_1 = ln(2)/T_1
-/
/-- Both sides of "Decay constant of the parent" carry the same physical dimension. -/
theorem eq4_lam_dim : d_lambda_1 = (Dim.div Dim.one d_T_1) := by decide
theorem eq4_lam_term1 : Dim.one = Dim.one := by decide
/-- The argument `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_lam_reg1  : 0 < (2 : ℝ) := by positivity
/-- The denominator `T_1` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_lam_reg2 (T_1 : ℝ) (hT_1 : 0 < T_1) : T_1 ≠ 0 := by positivity

/-! ## 5. Decay constant of the daughter

    lambda_2 = ln(2)/T_2
-/
/-- Both sides of "Decay constant of the daughter" carry the same physical dimension. -/
theorem eq5_lam2_dim : d_lambda_2 = (Dim.div Dim.one d_T_2) := by decide
theorem eq5_lam2_term1 : Dim.one = Dim.one := by decide
/-- The argument `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_lam2_reg1  : 0 < (2 : ℝ) := by positivity
/-- The denominator `T_2` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_lam2_reg2 (T_2 : ℝ) (hT_2 : 0 < T_2) : T_2 ≠ 0 := by positivity

/-! ## 6. Decay constant of the granddaughter

    lambda_3 = ln(2)/T_3
-/
/-- Both sides of "Decay constant of the granddaughter" carry the same physical dimension. -/
theorem eq6_lam3_dim : d_lambda_3 = (Dim.div Dim.one d_T_3) := by decide
theorem eq6_lam3_term1 : Dim.one = Dim.one := by decide
/-- The argument `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_lam3_reg1  : 0 < (2 : ℝ) := by positivity
/-- The denominator `T_3` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_lam3_reg2 (T_3 : ℝ) (hT_3 : 0 < T_3) : T_3 ≠ 0 := by positivity

/-! ## 7. Initial daughter inventory

    N_20 = 0*N_0
-/
/-- Both sides of "Initial daughter inventory" carry the same physical dimension. -/
theorem eq7_ic_dim : d_N_20 = (Dim.mul Dim.one d_N_0) := by decide

/-! ## 8. Time of maximum daughter activity

    t_max = ln(lambda_2/lambda_1)/(lambda_2 - lambda_1)
-/
/-- Both sides of "Time of maximum daughter activity" carry the same physical dimension. -/
theorem eq8_tm_dim : d_t_max = (Dim.div Dim.one d_lambda_2) := by decide
theorem eq8_tm_term1 : (Dim.div d_lambda_2 d_lambda_1) = Dim.one := by decide
theorem eq8_tm_term2 : d_lambda_2 = d_lambda_1 := by decide
/-- The denominator `lambda_1` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_tm_reg1 (lambda_1 : ℝ) (hlambda_1 : 0 < lambda_1) : lambda_1 ≠ 0 := by positivity
/-- The argument `lambda_2 / lambda_1` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_tm_reg2 (lambda_2 lambda_1 : ℝ) (hlambda_2 : 0 < lambda_2) (hlambda_1 : 0 < lambda_1) : 0 < lambda_2 / lambda_1 := by positivity
/-- Domain condition for `lambda_2 - lambda_1`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq8_tm_cond3 (lambda_2 lambda_1 : ℝ) (hdom : lambda_2 - lambda_1 ≠ 0) : lambda_2 - lambda_1 ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq8_tm_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

end Bespoke
