import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Simpson's paradox

Machine-checkable statements for this investigation (simpsons-paradox).
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
def d_d_adj : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Difference in success rate, A minus B, standardised to the whole population [1]
def d_d_agg : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Difference in pooled success rate, A minus B [1]
def d_n_A1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Group 1, treatment A: patients [1]
def d_n_A2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Group 2, treatment A: patients [1]
def d_n_B1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Group 1, treatment B: patients [1]
def d_n_B2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Group 2, treatment B: patients [1]
def d_p_A : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Pooled success rate of A [1]
def d_p_A1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Success rate of A in group 1 [1]
def d_p_A2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Success rate of A in group 2 [1]
def d_p_B : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Pooled success rate of B [1]
def d_p_B1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Success rate of B in group 1 [1]
def d_p_B2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Success rate of B in group 2 [1]
def d_s_A1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Group 1, treatment A: successes [1]
def d_s_A2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Group 2, treatment A: successes [1]
def d_s_B1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Group 1, treatment B: successes [1]
def d_s_B2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Group 2, treatment B: successes [1]
def d_w_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Share of all patients who are in group 1 [1]
def d_w_A : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Share of A patients who are in group 1 [1]
def d_w_B : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Share of B patients who are in group 1 [1]

/-! ## 1. Success rate of A in group 1

    p_A1 = min(s_A1, n_A1)/n_A1
-/
/-- Both sides of "Success rate of A in group 1" carry the same physical dimension. -/
theorem eq1_ra1_dim : d_p_A1 = (Dim.div d_s_A1 d_n_A1) := by decide
theorem eq1_ra1_term1 : d_s_A1 = d_n_A1 := by decide
/-- The denominator `n_A1` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_ra1_reg1 (n_A1 : ℝ) (hn_A1 : 0 < n_A1) : n_A1 ≠ 0 := by positivity

/-! ## 2. Success rate of A in group 2

    p_A2 = min(s_A2, n_A2)/n_A2
-/
/-- Both sides of "Success rate of A in group 2" carry the same physical dimension. -/
theorem eq2_ra2_dim : d_p_A2 = (Dim.div d_s_A2 d_n_A2) := by decide
theorem eq2_ra2_term1 : d_s_A2 = d_n_A2 := by decide
/-- The denominator `n_A2` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_ra2_reg1 (n_A2 : ℝ) (hn_A2 : 0 < n_A2) : n_A2 ≠ 0 := by positivity

/-! ## 3. Success rate of B in group 1

    p_B1 = min(s_B1, n_B1)/n_B1
-/
/-- Both sides of "Success rate of B in group 1" carry the same physical dimension. -/
theorem eq3_rb1_dim : d_p_B1 = (Dim.div d_s_B1 d_n_B1) := by decide
theorem eq3_rb1_term1 : d_s_B1 = d_n_B1 := by decide
/-- The denominator `n_B1` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_rb1_reg1 (n_B1 : ℝ) (hn_B1 : 0 < n_B1) : n_B1 ≠ 0 := by positivity

/-! ## 4. Success rate of B in group 2

    p_B2 = min(s_B2, n_B2)/n_B2
-/
/-- Both sides of "Success rate of B in group 2" carry the same physical dimension. -/
theorem eq4_rb2_dim : d_p_B2 = (Dim.div d_s_B2 d_n_B2) := by decide
theorem eq4_rb2_term1 : d_s_B2 = d_n_B2 := by decide
/-- The denominator `n_B2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_rb2_reg1 (n_B2 : ℝ) (hn_B2 : 0 < n_B2) : n_B2 ≠ 0 := by positivity

/-! ## 5. Share of all patients in group 1

    w_1 = (n_A1 + n_B1)/(n_A1 + n_A2 + n_B1 + n_B2)
-/
/-- Both sides of "Share of all patients in group 1" carry the same physical dimension. -/
theorem eq5_w1_dim : d_w_1 = (Dim.div d_n_A1 d_n_A1) := by decide
theorem eq5_w1_term1 : d_n_A1 = d_n_B1 := by decide
theorem eq5_w1_term2 : d_n_A1 = d_n_A2 := by decide
theorem eq5_w1_term3 : d_n_A1 = d_n_B1 := by decide
theorem eq5_w1_term4 : d_n_A1 = d_n_B2 := by decide
/-- The denominator `n_A1 + n_A2 + n_B1 + n_B2` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_w1_reg1 (n_A1 n_A2 n_B1 n_B2 : ℝ) (hn_A1 : 0 < n_A1) (hn_A2 : 0 < n_A2) (hn_B1 : 0 < n_B1) (hn_B2 : 0 < n_B2) : n_A1 + n_A2 + n_B1 + n_B2 ≠ 0 := by positivity

/-! ## 6. Share of A patients in group 1

    w_A = n_A1/(n_A1 + n_A2)
-/
/-- Both sides of "Share of A patients in group 1" carry the same physical dimension. -/
theorem eq6_wa_dim : d_w_A = (Dim.div d_n_A1 d_n_A1) := by decide
theorem eq6_wa_term1 : d_n_A1 = d_n_A2 := by decide
/-- The denominator `n_A1 + n_A2` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_wa_reg1 (n_A1 n_A2 : ℝ) (hn_A1 : 0 < n_A1) (hn_A2 : 0 < n_A2) : n_A1 + n_A2 ≠ 0 := by positivity

/-! ## 7. Share of B patients in group 1

    w_B = n_B1/(n_B1 + n_B2)
-/
/-- Both sides of "Share of B patients in group 1" carry the same physical dimension. -/
theorem eq7_wb_dim : d_w_B = (Dim.div d_n_B1 d_n_B1) := by decide
theorem eq7_wb_term1 : d_n_B1 = d_n_B2 := by decide
/-- The denominator `n_B1 + n_B2` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_wb_reg1 (n_B1 n_B2 : ℝ) (hn_B1 : 0 < n_B1) (hn_B2 : 0 < n_B2) : n_B1 + n_B2 ≠ 0 := by positivity

/-! ## 8. Pooled success rate of A

    p_A = w_A*p_A1 + (1 - w_A)*p_A2
-/
/-- Both sides of "Pooled success rate of A" carry the same physical dimension. -/
theorem eq8_pa_dim : d_p_A = (Dim.mul d_w_A d_p_A1) := by decide
theorem eq8_pa_term1 : Dim.one = d_w_A := by decide
theorem eq8_pa_term2 : (Dim.mul d_w_A d_p_A1) = (Dim.mul Dim.one d_p_A2) := by decide

/-! ## 9. Pooled success rate of B

    p_B = w_B*p_B1 + (1 - w_B)*p_B2
-/
/-- Both sides of "Pooled success rate of B" carry the same physical dimension. -/
theorem eq9_pb_dim : d_p_B = (Dim.mul d_w_B d_p_B1) := by decide
theorem eq9_pb_term1 : Dim.one = d_w_B := by decide
theorem eq9_pb_term2 : (Dim.mul d_w_B d_p_B1) = (Dim.mul Dim.one d_p_B2) := by decide

/-! ## 10. Pooled difference

    d_agg = p_A - p_B
-/
/-- Both sides of "Pooled difference" carry the same physical dimension. -/
theorem eq10_agg_dim : d_d_agg = d_p_A := by decide
theorem eq10_agg_term1 : d_p_A = d_p_B := by decide

/-! ## 11. Standardised difference

    d_adj = w_1*(p_A1 - p_B1) + (1 - w_1)*(p_A2 - p_B2)
-/
/-- Both sides of "Standardised difference" carry the same physical dimension. -/
theorem eq11_adj_dim : d_d_adj = (Dim.mul d_w_1 d_p_A1) := by decide
theorem eq11_adj_term1 : d_p_A1 = d_p_B1 := by decide
theorem eq11_adj_term2 : Dim.one = d_w_1 := by decide
theorem eq11_adj_term3 : d_p_A2 = d_p_B2 := by decide
theorem eq11_adj_term4 : (Dim.mul d_w_1 d_p_A1) = (Dim.mul Dim.one d_p_A2) := by decide

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (Better1 Better2 BetterAll : Prop) (h1 : Better1) (h2 : Better2) (h3 : ¬BetterAll) : ¬((Better1 ∧ Better2) → BetterAll) := by tauto

end Bespoke
