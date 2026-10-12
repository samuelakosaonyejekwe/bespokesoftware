import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Newcomb's problem

Machine-checkable statements for this investigation (newcomb-problem).
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
def d_EV_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Expected utility of taking one box [1]
def d_EV_2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Expected utility of taking both boxes [1]
def d_K_small : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Amount in the transparent box [1]
def d_M_big : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Amount in the opaque box if one-boxing was predicted [1]
def d_dEV : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Advantage of one-boxing [1]
def d_p_acc : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Predictor accuracy [1]
def d_p_star : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Accuracy at which the two acts are equally good [1]

/-! ## 1. Expected utility of one box

    EV_1 = p_acc*M_big
-/
/-- Both sides of "Expected utility of one box" carry the same physical dimension. -/
theorem eq1_ev1_dim : d_EV_1 = (Dim.mul d_p_acc d_M_big) := by decide

/-! ## 2. Expected utility of two boxes

    EV_2 = (1 - p_acc)*(M_big + K_small) + p_acc*K_small
-/
/-- Both sides of "Expected utility of two boxes" carry the same physical dimension. -/
theorem eq2_ev2_dim : d_EV_2 = (Dim.mul Dim.one d_M_big) := by decide
theorem eq2_ev2_term1 : Dim.one = d_p_acc := by decide
theorem eq2_ev2_term2 : d_M_big = d_K_small := by decide
theorem eq2_ev2_term3 : (Dim.mul Dim.one d_M_big) = (Dim.mul d_p_acc d_K_small) := by decide

/-! ## 3. Break-even accuracy

    p_star = (M_big + K_small)/(2*M_big)
-/
/-- Both sides of "Break-even accuracy" carry the same physical dimension. -/
theorem eq3_thr_dim : d_p_star = (Dim.div d_M_big (Dim.mul Dim.one d_M_big)) := by decide
theorem eq3_thr_term1 : d_M_big = d_K_small := by decide
/-- The denominator `2 * M_big` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_thr_reg1 (M_big : ℝ) (hM_big : 0 < M_big) : (2 : ℝ) * M_big ≠ 0 := by positivity

/-! ## 4. Advantage of one-boxing

    dEV = EV_1 - EV_2
-/
/-- Both sides of "Advantage of one-boxing" carry the same physical dimension. -/
theorem eq4_adv_dim : d_dEV = d_EV_1 := by decide
theorem eq4_adv_term1 : d_EV_1 = d_EV_2 := by decide

/-! ## Logical structure of the argument -/

/-- The premises are jointly contradictory. -/
theorem premises_inconsistent (Accurate Dominance MaxEU OneBox : Prop) (h1 : Dominance → (¬OneBox)) (h2 : (MaxEU ∧ Accurate) → OneBox) (h3 : Accurate) (h4 : Dominance) (h5 : MaxEU) : False := by tauto

end Bespoke
