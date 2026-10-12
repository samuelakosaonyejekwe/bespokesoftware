import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Monty Hall problem

Machine-checkable statements for this investigation (monty-hall).
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
def d_A_sw : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Advantage ratio of switching [1]
def d_P_st : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Probability of winning by staying [1]
def d_P_sw : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Probability of winning by switching to one remaining door [1]
def d_k_open : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Doors opened by the host [1]
def d_n_d : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of doors [1]
def d_n_left : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Other doors left closed [1]
def d_n_trials : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Simulated games [1]
def d_sigma_mc : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Standard error of the simulated frequency [1]

/-! ## 1. Other doors left closed

    n_left = n_d - min(k_open, n_d - 2) - 1
-/
/-- Both sides of "Other doors left closed" carry the same physical dimension. -/
theorem eq1_left_dim : d_n_left = d_n_d := by decide
theorem eq1_left_term1 : d_n_d = Dim.one := by decide
theorem eq1_left_term2 : d_k_open = d_n_d := by decide
theorem eq1_left_term3 : d_n_d = d_k_open := by decide
theorem eq1_left_term4 : d_n_d = Dim.one := by decide

/-! ## 2. Winning by staying

    P_st = 1/n_d
-/
/-- Both sides of "Winning by staying" carry the same physical dimension. -/
theorem eq2_stay_dim : d_P_st = (Dim.div Dim.one d_n_d) := by decide
/-- The denominator `n_d` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_stay_reg1 (n_d : ℝ) (hn_d : 0 < n_d) : n_d ≠ 0 := by positivity

/-! ## 3. Winning by switching to one of the remaining doors

    P_sw = (n_d - 1)/(n_d*n_left)
-/
/-- Both sides of "Winning by switching to one of the remaining doors" carry the same physical dimension. -/
theorem eq3_switch_dim : d_P_sw = (Dim.div d_n_d (Dim.mul d_n_d d_n_left)) := by decide
theorem eq3_switch_term1 : d_n_d = Dim.one := by decide
/-- The denominator `n_d * n_left` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_switch_reg1 (n_d n_left : ℝ) (hn_d : 0 < n_d) (hn_left : 0 < n_left) : n_d * n_left ≠ 0 := by positivity

/-! ## 4. Advantage of switching

    A_sw = P_sw/P_st
-/
/-- Both sides of "Advantage of switching" carry the same physical dimension. -/
theorem eq4_adv_dim : d_A_sw = (Dim.div d_P_sw d_P_st) := by decide
/-- The denominator `P_st` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_adv_reg1 (P_st : ℝ) (hP_st : 0 < P_st) : P_st ≠ 0 := by positivity

/-! ## 5. Standard error of a simulated frequency

    sigma_mc = sqrt(P_sw*(1 - P_sw)/n_trials)
-/
/-- Both sides of "Standard error of a simulated frequency" carry the same physical dimension. -/
theorem eq5_se_dim : d_sigma_mc = (Dim.pow (Dim.div (Dim.mul d_P_sw Dim.one) d_n_trials) 1 2) := by decide
theorem eq5_se_term1 : Dim.one = d_P_sw := by decide
/-- The denominator `n_trials` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_se_reg1 (n_trials : ℝ) (hn_trials : 0 < n_trials) : n_trials ≠ 0 := by positivity
/-- Domain condition for `P_sw * (1 - P_sw) / n_trials`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_se_cond2 (P_sw n_trials : ℝ) (hdom : 0 ≤ P_sw * ((1 : ℝ) - P_sw) / n_trials) : 0 ≤ P_sw * ((1 : ℝ) - P_sw) / n_trials := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq5_se_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (FirstCar HostGoat StayWins SwitchWins : Prop) (h1 : HostGoat) (h2 : FirstCar → StayWins) (h3 : ((¬FirstCar) ∧ HostGoat) → SwitchWins) (h4 : StayWins ↔ (¬SwitchWins)) : SwitchWins ↔ (¬FirstCar) := by tauto

end Bespoke
