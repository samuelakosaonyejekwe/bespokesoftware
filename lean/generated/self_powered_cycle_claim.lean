import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Test of a self-powered or over-unity device claim

Machine-checkable statements for this investigation (self-powered-cycle-claim).
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
def d_P_allow : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Largest admissible output [W]
def d_P_hid : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Hidden input needed to reconcile the claim [W]
def d_P_in : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Claimed input power [W]
def d_P_out : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Claimed output power [W]
def d_S_gen : Dim := ⟨12, 24, -36, 0, -12, 0, 0⟩  -- Entropy generation rate implied by the claim [W/K]
def d_T_c : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Heat-sink (ambient) temperature [°C]
def d_T_h : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Heat-source temperature [°C]
def d_eta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Claimed efficiency [1]
def d_eta_C : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Carnot efficiency [1]
def d_eta_lim : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Applicable efficiency limit [1]
def d_f_viol : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Second-law violation factor (multiplies the Carnot limit; 1 in our world) [1]

/-! ## 1. Claimed efficiency

    eta = P_out/P_in
-/
/-- Both sides of "Claimed efficiency" carry the same physical dimension. -/
theorem eq1_eta_dim : d_eta = (Dim.div d_P_out d_P_in) := by decide
/-- The denominator `P_in` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_eta_reg1 (P_in : ℝ) (hP_in : 0 < P_in) : P_in ≠ 0 := by positivity

/-! ## 2. Carnot efficiency

    eta_C = 1 - T_c/T_h
-/
/-- Both sides of "Carnot efficiency" carry the same physical dimension. -/
theorem eq2_carnot_dim : d_eta_C = Dim.one := by decide
theorem eq2_carnot_term1 : Dim.one = (Dim.div d_T_c d_T_h) := by decide
/-- The denominator `T_h` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_carnot_reg1 (T_h : ℝ) (hT_h : 0 < T_h) : T_h ≠ 0 := by positivity

/-! ## 3. Efficiency limit

    eta_lim = min(1, f_viol*eta_C)
-/
/-- Both sides of "Efficiency limit" carry the same physical dimension. -/
theorem eq3_lim_dim : d_eta_lim = Dim.one := by decide
theorem eq3_lim_term1 : Dim.one = (Dim.mul d_f_viol d_eta_C) := by decide

/-! ## 4. Largest admissible output

    P_allow = eta_lim*P_in
-/
/-- Both sides of "Largest admissible output" carry the same physical dimension. -/
theorem eq4_allow_dim : d_P_allow = (Dim.mul d_eta_lim d_P_in) := by decide

/-! ## 5. Hidden input that would reconcile the claim

    P_hid = max(P_out - P_allow, 0)
-/
/-- Both sides of "Hidden input that would reconcile the claim" carry the same physical dimension. -/
theorem eq5_hid_dim : d_P_hid = d_P_out := by decide
theorem eq5_hid_term1 : d_P_out = d_P_allow := by decide

/-! ## 6. Entropy generation rate implied by the claim

    S_gen = (P_in - P_out)/T_c - P_in/T_h
-/
/-- Both sides of "Entropy generation rate implied by the claim" carry the same physical dimension. -/
theorem eq6_sgen_dim : d_S_gen = (Dim.div d_P_in d_T_c) := by decide
theorem eq6_sgen_term1 : d_P_in = d_P_out := by decide
theorem eq6_sgen_term2 : (Dim.div d_P_in d_T_c) = (Dim.div d_P_in d_T_h) := by decide
/-- The denominator `T_c` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_sgen_reg1 (T_c : ℝ) (hT_c : 0 < T_c) : T_c ≠ 0 := by positivity
/-- The denominator `T_h` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_sgen_reg2 (T_h : ℝ) (hT_h : 0 < T_h) : T_h ≠ 0 := by positivity

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (C F H K O W : Prop) (h1 : (F ∧ C) → (¬O)) (h2 : (K ∧ H) → (¬W)) (h3 : F) (h4 : K) (h5 : C) (h6 : H) : (¬O) ∧ (¬W) := by tauto

end Bespoke
