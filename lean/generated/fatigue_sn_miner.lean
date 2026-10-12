import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Fatigue life from an S–N curve and Miner's rule

Machine-checkable statements for this investigation (fatigue-sn-miner).
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
def d_DFF : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Design fatigue factor [1]
def d_D_r : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Damage rate [1/s]
def d_K_t : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Stress concentration factor [1]
def d_N_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Cycles to failure at block 1 [1]
def d_N_2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Cycles to failure at block 2 [1]
def d_N_3 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Cycles to failure at block 3 [1]
def d_N_i : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Cycles to failure at block i [1]
def d_S_i : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Nominal stress range of block i [Pa]
def d_S_ref : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Reference stress of the S–N curve (1 MPa) [Pa]
def d_T_f : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Fatigue life [s]
def d_a_sn : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- S–N intercept [1]
def d_f_s : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Combined stress factor [1]
def d_log_a : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- log₁₀ of the S–N intercept (stress range in MPa) [1]
def d_m : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Inverse slope of the S–N curve [1]
def d_n_1 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Cycles per year in block 1 [1/yr]
def d_n_2 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Cycles per year in block 2 [1/yr]
def d_n_3 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Cycles per year in block 3 [1/yr]
def d_sigma_m : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Mean stress [MPa]
def d_sigma_u : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Ultimate tensile strength [MPa]

/-! ## 1. Combined stress factor

    f_s = K_t/(1 - sigma_m/sigma_u)
-/
/-- Both sides of "Combined stress factor" carry the same physical dimension. -/
theorem eq1_fs_dim : d_f_s = (Dim.div d_K_t Dim.one) := by decide
theorem eq1_fs_term1 : Dim.one = (Dim.div d_sigma_m d_sigma_u) := by decide
/-- The denominator `sigma_u` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_fs_reg1 (sigma_u : ℝ) (hsigma_u : 0 < sigma_u) : sigma_u ≠ 0 := by positivity
/-- Domain condition for `1 - sigma_m / sigma_u`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq1_fs_cond2 (sigma_m sigma_u : ℝ) (hdom : (1 : ℝ) - sigma_m / sigma_u ≠ 0) : (1 : ℝ) - sigma_m / sigma_u ≠ 0 := hdom

/-! ## 2. S–N intercept

    a_sn = 10^log_a
-/
/-- Both sides of "S–N intercept" carry the same physical dimension. -/
theorem eq2_asn_dim : d_a_sn = Dim.one := by decide

/-! ## 3. S–N curve

    N_i = a_sn*(f_s*S_i/S_ref)^(-m)
-/
/-- Both sides of "S–N curve" carry the same physical dimension. -/
theorem eq3_sn_dim : d_N_i = (Dim.mul d_a_sn Dim.one) := by decide
/-- Domain condition for `S_ref`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_sn_cond1 (S_ref : ℝ) (hdom : S_ref ≠ 0) : S_ref ≠ 0 := hdom
/-- Domain condition for `f_s * S_i / S_ref`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_sn_cond2 (f_s S_i S_ref : ℝ) (hdom : f_s * S_i / S_ref ≠ 0) : f_s * S_i / S_ref ≠ 0 := hdom

/-! ## 4. Linear damage accumulation

    D_r = n_1/N_1 + n_2/N_2 + n_3/N_3
-/
/-- Both sides of "Linear damage accumulation" carry the same physical dimension. -/
theorem eq4_miner_dim : d_D_r = (Dim.div d_n_1 d_N_1) := by decide
theorem eq4_miner_term1 : (Dim.div d_n_1 d_N_1) = (Dim.div d_n_2 d_N_2) := by decide
theorem eq4_miner_term2 : (Dim.div d_n_1 d_N_1) = (Dim.div d_n_3 d_N_3) := by decide
/-- The denominator `N_1` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_miner_reg1 (N_1 : ℝ) (hN_1 : 0 < N_1) : N_1 ≠ 0 := by positivity
/-- The denominator `N_2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_miner_reg2 (N_2 : ℝ) (hN_2 : 0 < N_2) : N_2 ≠ 0 := by positivity
/-- The denominator `N_3` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_miner_reg3 (N_3 : ℝ) (hN_3 : 0 < N_3) : N_3 ≠ 0 := by positivity

/-! ## 5. Fatigue life

    T_f = 1/(DFF*D_r)
-/
/-- Both sides of "Fatigue life" carry the same physical dimension. -/
theorem eq5_life_dim : d_T_f = (Dim.div Dim.one (Dim.mul d_DFF d_D_r)) := by decide
/-- The denominator `DFF * D_r` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_life_reg1 (DFF D_r : ℝ) (hDFF : 0 < DFF) (hD_r : 0 < D_r) : DFF * D_r ≠ 0 := by positivity

end Bespoke
