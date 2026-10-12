import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Column buckling: Euler, Johnson and imperfect columns

Machine-checkable statements for this investigation (column-buckling).
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
def d_A : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Cross-sectional area [cm^2]
def d_E : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Young's modulus [GPa]
def d_I_b : Dim := ⟨0, 48, 0, 0, 0, 0, 0⟩  -- Second moment of area about the buckling axis [cm^4]
def d_K : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Effective-length factor [1]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Column length [m]
def d_P : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Applied axial load [kN]
def d_P_E : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Euler critical load [N]
def d_P_cr : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Critical load [N]
def d_c_y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance from the centroid to the extreme fibre [mm]
def d_delta : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Lateral deflection at mid-height [m]
def d_e_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Initial bow amplitude or load eccentricity [mm]
def d_lambda : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Slenderness ratio [1]
def d_lambda_c : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Transition slenderness [1]
def d_r_g : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Radius of gyration [m]
def d_sigma_cr : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Critical stress [Pa]
def d_sigma_max : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Peak compressive stress [Pa]
def d_sigma_y : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Yield strength [MPa]

/-! ## 1. Radius of gyration

    r_g = sqrt(I_b/A)
-/
/-- Both sides of "Radius of gyration" carry the same physical dimension. -/
theorem eq1_rg_dim : d_r_g = (Dim.pow (Dim.div d_I_b d_A) 1 2) := by decide
/-- The denominator `A` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_rg_reg1 (A : ℝ) (hA : 0 < A) : A ≠ 0 := by positivity
/-- The argument `I_b / A` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_rg_reg2 (I_b A : ℝ) (hI_b : 0 < I_b) (hA : 0 < A) : 0 ≤ I_b / A := by positivity

/-! ## 2. Slenderness ratio

    lambda = K*L/r_g
-/
/-- Both sides of "Slenderness ratio" carry the same physical dimension. -/
theorem eq2_lam_dim : d_lambda = (Dim.div (Dim.mul d_K d_L) d_r_g) := by decide
/-- The denominator `r_g` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_lam_reg1 (r_g : ℝ) (hr_g : 0 < r_g) : r_g ≠ 0 := by positivity

/-! ## 3. Euler critical load

    P_E = pi^2*E*I_b/(K*L)^2
-/
/-- Both sides of "Euler critical load" carry the same physical dimension. -/
theorem eq3_pe_dim : d_P_E = (Dim.div (Dim.mul (Dim.mul (Dim.pow Dim.one 2 1) d_E) d_I_b) (Dim.pow (Dim.mul d_K d_L) 2 1)) := by decide
/-- The denominator `(K * L)^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_pe_reg1 (K L : ℝ) (hK : 0 < K) (hL : 0 < L) : (K * L) ^ 2 ≠ 0 := by positivity

/-! ## 4. Transition slenderness

    lambda_c = pi*sqrt(2*E/sigma_y)
-/
/-- Both sides of "Transition slenderness" carry the same physical dimension. -/
theorem eq4_lc_dim : d_lambda_c = (Dim.mul Dim.one (Dim.pow (Dim.div (Dim.mul Dim.one d_E) d_sigma_y) 1 2)) := by decide
/-- The denominator `sigma_y` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_lc_reg1 (sigma_y : ℝ) (hsigma_y : 0 < sigma_y) : sigma_y ≠ 0 := by positivity
/-- The argument `2 * E / sigma_y` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_lc_reg2 (E sigma_y : ℝ) (hE : 0 < E) (hsigma_y : 0 < sigma_y) : 0 ≤ (2 : ℝ) * E / sigma_y := by positivity

/-! ## 5. Critical stress: Johnson parabola below the transition, Euler hyperbola above

    sigma_cr = ifpos(lambda_c - lambda, sigma_y*(1 - sigma_y*lambda^2/(4*pi^2*E)), pi^2*E/lambda^2)
-/
/-- Both sides of "Critical stress: Johnson parabola below the transition, Euler hyperbola above" carry the same physical dimension. -/
theorem eq5_scr_dim : d_sigma_cr = (Dim.mul d_sigma_y Dim.one) := by decide
theorem eq5_scr_term1 : d_lambda_c = d_lambda := by decide
theorem eq5_scr_term2 : Dim.one = (Dim.div (Dim.mul d_sigma_y (Dim.pow d_lambda 2 1)) (Dim.mul (Dim.mul Dim.one (Dim.pow Dim.one 2 1)) d_E)) := by decide
theorem eq5_scr_term3 : (Dim.mul d_sigma_y Dim.one) = (Dim.div (Dim.mul (Dim.pow Dim.one 2 1) d_E) (Dim.pow d_lambda 2 1)) := by decide
/-- The denominator `4 * pi^2 * E` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_scr_reg1 (E : ℝ) (hE : 0 < E) : (4 : ℝ) * Real.pi ^ 2 * E ≠ 0 := by positivity
/-- The denominator `lambda^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_scr_reg2 (lambda : ℝ) (hlambda : 0 < lambda) : lambda ^ 2 ≠ 0 := by positivity

/-! ## 6. Critical load

    P_cr = sigma_cr*A
-/
/-- Both sides of "Critical load" carry the same physical dimension. -/
theorem eq6_pcr_dim : d_P_cr = (Dim.mul d_sigma_cr d_A) := by decide

/-! ## 7. Amplified bow

    delta = e_0/(1 - P/P_E)
-/
/-- Both sides of "Amplified bow" carry the same physical dimension. -/
theorem eq7_dl_dim : d_delta = (Dim.div d_e_0 Dim.one) := by decide
theorem eq7_dl_term1 : Dim.one = (Dim.div d_P d_P_E) := by decide
/-- The denominator `P_E` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_dl_reg1 (P_E : ℝ) (hP_E : 0 < P_E) : P_E ≠ 0 := by positivity
/-- Domain condition for `1 - P / P_E`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_dl_cond2 (P P_E : ℝ) (hdom : (1 : ℝ) - P / P_E ≠ 0) : (1 : ℝ) - P / P_E ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq7_dl_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 8. Peak stress

    sigma_max = P/A + P*delta*c_y/I_b
-/
/-- Both sides of "Peak stress" carry the same physical dimension. -/
theorem eq8_sm_dim : d_sigma_max = (Dim.div d_P d_A) := by decide
theorem eq8_sm_term1 : (Dim.div d_P d_A) = (Dim.div (Dim.mul (Dim.mul d_P d_delta) d_c_y) d_I_b) := by decide
/-- The denominator `A` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_sm_reg1 (A : ℝ) (hA : 0 < A) : A ≠ 0 := by positivity
/-- The denominator `I_b` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_sm_reg2 (I_b : ℝ) (hI_b : 0 < I_b) : I_b ≠ 0 := by positivity

end Bespoke
