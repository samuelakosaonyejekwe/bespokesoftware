import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Thick-walled cylinder under pressure (Lamé)

Machine-checkable statements for this investigation (pressure-vessel-lame).
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
def d_A_l : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Lamé constant A [Pa]
def d_B_l : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Lamé constant B [N]
def d_p_b : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Burst pressure [Pa]
def d_p_i : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Internal pressure [bar]
def d_p_o : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- External pressure [bar]
def d_r : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Radius [m]
def d_r_i : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Inner radius [mm]
def d_r_o : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Outer radius [m]
def d_sigma_eq : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Equivalent stress [Pa]
def d_sigma_r : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Radial stress [Pa]
def d_sigma_theta : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Hoop stress [Pa]
def d_sigma_u : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Ultimate tensile strength [MPa]
def d_sigma_y : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Yield strength [MPa]
def d_sigma_z : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Axial stress [Pa]
def d_t_w : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Wall thickness [mm]

/-! ## 1. Outer radius

    r_o = r_i + t_w
-/
/-- Both sides of "Outer radius" carry the same physical dimension. -/
theorem eq1_ro_dim : d_r_o = d_r_i := by decide
theorem eq1_ro_term1 : d_r_i = d_t_w := by decide

/-! ## 2. Radial equilibrium

    pd(sigma_r, r) = (sigma_theta - sigma_r)/r
-/
/-- Both sides of "Radial equilibrium" carry the same physical dimension. -/
theorem eq2_eqm_dim : (Dim.div d_sigma_r d_r) = (Dim.div d_sigma_theta d_r) := by decide
theorem eq2_eqm_term1 : d_sigma_theta = d_sigma_r := by decide
/-- Domain condition for `r`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_eqm_cond1 (r : ℝ) (hdom : r ≠ 0) : r ≠ 0 := hdom

/-! ## 3. Lamé constant A

    A_l = (p_i*r_i^2 - p_o*r_o^2)/(r_o^2 - r_i^2)
-/
/-- Both sides of "Lamé constant A" carry the same physical dimension. -/
theorem eq3_A_dim : d_A_l = (Dim.div (Dim.mul d_p_i (Dim.pow d_r_i 2 1)) (Dim.pow d_r_o 2 1)) := by decide
theorem eq3_A_term1 : (Dim.mul d_p_i (Dim.pow d_r_i 2 1)) = (Dim.mul d_p_o (Dim.pow d_r_o 2 1)) := by decide
theorem eq3_A_term2 : (Dim.pow d_r_o 2 1) = (Dim.pow d_r_i 2 1) := by decide
/-- Domain condition for `r_o^2 - r_i^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_A_cond1 (r_o r_i : ℝ) (hdom : r_o ^ 2 - r_i ^ 2 ≠ 0) : r_o ^ 2 - r_i ^ 2 ≠ 0 := hdom

/-! ## 4. Lamé constant B

    B_l = (p_i - p_o)*r_i^2*r_o^2/(r_o^2 - r_i^2)
-/
/-- Both sides of "Lamé constant B" carry the same physical dimension. -/
theorem eq4_B_dim : d_B_l = (Dim.div (Dim.mul (Dim.mul d_p_i (Dim.pow d_r_i 2 1)) (Dim.pow d_r_o 2 1)) (Dim.pow d_r_o 2 1)) := by decide
theorem eq4_B_term1 : d_p_i = d_p_o := by decide
theorem eq4_B_term2 : (Dim.pow d_r_o 2 1) = (Dim.pow d_r_i 2 1) := by decide
/-- Domain condition for `r_o^2 - r_i^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_B_cond1 (r_o r_i : ℝ) (hdom : r_o ^ 2 - r_i ^ 2 ≠ 0) : r_o ^ 2 - r_i ^ 2 ≠ 0 := hdom

/-! ## 5. Radial stress

    sigma_r = A_l - B_l/r^2
-/
/-- Both sides of "Radial stress" carry the same physical dimension. -/
theorem eq5_sr_dim : d_sigma_r = d_A_l := by decide
theorem eq5_sr_term1 : d_A_l = (Dim.div d_B_l (Dim.pow d_r 2 1)) := by decide
/-- Domain condition for `r^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_sr_cond1 (r : ℝ) (hdom : r ^ 2 ≠ 0) : r ^ 2 ≠ 0 := hdom

/-! ## 6. Hoop stress

    sigma_theta = A_l + B_l/r^2
-/
/-- Both sides of "Hoop stress" carry the same physical dimension. -/
theorem eq6_sh_dim : d_sigma_theta = d_A_l := by decide
theorem eq6_sh_term1 : d_A_l = (Dim.div d_B_l (Dim.pow d_r 2 1)) := by decide
/-- Domain condition for `r^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_sh_cond1 (r : ℝ) (hdom : r ^ 2 ≠ 0) : r ^ 2 ≠ 0 := hdom

/-! ## 7. Axial stress with closed ends

    sigma_z = (p_i*r_i^2 - p_o*r_o^2)/(r_o^2 - r_i^2)
-/
/-- Both sides of "Axial stress with closed ends" carry the same physical dimension. -/
theorem eq7_sz_dim : d_sigma_z = (Dim.div (Dim.mul d_p_i (Dim.pow d_r_i 2 1)) (Dim.pow d_r_o 2 1)) := by decide
theorem eq7_sz_term1 : (Dim.mul d_p_i (Dim.pow d_r_i 2 1)) = (Dim.mul d_p_o (Dim.pow d_r_o 2 1)) := by decide
theorem eq7_sz_term2 : (Dim.pow d_r_o 2 1) = (Dim.pow d_r_i 2 1) := by decide
/-- Domain condition for `r_o^2 - r_i^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_sz_cond1 (r_o r_i : ℝ) (hdom : r_o ^ 2 - r_i ^ 2 ≠ 0) : r_o ^ 2 - r_i ^ 2 ≠ 0 := hdom

/-! ## 8. Von Mises equivalent stress

    sigma_eq = sqrt(0.5*((sigma_theta - sigma_r)^2 + (sigma_r - sigma_z)^2 + (sigma_z - sigma_theta)^2))
-/
/-- Both sides of "Von Mises equivalent stress" carry the same physical dimension. -/
theorem eq8_eq_dim : d_sigma_eq = (Dim.pow (Dim.mul Dim.one (Dim.pow d_sigma_theta 2 1)) 1 2) := by decide
theorem eq8_eq_term1 : d_sigma_theta = d_sigma_r := by decide
theorem eq8_eq_term2 : d_sigma_r = d_sigma_z := by decide
theorem eq8_eq_term3 : (Dim.pow d_sigma_theta 2 1) = (Dim.pow d_sigma_r 2 1) := by decide
theorem eq8_eq_term4 : d_sigma_z = d_sigma_theta := by decide
theorem eq8_eq_term5 : (Dim.pow d_sigma_theta 2 1) = (Dim.pow d_sigma_z 2 1) := by decide
/-- Domain condition for `0.5 * ((sigma_theta - sigma_r)^2 + (sigma_r - sigma_z)^2 + (sigma_z - sigma_theta)^2)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq8_eq_cond1 (sigma_theta sigma_r sigma_z : ℝ) (hdom : 0 ≤ (0.5 : ℝ) * ((sigma_theta - sigma_r) ^ 2 + (sigma_r - sigma_z) ^ 2 + (sigma_z - sigma_theta) ^ 2)) : 0 ≤ (0.5 : ℝ) * ((sigma_theta - sigma_r) ^ 2 + (sigma_r - sigma_z) ^ 2 + (sigma_z - sigma_theta) ^ 2) := hdom

/-! ## 9. Burst pressure

    p_b = 2/sqrt(3)*sigma_y*(2 - sigma_y/max(sigma_u, sigma_y))*ln(r_o/r_i)
-/
/-- Both sides of "Burst pressure" carry the same physical dimension. -/
theorem eq9_pb_dim : d_p_b = (Dim.mul (Dim.mul (Dim.mul (Dim.div Dim.one (Dim.pow Dim.one 1 2)) d_sigma_y) Dim.one) Dim.one) := by decide
theorem eq9_pb_term1 : d_sigma_u = d_sigma_y := by decide
theorem eq9_pb_term2 : Dim.one = (Dim.div d_sigma_y d_sigma_u) := by decide
theorem eq9_pb_term3 : (Dim.div d_r_o d_r_i) = Dim.one := by decide
/-- The argument `3` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_pb_reg1  : 0 ≤ (3 : ℝ) := by positivity
/-- The denominator `sqrt(3)` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_pb_reg2  : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `max(sigma_u, sigma_y)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq9_pb_cond3 (sigma_u sigma_y : ℝ) (hdom : max sigma_u sigma_y ≠ 0) : max sigma_u sigma_y ≠ 0 := hdom
/-- The denominator `r_i` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_pb_reg4 (r_i : ℝ) (hr_i : 0 < r_i) : r_i ≠ 0 := by positivity
/-- Domain condition for `r_o / r_i`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq9_pb_cond5 (r_o r_i : ℝ) (hdom : 0 < r_o / r_i) : 0 < r_o / r_i := hdom

end Bespoke
