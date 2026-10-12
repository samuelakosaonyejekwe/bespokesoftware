import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Effective permittivity and conductivity of a filled composite

Machine-checkable statements for this investigation (effective-medium-composite).
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
def d_alpha_p : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Polarisability factor of an inclusion [1]
def d_eps_BR : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Bruggeman effective permittivity [1]
def d_eps_HSL : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Hashin–Shtrikman lower bound [1]
def d_eps_HSU : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Hashin–Shtrikman upper bound [1]
def d_eps_MG : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Maxwell Garnett effective permittivity [1]
def d_eps_Whi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Wiener upper bound (parallel) [1]
def d_eps_Wlo : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Wiener lower bound (series) [1]
def d_eps_i : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Relative permittivity of the filler [1]
def d_eps_m : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Relative permittivity of the matrix [1]
def d_phi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Filler volume fraction [1]
def d_sigma_MG : Dim := ⟨-12, -36, 36, 24, 0, 0, 0⟩  -- Maxwell Garnett effective conductivity [S/m]
def d_sigma_i : Dim := ⟨-12, -36, 36, 24, 0, 0, 0⟩  -- Conductivity of the filler [S/m]
def d_sigma_m : Dim := ⟨-12, -36, 36, 24, 0, 0, 0⟩  -- Conductivity of the matrix [S/m]

/-! ## 1. Polarisability factor

    alpha_p = (eps_i - eps_m)/(eps_i + 2*eps_m)
-/
/-- Both sides of "Polarisability factor" carry the same physical dimension. -/
theorem eq1_ap_dim : d_alpha_p = (Dim.div d_eps_i d_eps_i) := by decide
theorem eq1_ap_term1 : d_eps_i = d_eps_m := by decide
theorem eq1_ap_term2 : d_eps_i = (Dim.mul Dim.one d_eps_m) := by decide
/-- The denominator `eps_i + 2 * eps_m` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_ap_reg1 (eps_i eps_m : ℝ) (heps_i : 0 < eps_i) (heps_m : 0 < eps_m) : eps_i + (2 : ℝ) * eps_m ≠ 0 := by positivity

/-! ## 2. Maxwell Garnett mixing formula

    eps_MG = eps_m + phi*eps_m*(eps_i - eps_m)/(eps_m + 1/3*(1 - phi)*(eps_i - eps_m))
-/
/-- Both sides of "Maxwell Garnett mixing formula" carry the same physical dimension. -/
theorem eq2_mg_dim : d_eps_MG = d_eps_m := by decide
theorem eq2_mg_term1 : d_eps_i = d_eps_m := by decide
theorem eq2_mg_term2 : Dim.one = d_phi := by decide
theorem eq2_mg_term3 : d_eps_i = d_eps_m := by decide
theorem eq2_mg_term4 : d_eps_m = (Dim.mul (Dim.mul (Dim.div Dim.one Dim.one) Dim.one) d_eps_i) := by decide
theorem eq2_mg_term5 : d_eps_m = (Dim.div (Dim.mul (Dim.mul d_phi d_eps_m) d_eps_i) d_eps_m) := by decide
/-- The denominator `3` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_mg_reg1  : (3 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `eps_m + 1 / 3 * (1 - phi) * (eps_i - eps_m)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_mg_cond2 (eps_m phi eps_i : ℝ) (hdom : eps_m + (1 : ℝ) / (3 : ℝ) * ((1 : ℝ) - phi) * (eps_i - eps_m) ≠ 0) : eps_m + (1 : ℝ) / (3 : ℝ) * ((1 : ℝ) - phi) * (eps_i - eps_m) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq2_mg_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 3. Bruggeman self-consistency condition

    phi*(eps_i - eps_BR)/(eps_BR + 1/3*(eps_i - eps_BR)) + (1 - phi)*(eps_m - eps_BR)/(eps_BR + 1/3*(eps_m - eps_BR)) = 0
-/
/-- Both sides of "Bruggeman self-consistency condition" carry the same physical dimension. -/
theorem eq3_br_dim : (Dim.div (Dim.mul d_phi d_eps_i) d_eps_BR) = Dim.one := by decide
theorem eq3_br_term1 : d_eps_i = d_eps_BR := by decide
theorem eq3_br_term2 : d_eps_i = d_eps_BR := by decide
theorem eq3_br_term3 : d_eps_BR = (Dim.mul (Dim.div Dim.one Dim.one) d_eps_i) := by decide
theorem eq3_br_term4 : Dim.one = d_phi := by decide
theorem eq3_br_term5 : d_eps_m = d_eps_BR := by decide
theorem eq3_br_term6 : d_eps_m = d_eps_BR := by decide
theorem eq3_br_term7 : d_eps_BR = (Dim.mul (Dim.div Dim.one Dim.one) d_eps_m) := by decide
theorem eq3_br_term8 : (Dim.div (Dim.mul d_phi d_eps_i) d_eps_BR) = (Dim.div (Dim.mul Dim.one d_eps_m) d_eps_BR) := by decide
/-- The denominator `3` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_br_reg1  : (3 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `eps_BR + 1 / 3 * (eps_i - eps_BR)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_br_cond2 (eps_BR eps_i : ℝ) (hdom : eps_BR + (1 : ℝ) / (3 : ℝ) * (eps_i - eps_BR) ≠ 0) : eps_BR + (1 : ℝ) / (3 : ℝ) * (eps_i - eps_BR) ≠ 0 := hdom
/-- The denominator `3` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_br_reg3  : (3 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `eps_BR + 1 / 3 * (eps_m - eps_BR)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_br_cond4 (eps_BR eps_m : ℝ) (hdom : eps_BR + (1 : ℝ) / (3 : ℝ) * (eps_m - eps_BR) ≠ 0) : eps_BR + (1 : ℝ) / (3 : ℝ) * (eps_m - eps_BR) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq3_br_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 4. Hashin–Shtrikman bound with the matrix as host

    eps_HSL = eps_m + phi/(1/(eps_i - eps_m) + (1 - phi)/(3*eps_m))
-/
/-- Both sides of "Hashin–Shtrikman bound with the matrix as host" carry the same physical dimension. -/
theorem eq4_hsl_dim : d_eps_HSL = d_eps_m := by decide
theorem eq4_hsl_term1 : d_eps_i = d_eps_m := by decide
theorem eq4_hsl_term2 : Dim.one = d_phi := by decide
theorem eq4_hsl_term3 : (Dim.div Dim.one d_eps_i) = (Dim.div Dim.one (Dim.mul Dim.one d_eps_m)) := by decide
theorem eq4_hsl_term4 : d_eps_m = (Dim.div d_phi (Dim.div Dim.one d_eps_i)) := by decide
/-- Domain condition for `eps_i - eps_m`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_hsl_cond1 (eps_i eps_m : ℝ) (hdom : eps_i - eps_m ≠ 0) : eps_i - eps_m ≠ 0 := hdom
/-- The denominator `3 * eps_m` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_hsl_reg2 (eps_m : ℝ) (heps_m : 0 < eps_m) : (3 : ℝ) * eps_m ≠ 0 := by positivity
/-- Domain condition for `1 / (eps_i - eps_m) + (1 - phi) / (3 * eps_m)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_hsl_cond3 (eps_i eps_m phi : ℝ) (hdom : (1 : ℝ) / (eps_i - eps_m) + ((1 : ℝ) - phi) / ((3 : ℝ) * eps_m) ≠ 0) : (1 : ℝ) / (eps_i - eps_m) + ((1 : ℝ) - phi) / ((3 : ℝ) * eps_m) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq4_hsl_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 5. Hashin–Shtrikman bound with the filler as host

    eps_HSU = eps_i + (1 - phi)/(1/(eps_m - eps_i) + phi/(3*eps_i))
-/
/-- Both sides of "Hashin–Shtrikman bound with the filler as host" carry the same physical dimension. -/
theorem eq5_hsu_dim : d_eps_HSU = d_eps_i := by decide
theorem eq5_hsu_term1 : Dim.one = d_phi := by decide
theorem eq5_hsu_term2 : d_eps_m = d_eps_i := by decide
theorem eq5_hsu_term3 : (Dim.div Dim.one d_eps_m) = (Dim.div d_phi (Dim.mul Dim.one d_eps_i)) := by decide
theorem eq5_hsu_term4 : d_eps_i = (Dim.div Dim.one (Dim.div Dim.one d_eps_m)) := by decide
/-- Domain condition for `eps_m - eps_i`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_hsu_cond1 (eps_m eps_i : ℝ) (hdom : eps_m - eps_i ≠ 0) : eps_m - eps_i ≠ 0 := hdom
/-- The denominator `3 * eps_i` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_hsu_reg2 (eps_i : ℝ) (heps_i : 0 < eps_i) : (3 : ℝ) * eps_i ≠ 0 := by positivity
/-- Domain condition for `1 / (eps_m - eps_i) + phi / (3 * eps_i)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_hsu_cond3 (eps_m eps_i phi : ℝ) (hdom : (1 : ℝ) / (eps_m - eps_i) + phi / ((3 : ℝ) * eps_i) ≠ 0) : (1 : ℝ) / (eps_m - eps_i) + phi / ((3 : ℝ) * eps_i) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq5_hsu_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 6. Wiener bound, layers in series

    eps_Wlo = 1/(phi/eps_i + (1 - phi)/eps_m)
-/
/-- Both sides of "Wiener bound, layers in series" carry the same physical dimension. -/
theorem eq6_wlo_dim : d_eps_Wlo = (Dim.div Dim.one (Dim.div d_phi d_eps_i)) := by decide
theorem eq6_wlo_term1 : Dim.one = d_phi := by decide
theorem eq6_wlo_term2 : (Dim.div d_phi d_eps_i) = (Dim.div Dim.one d_eps_m) := by decide
/-- The denominator `eps_i` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_wlo_reg1 (eps_i : ℝ) (heps_i : 0 < eps_i) : eps_i ≠ 0 := by positivity
/-- The denominator `eps_m` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_wlo_reg2 (eps_m : ℝ) (heps_m : 0 < eps_m) : eps_m ≠ 0 := by positivity
/-- Domain condition for `phi / eps_i + (1 - phi) / eps_m`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_wlo_cond3 (phi eps_i eps_m : ℝ) (hdom : phi / eps_i + ((1 : ℝ) - phi) / eps_m ≠ 0) : phi / eps_i + ((1 : ℝ) - phi) / eps_m ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq6_wlo_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 7. Wiener bound, layers in parallel

    eps_Whi = phi*eps_i + (1 - phi)*eps_m
-/
/-- Both sides of "Wiener bound, layers in parallel" carry the same physical dimension. -/
theorem eq7_whi_dim : d_eps_Whi = (Dim.mul d_phi d_eps_i) := by decide
theorem eq7_whi_term1 : Dim.one = d_phi := by decide
theorem eq7_whi_term2 : (Dim.mul d_phi d_eps_i) = (Dim.mul Dim.one d_eps_m) := by decide

/-! ## 8. Maxwell Garnett effective conductivity

    sigma_MG = sigma_m + phi*sigma_m*(sigma_i - sigma_m)/(sigma_m + 1/3*(1 - phi)*(sigma_i - sigma_m))
-/
/-- Both sides of "Maxwell Garnett effective conductivity" carry the same physical dimension. -/
theorem eq8_smg_dim : d_sigma_MG = d_sigma_m := by decide
theorem eq8_smg_term1 : d_sigma_i = d_sigma_m := by decide
theorem eq8_smg_term2 : Dim.one = d_phi := by decide
theorem eq8_smg_term3 : d_sigma_i = d_sigma_m := by decide
theorem eq8_smg_term4 : d_sigma_m = (Dim.mul (Dim.mul (Dim.div Dim.one Dim.one) Dim.one) d_sigma_i) := by decide
theorem eq8_smg_term5 : d_sigma_m = (Dim.div (Dim.mul (Dim.mul d_phi d_sigma_m) d_sigma_i) d_sigma_m) := by decide
/-- The denominator `3` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_smg_reg1  : (3 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `sigma_m + 1 / 3 * (1 - phi) * (sigma_i - sigma_m)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq8_smg_cond2 (sigma_m phi sigma_i : ℝ) (hdom : sigma_m + (1 : ℝ) / (3 : ℝ) * ((1 : ℝ) - phi) * (sigma_i - sigma_m) ≠ 0) : sigma_m + (1 : ℝ) / (3 : ℝ) * ((1 : ℝ) - phi) * (sigma_i - sigma_m) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq8_smg_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

end Bespoke
