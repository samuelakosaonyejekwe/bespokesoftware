import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Infinite-slope stability

Machine-checkable statements for this investigation (slope-stability-infinite).
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
def d_FS : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Factor of safety [1]
def d_beta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Slope angle [deg]
def d_c_eff : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Effective cohesion [kPa]
def d_gamma : Dim := ⟨12, -24, -24, 0, 0, 0, 0⟩  -- Bulk unit weight above the water table [kN/m^3]
def d_gamma_a : Dim := ⟨12, -24, -24, 0, 0, 0, 0⟩  -- Average unit weight above the slip plane [N/m^3]
def d_gamma_sat : Dim := ⟨12, -24, -24, 0, 0, 0, 0⟩  -- Saturated unit weight [kN/m^3]
def d_gamma_w : Dim := ⟨12, -24, -24, 0, 0, 0, 0⟩  -- Unit weight of water [N/m^3]
def d_m_w : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Height of the water table above the slip plane as a fraction of its depth [1]
def d_phi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Effective friction angle [deg]
def d_sigma_n : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Total normal stress on the slip plane [Pa]
def d_tau : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Shear stress on the slip plane [Pa]
def d_tau_f : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Shear strength on the slip plane [Pa]
def d_u_p : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Pore pressure on the slip plane [Pa]
def d_z : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Depth of the slip plane (vertical) [m]

/-! ## 1. Average unit weight

    gamma_a = (1 - m_w)*gamma + m_w*gamma_sat
-/
/-- Both sides of "Average unit weight" carry the same physical dimension. -/
theorem eq1_ga_dim : d_gamma_a = (Dim.mul Dim.one d_gamma) := by decide
theorem eq1_ga_term1 : Dim.one = d_m_w := by decide
theorem eq1_ga_term2 : (Dim.mul Dim.one d_gamma) = (Dim.mul d_m_w d_gamma_sat) := by decide

/-! ## 2. Normal stress on the slip plane

    sigma_n = gamma_a*z*cos(beta)^2
-/
/-- Both sides of "Normal stress on the slip plane" carry the same physical dimension. -/
theorem eq2_sig_dim : d_sigma_n = (Dim.mul (Dim.mul d_gamma_a d_z) (Dim.pow Dim.one 2 1)) := by decide
theorem eq2_sig_term1 : d_beta = Dim.one := by decide

/-! ## 3. Shear stress on the slip plane

    tau = gamma_a*z*sin(beta)*cos(beta)
-/
/-- Both sides of "Shear stress on the slip plane" carry the same physical dimension. -/
theorem eq3_tau_dim : d_tau = (Dim.mul (Dim.mul (Dim.mul d_gamma_a d_z) Dim.one) Dim.one) := by decide
theorem eq3_tau_term1 : d_beta = Dim.one := by decide
theorem eq3_tau_term2 : d_beta = Dim.one := by decide

/-! ## 4. Pore pressure

    u_p = gamma_w*m_w*z*cos(beta)^2
-/
/-- Both sides of "Pore pressure" carry the same physical dimension. -/
theorem eq4_u_dim : d_u_p = (Dim.mul (Dim.mul (Dim.mul d_gamma_w d_m_w) d_z) (Dim.pow Dim.one 2 1)) := by decide
theorem eq4_u_term1 : d_beta = Dim.one := by decide

/-! ## 5. Shear strength

    tau_f = c_eff + (sigma_n - u_p)*tan(phi)
-/
/-- Both sides of "Shear strength" carry the same physical dimension. -/
theorem eq5_tf_dim : d_tau_f = d_c_eff := by decide
theorem eq5_tf_term1 : d_sigma_n = d_u_p := by decide
theorem eq5_tf_term2 : d_phi = Dim.one := by decide
theorem eq5_tf_term3 : d_c_eff = (Dim.mul d_sigma_n Dim.one) := by decide

/-! ## 6. Factor of safety

    FS = tau_f/tau
-/
/-- Both sides of "Factor of safety" carry the same physical dimension. -/
theorem eq6_fs_dim : d_FS = (Dim.div d_tau_f d_tau) := by decide
/-- The denominator `tau` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_fs_reg1 (tau : ℝ) (htau : 0 < tau) : tau ≠ 0 := by positivity

end Bespoke
