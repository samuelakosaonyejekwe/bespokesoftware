import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Olbers' paradox: why the night sky is dark

Machine-checkable statements for this investigation (olbers-paradox).
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
def d_F_R : Dim := ⟨12, 0, -36, 0, 0, 0, 0⟩  -- Flux summed out to a given radius [W/m^2]
def d_F_sky : Dim := ⟨12, 0, -36, 0, 0, 0, 0⟩  -- Flux received from the whole sky [W/m^2]
def d_F_surf : Dim := ⟨12, 0, -36, 0, 0, 0, 0⟩  -- Flux when every line of sight ends on a star [W/m^2]
def d_L_s : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Luminosity of a typical star [W]
def d_R_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Radius of a typical star [m]
def d_ell_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Mean free path of a line of sight before it meets a star [m]
def d_f_cov : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fraction of the sky covered by stellar discs [1]
def d_j_L : Dim := ⟨12, -12, -36, 0, 0, 0, 0⟩  -- Luminosity density [W/m^3]
def d_n_s : Dim := ⟨0, -36, 0, 0, 0, 0, 0⟩  -- Mean number density of stars [1/Mpc^3]
def d_r : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance from the observer [m]

/-! ## 1. Luminosity density

    j_L = n_s*L_s
-/
/-- Both sides of "Luminosity density" carry the same physical dimension. -/
theorem eq1_lum_dim : d_j_L = (Dim.mul d_n_s d_L_s) := by decide

/-! ## 2. Mean free path of a line of sight

    ell_s = 1/(n_s*pi*R_s^2)
-/
/-- Both sides of "Mean free path of a line of sight" carry the same physical dimension. -/
theorem eq2_path_dim : d_ell_s = (Dim.div Dim.one (Dim.mul (Dim.mul d_n_s Dim.one) (Dim.pow d_R_s 2 1))) := by decide
/-- The denominator `n_s * pi * R_s^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_path_reg1 (n_s R_s : ℝ) (hn_s : 0 < n_s) (hR_s : 0 < R_s) : n_s * Real.pi * R_s ^ 2 ≠ 0 := by positivity

/-! ## 3. Flux contributed per unit thickness of shell

    pd(F_R, r) = n_s*L_s
-/
/-- Both sides of "Flux contributed per unit thickness of shell" carry the same physical dimension. -/
theorem eq3_shell_dim : (Dim.div d_F_R d_r) = (Dim.mul d_n_s d_L_s) := by decide

/-! ## 4. Flux when the sky is covered by stellar discs

    F_surf = L_s/(pi*R_s^2)
-/
/-- Both sides of "Flux when the sky is covered by stellar discs" carry the same physical dimension. -/
theorem eq4_surf_dim : d_F_surf = (Dim.div d_L_s (Dim.mul Dim.one (Dim.pow d_R_s 2 1))) := by decide
/-- The denominator `pi * R_s^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_surf_reg1 (R_s : ℝ) (hR_s : 0 < R_s) : Real.pi * R_s ^ 2 ≠ 0 := by positivity

/-! ## 5. Sum out to radius r

    F_R = n_s*L_s*r
-/
/-- Both sides of "Sum out to radius r" carry the same physical dimension. -/
theorem eq5_tot_dim : d_F_R = (Dim.mul (Dim.mul d_n_s d_L_s) d_r) := by decide

/-! ## 6. Fraction of the sky covered by stars

    f_cov = F_sky/F_surf
-/
/-- Both sides of "Fraction of the sky covered by stars" carry the same physical dimension. -/
theorem eq6_cov_dim : d_f_cov = (Dim.div d_F_sky d_F_surf) := by decide
/-- The denominator `F_surf` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_cov_reg1 (F_surf : ℝ) (hF_surf : 0 < F_surf) : F_surf ≠ 0 := by positivity

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (Bright Eternal Infinite Static Uniform : Prop) (h1 : (((Infinite ∧ Static) ∧ Eternal) ∧ Uniform) → Bright) (h2 : ¬Bright) : ¬(((Infinite ∧ Static) ∧ Eternal) ∧ Uniform) := by tauto

end Bespoke
