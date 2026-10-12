import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Transient heat conduction in a slab

Machine-checkable statements for this investigation (transient-conduction-1d).
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
def d_Bi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Biot number [1]
def d_Fo : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fourier number [1]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Slab thickness (heated face to back face) [mm]
def d_T : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Temperature [K]
def d_T_inf : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Fluid (or imposed surface) temperature [°C]
def d_alpha : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Thermal diffusivity [m^2/s]
def d_cp : Dim := ⟨0, 24, -24, 0, -12, 0, 0⟩  -- Specific heat capacity [J/(kg K)]
def d_h : Dim := ⟨12, 0, -36, 0, -12, 0, 0⟩  -- Surface heat-transfer coefficient [W/(m^2 K)]
def d_k : Dim := ⟨12, 12, -36, 0, -12, 0, 0⟩  -- Thermal conductivity [W/(m K)]
def d_q_s : Dim := ⟨12, 0, -36, 0, 0, 0, 0⟩  -- Surface heat flux [W/m^2]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Density [kg/m^3]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_t_end : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Elapsed time [s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance from the heated face [m]

/-! ## 1. Heat equation

    rho*cp*pd(T,t) = k*pd2(T,x)
-/
/-- Both sides of "Heat equation" carry the same physical dimension. -/
theorem eq1_heat_dim : (Dim.mul (Dim.mul d_rho d_cp) (Dim.div d_T d_t)) = (Dim.mul d_k (Dim.div d_T (Dim.pow d_x 2 1))) := by decide

/-! ## 2. Heated-face condition

    -k*pd(T,x) = h*(T_inf - T)
-/
/-- Both sides of "Heated-face condition" carry the same physical dimension. -/
theorem eq2_bc0_dim : (Dim.mul d_k (Dim.div d_T d_x)) = (Dim.mul d_h d_T_inf) := by decide
theorem eq2_bc0_term1 : d_T_inf = d_T := by decide

/-! ## 3. Back-face condition

    k*pd(T,x) = 0*q_s
-/
/-- Both sides of "Back-face condition" carry the same physical dimension. -/
theorem eq3_bcL_dim : (Dim.mul d_k (Dim.div d_T d_x)) = (Dim.mul Dim.one d_q_s) := by decide

/-! ## 4. Thermal diffusivity

    alpha = k/(rho*cp)
-/
/-- Both sides of "Thermal diffusivity" carry the same physical dimension. -/
theorem eq4_alpha_dim : d_alpha = (Dim.div d_k (Dim.mul d_rho d_cp)) := by decide
/-- The denominator `rho * cp` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_alpha_reg1 (rho cp : ℝ) (hrho : 0 < rho) (hcp : 0 < cp) : rho * cp ≠ 0 := by positivity

/-! ## 5. Biot number

    Bi = h*L/k
-/
/-- Both sides of "Biot number" carry the same physical dimension. -/
theorem eq5_bi_dim : d_Bi = (Dim.div (Dim.mul d_h d_L) d_k) := by decide
/-- The denominator `k` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_bi_reg1 (k : ℝ) (hk : 0 < k) : k ≠ 0 := by positivity

/-! ## 6. Fourier number

    Fo = alpha*t_end/L^2
-/
/-- Both sides of "Fourier number" carry the same physical dimension. -/
theorem eq6_fo_dim : d_Fo = (Dim.div (Dim.mul d_alpha d_t_end) (Dim.pow d_L 2 1)) := by decide
/-- The denominator `L^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_fo_reg1 (L : ℝ) (hL : 0 < L) : L ^ 2 ≠ 0 := by positivity

/-! ## 7. Surface heat flux

    q_s = h*(T_inf - T)
-/
/-- Both sides of "Surface heat flux" carry the same physical dimension. -/
theorem eq7_qs_dim : d_q_s = (Dim.mul d_h d_T_inf) := by decide
theorem eq7_qs_term1 : d_T_inf = d_T := by decide

end Bespoke
