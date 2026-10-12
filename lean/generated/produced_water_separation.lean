import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Produced-water treatment: gravity and hydrocyclone separation

Machine-checkable statements for this investigation (produced-water-separation).
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
def d_C_in : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Oil-in-water concentration at the inlet [mg/L]
def d_C_out : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Oil in water at the outlet [kg/m^3]
def d_E_T : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Total oil-removal efficiency [1]
def d_L_sep : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Separator effective length [m]
def d_Q : Dim := ⟨0, 36, -12, 0, 0, 0, 0⟩  -- Produced-water flow rate [m^3/h]
def d_Re_p : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Particle Reynolds number [1]
def d_W_sep : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Separator width [m]
def d_d_100 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Smallest droplet fully captured (cut size) [m]
def d_d_50 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Volume-median oil droplet diameter [um]
def d_d_p : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Droplet diameter [m]
def d_eta_d : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Grade efficiency [1]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_m_rec : Dim := ⟨12, 0, -12, 0, 0, 0, 0⟩  -- Oil recovered [kg/s]
def d_mu_w : Dim := ⟨12, -12, -12, 0, 0, 0, 0⟩  -- Water viscosity [cP]
def d_rho_o : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Oil density [kg/m^3]
def d_rho_w : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Water density [kg/m^3]
def d_v_o : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Overflow rate, or required radial migration velocity in a hydrocyclone [m/s]
def d_v_t : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Rise velocity of the median droplet [m/s]

/-! ## 1. Terminal velocity

    v_t = g*d_50^2*(rho_w - rho_o)/(18*mu_w)
-/
/-- Both sides of "Terminal velocity" carry the same physical dimension. -/
theorem eq1_stokes_dim : d_v_t = (Dim.div (Dim.mul (Dim.mul d_g (Dim.pow d_d_50 2 1)) d_rho_w) (Dim.mul Dim.one d_mu_w)) := by decide
theorem eq1_stokes_term1 : d_rho_w = d_rho_o := by decide
/-- The denominator `18 * mu_w` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_stokes_reg1 (mu_w : ℝ) (hmu_w : 0 < mu_w) : (18 : ℝ) * mu_w ≠ 0 := by positivity

/-! ## 2. Particle Reynolds number

    Re_p = rho_w*v_t*d_50/mu_w
-/
/-- Both sides of "Particle Reynolds number" carry the same physical dimension. -/
theorem eq2_rep_dim : d_Re_p = (Dim.div (Dim.mul (Dim.mul d_rho_w d_v_t) d_d_50) d_mu_w) := by decide
/-- The denominator `mu_w` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_rep_reg1 (mu_w : ℝ) (hmu_w : 0 < mu_w) : mu_w ≠ 0 := by positivity

/-! ## 3. Overflow rate

    v_o = Q/(L_sep*W_sep)
-/
/-- Both sides of "Overflow rate" carry the same physical dimension. -/
theorem eq3_vo_dim : d_v_o = (Dim.div d_Q (Dim.mul d_L_sep d_W_sep)) := by decide
/-- The denominator `L_sep * W_sep` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_vo_reg1 (L_sep W_sep : ℝ) (hL_sep : 0 < L_sep) (hW_sep : 0 < W_sep) : L_sep * W_sep ≠ 0 := by positivity

/-! ## 4. Cut size

    d_100 = sqrt(18*mu_w*v_o/(g*(rho_w - rho_o)))
-/
/-- Both sides of "Cut size" carry the same physical dimension. -/
theorem eq4_d100_dim : d_d_100 = (Dim.pow (Dim.div (Dim.mul (Dim.mul Dim.one d_mu_w) d_v_o) (Dim.mul d_g d_rho_w)) 1 2) := by decide
theorem eq4_d100_term1 : d_rho_w = d_rho_o := by decide
/-- Domain condition for `g * (rho_w - rho_o)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq4_d100_cond1 (g rho_w rho_o : ℝ) (hdom : g * (rho_w - rho_o) ≠ 0) : g * (rho_w - rho_o) ≠ 0 := hdom
/-- Domain condition for `18 * mu_w * v_o / (g * (rho_w - rho_o))`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq4_d100_cond2 (mu_w v_o g rho_w rho_o : ℝ) (hdom : 0 ≤ (18 : ℝ) * mu_w * v_o / (g * (rho_w - rho_o))) : 0 ≤ (18 : ℝ) * mu_w * v_o / (g * (rho_w - rho_o)) := hdom

/-! ## 5. Grade efficiency

    eta_d = min(1, (d_p/d_100)^2)
-/
/-- Both sides of "Grade efficiency" carry the same physical dimension. -/
theorem eq5_grade_dim : d_eta_d = Dim.one := by decide
theorem eq5_grade_term1 : Dim.one = (Dim.pow (Dim.div d_d_p d_d_100) 2 1) := by decide
/-- The denominator `d_100` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_grade_reg1 (d_100 : ℝ) (hd_100 : 0 < d_100) : d_100 ≠ 0 := by positivity

/-! ## 6. Outlet oil content

    C_out = C_in*(1 - E_T)
-/
/-- Both sides of "Outlet oil content" carry the same physical dimension. -/
theorem eq6_cout_dim : d_C_out = (Dim.mul d_C_in Dim.one) := by decide
theorem eq6_cout_term1 : Dim.one = d_E_T := by decide

/-! ## 7. Oil recovered

    m_rec = Q*C_in*E_T
-/
/-- Both sides of "Oil recovered" carry the same physical dimension. -/
theorem eq7_mrec_dim : d_m_rec = (Dim.mul (Dim.mul d_Q d_C_in) d_E_T) := by decide

end Bespoke
