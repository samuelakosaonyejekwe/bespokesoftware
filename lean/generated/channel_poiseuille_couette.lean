import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Plane Poiseuille–Couette flow and its start-up

Machine-checkable statements for this investigation (channel-poiseuille-couette).
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
def d_G : Dim := ⟨12, -24, -24, 0, 0, 0, 0⟩  -- Pressure gradient −dp/dx (positive drives flow in +x) [Pa/m]
def d_U_w : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of the upper wall [m/s]
def d_h : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Gap between the plates [mm]
def d_mu : Dim := ⟨12, -12, -12, 0, 0, 0, 0⟩  -- Dynamic viscosity [cP]
def d_nu : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Kinematic viscosity [m^2/s]
def d_q_s : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Steady flow rate per unit width [m^2/s]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Density [kg/m^3]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_t_v : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Viscous time [s]
def d_tau_w : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Wall shear stress [Pa]
def d_u : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Velocity [m/s]
def d_u_s : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Steady velocity profile [m/s]
def d_y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance from the lower wall [m]

/-! ## 1. Momentum equation

    rho*pd(u,t) = mu*pd2(u,y) + G
-/
/-- Both sides of "Momentum equation" carry the same physical dimension. -/
theorem eq1_mom_dim : (Dim.mul d_rho (Dim.div d_u d_t)) = (Dim.mul d_mu (Dim.div d_u (Dim.pow d_y 2 1))) := by decide
theorem eq1_mom_term1 : (Dim.mul d_mu (Dim.div d_u (Dim.pow d_y 2 1))) = d_G := by decide

/-! ## 2. Upper-wall condition

    u = U_w
-/
/-- Both sides of "Upper-wall condition" carry the same physical dimension. -/
theorem eq2_bc_dim : d_u = d_U_w := by decide

/-! ## 3. Steady profile

    u_s = U_w*y/h + G*y*(h - y)/(2*mu)
-/
/-- Both sides of "Steady profile" carry the same physical dimension. -/
theorem eq3_steady_dim : d_u_s = (Dim.div (Dim.mul d_U_w d_y) d_h) := by decide
theorem eq3_steady_term1 : d_h = d_y := by decide
theorem eq3_steady_term2 : (Dim.div (Dim.mul d_U_w d_y) d_h) = (Dim.div (Dim.mul (Dim.mul d_G d_y) d_h) (Dim.mul Dim.one d_mu)) := by decide
/-- The denominator `h` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_steady_reg1 (h : ℝ) (hh : 0 < h) : h ≠ 0 := by positivity
/-- The denominator `2 * mu` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_steady_reg2 (mu : ℝ) (hmu : 0 < mu) : (2 : ℝ) * mu ≠ 0 := by positivity

/-! ## 4. Steady flow rate per unit width

    q_s = U_w*h/2 + G*h^3/(12*mu)
-/
/-- Both sides of "Steady flow rate per unit width" carry the same physical dimension. -/
theorem eq4_q_dim : d_q_s = (Dim.div (Dim.mul d_U_w d_h) Dim.one) := by decide
theorem eq4_q_term1 : (Dim.div (Dim.mul d_U_w d_h) Dim.one) = (Dim.div (Dim.mul d_G (Dim.pow d_h 3 1)) (Dim.mul Dim.one d_mu)) := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_q_reg1  : (2 : ℝ) ≠ 0 := by positivity
/-- The denominator `12 * mu` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_q_reg2 (mu : ℝ) (hmu : 0 < mu) : (12 : ℝ) * mu ≠ 0 := by positivity

/-! ## 5. Wall shear stress

    tau_w = mu*pd(u,y)
-/
/-- Both sides of "Wall shear stress" carry the same physical dimension. -/
theorem eq5_tw_dim : d_tau_w = (Dim.mul d_mu (Dim.div d_u d_y)) := by decide

/-! ## 6. Viscous time

    t_v = h^2/nu
-/
/-- Both sides of "Viscous time" carry the same physical dimension. -/
theorem eq6_tv_dim : d_t_v = (Dim.div (Dim.pow d_h 2 1) d_nu) := by decide
/-- The denominator `nu` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_tv_reg1 (nu : ℝ) (hnu : 0 < nu) : nu ≠ 0 := by positivity

/-! ## 7. Kinematic viscosity

    nu = mu/rho
-/
/-- Both sides of "Kinematic viscosity" carry the same physical dimension. -/
theorem eq7_nu_dim : d_nu = (Dim.div d_mu d_rho) := by decide
/-- The denominator `rho` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_nu_reg1 (rho : ℝ) (hrho : 0 < rho) : rho ≠ 0 := by positivity

end Bespoke
