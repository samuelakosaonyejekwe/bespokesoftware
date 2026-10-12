import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Large-angle pendulum with damping

Machine-checkable statements for this investigation (pendulum-nonlinear).
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
def d_E : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Mechanical energy [J]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Pendulum length [m]
def d_T : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Period at finite amplitude [s]
def d_T_0 : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Small-angle period [s]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Local gravitational acceleration [m/s^2]
def d_m : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass [kg]
def d_omega_0 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Small-angle angular frequency [1/s]
def d_phi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Integration variable [rad]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_theta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Angle from the vertical [rad]
def d_theta_0 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Release angle from the vertical [deg]
def d_zeta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Viscous damping ratio [1]

/-! ## 1. Equation of motion

    d2(theta,t) = -omega_0^2*sin(theta) - 2*zeta*omega_0*d(theta,t)
-/
/-- Both sides of "Equation of motion" carry the same physical dimension. -/
theorem eq1_mom_dim : (Dim.div d_theta (Dim.pow d_t 2 1)) = (Dim.mul (Dim.pow d_omega_0 2 1) Dim.one) := by decide
theorem eq1_mom_term1 : d_theta = Dim.one := by decide
theorem eq1_mom_term2 : (Dim.mul (Dim.pow d_omega_0 2 1) Dim.one) = (Dim.mul (Dim.mul (Dim.mul Dim.one d_zeta) d_omega_0) (Dim.div d_theta d_t)) := by decide

/-! ## 2. Natural frequency

    omega_0 = sqrt(g/L)
-/
/-- Both sides of "Natural frequency" carry the same physical dimension. -/
theorem eq2_w0_dim : d_omega_0 = (Dim.pow (Dim.div d_g d_L) 1 2) := by decide
/-- The denominator `L` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_w0_reg1 (L : ℝ) (hL : 0 < L) : L ≠ 0 := by positivity
/-- The argument `g / L` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_w0_reg2 (g L : ℝ) (hg : 0 < g) (hL : 0 < L) : 0 ≤ g / L := by positivity

/-! ## 3. Small-angle period

    T_0 = 2*pi/omega_0
-/
/-- Both sides of "Small-angle period" carry the same physical dimension. -/
theorem eq3_t0_dim : d_T_0 = (Dim.div (Dim.mul Dim.one Dim.one) d_omega_0) := by decide
/-- The denominator `omega_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_t0_reg1 (omega_0 : ℝ) (homega_0 : 0 < omega_0) : omega_0 ≠ 0 := by positivity

/-! ## 4. Period at amplitude θ₀ (undamped)

    T = 4/omega_0*int(1/sqrt(1 - sin(theta_0/2)^2*sin(phi)^2), phi)
-/
/-- Both sides of "Period at amplitude θ₀ (undamped)" carry the same physical dimension. -/
theorem eq4_per_dim : d_T = (Dim.mul (Dim.div Dim.one d_omega_0) (Dim.mul (Dim.div Dim.one (Dim.pow Dim.one 1 2)) d_phi)) := by decide
theorem eq4_per_term1 : (Dim.div d_theta_0 Dim.one) = Dim.one := by decide
theorem eq4_per_term2 : d_phi = Dim.one := by decide
theorem eq4_per_term3 : Dim.one = (Dim.mul (Dim.pow Dim.one 2 1) (Dim.pow Dim.one 2 1)) := by decide
/-- The denominator `omega_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_per_reg1 (omega_0 : ℝ) (homega_0 : 0 < omega_0) : omega_0 ≠ 0 := by positivity
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_per_reg2  : (2 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `1 - sin(theta_0 / 2)^2 * sin(phi)^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_per_cond3 (theta_0 phi : ℝ) (hdom : 0 ≤ (1 : ℝ) - Real.sin (theta_0 / (2 : ℝ)) ^ 2 * Real.sin phi ^ 2) : 0 ≤ (1 : ℝ) - Real.sin (theta_0 / (2 : ℝ)) ^ 2 * Real.sin phi ^ 2 := hdom
/-- Domain condition for `sqrt(1 - sin(theta_0 / 2)^2 * sin(phi)^2)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_per_cond4 (theta_0 phi : ℝ) (hdom : Real.sqrt ((1 : ℝ) - Real.sin (theta_0 / (2 : ℝ)) ^ 2 * Real.sin phi ^ 2) ≠ 0) : Real.sqrt ((1 : ℝ) - Real.sin (theta_0 / (2 : ℝ)) ^ 2 * Real.sin phi ^ 2) ≠ 0 := hdom

/-! ## 5. Mechanical energy

    E = 0.5*m*L^2*d(theta,t)^2 + m*g*L*(1 - cos(theta))
-/
/-- Both sides of "Mechanical energy" carry the same physical dimension. -/
theorem eq5_en_dim : d_E = (Dim.mul (Dim.mul (Dim.mul Dim.one d_m) (Dim.pow d_L 2 1)) (Dim.pow (Dim.div d_theta d_t) 2 1)) := by decide
theorem eq5_en_term1 : d_theta = Dim.one := by decide
theorem eq5_en_term2 : Dim.one = Dim.one := by decide
theorem eq5_en_term3 : (Dim.mul (Dim.mul (Dim.mul Dim.one d_m) (Dim.pow d_L 2 1)) (Dim.pow (Dim.div d_theta d_t) 2 1)) = (Dim.mul (Dim.mul (Dim.mul d_m d_g) d_L) Dim.one) := by decide

end Bespoke
