import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Orbits under a modified force law F ∝ 1/rⁿ

Machine-checkable statements for this investigation (modified-gravity-orbits).
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

/-! ## Dimensions of the symbols -/

def d_length : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩
def d_G : Dim := ⟨-12, 36, -24, 0, 0, 0, 0⟩  -- Gravitational constant [m^3/(kg s^2)]
def d_M : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Central mass [Msun]
def d_Omega_c : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Circular orbital frequency [1/s]
def d_a_r : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Radial acceleration due to the force [m/s^2]
def d_h_L : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Specific angular momentum [m^2/s]
def d_kappa_e : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Radial (epicyclic) frequency [1/s]
def d_n : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Exponent of the force law, F ∝ 1/rⁿ [1]
def d_psi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Apsidal angle [rad]
def d_r : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Orbital radius [m]
def d_r_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Starting radius, at which the force equals its Newtonian value [AU]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_theta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Orbital angle [rad]
def d_v_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Circular speed at the starting radius [m/s]

/-! ## 1. Force law

    a_r = -G*M/r_0^2*(r_0/r)^n
-/
/-- Both sides of "Force law" carry the same physical dimension. -/
theorem eq1_force_dim : d_a_r = (Dim.mul (Dim.div (Dim.mul d_G d_M) (Dim.pow d_r_0 2 1)) Dim.one) := by decide
/-- The denominator `r_0^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_force_reg1 (r_0 : ℝ) (hr_0 : 0 < r_0) : r_0 ^ 2 ≠ 0 := by positivity
/-- Domain condition for `r`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_force_cond2 (r : ℝ) (hdom : r ≠ 0) : r ≠ 0 := hdom

/-! ## 2. Conservation of angular momentum

    h_L = r^2*d(theta,t)
-/
/-- Both sides of "Conservation of angular momentum" carry the same physical dimension. -/
theorem eq2_ang_dim : d_h_L = (Dim.mul (Dim.pow d_r 2 1) (Dim.div d_theta d_t)) := by decide

/-! ## 3. Radial equation of motion

    d2(r,t) = h_L^2/r^3 + a_r
-/
/-- Both sides of "Radial equation of motion" carry the same physical dimension. -/
theorem eq3_rad_dim : (Dim.div d_r (Dim.pow d_t 2 1)) = (Dim.div (Dim.pow d_h_L 2 1) (Dim.pow d_r 3 1)) := by decide
theorem eq3_rad_term1 : (Dim.div (Dim.pow d_h_L 2 1) (Dim.pow d_r 3 1)) = d_a_r := by decide
/-- Domain condition for `r^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_rad_cond1 (r : ℝ) (hdom : r ^ 3 ≠ 0) : r ^ 3 ≠ 0 := hdom

/-! ## 4. Circular speed at the starting radius

    v_c = sqrt(G*M/r_0)
-/
/-- Both sides of "Circular speed at the starting radius" carry the same physical dimension. -/
theorem eq4_vc_dim : d_v_c = (Dim.pow (Dim.div (Dim.mul d_G d_M) d_r_0) 1 2) := by decide
/-- The denominator `r_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_vc_reg1 (r_0 : ℝ) (hr_0 : 0 < r_0) : r_0 ≠ 0 := by positivity
/-- The argument `G * M / r_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_vc_reg2 (G M r_0 : ℝ) (hG : 0 < G) (hM : 0 < M) (hr_0 : 0 < r_0) : 0 ≤ G * M / r_0 := by positivity

/-! ## 5. Radial oscillation frequency about a circular orbit

    kappa_e^2 = (3 - n)*Omega_c^2
-/
/-- Both sides of "Radial oscillation frequency about a circular orbit" carry the same physical dimension. -/
theorem eq5_epi_dim : (Dim.pow d_kappa_e 2 1) = (Dim.mul Dim.one (Dim.pow d_Omega_c 2 1)) := by decide
theorem eq5_epi_term1 : Dim.one = d_n := by decide

/-! ## 6. Apsidal angle of a nearly circular orbit

    psi = pi/sqrt(3 - n)
-/
/-- Both sides of "Apsidal angle of a nearly circular orbit" carry the same physical dimension. -/
theorem eq6_aps_dim : d_psi = (Dim.div Dim.one (Dim.pow Dim.one 1 2)) := by decide
theorem eq6_aps_term1 : Dim.one = d_n := by decide
/-- Domain condition for `3 - n`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_aps_cond1 (n : ℝ) (hdom : 0 ≤ (3 : ℝ) - n) : 0 ≤ (3 : ℝ) - n := hdom
/-- Domain condition for `sqrt(3 - n)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_aps_cond2 (n : ℝ) (hdom : Real.sqrt ((3 : ℝ) - n) ≠ 0) : Real.sqrt ((3 : ℝ) - n) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq6_aps_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

end Bespoke
