import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Planar three-body problem and sensitivity to initial conditions

Machine-checkable statements for this investigation (three-body-chaos).
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
def d_E : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Total energy [J]
def d_G : Dim := ⟨-12, 36, -24, 0, 0, 0, 0⟩  -- Gravitational constant [m^3/(kg s^2)]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Length scale of the configuration [AU]
def d_T_8 : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Figure-eight period [s]
def d_delta_s : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Phase-space separation of the twin trajectories (scaled) [1]
def d_lambda : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Finite-time Lyapunov exponent [1/s]
def d_m : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass of each body [Msun]
def d_r_12 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Separation of bodies 1 and 2 [m]
def d_r_13 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Separation of bodies 1 and 3 [m]
def d_r_23 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Separation of bodies 2 and 3 [m]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_tau : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Dynamical time unit [s]
def d_v_1 : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of body 1 [m/s]
def d_v_2 : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of body 2 [m/s]
def d_v_3 : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of body 3 [m/s]
def d_x_1 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position of body 1 (each Cartesian component) [m]
def d_x_2 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position of body 2 [m]
def d_x_3 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position of body 3 [m]

/-! ## 1. Body 1

    d2(x_1,t) = G*m*(x_2 - x_1)/r_12^3 + G*m*(x_3 - x_1)/r_13^3
-/
/-- Both sides of "Body 1" carry the same physical dimension. -/
theorem eq1_b1_dim : (Dim.div d_x_1 (Dim.pow d_t 2 1)) = (Dim.div (Dim.mul (Dim.mul d_G d_m) d_x_2) (Dim.pow d_r_12 3 1)) := by decide
theorem eq1_b1_term1 : d_x_2 = d_x_1 := by decide
theorem eq1_b1_term2 : d_x_3 = d_x_1 := by decide
theorem eq1_b1_term3 : (Dim.div (Dim.mul (Dim.mul d_G d_m) d_x_2) (Dim.pow d_r_12 3 1)) = (Dim.div (Dim.mul (Dim.mul d_G d_m) d_x_3) (Dim.pow d_r_13 3 1)) := by decide
/-- Domain condition for `r_12^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_b1_cond1 (r_12 : ℝ) (hdom : r_12 ^ 3 ≠ 0) : r_12 ^ 3 ≠ 0 := hdom
/-- Domain condition for `r_13^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_b1_cond2 (r_13 : ℝ) (hdom : r_13 ^ 3 ≠ 0) : r_13 ^ 3 ≠ 0 := hdom

/-! ## 2. Body 2

    d2(x_2,t) = G*m*(x_1 - x_2)/r_12^3 + G*m*(x_3 - x_2)/r_23^3
-/
/-- Both sides of "Body 2" carry the same physical dimension. -/
theorem eq2_b2_dim : (Dim.div d_x_2 (Dim.pow d_t 2 1)) = (Dim.div (Dim.mul (Dim.mul d_G d_m) d_x_1) (Dim.pow d_r_12 3 1)) := by decide
theorem eq2_b2_term1 : d_x_1 = d_x_2 := by decide
theorem eq2_b2_term2 : d_x_3 = d_x_2 := by decide
theorem eq2_b2_term3 : (Dim.div (Dim.mul (Dim.mul d_G d_m) d_x_1) (Dim.pow d_r_12 3 1)) = (Dim.div (Dim.mul (Dim.mul d_G d_m) d_x_3) (Dim.pow d_r_23 3 1)) := by decide
/-- Domain condition for `r_12^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_b2_cond1 (r_12 : ℝ) (hdom : r_12 ^ 3 ≠ 0) : r_12 ^ 3 ≠ 0 := hdom
/-- Domain condition for `r_23^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_b2_cond2 (r_23 : ℝ) (hdom : r_23 ^ 3 ≠ 0) : r_23 ^ 3 ≠ 0 := hdom

/-! ## 3. Body 3

    d2(x_3,t) = G*m*(x_1 - x_3)/r_13^3 + G*m*(x_2 - x_3)/r_23^3
-/
/-- Both sides of "Body 3" carry the same physical dimension. -/
theorem eq3_b3_dim : (Dim.div d_x_3 (Dim.pow d_t 2 1)) = (Dim.div (Dim.mul (Dim.mul d_G d_m) d_x_1) (Dim.pow d_r_13 3 1)) := by decide
theorem eq3_b3_term1 : d_x_1 = d_x_3 := by decide
theorem eq3_b3_term2 : d_x_2 = d_x_3 := by decide
theorem eq3_b3_term3 : (Dim.div (Dim.mul (Dim.mul d_G d_m) d_x_1) (Dim.pow d_r_13 3 1)) = (Dim.div (Dim.mul (Dim.mul d_G d_m) d_x_2) (Dim.pow d_r_23 3 1)) := by decide
/-- Domain condition for `r_13^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_b3_cond1 (r_13 : ℝ) (hdom : r_13 ^ 3 ≠ 0) : r_13 ^ 3 ≠ 0 := hdom
/-- Domain condition for `r_23^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_b3_cond2 (r_23 : ℝ) (hdom : r_23 ^ 3 ≠ 0) : r_23 ^ 3 ≠ 0 := hdom

/-! ## 4. Total energy

    E = 0.5*m*v_1^2 + 0.5*m*v_2^2 + 0.5*m*v_3^2 - G*m*m/r_12 - G*m*m/r_13 - G*m*m/r_23
-/
/-- Both sides of "Total energy" carry the same physical dimension. -/
theorem eq4_en_dim : d_E = (Dim.mul (Dim.mul Dim.one d_m) (Dim.pow d_v_1 2 1)) := by decide
theorem eq4_en_term1 : (Dim.mul (Dim.mul Dim.one d_m) (Dim.pow d_v_1 2 1)) = (Dim.mul (Dim.mul Dim.one d_m) (Dim.pow d_v_2 2 1)) := by decide
theorem eq4_en_term2 : (Dim.mul (Dim.mul Dim.one d_m) (Dim.pow d_v_1 2 1)) = (Dim.mul (Dim.mul Dim.one d_m) (Dim.pow d_v_3 2 1)) := by decide
theorem eq4_en_term3 : (Dim.mul (Dim.mul Dim.one d_m) (Dim.pow d_v_1 2 1)) = (Dim.div (Dim.mul (Dim.mul d_G d_m) d_m) d_r_12) := by decide
theorem eq4_en_term4 : (Dim.mul (Dim.mul Dim.one d_m) (Dim.pow d_v_1 2 1)) = (Dim.div (Dim.mul (Dim.mul d_G d_m) d_m) d_r_13) := by decide
theorem eq4_en_term5 : (Dim.mul (Dim.mul Dim.one d_m) (Dim.pow d_v_1 2 1)) = (Dim.div (Dim.mul (Dim.mul d_G d_m) d_m) d_r_23) := by decide
/-- Domain condition for `r_12`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_en_cond1 (r_12 : ℝ) (hdom : r_12 ≠ 0) : r_12 ≠ 0 := hdom
/-- Domain condition for `r_13`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_en_cond2 (r_13 : ℝ) (hdom : r_13 ≠ 0) : r_13 ≠ 0 := hdom
/-- Domain condition for `r_23`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_en_cond3 (r_23 : ℝ) (hdom : r_23 ≠ 0) : r_23 ≠ 0 := hdom

/-! ## 5. Dynamical time unit

    tau = sqrt(L^3/(G*m))
-/
/-- Both sides of "Dynamical time unit" carry the same physical dimension. -/
theorem eq5_tau_dim : d_tau = (Dim.pow (Dim.div (Dim.pow d_L 3 1) (Dim.mul d_G d_m)) 1 2) := by decide
/-- The denominator `G * m` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_tau_reg1 (G m : ℝ) (hG : 0 < G) (hm : 0 < m) : G * m ≠ 0 := by positivity
/-- The argument `L^3 / (G * m)` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_tau_reg2 (L G m : ℝ) (hL : 0 < L) (hG : 0 < G) (hm : 0 < m) : 0 ≤ L ^ 3 / (G * m) := by positivity

/-! ## 6. Figure-eight period

    T_8 = 6.32591398*tau
-/
/-- Both sides of "Figure-eight period" carry the same physical dimension. -/
theorem eq6_t8_dim : d_T_8 = (Dim.mul Dim.one d_tau) := by decide

/-! ## 7. Growth of the twin separation

    d(delta_s,t) = lambda*delta_s
-/
/-- Both sides of "Growth of the twin separation" carry the same physical dimension. -/
theorem eq7_lyap_dim : (Dim.div d_delta_s d_t) = (Dim.mul d_lambda d_delta_s) := by decide

end Bespoke
