import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Waves on a plucked or struck string

Machine-checkable statements for this investigation (vibrating-string-wave).
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
def d_A_n : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Amplitude of mode n [m]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- String length [m]
def d_T_s : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Tension [N]
def d_Z_w : Dim := ⟨12, 0, -12, 0, 0, 0, 0⟩  -- Wave impedance [kg/s]
def d_a_p : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Pluck amplitude [mm]
def d_c_w : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Wave speed [m/s]
def d_f_1 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Fundamental frequency [Hz]
def d_f_n : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Frequency of mode n [Hz]
def d_mu_l : Dim := ⟨12, -12, 0, 0, 0, 0, 0⟩  -- Mass per unit length [g/m]
def d_n : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Mode number [1]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_u : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Transverse displacement [m]
def d_u_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Initial displacement [m]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position along the string [m]
def d_x_p : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Pluck or strike position as a fraction of the length [1]

/-! ## 1. Equation of motion

    pd2(u,t) = c_w^2*pd2(u,x)
-/
/-- Both sides of "Equation of motion" carry the same physical dimension. -/
theorem eq1_wave_dim : (Dim.div d_u (Dim.pow d_t 2 1)) = (Dim.mul (Dim.pow d_c_w 2 1) (Dim.div d_u (Dim.pow d_x 2 1))) := by decide

/-! ## 2. Wave speed

    c_w = sqrt(T_s/mu_l)
-/
/-- Both sides of "Wave speed" carry the same physical dimension. -/
theorem eq2_c_dim : d_c_w = (Dim.pow (Dim.div d_T_s d_mu_l) 1 2) := by decide
/-- The denominator `mu_l` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_c_reg1 (mu_l : ℝ) (hmu_l : 0 < mu_l) : mu_l ≠ 0 := by positivity
/-- The argument `T_s / mu_l` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_c_reg2 (T_s mu_l : ℝ) (hT_s : 0 < T_s) (hmu_l : 0 < mu_l) : 0 ≤ T_s / mu_l := by positivity

/-! ## 3. Fundamental frequency

    f_1 = c_w/(2*L)
-/
/-- Both sides of "Fundamental frequency" carry the same physical dimension. -/
theorem eq3_f1_dim : d_f_1 = (Dim.div d_c_w (Dim.mul Dim.one d_L)) := by decide
/-- The denominator `2 * L` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_f1_reg1 (L : ℝ) (hL : 0 < L) : (2 : ℝ) * L ≠ 0 := by positivity

/-! ## 4. Mode frequencies

    f_n = n*f_1
-/
/-- Both sides of "Mode frequencies" carry the same physical dimension. -/
theorem eq4_fn_dim : d_f_n = (Dim.mul d_n d_f_1) := by decide

/-! ## 5. Initial shape, left of the pluck point

    u_0 = a_p*x/(x_p*L)
-/
/-- Both sides of "Initial shape, left of the pluck point" carry the same physical dimension. -/
theorem eq5_ic_dim : d_u_0 = (Dim.div (Dim.mul d_a_p d_x) (Dim.mul d_x_p d_L)) := by decide
/-- The denominator `x_p * L` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_ic_reg1 (x_p L : ℝ) (hx_p : 0 < x_p) (hL : 0 < L) : x_p * L ≠ 0 := by positivity

/-! ## 6. Harmonic amplitudes of a plucked string

    A_n = 2*a_p/(n^2*pi^2*x_p*(1 - x_p))*sin(n*pi*x_p)
-/
/-- Both sides of "Harmonic amplitudes of a plucked string" carry the same physical dimension. -/
theorem eq6_an_dim : d_A_n = (Dim.mul (Dim.div (Dim.mul Dim.one d_a_p) (Dim.mul (Dim.mul (Dim.mul (Dim.pow d_n 2 1) (Dim.pow Dim.one 2 1)) d_x_p) Dim.one)) Dim.one) := by decide
theorem eq6_an_term1 : Dim.one = d_x_p := by decide
theorem eq6_an_term2 : (Dim.mul (Dim.mul d_n Dim.one) d_x_p) = Dim.one := by decide
/-- Domain condition for `n^2 * pi^2 * x_p * (1 - x_p)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_an_cond1 (n x_p : ℝ) (hdom : n ^ 2 * Real.pi ^ 2 * x_p * ((1 : ℝ) - x_p) ≠ 0) : n ^ 2 * Real.pi ^ 2 * x_p * ((1 : ℝ) - x_p) ≠ 0 := hdom

/-! ## 7. Wave impedance

    Z_w = sqrt(T_s*mu_l)
-/
/-- Both sides of "Wave impedance" carry the same physical dimension. -/
theorem eq7_z_dim : d_Z_w = (Dim.pow (Dim.mul d_T_s d_mu_l) 1 2) := by decide
/-- The argument `T_s * mu_l` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_z_reg1 (T_s mu_l : ℝ) (hT_s : 0 < T_s) (hmu_l : 0 < mu_l) : 0 ≤ T_s * mu_l := by positivity

end Bespoke
