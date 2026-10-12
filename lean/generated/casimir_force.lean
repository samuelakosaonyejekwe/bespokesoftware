import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Casimir force between conducting surfaces

Machine-checkable statements for this investigation (casimir-force).
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
def d_A_p : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Area of the parallel plates [cm^2]
def d_E_A : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Casimir energy per unit area [J/m^2]
def d_F_pp : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Force between the plates [N]
def d_F_sp : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Sphere–plate force [N]
def d_P_C : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Casimir pressure between parallel plates [Pa]
def d_R_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Radius of the sphere (sphere–plate geometry) [um]
def d_T_eff : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Effective temperature of the gap [K]
def d_a : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Separation between the surfaces [nm]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light [m/s]
def d_hbar : Dim := ⟨12, 24, -12, 0, 0, 0, 0⟩  -- Reduced Planck constant [J s]
def d_k_B : Dim := ⟨12, 24, -24, 0, -12, 0, 0⟩  -- Boltzmann constant [J/K]

/-! ## 1. Casimir pressure

    P_C = pi^2*hbar*c/(240*a^4)
-/
/-- Both sides of "Casimir pressure" carry the same physical dimension. -/
theorem eq1_P_dim : d_P_C = (Dim.div (Dim.mul (Dim.mul (Dim.pow Dim.one 2 1) d_hbar) d_c) (Dim.mul Dim.one (Dim.pow d_a 4 1))) := by decide
/-- The denominator `240 * a^4` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_P_reg1 (a : ℝ) (ha : 0 < a) : (240 : ℝ) * a ^ 4 ≠ 0 := by positivity

/-! ## 2. Casimir energy per unit area (ideal, zero temperature)

    E_A = -pi^2*hbar*c/(720*a^3)
-/
/-- Both sides of "Casimir energy per unit area (ideal, zero temperature)" carry the same physical dimension. -/
theorem eq2_E_dim : d_E_A = (Dim.div (Dim.mul (Dim.mul (Dim.pow Dim.one 2 1) d_hbar) d_c) (Dim.mul Dim.one (Dim.pow d_a 3 1))) := by decide
/-- The denominator `720 * a^3` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_E_reg1 (a : ℝ) (ha : 0 < a) : (720 : ℝ) * a ^ 3 ≠ 0 := by positivity

/-! ## 3. Force between the plates

    F_pp = P_C*A_p
-/
/-- Both sides of "Force between the plates" carry the same physical dimension. -/
theorem eq3_F_dim : d_F_pp = (Dim.mul d_P_C d_A_p) := by decide

/-! ## 4. Sphere–plate force

    F_sp = pi^3*hbar*c*R_s/(360*a^3)
-/
/-- Both sides of "Sphere–plate force" carry the same physical dimension. -/
theorem eq4_sp_dim : d_F_sp = (Dim.div (Dim.mul (Dim.mul (Dim.mul (Dim.pow Dim.one 3 1) d_hbar) d_c) d_R_s) (Dim.mul Dim.one (Dim.pow d_a 3 1))) := by decide
/-- The denominator `360 * a^3` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_sp_reg1 (a : ℝ) (ha : 0 < a) : (360 : ℝ) * a ^ 3 ≠ 0 := by positivity

/-! ## 5. Effective temperature

    T_eff = hbar*c/(2*a*k_B)
-/
/-- Both sides of "Effective temperature" carry the same physical dimension. -/
theorem eq5_teff_dim : d_T_eff = (Dim.div (Dim.mul d_hbar d_c) (Dim.mul (Dim.mul Dim.one d_a) d_k_B)) := by decide
/-- The denominator `2 * a * k_B` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_teff_reg1 (a k_B : ℝ) (ha : 0 < a) (hk_B : 0 < k_B) : (2 : ℝ) * a * k_B ≠ 0 := by positivity

end Bespoke
