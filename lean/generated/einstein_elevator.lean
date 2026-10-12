import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Einstein's elevator and the equivalence principle

Machine-checkable statements for this investigation (einstein-elevator).
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
def d_a_acc : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Accelerometer reading [m/s^2]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light [m/s]
def d_delta_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Sag of the light beam across the cabin [m]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration, or rocket acceleration [m/s^2]
def d_h : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Cabin height (drop height and light path for the red-shift) [m]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_w : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Cabin width crossed by the light beam [m]
def d_y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Height of the ball above the floor [m]
def d_z : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fractional frequency shift [1]

/-! ## 1. Accelerometer reading

    a_acc = g
-/
/-- Both sides of "Accelerometer reading" carry the same physical dimension. -/
theorem eq1_acc_dim : d_a_acc = d_g := by decide

/-! ## 2. Dropped ball relative to the floor

    d2(y,t) = -g
-/
/-- Both sides of "Dropped ball relative to the floor" carry the same physical dimension. -/
theorem eq2_ball_dim : (Dim.div d_y (Dim.pow d_t 2 1)) = d_g := by decide

/-! ## 3. Sag of a light beam crossing the cabin

    delta_L = g*w^2/(2*c^2)
-/
/-- Both sides of "Sag of a light beam crossing the cabin" carry the same physical dimension. -/
theorem eq3_light_dim : d_delta_L = (Dim.div (Dim.mul d_g (Dim.pow d_w 2 1)) (Dim.mul Dim.one (Dim.pow d_c 2 1))) := by decide
/-- The denominator `2 * c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_light_reg1 (c : ℝ) (hc : 0 < c) : (2 : ℝ) * c ^ 2 ≠ 0 := by positivity

/-! ## 4. Gravitational red-shift over height h

    z = g*h/c^2
-/
/-- Both sides of "Gravitational red-shift over height h" carry the same physical dimension. -/
theorem eq4_red_dim : d_z = (Dim.div (Dim.mul d_g d_h) (Dim.pow d_c 2 1)) := by decide
/-- The denominator `c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_red_reg1 (c : ℝ) (hc : 0 < c) : c ^ 2 ≠ 0 := by positivity

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (C D E L : Prop) (h1 : L → (¬D)) (h2 : (¬D) → E) (h3 : D ↔ C) (h4 : L) : E ∧ (¬C) := by tauto

end Bespoke
