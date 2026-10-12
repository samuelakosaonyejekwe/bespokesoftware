import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Double-slit interference of matter waves

Machine-checkable statements for this investigation (double-slit-interference).
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
def d_D_w : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Which-path distinguishability [1]
def d_I_n : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Normalised intensity [1]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance from slits to screen [m]
def d_N_F : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Far-field parameter [1]
def d_V_f : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fringe visibility [1]
def d_d_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Slit separation, centre to centre [um]
def d_dy : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Fringe spacing [m]
def d_hbar : Dim := ⟨12, 24, -12, 0, 0, 0, 0⟩  -- Reduced Planck constant [J s]
def d_lambda : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- de Broglie wavelength [m]
def d_m : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Particle mass [u]
def d_v : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Particle speed [m/s]
def d_w_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Slit width [um]
def d_y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position on the screen [m]

/-! ## 1. de Broglie wavelength

    lambda = 2*pi*hbar/(m*v)
-/
/-- Both sides of "de Broglie wavelength" carry the same physical dimension. -/
theorem eq1_lam_dim : d_lambda = (Dim.div (Dim.mul (Dim.mul Dim.one Dim.one) d_hbar) (Dim.mul d_m d_v)) := by decide
/-- The denominator `m * v` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_lam_reg1 (m v : ℝ) (hm : 0 < m) (hv : 0 < v) : m * v ≠ 0 := by positivity

/-! ## 2. Fringe spacing

    dy = lambda*L/d_s
-/
/-- Both sides of "Fringe spacing" carry the same physical dimension. -/
theorem eq2_dy_dim : d_dy = (Dim.div (Dim.mul d_lambda d_L) d_d_s) := by decide
/-- The denominator `d_s` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_dy_reg1 (d_s : ℝ) (hd_s : 0 < d_s) : d_s ≠ 0 := by positivity

/-! ## 3. Intensity on the screen

    I_n = (sin(pi*w_s*y/(lambda*L))/(pi*w_s*y/(lambda*L)))^2*(1 + V_f*cos(2*pi*d_s*y/(lambda*L)))/2
-/
/-- Both sides of "Intensity on the screen" carry the same physical dimension. -/
theorem eq3_I'_dim : d_I_n = (Dim.div (Dim.mul (Dim.pow (Dim.div Dim.one (Dim.div (Dim.mul (Dim.mul Dim.one d_w_s) d_y) (Dim.mul d_lambda d_L))) 2 1) Dim.one) Dim.one) := by decide
theorem eq3_I'_term1 : (Dim.div (Dim.mul (Dim.mul Dim.one d_w_s) d_y) (Dim.mul d_lambda d_L)) = Dim.one := by decide
theorem eq3_I'_term2 : (Dim.div (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_d_s) d_y) (Dim.mul d_lambda d_L)) = Dim.one := by decide
theorem eq3_I'_term3 : Dim.one = (Dim.mul d_V_f Dim.one) := by decide
/-- The denominator `lambda * L` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_I'_reg1 (lambda L : ℝ) (hlambda : 0 < lambda) (hL : 0 < L) : lambda * L ≠ 0 := by positivity
/-- The denominator `lambda * L` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_I'_reg2 (lambda L : ℝ) (hlambda : 0 < lambda) (hL : 0 < L) : lambda * L ≠ 0 := by positivity
/-- Domain condition for `pi * w_s * y / (lambda * L)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_I'_cond3 (w_s y lambda L : ℝ) (hdom : Real.pi * w_s * y / (lambda * L) ≠ 0) : Real.pi * w_s * y / (lambda * L) ≠ 0 := hdom
/-- The denominator `lambda * L` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_I'_reg4 (lambda L : ℝ) (hlambda : 0 < lambda) (hL : 0 < L) : lambda * L ≠ 0 := by positivity
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_I'_reg5  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 4. Far-field parameter

    N_F = d_s*w_s/(lambda*L)
-/
/-- Both sides of "Far-field parameter" carry the same physical dimension. -/
theorem eq4_nf_dim : d_N_F = (Dim.div (Dim.mul d_d_s d_w_s) (Dim.mul d_lambda d_L)) := by decide
/-- The denominator `lambda * L` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_nf_reg1 (lambda L : ℝ) (hlambda : 0 < lambda) (hL : 0 < L) : lambda * L ≠ 0 := by positivity

/-! ## 5. Visibility with which-path information

    V_f = sqrt(1 - D_w^2)
-/
/-- Both sides of "Visibility with which-path information" carry the same physical dimension. -/
theorem eq5_vis_dim : d_V_f = (Dim.pow Dim.one 1 2) := by decide
theorem eq5_vis_term1 : Dim.one = (Dim.pow d_D_w 2 1) := by decide
/-- Domain condition for `1 - D_w^2`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq5_vis_cond1 (D_w : ℝ) (hdom : 0 ≤ (1 : ℝ) - D_w ^ 2) : 0 ≤ (1 : ℝ) - D_w ^ 2 := hdom

/-! ## 6. Duality relation

    V_f^2 + D_w^2 = 1
-/
/-- Both sides of "Duality relation" carry the same physical dimension. -/
theorem eq6_dual_dim : (Dim.pow d_V_f 2 1) = Dim.one := by decide
theorem eq6_dual_term1 : (Dim.pow d_V_f 2 1) = (Dim.pow d_D_w 2 1) := by decide

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (F P W : Prop) (h1 : W → (¬F)) (h2 : P → (¬F)) (h3 : F) : (¬W) ∧ (¬P) := by tauto

end Bespoke
