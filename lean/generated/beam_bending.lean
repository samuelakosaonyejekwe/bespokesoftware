import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Euler–Bernoulli beam under distributed and point loads

Machine-checkable statements for this investigation (beam-bending).
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
def d_E : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Young's modulus [GPa]
def d_I_b : Dim := ⟨0, 48, 0, 0, 0, 0, 0⟩  -- Second moment of area [cm^4]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Span (or cantilever length) [m]
def d_M_b : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Bending moment [N m]
def d_M_max : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Largest bending moment [N m]
def d_P : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Point load [kN]
def d_V_s : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Shear force [N]
def d_c_y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance from the neutral axis to the extreme fibre [mm]
def d_delta_P : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Deflection due to a central or tip point load [m]
def d_delta_w : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Deflection due to the distributed load [m]
def d_f_1 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- First natural frequency [1/s]
def d_m_l : Dim := ⟨12, -12, 0, 0, 0, 0, 0⟩  -- Mass per unit length of the beam [kg/m]
def d_sigma_max : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Largest bending stress [Pa]
def d_v_d : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Deflection [m]
def d_w : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Uniformly distributed load [kN/m]
def d_w_t : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Total distributed load [N/m]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance along the beam [m]

/-! ## 1. Distributed load

    w_t = w
-/
/-- Both sides of "Distributed load" carry the same physical dimension. -/
theorem eq1_wt_dim : d_w_t = d_w := by decide

/-! ## 2. Euler–Bernoulli beam equation

    E*I_b*pd2(pd2(v_d,x),x) = w_t
-/
/-- Both sides of "Euler–Bernoulli beam equation" carry the same physical dimension. -/
theorem eq2_eb_dim : (Dim.mul (Dim.mul d_E d_I_b) (Dim.div (Dim.div d_v_d (Dim.pow d_x 2 1)) (Dim.pow d_x 2 1))) = d_w_t := by decide

/-! ## 3. Moment–curvature relation

    M_b = -E*I_b*pd2(v_d,x)
-/
/-- Both sides of "Moment–curvature relation" carry the same physical dimension. -/
theorem eq3_mk_dim : d_M_b = (Dim.mul (Dim.mul d_E d_I_b) (Dim.div d_v_d (Dim.pow d_x 2 1))) := by decide

/-! ## 4. Shear force

    V_s = pd(M_b,x)
-/
/-- Both sides of "Shear force" carry the same physical dimension. -/
theorem eq4_vm_dim : d_V_s = (Dim.div d_M_b d_x) := by decide

/-! ## 5. Mid-span deflection under uniform load

    delta_w = 5*w_t*L^4/(384*E*I_b)
-/
/-- Both sides of "Mid-span deflection under uniform load" carry the same physical dimension. -/
theorem eq5_dw_dim : d_delta_w = (Dim.div (Dim.mul (Dim.mul Dim.one d_w_t) (Dim.pow d_L 4 1)) (Dim.mul (Dim.mul Dim.one d_E) d_I_b)) := by decide
/-- The denominator `384 * E * I_b` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_dw_reg1 (E I_b : ℝ) (hE : 0 < E) (hI_b : 0 < I_b) : (384 : ℝ) * E * I_b ≠ 0 := by positivity

/-! ## 6. Mid-span deflection under a central point load

    delta_P = P*L^3/(48*E*I_b)
-/
/-- Both sides of "Mid-span deflection under a central point load" carry the same physical dimension. -/
theorem eq6_dp_dim : d_delta_P = (Dim.div (Dim.mul d_P (Dim.pow d_L 3 1)) (Dim.mul (Dim.mul Dim.one d_E) d_I_b)) := by decide
/-- The denominator `48 * E * I_b` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_dp_reg1 (E I_b : ℝ) (hE : 0 < E) (hI_b : 0 < I_b) : (48 : ℝ) * E * I_b ≠ 0 := by positivity

/-! ## 7. Bending stress

    sigma_max = M_max*c_y/I_b
-/
/-- Both sides of "Bending stress" carry the same physical dimension. -/
theorem eq7_sig_dim : d_sigma_max = (Dim.div (Dim.mul d_M_max d_c_y) d_I_b) := by decide
/-- The denominator `I_b` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_sig_reg1 (I_b : ℝ) (hI_b : 0 < I_b) : I_b ≠ 0 := by positivity

/-! ## 8. First natural frequency

    f_1 = pi/(2*L^2)*sqrt(E*I_b/m_l)
-/
/-- Both sides of "First natural frequency" carry the same physical dimension. -/
theorem eq8_f1_dim : d_f_1 = (Dim.mul (Dim.div Dim.one (Dim.mul Dim.one (Dim.pow d_L 2 1))) (Dim.pow (Dim.div (Dim.mul d_E d_I_b) d_m_l) 1 2)) := by decide
/-- The denominator `2 * L^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_f1_reg1 (L : ℝ) (hL : 0 < L) : (2 : ℝ) * L ^ 2 ≠ 0 := by positivity
/-- The denominator `m_l` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_f1_reg2 (m_l : ℝ) (hm_l : 0 < m_l) : m_l ≠ 0 := by positivity
/-- The argument `E * I_b / m_l` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_f1_reg3 (E I_b m_l : ℝ) (hE : 0 < E) (hI_b : 0 < I_b) (hm_l : 0 < m_l) : 0 ≤ E * I_b / m_l := by positivity

end Bespoke
