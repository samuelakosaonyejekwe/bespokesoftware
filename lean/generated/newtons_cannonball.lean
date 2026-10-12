import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Newton's cannonball

Machine-checkable statements for this investigation (newtons-cannonball).
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
def d_GM : Dim := ⟨0, 36, -24, 0, 0, 0, 0⟩  -- Gravitational parameter of the planet [m^3/s^2]
def d_R_p : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Radius of the planet [km]
def d_a_sm : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Semi-major axis [m]
def d_ecc : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Eccentricity [1]
def d_eps : Dim := ⟨0, 24, -24, 0, 0, 0, 0⟩  -- Specific orbital energy [J/kg]
def d_h_a : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Specific angular momentum [m^2/s]
def d_h_m : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Height of the mountain above the surface [km]
def d_r : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance from the planet centre [m]
def d_r_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Launch distance from the centre [m]
def d_r_p : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Periapsis distance [m]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_v_0 : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Muzzle speed [km/s]
def d_v_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Circular speed at the launch point [m/s]
def d_v_e : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Escape speed at the launch point [m/s]
def d_v_i : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Launch speed in the non-rotating frame [m/s]
def d_v_min : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Least horizontal speed that clears the planet [m/s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position, horizontal component [m]

/-! ## 1. Launch distance from the centre

    r_0 = R_p + h_m
-/
/-- Both sides of "Launch distance from the centre" carry the same physical dimension. -/
theorem eq1_r0_dim : d_r_0 = d_R_p := by decide
theorem eq1_r0_term1 : d_R_p = d_h_m := by decide

/-! ## 2. Launch speed in the non-rotating frame

    v_i = v_0
-/
/-- Both sides of "Launch speed in the non-rotating frame" carry the same physical dimension. -/
theorem eq2_vi_dim : d_v_i = d_v_0 := by decide

/-! ## 3. Equation of motion

    d2(x,t) = -GM*x/r^3
-/
/-- Both sides of "Equation of motion" carry the same physical dimension. -/
theorem eq3_mx_dim : (Dim.div d_x (Dim.pow d_t 2 1)) = (Dim.div (Dim.mul d_GM d_x) (Dim.pow d_r 3 1)) := by decide
/-- Domain condition for `r^3`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_mx_cond1 (r : ℝ) (hdom : r ^ 3 ≠ 0) : r ^ 3 ≠ 0 := hdom

/-! ## 4. Circular speed

    v_c = sqrt(GM/r_0)
-/
/-- Both sides of "Circular speed" carry the same physical dimension. -/
theorem eq4_vc_dim : d_v_c = (Dim.pow (Dim.div d_GM d_r_0) 1 2) := by decide
/-- Domain condition for `r_0`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_vc_cond1 (r_0 : ℝ) (hdom : r_0 ≠ 0) : r_0 ≠ 0 := hdom
/-- Domain condition for `GM / r_0`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_vc_cond2 (GM r_0 : ℝ) (hdom : 0 ≤ GM / r_0) : 0 ≤ GM / r_0 := hdom

/-! ## 5. Escape speed

    v_e = sqrt(2*GM/r_0)
-/
/-- Both sides of "Escape speed" carry the same physical dimension. -/
theorem eq5_ve_dim : d_v_e = (Dim.pow (Dim.div (Dim.mul Dim.one d_GM) d_r_0) 1 2) := by decide
/-- Domain condition for `r_0`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_ve_cond1 (r_0 : ℝ) (hdom : r_0 ≠ 0) : r_0 ≠ 0 := hdom
/-- Domain condition for `2 * GM / r_0`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_ve_cond2 (GM r_0 : ℝ) (hdom : 0 ≤ (2 : ℝ) * GM / r_0) : 0 ≤ (2 : ℝ) * GM / r_0 := hdom

/-! ## 6. Least speed that clears the planet

    v_min = sqrt(2*GM*R_p/(r_0*(R_p + r_0)))
-/
/-- Both sides of "Least speed that clears the planet" carry the same physical dimension. -/
theorem eq6_vmin_dim : d_v_min = (Dim.pow (Dim.div (Dim.mul (Dim.mul Dim.one d_GM) d_R_p) (Dim.mul d_r_0 d_R_p)) 1 2) := by decide
theorem eq6_vmin_term1 : d_R_p = d_r_0 := by decide
/-- Domain condition for `r_0 * (R_p + r_0)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_vmin_cond1 (r_0 R_p : ℝ) (hdom : r_0 * (R_p + r_0) ≠ 0) : r_0 * (R_p + r_0) ≠ 0 := hdom
/-- Domain condition for `2 * GM * R_p / (r_0 * (R_p + r_0))`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_vmin_cond2 (GM R_p r_0 : ℝ) (hdom : 0 ≤ (2 : ℝ) * GM * R_p / (r_0 * (R_p + r_0))) : 0 ≤ (2 : ℝ) * GM * R_p / (r_0 * (R_p + r_0)) := hdom

/-! ## 7. Specific orbital energy

    eps = v_i^2/2 - GM/r_0
-/
/-- Both sides of "Specific orbital energy" carry the same physical dimension. -/
theorem eq7_en_dim : d_eps = (Dim.div (Dim.pow d_v_i 2 1) Dim.one) := by decide
theorem eq7_en_term1 : (Dim.div (Dim.pow d_v_i 2 1) Dim.one) = (Dim.div d_GM d_r_0) := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_en_reg1  : (2 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `r_0`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_en_cond2 (r_0 : ℝ) (hdom : r_0 ≠ 0) : r_0 ≠ 0 := hdom

/-! ## 8. Specific angular momentum

    h_a = r_0*v_i
-/
/-- Both sides of "Specific angular momentum" carry the same physical dimension. -/
theorem eq8_am_dim : d_h_a = (Dim.mul d_r_0 d_v_i) := by decide

/-! ## 9. Semi-major axis

    a_sm = -GM/(2*eps)
-/
/-- Both sides of "Semi-major axis" carry the same physical dimension. -/
theorem eq9_sma_dim : d_a_sm = (Dim.div d_GM (Dim.mul Dim.one d_eps)) := by decide
/-- Domain condition for `2 * eps`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq9_sma_cond1 (eps : ℝ) (hdom : (2 : ℝ) * eps ≠ 0) : (2 : ℝ) * eps ≠ 0 := hdom

/-! ## 10. Eccentricity

    ecc = sqrt(1 + 2*eps*h_a^2/GM^2)
-/
/-- Both sides of "Eccentricity" carry the same physical dimension. -/
theorem eq10_ecc_dim : d_ecc = (Dim.pow Dim.one 1 2) := by decide
theorem eq10_ecc_term1 : Dim.one = (Dim.div (Dim.mul (Dim.mul Dim.one d_eps) (Dim.pow d_h_a 2 1)) (Dim.pow d_GM 2 1)) := by decide
/-- The denominator `GM^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_ecc_reg1 (GM : ℝ) (hGM : 0 < GM) : GM ^ 2 ≠ 0 := by positivity
/-- Domain condition for `1 + 2 * eps * h_a^2 / GM^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_ecc_cond2 (eps h_a GM : ℝ) (hdom : 0 ≤ (1 : ℝ) + (2 : ℝ) * eps * h_a ^ 2 / GM ^ 2) : 0 ≤ (1 : ℝ) + (2 : ℝ) * eps * h_a ^ 2 / GM ^ 2 := hdom

/-! ## 11. Periapsis distance

    r_p = h_a^2/(GM*(1 + ecc))
-/
/-- Both sides of "Periapsis distance" carry the same physical dimension. -/
theorem eq11_rp_dim : d_r_p = (Dim.div (Dim.pow d_h_a 2 1) (Dim.mul d_GM Dim.one)) := by decide
theorem eq11_rp_term1 : Dim.one = d_ecc := by decide
/-- The denominator `GM * (1 + ecc)` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_rp_reg1 (GM ecc : ℝ) (hGM : 0 < GM) (hecc : 0 < ecc) : GM * ((1 : ℝ) + ecc) ≠ 0 := by positivity

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (B F L M O U : Prop) (h1 : F → (¬L)) (h2 : ((¬L) ∧ B) → O) (h3 : (O ∧ U) → M) : ((F ∧ B) ∧ U) → M := by tauto

end Bespoke
