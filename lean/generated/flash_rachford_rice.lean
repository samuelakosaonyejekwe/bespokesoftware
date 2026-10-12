import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Isothermal flash of a benzene–toluene–xylene mixture

Machine-checkable statements for this investigation (flash-rachford-rice).
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
def d_A_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Antoine A of benzene [1]
def d_B_1 : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Antoine B of benzene [K]
def d_C_1 : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Antoine C of benzene [K]
def d_F : Dim := ⟨0, 0, -12, 0, 0, 12, 0⟩  -- Feed rate [kmol/h]
def d_K_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- K-value of benzene [1]
def d_K_2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- K-value of toluene [1]
def d_K_3 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- K-value of o-xylene [1]
def d_L : Dim := ⟨0, 0, -12, 0, 0, 12, 0⟩  -- Liquid rate [mol/s]
def d_T : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Flash temperature [°C]
def d_T_z : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Ice-point temperature 273.15 K [K]
def d_V : Dim := ⟨0, 0, -12, 0, 0, 12, 0⟩  -- Vapour rate [mol/s]
def d_p : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Flash pressure [bar]
def d_p_mm : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Reference pressure 1 mmHg [Pa]
def d_p_s1 : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Vapour pressure of benzene [Pa]
def d_psi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Vapour fraction V/F [1]
def d_x_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Benzene in the liquid [1]
def d_y_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Benzene in the vapour [1]
def d_z_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Benzene mole fraction in the feed [1]
def d_z_2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Toluene mole fraction in the feed [1]
def d_z_3 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- o-Xylene mole fraction in the feed [1]

/-! ## 1. Feed composition closure

    z_3 = 1 - z_1 - z_2
-/
/-- Both sides of "Feed composition closure" carry the same physical dimension. -/
theorem eq1_z3_dim : d_z_3 = Dim.one := by decide
theorem eq1_z3_term1 : Dim.one = d_z_1 := by decide
theorem eq1_z3_term2 : Dim.one = d_z_2 := by decide

/-! ## 2. Antoine vapour pressure (shown for benzene)

    log10(p_s1/p_mm) = A_1 - B_1/(C_1 + T - T_z)
-/
/-- Both sides of "Antoine vapour pressure (shown for benzene)" carry the same physical dimension. -/
theorem eq2_ant_dim : Dim.one = d_A_1 := by decide
theorem eq2_ant_term1 : (Dim.div d_p_s1 d_p_mm) = Dim.one := by decide
theorem eq2_ant_term2 : d_C_1 = d_T := by decide
theorem eq2_ant_term3 : d_C_1 = d_T_z := by decide
theorem eq2_ant_term4 : d_A_1 = (Dim.div d_B_1 d_C_1) := by decide
/-- Domain condition for `p_mm`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_ant_cond1 (p_mm : ℝ) (hdom : p_mm ≠ 0) : p_mm ≠ 0 := hdom
/-- Domain condition for `p_s1 / p_mm`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_ant_cond2 (p_s1 p_mm : ℝ) (hdom : 0 < p_s1 / p_mm) : 0 < p_s1 / p_mm := hdom
/-- Domain condition for `C_1 + T - T_z`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_ant_cond3 (C_1 T T_z : ℝ) (hdom : C_1 + T - T_z ≠ 0) : C_1 + T - T_z ≠ 0 := hdom

/-! ## 3. Raoult’s law (shown for benzene)

    K_1 = p_s1/p
-/
/-- Both sides of "Raoult’s law (shown for benzene)" carry the same physical dimension. -/
theorem eq3_k_dim : d_K_1 = (Dim.div d_p_s1 d_p) := by decide
/-- The denominator `p` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_k_reg1 (p : ℝ) (hp : 0 < p) : p ≠ 0 := by positivity

/-! ## 4. Rachford–Rice equation

    z_1*(K_1 - 1)/(1 + psi*(K_1 - 1)) + z_2*(K_2 - 1)/(1 + psi*(K_2 - 1)) + z_3*(K_3 - 1)/(1 + psi*(K_3 - 1)) = 0
-/
/-- Both sides of "Rachford–Rice equation" carry the same physical dimension. -/
theorem eq4_rr_dim : (Dim.div (Dim.mul d_z_1 d_K_1) Dim.one) = Dim.one := by decide
theorem eq4_rr_term1 : d_K_1 = Dim.one := by decide
theorem eq4_rr_term2 : d_K_1 = Dim.one := by decide
theorem eq4_rr_term3 : Dim.one = (Dim.mul d_psi d_K_1) := by decide
theorem eq4_rr_term4 : d_K_2 = Dim.one := by decide
theorem eq4_rr_term5 : d_K_2 = Dim.one := by decide
theorem eq4_rr_term6 : Dim.one = (Dim.mul d_psi d_K_2) := by decide
theorem eq4_rr_term7 : (Dim.div (Dim.mul d_z_1 d_K_1) Dim.one) = (Dim.div (Dim.mul d_z_2 d_K_2) Dim.one) := by decide
theorem eq4_rr_term8 : d_K_3 = Dim.one := by decide
theorem eq4_rr_term9 : d_K_3 = Dim.one := by decide
theorem eq4_rr_term10 : Dim.one = (Dim.mul d_psi d_K_3) := by decide
theorem eq4_rr_term11 : (Dim.div (Dim.mul d_z_1 d_K_1) Dim.one) = (Dim.div (Dim.mul d_z_3 d_K_3) Dim.one) := by decide
/-- Domain condition for `1 + psi * (K_1 - 1)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_rr_cond1 (psi K_1 : ℝ) (hdom : (1 : ℝ) + psi * (K_1 - (1 : ℝ)) ≠ 0) : (1 : ℝ) + psi * (K_1 - (1 : ℝ)) ≠ 0 := hdom
/-- Domain condition for `1 + psi * (K_2 - 1)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_rr_cond2 (psi K_2 : ℝ) (hdom : (1 : ℝ) + psi * (K_2 - (1 : ℝ)) ≠ 0) : (1 : ℝ) + psi * (K_2 - (1 : ℝ)) ≠ 0 := hdom
/-- Domain condition for `1 + psi * (K_3 - 1)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_rr_cond3 (psi K_3 : ℝ) (hdom : (1 : ℝ) + psi * (K_3 - (1 : ℝ)) ≠ 0) : (1 : ℝ) + psi * (K_3 - (1 : ℝ)) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq4_rr_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 5. Liquid composition (shown for benzene)

    x_1 = z_1/(1 + psi*(K_1 - 1))
-/
/-- Both sides of "Liquid composition (shown for benzene)" carry the same physical dimension. -/
theorem eq5_x_dim : d_x_1 = (Dim.div d_z_1 Dim.one) := by decide
theorem eq5_x_term1 : d_K_1 = Dim.one := by decide
theorem eq5_x_term2 : Dim.one = (Dim.mul d_psi d_K_1) := by decide
/-- Domain condition for `1 + psi * (K_1 - 1)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_x_cond1 (psi K_1 : ℝ) (hdom : (1 : ℝ) + psi * (K_1 - (1 : ℝ)) ≠ 0) : (1 : ℝ) + psi * (K_1 - (1 : ℝ)) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq5_x_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 6. Vapour composition (shown for benzene)

    y_1 = K_1*x_1
-/
/-- Both sides of "Vapour composition (shown for benzene)" carry the same physical dimension. -/
theorem eq6_y_dim : d_y_1 = (Dim.mul d_K_1 d_x_1) := by decide

/-! ## 7. Vapour rate

    V = psi*F
-/
/-- Both sides of "Vapour rate" carry the same physical dimension. -/
theorem eq7_v_dim : d_V = (Dim.mul d_psi d_F) := by decide

/-! ## 8. Liquid rate

    L = (1 - psi)*F
-/
/-- Both sides of "Liquid rate" carry the same physical dimension. -/
theorem eq8_l_dim : d_L = (Dim.mul Dim.one d_F) := by decide
theorem eq8_l_term1 : Dim.one = d_psi := by decide

end Bespoke
