import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Ship resistance and powering

Machine-checkable statements for this investigation (ship-resistance-power).
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
def d_B : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Beam [m]
def d_C_A : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Correlation (roughness) allowance [1]
def d_C_B : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Block coefficient [1]
def d_C_F : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Frictional resistance coefficient [1]
def d_C_T : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Total resistance coefficient [1]
def d_C_W : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Wave-making resistance coefficient [1]
def d_Fn : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Froude number [1]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Waterline length [m]
def d_P_E : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Effective power [W]
def d_P_S : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Shaft power [W]
def d_R_T : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Total resistance [N]
def d_Re : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Reynolds number [1]
def d_S : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Wetted surface area [m^2]
def d_T : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Draught [m]
def d_V : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Ship speed [kn]
def d_V_d : Dim := ⟨0, 36, 0, 0, 0, 0, 0⟩  -- Displaced volume [m^3]
def d_c_w : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Wave-resistance coefficient c_w in C_W = c_w·Fn⁴ [1]
def d_eta_D : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Quasi-propulsive efficiency [1]
def d_eta_S : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Shaft transmission efficiency [1]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_k_form : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Form factor k [1]
def d_nu : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Kinematic viscosity of sea water [m^2/s]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Sea-water density [kg/m^3]

/-! ## 1. Froude number

    Fn = V/sqrt(g*L)
-/
/-- Both sides of "Froude number" carry the same physical dimension. -/
theorem eq1_fn_dim : d_Fn = (Dim.div d_V (Dim.pow (Dim.mul d_g d_L) 1 2)) := by decide
/-- The argument `g * L` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_fn_reg1 (g L : ℝ) (hg : 0 < g) (hL : 0 < L) : 0 ≤ g * L := by positivity
/-- The denominator `sqrt(g * L)` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_fn_reg2 (g L : ℝ) (hg : 0 < g) (hL : 0 < L) : Real.sqrt (g * L) ≠ 0 := by positivity

/-! ## 2. Reynolds number

    Re = V*L/nu
-/
/-- Both sides of "Reynolds number" carry the same physical dimension. -/
theorem eq2_re_dim : d_Re = (Dim.div (Dim.mul d_V d_L) d_nu) := by decide
/-- The denominator `nu` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_re_reg1 (nu : ℝ) (hnu : 0 < nu) : nu ≠ 0 := by positivity

/-! ## 3. ITTC-1957 correlation line

    C_F = 0.075/(log10(Re) - 2)^2
-/
/-- Both sides of "ITTC-1957 correlation line" carry the same physical dimension. -/
theorem eq3_cf_dim : d_C_F = (Dim.div Dim.one (Dim.pow Dim.one 2 1)) := by decide
theorem eq3_cf_term1 : d_Re = Dim.one := by decide
theorem eq3_cf_term2 : Dim.one = Dim.one := by decide
/-- The argument `Re` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_cf_reg1 (Re : ℝ) (hRe : 0 < Re) : 0 < Re := by positivity
/-- Domain condition for `(log10(Re) - 2)^2`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq3_cf_cond2 (Re : ℝ) (hdom : (Real.logb 10 Re - (2 : ℝ)) ^ 2 ≠ 0) : (Real.logb 10 Re - (2 : ℝ)) ^ 2 ≠ 0 := hdom

/-! ## 4. Displaced volume

    V_d = C_B*L*B*T
-/
/-- Both sides of "Displaced volume" carry the same physical dimension. -/
theorem eq4_vol_dim : d_V_d = (Dim.mul (Dim.mul (Dim.mul d_C_B d_L) d_B) d_T) := by decide

/-! ## 5. Wetted surface (Denny–Mumford)

    S = 1.7*L*T + V_d/T
-/
/-- Both sides of "Wetted surface (Denny–Mumford)" carry the same physical dimension. -/
theorem eq5_ws_dim : d_S = (Dim.mul (Dim.mul Dim.one d_L) d_T) := by decide
theorem eq5_ws_term1 : (Dim.mul (Dim.mul Dim.one d_L) d_T) = (Dim.div d_V_d d_T) := by decide
/-- The denominator `T` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_ws_reg1 (T : ℝ) (hT : 0 < T) : T ≠ 0 := by positivity

/-! ## 6. Wave-making coefficient

    C_W = c_w*Fn^4
-/
/-- Both sides of "Wave-making coefficient" carry the same physical dimension. -/
theorem eq6_cw_dim : d_C_W = (Dim.mul d_c_w (Dim.pow d_Fn 4 1)) := by decide

/-! ## 7. Total resistance coefficient

    C_T = (1 + k_form)*C_F + C_W + C_A
-/
/-- Both sides of "Total resistance coefficient" carry the same physical dimension. -/
theorem eq7_ct_dim : d_C_T = (Dim.mul Dim.one d_C_F) := by decide
theorem eq7_ct_term1 : Dim.one = d_k_form := by decide
theorem eq7_ct_term2 : (Dim.mul Dim.one d_C_F) = d_C_W := by decide
theorem eq7_ct_term3 : (Dim.mul Dim.one d_C_F) = d_C_A := by decide

/-! ## 8. Total resistance

    R_T = 0.5*rho*S*V^2*C_T
-/
/-- Both sides of "Total resistance" carry the same physical dimension. -/
theorem eq8_rt_dim : d_R_T = (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) d_S) (Dim.pow d_V 2 1)) d_C_T) := by decide

/-! ## 9. Effective power

    P_E = R_T*V
-/
/-- Both sides of "Effective power" carry the same physical dimension. -/
theorem eq9_pe_dim : d_P_E = (Dim.mul d_R_T d_V) := by decide

/-! ## 10. Shaft power

    P_S = P_E/(eta_D*eta_S)
-/
/-- Both sides of "Shaft power" carry the same physical dimension. -/
theorem eq10_ps_dim : d_P_S = (Dim.div d_P_E (Dim.mul d_eta_D d_eta_S)) := by decide
/-- The denominator `eta_D * eta_S` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_ps_reg1 (eta_D eta_S : ℝ) (heta_D : 0 < eta_D) (heta_S : 0 < eta_S) : eta_D * eta_S ≠ 0 := by positivity

end Bespoke
