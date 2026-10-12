import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Hydrate formation risk in a high-pressure, low-temperature line

Machine-checkable statements for this investigation (hydrate-formation-risk).
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
def d_A : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Flow area [m^2]
def d_A_s : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Steel cross-section [m^2]
def d_D : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Inner diameter [in]
def d_K_H : Dim := ⟨12, 0, 0, 0, 12, -12, 0⟩  -- Hammerschmidt constant [K kg/mol]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Flowline length [km]
def d_M_i : Dim := ⟨12, 0, 0, 0, 0, -12, 0⟩  -- Inhibitor molar mass [kg/mol]
def d_T : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Fluid temperature [K]
def d_T_amb : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Seabed temperature [°C]
def d_T_eq : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Hydrate equilibrium temperature [K]
def d_U : Dim := ⟨12, 0, -36, 0, -12, 0, 0⟩  -- Overall heat-transfer coefficient [W/(m^2 K)]
def d_W : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Inhibitor mass fraction in the aqueous phase [1]
def d_c_s : Dim := ⟨0, 24, -24, 0, -12, 0, 0⟩  -- Steel specific heat [J/(kg K)]
def d_cp : Dim := ⟨0, 24, -24, 0, -12, 0, 0⟩  -- Mixture specific heat [J/(kg K)]
def d_dT_H : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Hydrate-temperature depression [K]
def d_dT_sub : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Subcooling [K]
def d_dp : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Pressure drop over the line [bar]
def d_k_g : Dim := ⟨0, 0, -12, 0, -12, 0, 0⟩  -- Hydrate growth coefficient [1/(K s)]
def d_mdot : Dim := ⟨12, 0, -12, 0, 0, 0, 0⟩  -- Total mass flow rate [kg/s]
def d_p : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Pressure [Pa]
def d_p_in : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Inlet pressure [bar]
def d_phi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Hydrate volume fraction [1]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Mixture density at line conditions [kg/m^3]
def d_rho_s : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Steel density [kg/m^3]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance [m]

/-! ## 1. Flowing energy balance

    mdot*cp*pd(T,x) = -U*pi*D*(T - T_amb)
-/
/-- Both sides of "Flowing energy balance" carry the same physical dimension. -/
theorem eq1_en_dim : (Dim.mul (Dim.mul d_mdot d_cp) (Dim.div d_T d_x)) = (Dim.mul (Dim.mul (Dim.mul d_U Dim.one) d_D) d_T) := by decide
theorem eq1_en_term1 : d_T = d_T_amb := by decide

/-! ## 2. Pressure profile

    p = p_in - dp*x/L
-/
/-- Both sides of "Pressure profile" carry the same physical dimension. -/
theorem eq2_pp_dim : d_p = d_p_in := by decide
theorem eq2_pp_term1 : d_p_in = (Dim.div (Dim.mul d_dp d_x) d_L) := by decide
/-- The denominator `L` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_pp_reg1 (L : ℝ) (hL : 0 < L) : L ≠ 0 := by positivity

/-! ## 3. Subcooling

    dT_sub = T_eq - T
-/
/-- Both sides of "Subcooling" carry the same physical dimension. -/
theorem eq3_sub_dim : d_dT_sub = d_T_eq := by decide
theorem eq3_sub_term1 : d_T_eq = d_T := by decide

/-! ## 4. Inhibitor depression

    dT_H = K_H*W/(M_i*(1 - W))
-/
/-- Both sides of "Inhibitor depression" carry the same physical dimension. -/
theorem eq4_ham_dim : d_dT_H = (Dim.div (Dim.mul d_K_H d_W) (Dim.mul d_M_i Dim.one)) := by decide
theorem eq4_ham_term1 : Dim.one = d_W := by decide
/-- Domain condition for `M_i * (1 - W)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_ham_cond1 (M_i W : ℝ) (hdom : M_i * ((1 : ℝ) - W) ≠ 0) : M_i * ((1 : ℝ) - W) ≠ 0 := hdom

/-! ## 5. Shut-in cool-down

    (rho*cp*A + rho_s*c_s*A_s)*d(T,t) = -U*pi*D*(T - T_amb)
-/
/-- Both sides of "Shut-in cool-down" carry the same physical dimension. -/
theorem eq5_cool_dim : (Dim.mul (Dim.mul (Dim.mul d_rho d_cp) d_A) (Dim.div d_T d_t)) = (Dim.mul (Dim.mul (Dim.mul d_U Dim.one) d_D) d_T) := by decide
theorem eq5_cool_term1 : (Dim.mul (Dim.mul d_rho d_cp) d_A) = (Dim.mul (Dim.mul d_rho_s d_c_s) d_A_s) := by decide
theorem eq5_cool_term2 : d_T = d_T_amb := by decide

/-! ## 6. Hydrate growth

    d(phi,t) = k_g*max(dT_sub, 0)*(1 - phi)
-/
/-- Both sides of "Hydrate growth" carry the same physical dimension. -/
theorem eq6_grow_dim : (Dim.div d_phi d_t) = (Dim.mul (Dim.mul d_k_g d_dT_sub) Dim.one) := by decide
theorem eq6_grow_term1 : Dim.one = d_phi := by decide

end Bespoke
