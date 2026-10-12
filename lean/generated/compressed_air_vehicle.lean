import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Vehicle driven by stored compressed air

Machine-checkable statements for this investigation (compressed-air-vehicle).
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
def d_C_rr : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Rolling-resistance coefficient [1]
def d_CdA : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Drag area C_d·A [m^2]
def d_E_in : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- External energy to recharge [J]
def d_E_w : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Work delivered at the wheels [J]
def d_F_r : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Road load [N]
def d_P_max : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Rated motor power at the wheels [kW]
def d_R_range : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Range [m]
def d_R_s : Dim := ⟨0, 24, -24, 0, -12, 0, 0⟩  -- Specific gas constant of air [J/(kg K)]
def d_T_0 : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Ambient temperature [°C]
def d_V_tank : Dim := ⟨0, 36, 0, 0, 0, 0, 0⟩  -- Tank volume [L]
def d_W_gas : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Gross isothermal expansion work [J]
def d_W_loop : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Net work of an expand–recompress loop [J]
def d_X : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Tank exergy (maximum work) [J]
def d_eta_comp : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Compressor efficiency, work to stored exergy [1]
def d_eta_exp : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Expander efficiency, tank exergy to wheels [1]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_m_air : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass of stored air [kg]
def d_m_veh : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Vehicle mass including occupants [kg]
def d_p_0 : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Atmospheric pressure [bar]
def d_p_tank : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Tank pressure when full [bar]
def d_rho_air : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Ambient air density [kg/m^3]
def d_v_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Cruise speed [kph]
def d_v_top : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Top speed [m/s]

/-! ## 1. Stored mass

    m_air = p_tank*V_tank/(R_s*T_0)
-/
/-- Both sides of "Stored mass" carry the same physical dimension. -/
theorem eq1_mass_dim : d_m_air = (Dim.div (Dim.mul d_p_tank d_V_tank) (Dim.mul d_R_s d_T_0)) := by decide
/-- Domain condition for `R_s * T_0`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_mass_cond1 (R_s T_0 : ℝ) (hdom : R_s * T_0 ≠ 0) : R_s * T_0 ≠ 0 := hdom

/-! ## 2. Gross isothermal expansion work

    W_gas = p_tank*V_tank*ln(p_tank/p_0)
-/
/-- Both sides of "Gross isothermal expansion work" carry the same physical dimension. -/
theorem eq2_gross_dim : d_W_gas = (Dim.mul (Dim.mul d_p_tank d_V_tank) Dim.one) := by decide
theorem eq2_gross_term1 : (Dim.div d_p_tank d_p_0) = Dim.one := by decide
/-- The denominator `p_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_gross_reg1 (p_0 : ℝ) (hp_0 : 0 < p_0) : p_0 ≠ 0 := by positivity
/-- The argument `p_tank / p_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_gross_reg2 (p_tank p_0 : ℝ) (hp_tank : 0 < p_tank) (hp_0 : 0 < p_0) : 0 < p_tank / p_0 := by positivity

/-! ## 3. Tank exergy

    X = p_tank*V_tank*ln(p_tank/p_0) - (p_tank - p_0)*V_tank
-/
/-- Both sides of "Tank exergy" carry the same physical dimension. -/
theorem eq3_exergy_dim : d_X = (Dim.mul (Dim.mul d_p_tank d_V_tank) Dim.one) := by decide
theorem eq3_exergy_term1 : (Dim.div d_p_tank d_p_0) = Dim.one := by decide
theorem eq3_exergy_term2 : d_p_tank = d_p_0 := by decide
theorem eq3_exergy_term3 : (Dim.mul (Dim.mul d_p_tank d_V_tank) Dim.one) = (Dim.mul d_p_tank d_V_tank) := by decide
/-- The denominator `p_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_exergy_reg1 (p_0 : ℝ) (hp_0 : 0 < p_0) : p_0 ≠ 0 := by positivity
/-- The argument `p_tank / p_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_exergy_reg2 (p_tank p_0 : ℝ) (hp_tank : 0 < p_tank) (hp_0 : 0 < p_0) : 0 < p_tank / p_0 := by positivity

/-! ## 4. Work at the wheels

    E_w = eta_exp*X
-/
/-- Both sides of "Work at the wheels" carry the same physical dimension. -/
theorem eq4_ew_dim : d_E_w = (Dim.mul d_eta_exp d_X) := by decide

/-! ## 5. Road load

    F_r = 0.5*rho_air*CdA*v_c^2 + C_rr*m_veh*g
-/
/-- Both sides of "Road load" carry the same physical dimension. -/
theorem eq5_road_dim : d_F_r = (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho_air) d_CdA) (Dim.pow d_v_c 2 1)) := by decide
theorem eq5_road_term1 : (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho_air) d_CdA) (Dim.pow d_v_c 2 1)) = (Dim.mul (Dim.mul d_C_rr d_m_veh) d_g) := by decide

/-! ## 6. Range

    R_range = E_w/F_r
-/
/-- Both sides of "Range" carry the same physical dimension. -/
theorem eq6_range_dim : d_R_range = (Dim.div d_E_w d_F_r) := by decide
/-- The denominator `F_r` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_range_reg1 (F_r : ℝ) (hF_r : 0 < F_r) : F_r ≠ 0 := by positivity

/-! ## 7. Top speed

    P_max = (0.5*rho_air*CdA*v_top^2 + C_rr*m_veh*g)*v_top
-/
/-- Both sides of "Top speed" carry the same physical dimension. -/
theorem eq7_top_dim : d_P_max = (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho_air) d_CdA) (Dim.pow d_v_top 2 1)) d_v_top) := by decide
theorem eq7_top_term1 : (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho_air) d_CdA) (Dim.pow d_v_top 2 1)) = (Dim.mul (Dim.mul d_C_rr d_m_veh) d_g) := by decide

/-! ## 8. External recharge energy

    E_in = X/eta_comp
-/
/-- Both sides of "External recharge energy" carry the same physical dimension. -/
theorem eq8_ein_dim : d_E_in = (Dim.div d_X d_eta_comp) := by decide
/-- The denominator `eta_comp` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_ein_reg1 (eta_comp : ℝ) (heta_comp : 0 < eta_comp) : eta_comp ≠ 0 := by positivity

/-! ## 9. Net work of an expand–recompress loop

    W_loop = eta_exp*X - X/eta_comp
-/
/-- Both sides of "Net work of an expand–recompress loop" carry the same physical dimension. -/
theorem eq9_loop_dim : d_W_loop = (Dim.mul d_eta_exp d_X) := by decide
theorem eq9_loop_term1 : (Dim.mul d_eta_exp d_X) = (Dim.div d_X d_eta_comp) := by decide
/-- The denominator `eta_comp` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_loop_reg1 (eta_comp : ℝ) (heta_comp : 0 < eta_comp) : eta_comp ≠ 0 := by positivity

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (E L M R : Prop) (h1 : ((E ∧ R) ∧ L) → (¬M)) (h2 : E) (h3 : R) (h4 : L) : ¬M := by tauto

end Bespoke
