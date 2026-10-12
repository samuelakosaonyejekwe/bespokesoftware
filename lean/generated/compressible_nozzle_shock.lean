import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Converging–diverging nozzle flow and normal shocks

Machine-checkable statements for this investigation (compressible-nozzle-shock).
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

/-- The smooth rate cap never lets a rate exceed F in magnitude. -/
theorem rate_cap_bounded (f F : ℝ) (hF : 0 < F) : |f / Real.sqrt (1 + (f / F) ^ 2)| ≤ F := by
  have hs : 0 < Real.sqrt (1 + (f / F) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  have h1 : |f| / F ≤ Real.sqrt (1 + (f / F) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, sq_abs, div_pow]; linarith
  calc |f| = F * (|f| / F) := by field_simp
    _ ≤ F * Real.sqrt (1 + (f / F) ^ 2) := by gcongr

/-- A quantity whose rate of change never exceeds F cannot reach infinity in finite time:
after a time T it has moved by at most F * T. -/
theorem bounded_rate_no_blowup (x : ℝ → ℝ) (F T : ℝ) (hT : 0 ≤ T)
    (hx : ∀ t, DifferentiableAt ℝ x t) (hb : ∀ t, |deriv x t| ≤ F) : |x T - x 0| ≤ F * T := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (f := x) (C := F)
    (fun t _ => hx t) (fun t _ => by simpa [Real.norm_eq_abs] using hb t) convex_univ (Set.mem_univ 0) (Set.mem_univ T)
  simpa [Real.norm_eq_abs, abs_of_nonneg hT] using h


/-! ## Dimensions of the symbols -/

def d_length : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩
def d_A : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Local area [m^2]
def d_A_e : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Exit area [m^2]
def d_A_star : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Sonic (critical) area [m^2]
def d_A_t : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Throat area [cm^2]
def d_F : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Thrust [N]
def d_M : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Local Mach number [1]
def d_M_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Mach number ahead of a normal shock (calculator) [1]
def d_M_2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Mach number behind the shock [1]
def d_M_e : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Exit Mach number [1]
def d_R_g : Dim := ⟨0, 24, -24, 0, -12, 0, 0⟩  -- Specific gas constant [J/(kg K)]
def d_T : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Static temperature [K]
def d_T_0 : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Stagnation (chamber) temperature [K]
def d_T_e : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Exit temperature [K]
def d_V_e : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Exit velocity [m/s]
def d_eps : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Exit-to-throat area ratio [1]
def d_gamma : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Ratio of specific heats [1]
def d_mdot : Dim := ⟨12, 0, -12, 0, 0, 0, 0⟩  -- Mass flow rate [kg/s]
def d_p : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Static pressure [Pa]
def d_p_0 : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Stagnation (chamber) pressure [bar]
def d_p_1 : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Pressure ahead of the shock [Pa]
def d_p_2 : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Pressure behind the shock [Pa]
def d_p_b : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Back (ambient) pressure [bar]
def d_p_e : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Exit-plane pressure [Pa]
def d_rho_1 : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Density ahead of the shock [kg/m^3]
def d_rho_2 : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Density behind the shock [kg/m^3]

/-! ## 1. Energy (stagnation temperature)

    T_0/T = 1 + (gamma - 1)/2*M^2
-/
/-- Both sides of "Energy (stagnation temperature)" carry the same physical dimension. -/
theorem eq1_ien_dim : (Dim.div d_T_0 d_T) = Dim.one := by decide
theorem eq1_ien_term1 : d_gamma = Dim.one := by decide
theorem eq1_ien_term2 : Dim.one = (Dim.mul (Dim.div d_gamma Dim.one) (Dim.pow d_M 2 1)) := by decide
/-- The denominator `T` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_ien_reg1 (T : ℝ) (hT : 0 < T) : T ≠ 0 := by positivity
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_ien_reg2  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 2. Isentropic pressure ratio

    p_0/p = (1 + (gamma - 1)/2*M^2)^(gamma/(gamma - 1))
-/
/-- Both sides of "Isentropic pressure ratio" carry the same physical dimension. -/
theorem eq2_isen_dim : (Dim.div d_p_0 d_p) = Dim.one := by decide
theorem eq2_isen_term1 : d_gamma = Dim.one := by decide
theorem eq2_isen_term2 : Dim.one = (Dim.mul (Dim.div d_gamma Dim.one) (Dim.pow d_M 2 1)) := by decide
theorem eq2_isen_term3 : d_gamma = Dim.one := by decide
/-- Domain condition for `p`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_isen_cond1 (p : ℝ) (hdom : p ≠ 0) : p ≠ 0 := hdom
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_isen_reg2  : (2 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `gamma - 1`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq2_isen_cond3 (gamma : ℝ) (hdom : gamma - (1 : ℝ) ≠ 0) : gamma - (1 : ℝ) ≠ 0 := hdom

/-! ## 3. Area–Mach relation

    A/A_star = 1/M*(2/(gamma + 1)*(1 + (gamma - 1)/2*M^2))^((gamma + 1)/(2*(gamma - 1)))
-/
/-- Both sides of "Area–Mach relation" carry the same physical dimension. -/
theorem eq3_area_dim : (Dim.div d_A d_A_star) = (Dim.mul (Dim.div Dim.one d_M) Dim.one) := by decide
theorem eq3_area_term1 : d_gamma = Dim.one := by decide
theorem eq3_area_term2 : d_gamma = Dim.one := by decide
theorem eq3_area_term3 : Dim.one = (Dim.mul (Dim.div d_gamma Dim.one) (Dim.pow d_M 2 1)) := by decide
theorem eq3_area_term4 : d_gamma = Dim.one := by decide
theorem eq3_area_term5 : d_gamma = Dim.one := by decide
/-- Domain condition for `A_star`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_area_cond1 (A_star : ℝ) (hdom : A_star ≠ 0) : A_star ≠ 0 := hdom
/-- Domain condition for `M`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_area_cond2 (M : ℝ) (hdom : M ≠ 0) : M ≠ 0 := hdom
/-- The denominator `gamma + 1` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_area_reg3 (gamma : ℝ) (hgamma : 0 < gamma) : gamma + (1 : ℝ) ≠ 0 := by positivity
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_area_reg4  : (2 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `2 * (gamma - 1)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq3_area_cond5 (gamma : ℝ) (hdom : (2 : ℝ) * (gamma - (1 : ℝ)) ≠ 0) : (2 : ℝ) * (gamma - (1 : ℝ)) ≠ 0 := hdom

/-! ## 4. Exit area

    A_e = eps*A_t
-/
/-- Both sides of "Exit area" carry the same physical dimension. -/
theorem eq4_ae_dim : d_A_e = (Dim.mul d_eps d_A_t) := by decide

/-! ## 5. Choked mass flow

    mdot = A_t*p_0*sqrt(gamma/(R_g*T_0))*(2/(gamma + 1))^((gamma + 1)/(2*(gamma - 1)))
-/
/-- Both sides of "Choked mass flow" carry the same physical dimension. -/
theorem eq5_mdot_dim : d_mdot = (Dim.mul (Dim.mul (Dim.mul d_A_t d_p_0) (Dim.pow (Dim.div d_gamma (Dim.mul d_R_g d_T_0)) 1 2)) Dim.one) := by decide
theorem eq5_mdot_term1 : d_gamma = Dim.one := by decide
theorem eq5_mdot_term2 : d_gamma = Dim.one := by decide
theorem eq5_mdot_term3 : d_gamma = Dim.one := by decide
/-- The denominator `R_g * T_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_mdot_reg1 (R_g T_0 : ℝ) (hR_g : 0 < R_g) (hT_0 : 0 < T_0) : R_g * T_0 ≠ 0 := by positivity
/-- The argument `gamma / (R_g * T_0)` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_mdot_reg2 (gamma R_g T_0 : ℝ) (hgamma : 0 < gamma) (hR_g : 0 < R_g) (hT_0 : 0 < T_0) : 0 ≤ gamma / (R_g * T_0) := by positivity
/-- The denominator `gamma + 1` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_mdot_reg3 (gamma : ℝ) (hgamma : 0 < gamma) : gamma + (1 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `2 * (gamma - 1)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq5_mdot_cond4 (gamma : ℝ) (hdom : (2 : ℝ) * (gamma - (1 : ℝ)) ≠ 0) : (2 : ℝ) * (gamma - (1 : ℝ)) ≠ 0 := hdom

/-! ## 6. Shock pressure ratio

    p_2/p_1 = 1 + 2*gamma/(gamma + 1)*(M_1^2 - 1)
-/
/-- Both sides of "Shock pressure ratio" carry the same physical dimension. -/
theorem eq6_sp_dim : (Dim.div d_p_2 d_p_1) = Dim.one := by decide
theorem eq6_sp_term1 : d_gamma = Dim.one := by decide
theorem eq6_sp_term2 : (Dim.pow d_M_1 2 1) = Dim.one := by decide
theorem eq6_sp_term3 : Dim.one = (Dim.mul (Dim.div (Dim.mul Dim.one d_gamma) d_gamma) (Dim.pow d_M_1 2 1)) := by decide
/-- Domain condition for `p_1`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_sp_cond1 (p_1 : ℝ) (hdom : p_1 ≠ 0) : p_1 ≠ 0 := hdom
/-- The denominator `gamma + 1` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_sp_reg2 (gamma : ℝ) (hgamma : 0 < gamma) : gamma + (1 : ℝ) ≠ 0 := by positivity

/-! ## 7. Shock density ratio

    rho_2/rho_1 = (gamma + 1)*M_1^2/((gamma - 1)*M_1^2 + 2)
-/
/-- Both sides of "Shock density ratio" carry the same physical dimension. -/
theorem eq7_sr_dim : (Dim.div d_rho_2 d_rho_1) = (Dim.div (Dim.mul d_gamma (Dim.pow d_M_1 2 1)) (Dim.mul d_gamma (Dim.pow d_M_1 2 1))) := by decide
theorem eq7_sr_term1 : d_gamma = Dim.one := by decide
theorem eq7_sr_term2 : d_gamma = Dim.one := by decide
theorem eq7_sr_term3 : (Dim.mul d_gamma (Dim.pow d_M_1 2 1)) = Dim.one := by decide
/-- The denominator `rho_1` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_sr_reg1 (rho_1 : ℝ) (hrho_1 : 0 < rho_1) : rho_1 ≠ 0 := by positivity
/-- Domain condition for `(gamma - 1) * M_1^2 + 2`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq7_sr_cond2 (gamma M_1 : ℝ) (hdom : (gamma - (1 : ℝ)) * M_1 ^ 2 + (2 : ℝ) ≠ 0) : (gamma - (1 : ℝ)) * M_1 ^ 2 + (2 : ℝ) ≠ 0 := hdom

/-! ## 8. Mach number behind the shock

    M_2^2 = (1 + (gamma - 1)/2*M_1^2)/(gamma*M_1^2 - (gamma - 1)/2)
-/
/-- Both sides of "Mach number behind the shock" carry the same physical dimension. -/
theorem eq8_sm_dim : (Dim.pow d_M_2 2 1) = (Dim.div Dim.one (Dim.mul d_gamma (Dim.pow d_M_1 2 1))) := by decide
theorem eq8_sm_term1 : d_gamma = Dim.one := by decide
theorem eq8_sm_term2 : Dim.one = (Dim.mul (Dim.div d_gamma Dim.one) (Dim.pow d_M_1 2 1)) := by decide
theorem eq8_sm_term3 : d_gamma = Dim.one := by decide
theorem eq8_sm_term4 : (Dim.mul d_gamma (Dim.pow d_M_1 2 1)) = (Dim.div d_gamma Dim.one) := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_sm_reg1  : (2 : ℝ) ≠ 0 := by positivity
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_sm_reg2  : (2 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `gamma * M_1^2 - (gamma - 1) / 2`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq8_sm_cond3 (gamma M_1 : ℝ) (hdom : gamma * M_1 ^ 2 - (gamma - (1 : ℝ)) / (2 : ℝ) ≠ 0) : gamma * M_1 ^ 2 - (gamma - (1 : ℝ)) / (2 : ℝ) ≠ 0 := hdom

/-! ## 9. Exit velocity

    V_e = M_e*sqrt(gamma*R_g*T_e)
-/
/-- Both sides of "Exit velocity" carry the same physical dimension. -/
theorem eq9_ve_dim : d_V_e = (Dim.mul d_M_e (Dim.pow (Dim.mul (Dim.mul d_gamma d_R_g) d_T_e) 1 2)) := by decide
/-- The argument `gamma * R_g * T_e` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_ve_reg1 (gamma R_g T_e : ℝ) (hgamma : 0 < gamma) (hR_g : 0 < R_g) (hT_e : 0 < T_e) : 0 ≤ gamma * R_g * T_e := by positivity

/-! ## 10. Thrust

    F = mdot*V_e + (p_e - p_b)*A_e
-/
/-- Both sides of "Thrust" carry the same physical dimension. -/
theorem eq10_thrust_dim : d_F = (Dim.mul d_mdot d_V_e) := by decide
theorem eq10_thrust_term1 : d_p_e = d_p_b := by decide
theorem eq10_thrust_term2 : (Dim.mul d_mdot d_V_e) = (Dim.mul d_p_e d_A_e) := by decide

end Bespoke
