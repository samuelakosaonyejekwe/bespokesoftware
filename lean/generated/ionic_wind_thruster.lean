import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Ionic-wind (electrohydrodynamic) thruster and hover feasibility

Machine-checkable statements for this investigation (ionic-wind-thruster).
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
def d_E : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Electric field in the drift region [V/m]
def d_E_bd : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Mean field at spark-over [MV/m]
def d_J : Dim := ⟨0, -24, 0, 12, 0, 0, 0⟩  -- Current density [A/m^2]
def d_N_s : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of sectors in the annular array [1]
def d_P : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Total electrical power [W]
def d_T : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Total thrust [N]
def d_TWR : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Thrust-to-weight ratio [1]
def d_T_A : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Electrostatic thrust per unit area [N/m^2]
def d_T_max : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Thrust density at the spark-over field [N/m^2]
def d_T_n : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Net thrust per unit area [N/m^2]
def d_V : Dim := ⟨12, 24, -36, -12, 0, 0, 0⟩  -- Applied voltage [kV]
def d_W : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Total weight [N]
def d_b_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Emitter span of one sector [m]
def d_d_gap : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Emitter-to-collector gap [mm]
def d_eps_0 : Dim := ⟨-12, -36, 48, 24, 0, 0, 0⟩  -- Vacuum permittivity [F/m]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_m_0 : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Fixed mass: airframe, payload and energy store [kg]
def d_m_A : Dim := ⟨12, -24, 0, 0, 0, 0, 0⟩  -- Electrode structure mass per unit drift area [kg/m^2]
def d_mu_e : Dim := ⟨-12, 0, 24, 12, 0, 0, 0⟩  -- Effective ion mobility [m^2/(V s)]
def d_mu_i : Dim := ⟨-12, 0, 24, 12, 0, 0, 0⟩  -- Ion mobility at sea-level density [cm^2/(V s)]
def d_rho_air : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Air density [kg/m^3]
def d_rho_q : Dim := ⟨0, -36, 12, 12, 0, 0, 0⟩  -- Ion charge density [C/m^3]
def d_sp_psu : Dim := ⟨0, 24, -36, 0, 0, 0, 0⟩  -- Specific power of the high-voltage supply [kW/kg]
def d_theta_TP : Dim := ⟨0, -12, 12, 0, 0, 0, 0⟩  -- Thrust-to-power ratio [N/W]
def d_u_d : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Induced air speed at the electrode plane [m/s]
def d_w_c : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Width of the drift region (collector chord) [mm]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance from the emitter [m]

/-! ## 1. Ion mobility

    mu_e = mu_i
-/
/-- Both sides of "Ion mobility" carry the same physical dimension. -/
theorem eq1_mob_dim : d_mu_e = d_mu_i := by decide

/-! ## 2. Gauss's law in the drift region

    eps_0*pd(E,x) = rho_q
-/
/-- Both sides of "Gauss's law in the drift region" carry the same physical dimension. -/
theorem eq2_gauss_dim : (Dim.mul d_eps_0 (Dim.div d_E d_x)) = d_rho_q := by decide

/-! ## 3. Ion drift current

    J = rho_q*mu_e*E
-/
/-- Both sides of "Ion drift current" carry the same physical dimension. -/
theorem eq3_drift_dim : d_J = (Dim.mul (Dim.mul d_rho_q d_mu_e) d_E) := by decide

/-! ## 4. Space-charge-limited current density

    J = 9/8*eps_0*mu_e*V^2/d_gap^3
-/
/-- Both sides of "Space-charge-limited current density" carry the same physical dimension. -/
theorem eq4_mg_dim : d_J = (Dim.div (Dim.mul (Dim.mul (Dim.mul (Dim.div Dim.one Dim.one) d_eps_0) d_mu_e) (Dim.pow d_V 2 1)) (Dim.pow d_d_gap 3 1)) := by decide
/-- The denominator `8` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_mg_reg1  : (8 : ℝ) ≠ 0 := by positivity
/-- The denominator `d_gap^3` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_mg_reg2 (d_gap : ℝ) (hd_gap : 0 < d_gap) : d_gap ^ 3 ≠ 0 := by positivity

/-! ## 5. Coulomb body force on the air

    T_A = int(rho_q*E, x)
-/
/-- Both sides of "Coulomb body force on the air" carry the same physical dimension. -/
theorem eq5_force_dim : d_T_A = (Dim.mul (Dim.mul d_rho_q d_E) d_x) := by decide

/-! ## 6. Thrust per unit area

    T_A = J*d_gap/mu_e
-/
/-- Both sides of "Thrust per unit area" carry the same physical dimension. -/
theorem eq6_thr_dim : d_T_A = (Dim.div (Dim.mul d_J d_d_gap) d_mu_e) := by decide
/-- The denominator `mu_e` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_thr_reg1 (mu_e : ℝ) (hmu_e : 0 < mu_e) : mu_e ≠ 0 := by positivity

/-! ## 7. Thrust-to-power ratio

    theta_TP = d_gap/(mu_e*V)
-/
/-- Both sides of "Thrust-to-power ratio" carry the same physical dimension. -/
theorem eq7_tp_dim : d_theta_TP = (Dim.div d_d_gap (Dim.mul d_mu_e d_V)) := by decide
/-- The denominator `mu_e * V` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_tp_reg1 (mu_e V : ℝ) (hmu_e : 0 < mu_e) (hV : 0 < V) : mu_e * V ≠ 0 := by positivity

/-! ## 8. Net thrust per unit area

    T_n = T_A
-/
/-- Both sides of "Net thrust per unit area" carry the same physical dimension. -/
theorem eq8_net_dim : d_T_n = d_T_A := by decide

/-! ## 9. Induced air speed at the electrode plane

    u_d = sqrt(T_n/(2*rho_air))
-/
/-- Both sides of "Induced air speed at the electrode plane" carry the same physical dimension. -/
theorem eq9_ud_dim : d_u_d = (Dim.pow (Dim.div d_T_n (Dim.mul Dim.one d_rho_air)) 1 2) := by decide
/-- The denominator `2 * rho_air` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_ud_reg1 (rho_air : ℝ) (hrho_air : 0 < rho_air) : (2 : ℝ) * rho_air ≠ 0 := by positivity
/-- The argument `T_n / (2 * rho_air)` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_ud_reg2 (T_n rho_air : ℝ) (hT_n : 0 < T_n) (hrho_air : 0 < rho_air) : 0 ≤ T_n / ((2 : ℝ) * rho_air) := by positivity

/-! ## 10. Total thrust of the array

    T = T_n*N_s*b_s*w_c
-/
/-- Both sides of "Total thrust of the array" carry the same physical dimension. -/
theorem eq10_tot_dim : d_T = (Dim.mul (Dim.mul (Dim.mul d_T_n d_N_s) d_b_s) d_w_c) := by decide

/-! ## 11. Total electrical power

    P = J*V*N_s*b_s*w_c
-/
/-- Both sides of "Total electrical power" carry the same physical dimension. -/
theorem eq11_pow_dim : d_P = (Dim.mul (Dim.mul (Dim.mul (Dim.mul d_J d_V) d_N_s) d_b_s) d_w_c) := by decide

/-! ## 12. Total weight with on-board supply

    W = g*(m_0 + m_A*N_s*b_s*w_c + P/sp_psu)
-/
/-- Both sides of "Total weight with on-board supply" carry the same physical dimension. -/
theorem eq12_wt_dim : d_W = (Dim.mul d_g d_m_0) := by decide
theorem eq12_wt_term1 : d_m_0 = (Dim.mul (Dim.mul (Dim.mul d_m_A d_N_s) d_b_s) d_w_c) := by decide
theorem eq12_wt_term2 : d_m_0 = (Dim.div d_P d_sp_psu) := by decide
/-- The denominator `sp_psu` stays away from its singular set whenever the quantities are positive. -/
theorem eq12_wt_reg1 (sp_psu : ℝ) (hsp_psu : 0 < sp_psu) : sp_psu ≠ 0 := by positivity

/-! ## 13. Thrust-to-weight ratio

    TWR = T/W
-/
/-- Both sides of "Thrust-to-weight ratio" carry the same physical dimension. -/
theorem eq13_twr_dim : d_TWR = (Dim.div d_T d_W) := by decide
/-- The denominator `W` stays away from its singular set whenever the quantities are positive. -/
theorem eq13_twr_reg1 (W : ℝ) (hW : 0 < W) : W ≠ 0 := by positivity

/-! ## 14. Thrust density at the spark-over field

    T_max = 9/8*eps_0*E_bd^2
-/
/-- Both sides of "Thrust density at the spark-over field" carry the same physical dimension. -/
theorem eq14_lim_dim : d_T_max = (Dim.mul (Dim.mul (Dim.div Dim.one Dim.one) d_eps_0) (Dim.pow d_E_bd 2 1)) := by decide
/-- The denominator `8` stays away from its singular set whenever the quantities are positive. -/
theorem eq14_lim_reg1  : (8 : ℝ) ≠ 0 := by positivity

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (D H M W : Prop) (h1 : H → W) (h2 : W → (D ∧ M)) : H → M := by tauto

end Bespoke
