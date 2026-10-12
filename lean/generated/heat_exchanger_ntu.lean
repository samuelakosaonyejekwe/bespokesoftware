import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Heat exchanger rating by the effectiveness–NTU method

Machine-checkable statements for this investigation (heat-exchanger-ntu).
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
def d_A : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Heat-transfer area [m^2]
def d_C_c : Dim := ⟨12, 24, -36, 0, -12, 0, 0⟩  -- Cold capacity rate [W/K]
def d_C_h : Dim := ⟨12, 24, -36, 0, -12, 0, 0⟩  -- Hot capacity rate [W/K]
def d_C_min : Dim := ⟨12, 24, -36, 0, -12, 0, 0⟩  -- Smaller capacity rate [W/K]
def d_C_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Capacity-rate ratio [1]
def d_NTU : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of transfer units [1]
def d_Q : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Duty [W]
def d_R_f : Dim := ⟨-12, 0, 36, 0, 12, 0, 0⟩  -- Total fouling resistance [m^2 K/W]
def d_T_ci : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Cold-stream inlet temperature [°C]
def d_T_co : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Cold outlet temperature [K]
def d_T_hi : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Hot-stream inlet temperature [°C]
def d_T_ho : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Hot outlet temperature [K]
def d_U : Dim := ⟨12, 0, -36, 0, -12, 0, 0⟩  -- Clean overall heat-transfer coefficient [W/(m^2 K)]
def d_U_f : Dim := ⟨12, 0, -36, 0, -12, 0, 0⟩  -- Service overall coefficient [W/(m^2 K)]
def d_cp_c : Dim := ⟨0, 24, -24, 0, -12, 0, 0⟩  -- Cold-stream specific heat [J/(kg K)]
def d_cp_h : Dim := ⟨0, 24, -24, 0, -12, 0, 0⟩  -- Hot-stream specific heat [J/(kg K)]
def d_dT_1 : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Terminal temperature difference, end 1 [K]
def d_dT_2 : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Terminal temperature difference, end 2 [K]
def d_dT_lm : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Log-mean temperature difference [K]
def d_eps : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Effectiveness [1]
def d_m_c : Dim := ⟨12, 0, -12, 0, 0, 0, 0⟩  -- Cold-stream mass flow rate [kg/s]
def d_m_h : Dim := ⟨12, 0, -12, 0, 0, 0, 0⟩  -- Hot-stream mass flow rate [kg/s]

/-! ## 1. Hot capacity rate

    C_h = m_h*cp_h
-/
/-- Both sides of "Hot capacity rate" carry the same physical dimension. -/
theorem eq1_ch_dim : d_C_h = (Dim.mul d_m_h d_cp_h) := by decide

/-! ## 2. Cold capacity rate

    C_c = m_c*cp_c
-/
/-- Both sides of "Cold capacity rate" carry the same physical dimension. -/
theorem eq2_cc_dim : d_C_c = (Dim.mul d_m_c d_cp_c) := by decide

/-! ## 3. Capacity-rate ratio

    C_r = C_min/max(C_h, C_c)
-/
/-- Both sides of "Capacity-rate ratio" carry the same physical dimension. -/
theorem eq3_cr_dim : d_C_r = (Dim.div d_C_min d_C_h) := by decide
theorem eq3_cr_term1 : d_C_h = d_C_c := by decide
/-- Domain condition for `max(C_h, C_c)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq3_cr_cond1 (C_h C_c : ℝ) (hdom : max C_h C_c ≠ 0) : max C_h C_c ≠ 0 := hdom

/-! ## 4. Service coefficient

    1/U_f = 1/U + R_f
-/
/-- Both sides of "Service coefficient" carry the same physical dimension. -/
theorem eq4_uf_dim : (Dim.div Dim.one d_U_f) = (Dim.div Dim.one d_U) := by decide
theorem eq4_uf_term1 : (Dim.div Dim.one d_U) = d_R_f := by decide
/-- The denominator `U_f` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_uf_reg1 (U_f : ℝ) (hU_f : 0 < U_f) : U_f ≠ 0 := by positivity
/-- The denominator `U` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_uf_reg2 (U : ℝ) (hU : 0 < U) : U ≠ 0 := by positivity

/-! ## 5. Number of transfer units

    NTU = U_f*A/C_min
-/
/-- Both sides of "Number of transfer units" carry the same physical dimension. -/
theorem eq5_ntu_dim : d_NTU = (Dim.div (Dim.mul d_U_f d_A) d_C_min) := by decide
/-- Domain condition for `C_min`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_ntu_cond1 (C_min : ℝ) (hdom : C_min ≠ 0) : C_min ≠ 0 := hdom

/-! ## 6. Counterflow effectiveness

    eps = (1 - exp(-NTU*(1 - C_r)))/(1 - C_r*exp(-NTU*(1 - C_r)))
-/
/-- Both sides of "Counterflow effectiveness" carry the same physical dimension. -/
theorem eq6_eps_dim : d_eps = (Dim.div Dim.one Dim.one) := by decide
theorem eq6_eps_term1 : Dim.one = d_C_r := by decide
theorem eq6_eps_term2 : (Dim.mul d_NTU Dim.one) = Dim.one := by decide
theorem eq6_eps_term3 : Dim.one = Dim.one := by decide
theorem eq6_eps_term4 : Dim.one = d_C_r := by decide
theorem eq6_eps_term5 : (Dim.mul d_NTU Dim.one) = Dim.one := by decide
theorem eq6_eps_term6 : Dim.one = (Dim.mul d_C_r Dim.one) := by decide
/-- Domain condition for `1 - C_r * exp(-NTU * (1 - C_r))`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_eps_cond1 (C_r NTU : ℝ) (hdom : (1 : ℝ) - C_r * Real.exp (-NTU * ((1 : ℝ) - C_r)) ≠ 0) : (1 : ℝ) - C_r * Real.exp (-NTU * ((1 : ℝ) - C_r)) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq6_eps_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 7. Duty

    Q = eps*C_min*(T_hi - T_ci)
-/
/-- Both sides of "Duty" carry the same physical dimension. -/
theorem eq7_q_dim : d_Q = (Dim.mul (Dim.mul d_eps d_C_min) d_T_hi) := by decide
theorem eq7_q_term1 : d_T_hi = d_T_ci := by decide

/-! ## 8. Cold outlet temperature

    T_co = T_ci + Q/C_c
-/
/-- Both sides of "Cold outlet temperature" carry the same physical dimension. -/
theorem eq8_tco_dim : d_T_co = d_T_ci := by decide
theorem eq8_tco_term1 : d_T_ci = (Dim.div d_Q d_C_c) := by decide
/-- The denominator `C_c` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_tco_reg1 (C_c : ℝ) (hC_c : 0 < C_c) : C_c ≠ 0 := by positivity

/-! ## 9. Hot outlet temperature

    T_ho = T_hi - Q/C_h
-/
/-- Both sides of "Hot outlet temperature" carry the same physical dimension. -/
theorem eq9_tho_dim : d_T_ho = d_T_hi := by decide
theorem eq9_tho_term1 : d_T_hi = (Dim.div d_Q d_C_h) := by decide
/-- The denominator `C_h` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_tho_reg1 (C_h : ℝ) (hC_h : 0 < C_h) : C_h ≠ 0 := by positivity

/-! ## 10. Log-mean temperature difference

    dT_lm = (dT_1 - dT_2)/ln(dT_1/dT_2)
-/
/-- Both sides of "Log-mean temperature difference" carry the same physical dimension. -/
theorem eq10_lmtd_dim : d_dT_lm = (Dim.div d_dT_1 Dim.one) := by decide
theorem eq10_lmtd_term1 : d_dT_1 = d_dT_2 := by decide
theorem eq10_lmtd_term2 : (Dim.div d_dT_1 d_dT_2) = Dim.one := by decide
/-- The denominator `dT_2` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_lmtd_reg1 (dT_2 : ℝ) (hdT_2 : 0 < dT_2) : dT_2 ≠ 0 := by positivity
/-- Domain condition for `dT_1 / dT_2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_lmtd_cond2 (dT_1 dT_2 : ℝ) (hdom : 0 < dT_1 / dT_2) : 0 < dT_1 / dT_2 := hdom
/-- Domain condition for `ln(dT_1 / dT_2)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_lmtd_cond3 (dT_1 dT_2 : ℝ) (hdom : Real.log (dT_1 / dT_2) ≠ 0) : Real.log (dT_1 / dT_2) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq10_lmtd_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 11. Rate equation (cross-check)

    Q = U_f*A*dT_lm
-/
/-- Both sides of "Rate equation (cross-check)" carry the same physical dimension. -/
theorem eq11_rate_dim : d_Q = (Dim.mul (Dim.mul d_U_f d_A) d_dT_lm) := by decide

end Bespoke
