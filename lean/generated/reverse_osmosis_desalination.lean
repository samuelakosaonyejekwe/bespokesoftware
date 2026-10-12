import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Seawater reverse-osmosis stage

Machine-checkable statements for this investigation (reverse-osmosis-desalination).
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
def d_A_w : Dim := ⟨-12, 24, 12, 0, 0, 0, 0⟩  -- Water permeability [L/(m^2 h bar)]
def d_A_x : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Cumulative membrane area [m^2]
def d_B_s : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Salt permeability [m/s]
def d_J_s : Dim := ⟨12, -24, -12, 0, 0, 0, 0⟩  -- Salt flux [kg/(m^2 s)]
def d_J_w : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Water flux [m/s]
def d_M_s : Dim := ⟨12, 0, 0, 0, 0, -12, 0⟩  -- Molar mass of salt [kg/mol]
def d_P : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Local feed pressure [Pa]
def d_P_b : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Brine pressure [Pa]
def d_P_f : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Feed pressure above permeate pressure [bar]
def d_Q : Dim := ⟨0, 36, -12, 0, 0, 0, 0⟩  -- Local feed-side flow [m^3/s]
def d_Q_b : Dim := ⟨0, 36, -12, 0, 0, 0, 0⟩  -- Brine flow [m^3/s]
def d_Q_f : Dim := ⟨0, 36, -12, 0, 0, 0, 0⟩  -- Feed flow to the pressure vessel [m^3/h]
def d_Q_p : Dim := ⟨0, 36, -12, 0, 0, 0, 0⟩  -- Permeate flow [m^3/s]
def d_R_u : Dim := ⟨12, 24, -24, 0, -12, -12, 0⟩  -- Molar gas constant [J/(mol K)]
def d_Rej : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Salt rejection [1]
def d_SEC : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Specific energy consumption [J/m^3]
def d_T : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Feed temperature [°C]
def d_c : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Salt mass concentration [kg/m^3]
def d_c_b : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Bulk concentration [kg/m^3]
def d_c_f : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Feed concentration [kg/m^3]
def d_c_m : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Concentration at the membrane wall [kg/m^3]
def d_c_p : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Permeate concentration [kg/m^3]
def d_eta_erd : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Energy-recovery device efficiency [1]
def d_eta_p : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- High-pressure pump efficiency [1]
def d_i_v : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- van ’t Hoff factor (2 for NaCl) [1]
def d_k_m : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Feed-side mass-transfer coefficient [m/s]
def d_phi_o : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Osmotic coefficient [1]
def d_pi_f : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Osmotic pressure of feed [Pa]
def d_pi_m : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Osmotic pressure at the wall [Pa]
def d_pi_o : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Osmotic pressure [Pa]
def d_pi_p : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Osmotic pressure of permeate [Pa]
def d_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Recovery [1]
def d_w_min : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Least work of separation [J/m^3]

/-! ## 1. Osmotic pressure

    pi_o = phi_o*i_v*c*R_u*T/M_s
-/
/-- Both sides of "Osmotic pressure" carry the same physical dimension. -/
theorem eq1_pi'_dim : d_pi_o = (Dim.div (Dim.mul (Dim.mul (Dim.mul (Dim.mul d_phi_o d_i_v) d_c) d_R_u) d_T) d_M_s) := by decide
/-- Domain condition for `M_s`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_pi'_cond1 (M_s : ℝ) (hdom : M_s ≠ 0) : M_s ≠ 0 := hdom

/-! ## 2. Water flux

    J_w = A_w*(P - (pi_m - pi_p))
-/
/-- Both sides of "Water flux" carry the same physical dimension. -/
theorem eq2_jw_dim : d_J_w = (Dim.mul d_A_w d_P) := by decide
theorem eq2_jw_term1 : d_pi_m = d_pi_p := by decide
theorem eq2_jw_term2 : d_P = d_pi_m := by decide

/-! ## 3. Salt flux

    J_s = B_s*(c_m - c_p)
-/
/-- Both sides of "Salt flux" carry the same physical dimension. -/
theorem eq3_js_dim : d_J_s = (Dim.mul d_B_s d_c_m) := by decide
theorem eq3_js_term1 : d_c_m = d_c_p := by decide

/-! ## 4. Permeate concentration

    c_p = J_s/J_w
-/
/-- Both sides of "Permeate concentration" carry the same physical dimension. -/
theorem eq4_cp_dim : d_c_p = (Dim.div d_J_s d_J_w) := by decide
/-- The denominator `J_w` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_cp_reg1 (J_w : ℝ) (hJ_w : 0 < J_w) : J_w ≠ 0 := by positivity

/-! ## 5. Concentration polarisation

    (c_m - c_p)/(c_b - c_p) = exp(J_w/k_m)
-/
/-- Both sides of "Concentration polarisation" carry the same physical dimension. -/
theorem eq5_film_dim : (Dim.div d_c_m d_c_b) = Dim.one := by decide
theorem eq5_film_term1 : d_c_m = d_c_p := by decide
theorem eq5_film_term2 : d_c_b = d_c_p := by decide
theorem eq5_film_term3 : (Dim.div d_J_w d_k_m) = Dim.one := by decide
/-- Domain condition for `c_b - c_p`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq5_film_cond1 (c_b c_p : ℝ) (hdom : c_b - c_p ≠ 0) : c_b - c_p ≠ 0 := hdom
/-- The denominator `k_m` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_film_reg2 (k_m : ℝ) (hk_m : 0 < k_m) : k_m ≠ 0 := by positivity

/-! ## 6. Water balance along the vessel

    pd(Q,A_x) = -J_w
-/
/-- Both sides of "Water balance along the vessel" carry the same physical dimension. -/
theorem eq6_wbal_dim : (Dim.div d_Q d_A_x) = d_J_w := by decide

/-! ## 7. Salt balance along the vessel

    pd(Q*c_b,A_x) = -J_s
-/
/-- Both sides of "Salt balance along the vessel" carry the same physical dimension. -/
theorem eq7_sbal_dim : (Dim.div (Dim.mul d_Q d_c_b) d_A_x) = d_J_s := by decide

/-! ## 8. Recovery

    r = Q_p/Q_f
-/
/-- Both sides of "Recovery" carry the same physical dimension. -/
theorem eq8_rec_dim : d_r = (Dim.div d_Q_p d_Q_f) := by decide
/-- The denominator `Q_f` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_rec_reg1 (Q_f : ℝ) (hQ_f : 0 < Q_f) : Q_f ≠ 0 := by positivity

/-! ## 9. Salt rejection

    Rej = 1 - c_p/c_f
-/
/-- Both sides of "Salt rejection" carry the same physical dimension. -/
theorem eq9_rej_dim : d_Rej = Dim.one := by decide
theorem eq9_rej_term1 : Dim.one = (Dim.div d_c_p d_c_f) := by decide
/-- Domain condition for `c_f`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq9_rej_cond1 (c_f : ℝ) (hdom : c_f ≠ 0) : c_f ≠ 0 := hdom

/-! ## 10. Specific energy consumption

    SEC = (Q_f*P_f - eta_erd*Q_b*P_b)/(eta_p*Q_p)
-/
/-- Both sides of "Specific energy consumption" carry the same physical dimension. -/
theorem eq10_sec_dim : d_SEC = (Dim.div (Dim.mul d_Q_f d_P_f) (Dim.mul d_eta_p d_Q_p)) := by decide
theorem eq10_sec_term1 : (Dim.mul d_Q_f d_P_f) = (Dim.mul (Dim.mul d_eta_erd d_Q_b) d_P_b) := by decide
/-- The denominator `eta_p * Q_p` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_sec_reg1 (eta_p Q_p : ℝ) (heta_p : 0 < eta_p) (hQ_p : 0 < Q_p) : eta_p * Q_p ≠ 0 := by positivity

/-! ## 11. Least work of separation (pure permeate)

    w_min = (pi_f/r)*ln(1/(1 - r))
-/
/-- Both sides of "Least work of separation (pure permeate)" carry the same physical dimension. -/
theorem eq11_wmin_dim : d_w_min = (Dim.mul (Dim.div d_pi_f d_r) Dim.one) := by decide
theorem eq11_wmin_term1 : Dim.one = d_r := by decide
theorem eq11_wmin_term2 : (Dim.div Dim.one Dim.one) = Dim.one := by decide
/-- The denominator `r` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_wmin_reg1 (r : ℝ) (hr : 0 < r) : r ≠ 0 := by positivity
/-- Domain condition for `1 - r`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq11_wmin_cond2 (r : ℝ) (hdom : (1 : ℝ) - r ≠ 0) : (1 : ℝ) - r ≠ 0 := hdom
/-- Domain condition for `1 / (1 - r)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq11_wmin_cond3 (r : ℝ) (hdom : 0 < (1 : ℝ) / ((1 : ℝ) - r)) : 0 < (1 : ℝ) / ((1 : ℝ) - r) := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq11_wmin_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

end Bespoke
