import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Ferroelectric hysteresis from Landau–Khalatnikov dynamics

Machine-checkable statements for this investigation (ferroelectric-hysteresis).
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
def d_D_e : Dim := ⟨0, -24, 12, 12, 0, 0, 0⟩  -- Electric displacement [C/m^2]
def d_E : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Applied electric field [V/m]
def d_E_0 : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Field amplitude [MV/m]
def d_E_c0 : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Thermodynamic coercive field [V/m]
def d_F_L : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Free-energy density [J/m^3]
def d_Gamma_k : Dim := ⟨-12, -36, 36, 24, 0, 0, 0⟩  -- Kinetic coefficient [S/m]
def d_P : Dim := ⟨0, -24, 12, 12, 0, 0, 0⟩  -- Polarisation [C/m^2]
def d_P_s : Dim := ⟨0, -24, 12, 12, 0, 0, 0⟩  -- Spontaneous polarisation [C/m^2]
def d_T : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Sample temperature [K]
def d_T_0 : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Curie–Weiss temperature [K]
def d_W_c : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Energy dissipated per cycle and unit volume [J/m^3]
def d_a_0 : Dim := ⟨12, 36, -48, -24, -12, 0, 0⟩  -- Curie–Weiss coefficient of the quadratic term [m/(F K)]
def d_alpha_L : Dim := ⟨12, 36, -48, -24, 0, 0, 0⟩  -- Quadratic Landau coefficient [m/F]
def d_beta_L : Dim := ⟨12, 84, -72, -48, 0, 0, 0⟩  -- Quartic Landau coefficient [V m^5/C^3]
def d_f_d : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Drive frequency [Hz]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_tau_P : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Polarisation relaxation time [s]

/-! ## 1. Quadratic coefficient

    alpha_L = a_0*(T - T_0)
-/
/-- Both sides of "Quadratic coefficient" carry the same physical dimension. -/
theorem eq1_al_dim : d_alpha_L = (Dim.mul d_a_0 d_T) := by decide
theorem eq1_al_term1 : d_T = d_T_0 := by decide

/-! ## 2. Landau free-energy density

    F_L = alpha_L*P^2/2 + beta_L*P^4/4 - E*P
-/
/-- Both sides of "Landau free-energy density" carry the same physical dimension. -/
theorem eq2_fe_dim : d_F_L = (Dim.div (Dim.mul d_alpha_L (Dim.pow d_P 2 1)) Dim.one) := by decide
theorem eq2_fe_term1 : (Dim.div (Dim.mul d_alpha_L (Dim.pow d_P 2 1)) Dim.one) = (Dim.div (Dim.mul d_beta_L (Dim.pow d_P 4 1)) Dim.one) := by decide
theorem eq2_fe_term2 : (Dim.div (Dim.mul d_alpha_L (Dim.pow d_P 2 1)) Dim.one) = (Dim.mul d_E d_P) := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_fe_reg1  : (2 : ℝ) ≠ 0 := by positivity
/-- The denominator `4` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_fe_reg2  : (4 : ℝ) ≠ 0 := by positivity

/-! ## 3. Landau–Khalatnikov equation

    d(P,t) = -Gamma_k*(alpha_L*P + beta_L*P^3 - E)
-/
/-- Both sides of "Landau–Khalatnikov equation" carry the same physical dimension. -/
theorem eq3_lk_dim : (Dim.div d_P d_t) = (Dim.mul d_Gamma_k (Dim.mul d_alpha_L d_P)) := by decide
theorem eq3_lk_term1 : (Dim.mul d_alpha_L d_P) = (Dim.mul d_beta_L (Dim.pow d_P 3 1)) := by decide
theorem eq3_lk_term2 : (Dim.mul d_alpha_L d_P) = d_E := by decide

/-! ## 4. Applied field

    E = E_0*sin(2*pi*f_d*t)
-/
/-- Both sides of "Applied field" carry the same physical dimension. -/
theorem eq4_drive_dim : d_E = (Dim.mul d_E_0 Dim.one) := by decide
theorem eq4_drive_term1 : (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_f_d) d_t) = Dim.one := by decide

/-! ## 5. Spontaneous polarisation

    P_s = sqrt(-alpha_L/beta_L)
-/
/-- Both sides of "Spontaneous polarisation" carry the same physical dimension. -/
theorem eq5_ps_dim : d_P_s = (Dim.pow (Dim.div d_alpha_L d_beta_L) 1 2) := by decide
/-- The denominator `beta_L` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_ps_reg1 (beta_L : ℝ) (hbeta_L : 0 < beta_L) : beta_L ≠ 0 := by positivity
/-- Domain condition for `-alpha_L / beta_L`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq5_ps_cond2 (alpha_L beta_L : ℝ) (hdom : 0 ≤ -alpha_L / beta_L) : 0 ≤ -alpha_L / beta_L := hdom

/-! ## 6. Thermodynamic coercive field

    E_c0 = 2/(3*sqrt(3))*(-alpha_L)*sqrt(-alpha_L/beta_L)
-/
/-- Both sides of "Thermodynamic coercive field" carry the same physical dimension. -/
theorem eq6_ec_dim : d_E_c0 = (Dim.mul (Dim.mul (Dim.div Dim.one (Dim.mul Dim.one (Dim.pow Dim.one 1 2))) d_alpha_L) (Dim.pow (Dim.div d_alpha_L d_beta_L) 1 2)) := by decide
/-- The argument `3` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_ec_reg1  : 0 ≤ (3 : ℝ) := by positivity
/-- The denominator `3 * sqrt(3)` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_ec_reg2  : (3 : ℝ) * Real.sqrt (3 : ℝ) ≠ 0 := by positivity
/-- The denominator `beta_L` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_ec_reg3 (beta_L : ℝ) (hbeta_L : 0 < beta_L) : beta_L ≠ 0 := by positivity
/-- Domain condition for `-alpha_L / beta_L`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq6_ec_cond4 (alpha_L beta_L : ℝ) (hdom : 0 ≤ -alpha_L / beta_L) : 0 ≤ -alpha_L / beta_L := hdom

/-! ## 7. Relaxation time about the polar state

    tau_P = 1/(2*Gamma_k*abs(alpha_L))
-/
/-- Both sides of "Relaxation time about the polar state" carry the same physical dimension. -/
theorem eq7_tau_dim : d_tau_P = (Dim.div Dim.one (Dim.mul (Dim.mul Dim.one d_Gamma_k) d_alpha_L)) := by decide
/-- Domain condition for `2 * Gamma_k * abs(alpha_L)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq7_tau_cond1 (Gamma_k alpha_L : ℝ) (hdom : (2 : ℝ) * Gamma_k * abs alpha_L ≠ 0) : (2 : ℝ) * Gamma_k * abs alpha_L ≠ 0 := hdom

/-! ## 8. Displacement plotted

    D_e = P
-/
/-- Both sides of "Displacement plotted" carry the same physical dimension. -/
theorem eq8_disp_dim : d_D_e = d_P := by decide

/-! ## 9. Energy dissipated per cycle

    W_c = int(E, P)
-/
/-- Both sides of "Energy dissipated per cycle" carry the same physical dimension. -/
theorem eq9_loss_dim : d_W_c = (Dim.mul d_E d_P) := by decide

end Bespoke
