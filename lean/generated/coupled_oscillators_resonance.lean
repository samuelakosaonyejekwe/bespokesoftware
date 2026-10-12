import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Two coupled oscillators: normal modes, beating and synchronisation

Machine-checkable statements for this investigation (coupled-oscillators-resonance).
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
def d_T_ex : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Energy-exchange time [s]
def d_eta_tr : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Largest fraction of energy transferred [1]
def d_f_beat : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Beat frequency [Hz]
def d_k : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Spring stiffness of each oscillator [N/m]
def d_k_2 : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Stiffness of the second oscillator [N/m]
def d_k_c : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Coupling spring stiffness [N/m]
def d_m : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass of each oscillator [kg]
def d_omega_a : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Lower normal-mode angular frequency [1/s]
def d_omega_b : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Upper normal-mode angular frequency [1/s]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_x_1 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Displacement of mass 1 [m]
def d_x_2 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Displacement of mass 2 [m]

/-! ## 1. Equation of motion, mass 1

    m*d2(x_1,t) = -k*x_1 - k_c*(x_1 - x_2)
-/
/-- Both sides of "Equation of motion, mass 1" carry the same physical dimension. -/
theorem eq1_eom1_dim : (Dim.mul d_m (Dim.div d_x_1 (Dim.pow d_t 2 1))) = (Dim.mul d_k d_x_1) := by decide
theorem eq1_eom1_term1 : d_x_1 = d_x_2 := by decide
theorem eq1_eom1_term2 : (Dim.mul d_k d_x_1) = (Dim.mul d_k_c d_x_1) := by decide

/-! ## 2. Equation of motion, mass 2

    m*d2(x_2,t) = -k_2*x_2 - k_c*(x_2 - x_1)
-/
/-- Both sides of "Equation of motion, mass 2" carry the same physical dimension. -/
theorem eq2_eom2_dim : (Dim.mul d_m (Dim.div d_x_2 (Dim.pow d_t 2 1))) = (Dim.mul d_k_2 d_x_2) := by decide
theorem eq2_eom2_term1 : d_x_2 = d_x_1 := by decide
theorem eq2_eom2_term2 : (Dim.mul d_k_2 d_x_2) = (Dim.mul d_k_c d_x_2) := by decide

/-! ## 3. Second spring

    k_2 = k
-/
/-- Both sides of "Second spring" carry the same physical dimension. -/
theorem eq3_k2_dim : d_k_2 = d_k := by decide

/-! ## 4. In-phase mode

    omega_a = sqrt(k/m)
-/
/-- Both sides of "In-phase mode" carry the same physical dimension. -/
theorem eq4_wa_dim : d_omega_a = (Dim.pow (Dim.div d_k d_m) 1 2) := by decide
/-- The denominator `m` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_wa_reg1 (m : ℝ) (hm : 0 < m) : m ≠ 0 := by positivity
/-- The argument `k / m` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_wa_reg2 (k m : ℝ) (hk : 0 < k) (hm : 0 < m) : 0 ≤ k / m := by positivity

/-! ## 5. Anti-phase mode

    omega_b = sqrt((k + 2*k_c)/m)
-/
/-- Both sides of "Anti-phase mode" carry the same physical dimension. -/
theorem eq5_wb_dim : d_omega_b = (Dim.pow (Dim.div d_k d_m) 1 2) := by decide
theorem eq5_wb_term1 : d_k = (Dim.mul Dim.one d_k_c) := by decide
/-- The denominator `m` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_wb_reg1 (m : ℝ) (hm : 0 < m) : m ≠ 0 := by positivity
/-- The argument `(k + 2 * k_c) / m` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_wb_reg2 (k k_c m : ℝ) (hk : 0 < k) (hk_c : 0 < k_c) (hm : 0 < m) : 0 ≤ (k + (2 : ℝ) * k_c) / m := by positivity

/-! ## 6. Beat frequency

    f_beat = (omega_b - omega_a)/(2*pi)
-/
/-- Both sides of "Beat frequency" carry the same physical dimension. -/
theorem eq6_fb_dim : d_f_beat = (Dim.div d_omega_b (Dim.mul Dim.one Dim.one)) := by decide
theorem eq6_fb_term1 : d_omega_b = d_omega_a := by decide
/-- The denominator `2 * pi` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_fb_reg1  : (2 : ℝ) * Real.pi ≠ 0 := by positivity

/-! ## 7. Energy-exchange time

    T_ex = pi/(omega_b - omega_a)
-/
/-- Both sides of "Energy-exchange time" carry the same physical dimension. -/
theorem eq7_tex_dim : d_T_ex = (Dim.div Dim.one d_omega_b) := by decide
theorem eq7_tex_term1 : d_omega_b = d_omega_a := by decide
/-- Domain condition for `omega_b - omega_a`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_tex_cond1 (omega_b omega_a : ℝ) (hdom : omega_b - omega_a ≠ 0) : omega_b - omega_a ≠ 0 := hdom

/-! ## 8. Largest energy transfer

    eta_tr = 1
-/
/-- Both sides of "Largest energy transfer" carry the same physical dimension. -/
theorem eq8_tr_dim : d_eta_tr = Dim.one := by decide

end Bespoke
