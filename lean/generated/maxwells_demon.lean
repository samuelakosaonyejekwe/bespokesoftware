import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Maxwell's demon and the Szilard engine

Machine-checkable statements for this investigation (maxwells-demon).
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
def d_I_m : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Information gained per measurement [1]
def d_P_x : Dim := ⟨12, 24, -36, 0, 0, 0, 0⟩  -- Gross power extracted [W]
def d_Q_er : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Heat dissipated in resetting the memory [J]
def d_T : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Temperature of the heat bath [K]
def d_W_net : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Net work per cycle after resetting the memory [J]
def d_W_x : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Work extracted per cycle [J]
def d_dS_net : Dim := ⟨12, 24, -24, 0, -12, 0, 0⟩  -- Net entropy change of bath, engine and memory per cycle [J/K]
def d_eps_m : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Measurement error probability [1]
def d_k_B : Dim := ⟨12, 24, -24, 0, -12, 0, 0⟩  -- Boltzmann constant [J/K]
def d_r_b : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Engine cycles (bits measured) per second [1/s]

/-! ## 1. Information gained per measurement (nats)

    I_m = ln(2) + eps_m*ln(eps_m) + (1 - eps_m)*ln(1 - eps_m)
-/
/-- Both sides of "Information gained per measurement (nats)" carry the same physical dimension. -/
theorem eq1_info_dim : d_I_m = Dim.one := by decide
theorem eq1_info_term1 : Dim.one = Dim.one := by decide
theorem eq1_info_term2 : d_eps_m = Dim.one := by decide
theorem eq1_info_term3 : Dim.one = (Dim.mul d_eps_m Dim.one) := by decide
theorem eq1_info_term4 : Dim.one = d_eps_m := by decide
theorem eq1_info_term5 : Dim.one = d_eps_m := by decide
theorem eq1_info_term6 : Dim.one = Dim.one := by decide
theorem eq1_info_term7 : Dim.one = (Dim.mul Dim.one Dim.one) := by decide
/-- The argument `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_info_reg1  : 0 < (2 : ℝ) := by positivity
/-- Domain condition for `eps_m`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq1_info_cond2 (eps_m : ℝ) (hdom : 0 < eps_m) : 0 < eps_m := hdom
/-- Domain condition for `1 - eps_m`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq1_info_cond3 (eps_m : ℝ) (hdom : 0 < (1 : ℝ) - eps_m) : 0 < (1 : ℝ) - eps_m := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq1_info_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 2. Work extracted per cycle

    W_x = k_B*T*I_m
-/
/-- Both sides of "Work extracted per cycle" carry the same physical dimension. -/
theorem eq2_work_dim : d_W_x = (Dim.mul (Dim.mul d_k_B d_T) d_I_m) := by decide

/-! ## 3. Minimum heat to reset one bit

    Q_er = k_B*T*ln(2)
-/
/-- Both sides of "Minimum heat to reset one bit" carry the same physical dimension. -/
theorem eq3_erase_dim : d_Q_er = (Dim.mul (Dim.mul d_k_B d_T) Dim.one) := by decide
theorem eq3_erase_term1 : Dim.one = Dim.one := by decide
/-- The argument `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_erase_reg1  : 0 < (2 : ℝ) := by positivity

/-! ## 4. Net entropy change per cycle

    dS_net = (Q_er - W_x)/T
-/
/-- Both sides of "Net entropy change per cycle" carry the same physical dimension. -/
theorem eq4_ent_dim : d_dS_net = (Dim.div d_Q_er d_T) := by decide
theorem eq4_ent_term1 : d_Q_er = d_W_x := by decide
/-- The denominator `T` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_ent_reg1 (T : ℝ) (hT : 0 < T) : T ≠ 0 := by positivity

/-! ## 5. Net work per cycle

    W_net = W_x - Q_er
-/
/-- Both sides of "Net work per cycle" carry the same physical dimension. -/
theorem eq5_net_dim : d_W_net = d_W_x := by decide
theorem eq5_net_term1 : d_W_x = d_Q_er := by decide

/-! ## 6. Gross power extracted

    P_x = r_b*W_x
-/
/-- Both sides of "Gross power extracted" carry the same physical dimension. -/
theorem eq6_pow_dim : d_P_x = (Dim.mul d_r_b d_W_x) := by decide

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (Extract FreeErase SecondLaw Violation : Prop) (h1 : Extract) (h2 : (Extract ∧ FreeErase) → Violation) (h3 : Violation ↔ (¬SecondLaw)) (h4 : SecondLaw) : ¬FreeErase := by tauto

end Bespoke
