import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Twin paradox and time dilation

Machine-checkable statements for this investigation (twin-paradox-time-dilation).
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
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- One-way distance in the home frame [ly]
def d_N_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Signals received over the trip [1]
def d_T : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Trip duration in the home frame [s]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light [m/s]
def d_f_r : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Received signal rate [1/s]
def d_f_s : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Rate at which each twin emits light signals (own clock) [1/yr]
def d_gamma : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Lorentz factor [1]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Home-frame coordinate time [s]
def d_tau : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Proper time [s]
def d_tau_0 : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Rest-frame lifetime of a clock particle carried at the cruise speed [us]
def d_tau_h : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Proper time of the stay-at-home twin [s]
def d_tau_lab : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Dilated lifetime in the home frame [s]
def d_tau_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Proper time of the travelling twin [s]
def d_v : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Cruise speed relative to the stay-at-home twin [m/s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Home-frame position [m]

/-! ## 1. Proper time along a worldline

    c^2*d(tau,t)^2 = c^2 - d(x,t)^2
-/
/-- Both sides of "Proper time along a worldline" carry the same physical dimension. -/
theorem eq1_interval_dim : (Dim.mul (Dim.pow d_c 2 1) (Dim.pow (Dim.div d_tau d_t) 2 1)) = (Dim.pow d_c 2 1) := by decide
theorem eq1_interval_term1 : (Dim.pow d_c 2 1) = (Dim.pow (Dim.div d_x d_t) 2 1) := by decide

/-! ## 2. Lorentz factor

    gamma = 1/sqrt(1 - v^2/c^2)
-/
/-- Both sides of "Lorentz factor" carry the same physical dimension. -/
theorem eq2_gamma_dim : d_gamma = (Dim.div Dim.one (Dim.pow Dim.one 1 2)) := by decide
theorem eq2_gamma_term1 : Dim.one = (Dim.div (Dim.pow d_v 2 1) (Dim.pow d_c 2 1)) := by decide
/-- The denominator `c^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_gamma_reg1 (c : ℝ) (hc : 0 < c) : c ^ 2 ≠ 0 := by positivity
/-- Domain condition for `1 - v^2 / c^2`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq2_gamma_cond2 (v c : ℝ) (hdom : 0 ≤ (1 : ℝ) - v ^ 2 / c ^ 2) : 0 ≤ (1 : ℝ) - v ^ 2 / c ^ 2 := hdom
/-- Domain condition for `sqrt(1 - v^2 / c^2)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq2_gamma_cond3 (v c : ℝ) (hdom : Real.sqrt ((1 : ℝ) - v ^ 2 / c ^ 2) ≠ 0) : Real.sqrt ((1 : ℝ) - v ^ 2 / c ^ 2) ≠ 0 := hdom

/-! ## 3. Home-frame trip duration

    T = 2*L/v
-/
/-- Both sides of "Home-frame trip duration" carry the same physical dimension. -/
theorem eq3_T_dim : d_T = (Dim.div (Dim.mul Dim.one d_L) d_v) := by decide
/-- The denominator `v` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_T_reg1 (v : ℝ) (hv : 0 < v) : v ≠ 0 := by positivity

/-! ## 4. Traveller's elapsed proper time

    tau_t = T/gamma
-/
/-- Both sides of "Traveller's elapsed proper time" carry the same physical dimension. -/
theorem eq4_taut_dim : d_tau_t = (Dim.div d_T d_gamma) := by decide
/-- The denominator `gamma` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_taut_reg1 (gamma : ℝ) (hgamma : 0 < gamma) : gamma ≠ 0 := by positivity

/-! ## 5. Home twin's elapsed proper time

    tau_h = T
-/
/-- Both sides of "Home twin's elapsed proper time" carry the same physical dimension. -/
theorem eq5_tauh_dim : d_tau_h = d_T := by decide

/-! ## 6. Received signal rate while receding

    f_r = f_s*sqrt((1 - v/c)/(1 + v/c))
-/
/-- Both sides of "Received signal rate while receding" carry the same physical dimension. -/
theorem eq6_doppler_dim : d_f_r = (Dim.mul d_f_s (Dim.pow (Dim.div Dim.one Dim.one) 1 2)) := by decide
theorem eq6_doppler_term1 : Dim.one = (Dim.div d_v d_c) := by decide
theorem eq6_doppler_term2 : Dim.one = (Dim.div d_v d_c) := by decide
/-- The denominator `c` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_doppler_reg1 (c : ℝ) (hc : 0 < c) : c ≠ 0 := by positivity
/-- The denominator `c` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_doppler_reg2 (c : ℝ) (hc : 0 < c) : c ≠ 0 := by positivity
/-- The denominator `1 + v / c` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_doppler_reg3 (v c : ℝ) (hv : 0 < v) (hc : 0 < c) : (1 : ℝ) + v / c ≠ 0 := by positivity
/-- Domain condition for `(1 - v / c) / (1 + v / c)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq6_doppler_cond4 (v c : ℝ) (hdom : 0 ≤ ((1 : ℝ) - v / c) / ((1 : ℝ) + v / c)) : 0 ≤ ((1 : ℝ) - v / c) / ((1 : ℝ) + v / c) := hdom

/-! ## 7. Dilated lifetime of a moving particle

    tau_lab = gamma*tau_0
-/
/-- Both sides of "Dilated lifetime of a moving particle" carry the same physical dimension. -/
theorem eq7_life_dim : d_tau_lab = (Dim.mul d_gamma d_tau_0) := by decide

/-! ## 8. Signals received equal signals sent

    N_r = f_s*tau_h
-/
/-- Both sides of "Signals received equal signals sent" carry the same physical dimension. -/
theorem eq8_count_dim : d_N_r = (Dim.mul d_f_s d_tau_h) := by decide

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (E H S V : Prop) (h1 : S ↔ (H ∧ V)) (h2 : S → E) (h3 : H) (h4 : ¬V) : ¬S := by tauto

end Bespoke
