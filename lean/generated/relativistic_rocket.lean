import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Relativistic rocket at constant proper acceleration

Machine-checkable statements for this investigation (relativistic-rocket).
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
def d_a : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Proper acceleration felt on board [m/s^2]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light [m/s]
def d_m_0 : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Launch mass [kg]
def d_m_f : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Final mass (structure and payload) [kg]
def d_phi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Rapidity [1]
def d_phi_tot : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Total rapidity change of all burns [1]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Earth-frame time [s]
def d_tau : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Ship (proper) time [s]
def d_u : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed in the Earth frame [m/s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance from start [m]

/-! ## 1. Rapidity

    phi = a*tau/c
-/
/-- Both sides of "Rapidity" carry the same physical dimension. -/
theorem eq1_rap_dim : d_phi = (Dim.div (Dim.mul d_a d_tau) d_c) := by decide
/-- The denominator `c` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_rap_reg1 (c : ℝ) (hc : 0 < c) : c ≠ 0 := by positivity

/-! ## 2. Speed

    u = c*tanh(a*tau/c)
-/
/-- Both sides of "Speed" carry the same physical dimension. -/
theorem eq2_vel_dim : d_u = (Dim.mul d_c Dim.one) := by decide
theorem eq2_vel_term1 : (Dim.div (Dim.mul d_a d_tau) d_c) = Dim.one := by decide
/-- The denominator `c` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_vel_reg1 (c : ℝ) (hc : 0 < c) : c ≠ 0 := by positivity

/-! ## 3. Distance covered

    x = c^2/a*(cosh(a*tau/c) - 1)
-/
/-- Both sides of "Distance covered" carry the same physical dimension. -/
theorem eq3_pos_dim : d_x = (Dim.mul (Dim.div (Dim.pow d_c 2 1) d_a) Dim.one) := by decide
theorem eq3_pos_term1 : (Dim.div (Dim.mul d_a d_tau) d_c) = Dim.one := by decide
theorem eq3_pos_term2 : Dim.one = Dim.one := by decide
/-- The denominator `a` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_pos_reg1 (a : ℝ) (ha : 0 < a) : a ≠ 0 := by positivity
/-- The denominator `c` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_pos_reg2 (c : ℝ) (hc : 0 < c) : c ≠ 0 := by positivity

/-! ## 4. Earth-frame time

    t = c/a*sinh(a*tau/c)
-/
/-- Both sides of "Earth-frame time" carry the same physical dimension. -/
theorem eq4_time_dim : d_t = (Dim.mul (Dim.div d_c d_a) Dim.one) := by decide
theorem eq4_time_term1 : (Dim.div (Dim.mul d_a d_tau) d_c) = Dim.one := by decide
/-- The denominator `a` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_time_reg1 (a : ℝ) (ha : 0 < a) : a ≠ 0 := by positivity
/-- The denominator `c` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_time_reg2 (c : ℝ) (hc : 0 < c) : c ≠ 0 := by positivity

/-! ## 5. Photon-rocket mass ratio

    m_0/m_f = exp(phi_tot)
-/
/-- Both sides of "Photon-rocket mass ratio" carry the same physical dimension. -/
theorem eq5_mass_dim : (Dim.div d_m_0 d_m_f) = Dim.one := by decide
theorem eq5_mass_term1 : d_phi_tot = Dim.one := by decide
/-- The denominator `m_f` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_mass_reg1 (m_f : ℝ) (hm_f : 0 < m_f) : m_f ≠ 0 := by positivity

end Bespoke
