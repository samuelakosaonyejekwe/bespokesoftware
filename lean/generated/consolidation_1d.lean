import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# One-dimensional consolidation of a clay layer

Machine-checkable statements for this investigation (consolidation-1d).
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
def d_H_c : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Clay layer thickness [m]
def d_T_v : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Time factor [1]
def d_U_avg : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Average degree of consolidation [1]
def d_c_v : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Coefficient of consolidation [m^2/yr]
def d_d_r : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Longest drainage path [m]
def d_dq : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Applied surface load [kPa]
def d_m_v : Dim := ⟨-12, 12, 24, 0, 0, 0, 0⟩  -- Coefficient of volume compressibility [1/MPa]
def d_s_inf : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Final consolidation settlement [m]
def d_s_t : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Settlement at time t [m]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_t_end : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time of interest [yr]
def d_u : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Excess pore pressure [Pa]
def d_z : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Depth below the top of the layer [m]

/-! ## 1. Terzaghi consolidation equation

    pd(u,t) = c_v*pd2(u,z)
-/
/-- Both sides of "Terzaghi consolidation equation" carry the same physical dimension. -/
theorem eq1_pde_dim : (Dim.div d_u d_t) = (Dim.mul d_c_v (Dim.div d_u (Dim.pow d_z 2 1))) := by decide

/-! ## 2. Initial condition

    u = dq
-/
/-- Both sides of "Initial condition" carry the same physical dimension. -/
theorem eq2_ic_dim : d_u = d_dq := by decide

/-! ## 3. Drainage path

    d_r = H_c/2
-/
/-- Both sides of "Drainage path" carry the same physical dimension. -/
theorem eq3_dr_dim : d_d_r = (Dim.div d_H_c Dim.one) := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_dr_reg1  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 4. Time factor

    T_v = c_v*t_end/d_r^2
-/
/-- Both sides of "Time factor" carry the same physical dimension. -/
theorem eq4_tv_dim : d_T_v = (Dim.div (Dim.mul d_c_v d_t_end) (Dim.pow d_d_r 2 1)) := by decide
/-- The denominator `d_r^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_tv_reg1 (d_r : ℝ) (hd_r : 0 < d_r) : d_r ^ 2 ≠ 0 := by positivity

/-! ## 5. Average degree of consolidation

    U_avg = 1 - int(u, z)/(dq*H_c)
-/
/-- Both sides of "Average degree of consolidation" carry the same physical dimension. -/
theorem eq5_U_dim : d_U_avg = Dim.one := by decide
theorem eq5_U_term1 : Dim.one = (Dim.div (Dim.mul d_u d_z) (Dim.mul d_dq d_H_c)) := by decide
/-- The denominator `dq * H_c` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_U_reg1 (dq H_c : ℝ) (hdq : 0 < dq) (hH_c : 0 < H_c) : dq * H_c ≠ 0 := by positivity

/-! ## 6. Final settlement

    s_inf = m_v*dq*H_c
-/
/-- Both sides of "Final settlement" carry the same physical dimension. -/
theorem eq6_sinf_dim : d_s_inf = (Dim.mul (Dim.mul d_m_v d_dq) d_H_c) := by decide

/-! ## 7. Settlement at time t

    s_t = U_avg*s_inf
-/
/-- Both sides of "Settlement at time t" carry the same physical dimension. -/
theorem eq7_st_dim : d_s_t = (Dim.mul d_U_avg d_s_inf) := by decide

end Bespoke
