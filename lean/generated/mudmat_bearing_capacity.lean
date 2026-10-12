import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Bearing capacity and sliding of a subsea mudmat

Machine-checkable statements for this investigation (mudmat-bearing-capacity).
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
def d_B : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Mudmat width [m]
def d_D_f : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Embedment (skirt) depth [m]
def d_FS_b : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Factor of safety on bearing [1]
def d_FS_s : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Factor of safety on sliding [1]
def d_H : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Horizontal load [kN]
def d_H_u : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Ultimate sliding resistance [N]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Mudmat length [m]
def d_N_c : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Bearing-capacity factor for cohesion [1]
def d_Q_u : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Ultimate vertical capacity [N]
def d_V : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Vertical load (submerged weight and operating loads) [kN]
def d_alpha_s : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Base interface roughness factor [1]
def d_gamma_sub : Dim := ⟨12, -24, -24, 0, 0, 0, 0⟩  -- Submerged unit weight of soil [kN/m^3]
def d_i_ca : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Inclination term [1]
def d_q_u : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Ultimate bearing pressure [Pa]
def d_s_ca : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Shape term [1]
def d_s_u : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Undrained shear strength [kPa]

/-! ## 1. Prandtl bearing-capacity factor

    N_c = pi + 2
-/
/-- Both sides of "Prandtl bearing-capacity factor" carry the same physical dimension. -/
theorem eq1_nc_dim : d_N_c = Dim.one := by decide
theorem eq1_nc_term1 : Dim.one = Dim.one := by decide

/-! ## 2. Shape term

    s_ca = 0.2*B/L
-/
/-- Both sides of "Shape term" carry the same physical dimension. -/
theorem eq2_sc_dim : d_s_ca = (Dim.div (Dim.mul Dim.one d_B) d_L) := by decide
/-- The denominator `L` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_sc_reg1 (L : ℝ) (hL : 0 < L) : L ≠ 0 := by positivity

/-! ## 3. Inclination term

    i_ca = 0.5 - 0.5*sqrt(1 - H/(B*L*s_u))
-/
/-- Both sides of "Inclination term" carry the same physical dimension. -/
theorem eq3_ic_dim : d_i_ca = Dim.one := by decide
theorem eq3_ic_term1 : Dim.one = (Dim.div d_H (Dim.mul (Dim.mul d_B d_L) d_s_u)) := by decide
theorem eq3_ic_term2 : Dim.one = (Dim.mul Dim.one (Dim.pow Dim.one 1 2)) := by decide
/-- The denominator `B * L * s_u` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_ic_reg1 (B L s_u : ℝ) (hB : 0 < B) (hL : 0 < L) (hs_u : 0 < s_u) : B * L * s_u ≠ 0 := by positivity
/-- Domain condition for `1 - H / (B * L * s_u)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_ic_cond2 (H B L s_u : ℝ) (hdom : 0 ≤ (1 : ℝ) - H / (B * L * s_u)) : 0 ≤ (1 : ℝ) - H / (B * L * s_u) := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq3_ic_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 4. Ultimate bearing pressure

    q_u = N_c*s_u*(1 + s_ca - i_ca) + gamma_sub*D_f
-/
/-- Both sides of "Ultimate bearing pressure" carry the same physical dimension. -/
theorem eq4_qu_dim : d_q_u = (Dim.mul (Dim.mul d_N_c d_s_u) Dim.one) := by decide
theorem eq4_qu_term1 : Dim.one = d_s_ca := by decide
theorem eq4_qu_term2 : Dim.one = d_i_ca := by decide
theorem eq4_qu_term3 : (Dim.mul (Dim.mul d_N_c d_s_u) Dim.one) = (Dim.mul d_gamma_sub d_D_f) := by decide

/-! ## 5. Sliding resistance

    H_u = alpha_s*s_u*B*L
-/
/-- Both sides of "Sliding resistance" carry the same physical dimension. -/
theorem eq5_hu_dim : d_H_u = (Dim.mul (Dim.mul (Dim.mul d_alpha_s d_s_u) d_B) d_L) := by decide

/-! ## 6. Ultimate vertical capacity

    Q_u = q_u*B*L
-/
/-- Both sides of "Ultimate vertical capacity" carry the same physical dimension. -/
theorem eq6_Qu_dim : d_Q_u = (Dim.mul (Dim.mul d_q_u d_B) d_L) := by decide

/-! ## 7. Factor of safety on bearing

    FS_b = Q_u/V
-/
/-- Both sides of "Factor of safety on bearing" carry the same physical dimension. -/
theorem eq7_fsb_dim : d_FS_b = (Dim.div d_Q_u d_V) := by decide
/-- The denominator `V` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_fsb_reg1 (V : ℝ) (hV : 0 < V) : V ≠ 0 := by positivity

/-! ## 8. Factor of safety on sliding

    FS_s = H_u/H
-/
/-- Both sides of "Factor of safety on sliding" carry the same physical dimension. -/
theorem eq8_fss_dim : d_FS_s = (Dim.div d_H_u d_H) := by decide
/-- Domain condition for `H`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq8_fss_cond1 (H : ℝ) (hdom : H ≠ 0) : H ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq8_fss_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

end Bespoke
