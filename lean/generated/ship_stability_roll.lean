import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Intact stability and roll of a wall-sided hull

Machine-checkable statements for this investigation (ship-stability-roll).
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
def d_B : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Beam [m]
def d_BM : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Metacentric radius [m]
def d_GM : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Metacentric height [m]
def d_GZ : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Righting lever [m]
def d_I_T : Dim := ⟨0, 48, 0, 0, 0, 0, 0⟩  -- Transverse second moment of the waterplane [m^4]
def d_KB : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Centre of buoyancy above keel [m]
def d_KG : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Height of centre of gravity above keel [m]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Length [m]
def d_T : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Draught [m]
def d_T_r : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Natural roll period [s]
def d_V_d : Dim := ⟨0, 36, 0, 0, 0, 0, 0⟩  -- Displaced volume [m^3]
def d_beta_q : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Quadratic roll damping coefficient [1]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_k_B : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Roll radius of gyration as a fraction of beam [1]
def d_k_xx : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Roll radius of gyration [m]
def d_omega_r : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Natural roll frequency [1/s]
def d_phi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Heel angle [rad]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_zeta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Linear roll damping ratio [1]

/-! ## 1. Displaced volume of a box

    V_d = L*B*T
-/
/-- Both sides of "Displaced volume of a box" carry the same physical dimension. -/
theorem eq1_vol_dim : d_V_d = (Dim.mul (Dim.mul d_L d_B) d_T) := by decide

/-! ## 2. Centre of buoyancy

    KB = T/2
-/
/-- Both sides of "Centre of buoyancy" carry the same physical dimension. -/
theorem eq2_kb_dim : d_KB = (Dim.div d_T Dim.one) := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_kb_reg1  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 3. Waterplane second moment

    I_T = L*B^3/12
-/
/-- Both sides of "Waterplane second moment" carry the same physical dimension. -/
theorem eq3_it_dim : d_I_T = (Dim.div (Dim.mul d_L (Dim.pow d_B 3 1)) Dim.one) := by decide
/-- The denominator `12` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_it_reg1  : (12 : ℝ) ≠ 0 := by positivity

/-! ## 4. Metacentric radius

    BM = I_T/V_d
-/
/-- Both sides of "Metacentric radius" carry the same physical dimension. -/
theorem eq4_bm_dim : d_BM = (Dim.div d_I_T d_V_d) := by decide
/-- Domain condition for `V_d`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_bm_cond1 (V_d : ℝ) (hdom : V_d ≠ 0) : V_d ≠ 0 := hdom

/-! ## 5. Metacentric height

    GM = KB + BM - KG
-/
/-- Both sides of "Metacentric height" carry the same physical dimension. -/
theorem eq5_gm_dim : d_GM = d_KB := by decide
theorem eq5_gm_term1 : d_KB = d_BM := by decide
theorem eq5_gm_term2 : d_KB = d_KG := by decide

/-! ## 6. Wall-sided righting lever

    GZ = sin(phi)*(GM + 0.5*BM*tan(phi)^2)
-/
/-- Both sides of "Wall-sided righting lever" carry the same physical dimension. -/
theorem eq6_gz_dim : d_GZ = (Dim.mul Dim.one d_GM) := by decide
theorem eq6_gz_term1 : d_phi = Dim.one := by decide
theorem eq6_gz_term2 : d_phi = Dim.one := by decide
theorem eq6_gz_term3 : d_GM = (Dim.mul (Dim.mul Dim.one d_BM) (Dim.pow Dim.one 2 1)) := by decide

/-! ## 7. Roll radius of gyration

    k_xx = k_B*B
-/
/-- Both sides of "Roll radius of gyration" carry the same physical dimension. -/
theorem eq7_kxx_dim : d_k_xx = (Dim.mul d_k_B d_B) := by decide

/-! ## 8. Natural roll period

    T_r = 2*pi*k_xx/sqrt(g*GM)
-/
/-- Both sides of "Natural roll period" carry the same physical dimension. -/
theorem eq8_tr_dim : d_T_r = (Dim.div (Dim.mul (Dim.mul Dim.one Dim.one) d_k_xx) (Dim.pow (Dim.mul d_g d_GM) 1 2)) := by decide
/-- The argument `g * GM` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_tr_reg1 (g GM : ℝ) (hg : 0 < g) (hGM : 0 < GM) : 0 ≤ g * GM := by positivity
/-- The denominator `sqrt(g * GM)` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_tr_reg2 (g GM : ℝ) (hg : 0 < g) (hGM : 0 < GM) : Real.sqrt (g * GM) ≠ 0 := by positivity

/-! ## 9. Natural roll frequency

    omega_r = sqrt(g*GM)/k_xx
-/
/-- Both sides of "Natural roll frequency" carry the same physical dimension. -/
theorem eq9_wr_dim : d_omega_r = (Dim.div (Dim.pow (Dim.mul d_g d_GM) 1 2) d_k_xx) := by decide
/-- The argument `g * GM` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_wr_reg1 (g GM : ℝ) (hg : 0 < g) (hGM : 0 < GM) : 0 ≤ g * GM := by positivity
/-- Domain condition for `k_xx`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq9_wr_cond2 (k_xx : ℝ) (hdom : k_xx ≠ 0) : k_xx ≠ 0 := hdom

/-! ## 10. Free roll equation

    d2(phi,t) = -2*zeta*omega_r*d(phi,t) - beta_q*abs(d(phi,t))*d(phi,t) - g*GZ/k_xx^2
-/
/-- Both sides of "Free roll equation" carry the same physical dimension. -/
theorem eq10_roll_dim : (Dim.div d_phi (Dim.pow d_t 2 1)) = (Dim.mul (Dim.mul (Dim.mul Dim.one d_zeta) d_omega_r) (Dim.div d_phi d_t)) := by decide
theorem eq10_roll_term1 : (Dim.mul (Dim.mul (Dim.mul Dim.one d_zeta) d_omega_r) (Dim.div d_phi d_t)) = (Dim.mul (Dim.mul d_beta_q (Dim.div d_phi d_t)) (Dim.div d_phi d_t)) := by decide
theorem eq10_roll_term2 : (Dim.mul (Dim.mul (Dim.mul Dim.one d_zeta) d_omega_r) (Dim.div d_phi d_t)) = (Dim.div (Dim.mul d_g d_GZ) (Dim.pow d_k_xx 2 1)) := by decide
/-- Domain condition for `k_xx^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq10_roll_cond1 (k_xx : ℝ) (hdom : k_xx ^ 2 ≠ 0) : k_xx ^ 2 ≠ 0 := hdom

end Bespoke
