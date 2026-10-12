import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Electrostatic field between a high-voltage electrode and a grounded plane

Machine-checkable statements for this investigation (electrostatic-field-2d).
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
def d_E : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Electric field magnitude [V/m]
def d_E_0 : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Uniform-field reference [V/m]
def d_E_bd : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Breakdown field of the gas [MV/m]
def d_E_peak : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Peak field in the air [V/m]
def d_E_w : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Closed-form peak field, cylinder above a plane [V/m]
def d_L_cr : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Creepage path available along the insulation [mm]
def d_L_req : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Required creepage distance [m]
def d_M_bd : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Breakdown margin [1]
def d_M_cr : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Creepage margin [1]
def d_V_0 : Dim := ⟨12, 24, -36, -12, 0, 0, 0⟩  -- Electrode voltage [kV]
def d_beta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Field-enhancement factor [1]
def d_d_gap : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Gap from electrode surface to grounded plane [mm]
def d_h_c : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Height of the electrode axis [m]
def d_phi : Dim := ⟨12, 24, -36, -12, 0, 0, 0⟩  -- Electrostatic potential [V]
def d_r_e : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Electrode radius (half-width) [mm]
def d_s_cr : Dim := ⟨-12, -12, 36, 12, 0, 0, 0⟩  -- Required specific creepage distance [mm/kV]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Horizontal coordinate [m]
def d_y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Height above the plane [m]

/-! ## 1. Laplace equation

    pd2(phi,x) = -pd2(phi,y)
-/
/-- Both sides of "Laplace equation" carry the same physical dimension. -/
theorem eq1_gov_dim : (Dim.div d_phi (Dim.pow d_x 2 1)) = (Dim.div d_phi (Dim.pow d_y 2 1)) := by decide

/-! ## 2. Electric field magnitude

    E = sqrt(pd(phi,x)^2 + pd(phi,y)^2)
-/
/-- Both sides of "Electric field magnitude" carry the same physical dimension. -/
theorem eq2_field_dim : d_E = (Dim.pow (Dim.pow (Dim.div d_phi d_x) 2 1) 1 2) := by decide
theorem eq2_field_term1 : (Dim.pow (Dim.div d_phi d_x) 2 1) = (Dim.pow (Dim.div d_phi d_y) 2 1) := by decide

/-! ## 3. Uniform-field reference

    E_0 = V_0/d_gap
-/
/-- Both sides of "Uniform-field reference" carry the same physical dimension. -/
theorem eq3_e0_dim : d_E_0 = (Dim.div d_V_0 d_d_gap) := by decide
/-- The denominator `d_gap` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_e0_reg1 (d_gap : ℝ) (hd_gap : 0 < d_gap) : d_gap ≠ 0 := by positivity

/-! ## 4. Field-enhancement factor

    beta = E_peak/E_0
-/
/-- Both sides of "Field-enhancement factor" carry the same physical dimension. -/
theorem eq4_fef_dim : d_beta = (Dim.div d_E_peak d_E_0) := by decide
/-- The denominator `E_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_fef_reg1 (E_0 : ℝ) (hE_0 : 0 < E_0) : E_0 ≠ 0 := by positivity

/-! ## 5. Margin against breakdown

    M_bd = E_bd/E_peak
-/
/-- Both sides of "Margin against breakdown" carry the same physical dimension. -/
theorem eq5_mbd_dim : d_M_bd = (Dim.div d_E_bd d_E_peak) := by decide
/-- The denominator `E_peak` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_mbd_reg1 (E_peak : ℝ) (hE_peak : 0 < E_peak) : E_peak ≠ 0 := by positivity

/-! ## 6. Height of the electrode axis

    h_c = d_gap + r_e
-/
/-- Both sides of "Height of the electrode axis" carry the same physical dimension. -/
theorem eq6_hc_dim : d_h_c = d_d_gap := by decide
theorem eq6_hc_term1 : d_d_gap = d_r_e := by decide

/-! ## 7. Peak field of an isolated cylinder above a plane

    E_w = V_0*sqrt((h_c + r_e)/(h_c - r_e))/(r_e*ln(h_c/r_e + sqrt((h_c/r_e)^2 - 1)))
-/
/-- Both sides of "Peak field of an isolated cylinder above a plane" carry the same physical dimension. -/
theorem eq7_wire_dim : d_E_w = (Dim.div (Dim.mul d_V_0 (Dim.pow (Dim.div d_h_c d_h_c) 1 2)) (Dim.mul d_r_e Dim.one)) := by decide
theorem eq7_wire_term1 : d_h_c = d_r_e := by decide
theorem eq7_wire_term2 : d_h_c = d_r_e := by decide
theorem eq7_wire_term3 : (Dim.pow (Dim.div d_h_c d_r_e) 2 1) = Dim.one := by decide
theorem eq7_wire_term4 : (Dim.div d_h_c d_r_e) = (Dim.pow (Dim.pow (Dim.div d_h_c d_r_e) 2 1) 1 2) := by decide
theorem eq7_wire_term5 : (Dim.div d_h_c d_r_e) = Dim.one := by decide
/-- Domain condition for `h_c - r_e`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_wire_cond1 (h_c r_e : ℝ) (hdom : h_c - r_e ≠ 0) : h_c - r_e ≠ 0 := hdom
/-- Domain condition for `(h_c + r_e) / (h_c - r_e)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_wire_cond2 (h_c r_e : ℝ) (hdom : 0 ≤ (h_c + r_e) / (h_c - r_e)) : 0 ≤ (h_c + r_e) / (h_c - r_e) := hdom
/-- The denominator `r_e` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_wire_reg3 (r_e : ℝ) (hr_e : 0 < r_e) : r_e ≠ 0 := by positivity
/-- The denominator `r_e` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_wire_reg4 (r_e : ℝ) (hr_e : 0 < r_e) : r_e ≠ 0 := by positivity
/-- Domain condition for `(h_c / r_e)^2 - 1`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_wire_cond5 (h_c r_e : ℝ) (hdom : 0 ≤ (h_c / r_e) ^ 2 - (1 : ℝ)) : 0 ≤ (h_c / r_e) ^ 2 - (1 : ℝ) := hdom
/-- Domain condition for `h_c / r_e + sqrt((h_c / r_e)^2 - 1)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_wire_cond6 (h_c r_e : ℝ) (hdom : 0 < h_c / r_e + Real.sqrt ((h_c / r_e) ^ 2 - (1 : ℝ))) : 0 < h_c / r_e + Real.sqrt ((h_c / r_e) ^ 2 - (1 : ℝ)) := hdom
/-- Domain condition for `r_e * ln(h_c / r_e + sqrt((h_c / r_e)^2 - 1))`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_wire_cond7 (r_e h_c : ℝ) (hdom : r_e * Real.log (h_c / r_e + Real.sqrt ((h_c / r_e) ^ 2 - (1 : ℝ))) ≠ 0) : r_e * Real.log (h_c / r_e + Real.sqrt ((h_c / r_e) ^ 2 - (1 : ℝ))) ≠ 0 := hdom

/-! ## 8. Required creepage distance

    L_req = s_cr*V_0
-/
/-- Both sides of "Required creepage distance" carry the same physical dimension. -/
theorem eq8_creq_dim : d_L_req = (Dim.mul d_s_cr d_V_0) := by decide

/-! ## 9. Creepage margin

    M_cr = L_cr/L_req
-/
/-- Both sides of "Creepage margin" carry the same physical dimension. -/
theorem eq9_mcr_dim : d_M_cr = (Dim.div d_L_cr d_L_req) := by decide
/-- The denominator `L_req` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_mcr_reg1 (L_req : ℝ) (hL_req : 0 < L_req) : L_req ≠ 0 := by positivity

end Bespoke
