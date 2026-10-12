import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Bound states of a finite quantum well

Machine-checkable statements for this investigation (quantum-well-levels).
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
def d_E_1 : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Ground-state energy [J]
def d_E_2 : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- First excited-state energy [J]
def d_E_n : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Energy of level n above the well bottom [J]
def d_L_w : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Well width [nm]
def d_N_b : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of bound states [1]
def d_U : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Potential energy [J]
def d_V_0 : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Well depth (barrier height) [eV]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light [m/s]
def d_hbar : Dim := ⟨12, 24, -12, 0, 0, 0, 0⟩  -- Reduced Planck constant [J s]
def d_k_w : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Wavenumber in the well [1/m]
def d_kappa_b : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Decay constant in the barrier [1/m]
def d_lambda_21 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Wavelength of the 2→1 transition [m]
def d_m_e : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Electron mass [kg]
def d_m_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Effective mass in the well, in electron masses [1]
def d_n : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Quantum number [1]
def d_psi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Wavefunction [1]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position [m]

/-! ## 1. Time-independent Schrödinger equation

    -hbar^2/(2*m_r*m_e)*pd2(psi,x) + U*psi = E_n*psi
-/
/-- Both sides of "Time-independent Schrödinger equation" carry the same physical dimension. -/
theorem eq1_se_dim : (Dim.mul (Dim.div (Dim.pow d_hbar 2 1) (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e)) (Dim.div d_psi (Dim.pow d_x 2 1))) = (Dim.mul d_E_n d_psi) := by decide
theorem eq1_se_term1 : (Dim.mul (Dim.div (Dim.pow d_hbar 2 1) (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e)) (Dim.div d_psi (Dim.pow d_x 2 1))) = (Dim.mul d_U d_psi) := by decide
/-- The denominator `2 * m_r * m_e` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_se_reg1 (m_r m_e : ℝ) (hm_r : 0 < m_r) (hm_e : 0 < m_e) : (2 : ℝ) * m_r * m_e ≠ 0 := by positivity

/-! ## 2. Wavenumber in the well

    k_w = sqrt(2*m_r*m_e*E_n)/hbar
-/
/-- Both sides of "Wavenumber in the well" carry the same physical dimension. -/
theorem eq2_kw_dim : d_k_w = (Dim.div (Dim.pow (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e) d_E_n) 1 2) d_hbar) := by decide
/-- Domain condition for `2 * m_r * m_e * E_n`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq2_kw_cond1 (m_r m_e E_n : ℝ) (hdom : 0 ≤ (2 : ℝ) * m_r * m_e * E_n) : 0 ≤ (2 : ℝ) * m_r * m_e * E_n := hdom
/-- The denominator `hbar` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_kw_reg2 (hbar : ℝ) (hhbar : 0 < hbar) : hbar ≠ 0 := by positivity

/-! ## 3. Decay constant in the barrier

    kappa_b = sqrt(2*m_r*m_e*(V_0 - E_n))/hbar
-/
/-- Both sides of "Decay constant in the barrier" carry the same physical dimension. -/
theorem eq3_kb_dim : d_kappa_b = (Dim.div (Dim.pow (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e) d_V_0) 1 2) d_hbar) := by decide
theorem eq3_kb_term1 : d_V_0 = d_E_n := by decide
/-- Domain condition for `2 * m_r * m_e * (V_0 - E_n)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_kb_cond1 (m_r m_e V_0 E_n : ℝ) (hdom : 0 ≤ (2 : ℝ) * m_r * m_e * (V_0 - E_n)) : 0 ≤ (2 : ℝ) * m_r * m_e * (V_0 - E_n) := hdom
/-- The denominator `hbar` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_kb_reg2 (hbar : ℝ) (hhbar : 0 < hbar) : hbar ≠ 0 := by positivity

/-! ## 4. Quantisation condition

    k_w*L_w = (n - 1)*pi + 2*atan(kappa_b/k_w)
-/
/-- Both sides of "Quantisation condition" carry the same physical dimension. -/
theorem eq4_quant_dim : (Dim.mul d_k_w d_L_w) = (Dim.mul d_n Dim.one) := by decide
theorem eq4_quant_term1 : d_n = Dim.one := by decide
theorem eq4_quant_term2 : (Dim.div d_kappa_b d_k_w) = Dim.one := by decide
theorem eq4_quant_term3 : (Dim.mul d_n Dim.one) = (Dim.mul Dim.one Dim.one) := by decide
/-- Domain condition for `k_w`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_quant_cond1 (k_w : ℝ) (hdom : k_w ≠ 0) : k_w ≠ 0 := hdom

/-! ## 5. Number of bound states

    N_b = floor(sqrt(2*m_r*m_e*V_0)*L_w/(pi*hbar)) + 1
-/
/-- Both sides of "Number of bound states" carry the same physical dimension. -/
theorem eq5_nb_dim : d_N_b = (Dim.div (Dim.mul (Dim.pow (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e) d_V_0) 1 2) d_L_w) (Dim.mul Dim.one d_hbar)) := by decide
theorem eq5_nb_term1 : (Dim.div (Dim.mul (Dim.pow (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e) d_V_0) 1 2) d_L_w) (Dim.mul Dim.one d_hbar)) = Dim.one := by decide
/-- The argument `2 * m_r * m_e * V_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_nb_reg1 (m_r m_e V_0 : ℝ) (hm_r : 0 < m_r) (hm_e : 0 < m_e) (hV_0 : 0 < V_0) : 0 ≤ (2 : ℝ) * m_r * m_e * V_0 := by positivity
/-- The denominator `pi * hbar` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_nb_reg2 (hbar : ℝ) (hhbar : 0 < hbar) : Real.pi * hbar ≠ 0 := by positivity

/-! ## 6. Transition wavelength

    lambda_21 = 2*pi*hbar*c/(E_2 - E_1)
-/
/-- Both sides of "Transition wavelength" carry the same physical dimension. -/
theorem eq6_lam_dim : d_lambda_21 = (Dim.div (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_hbar) d_c) d_E_2) := by decide
theorem eq6_lam_term1 : d_E_2 = d_E_1 := by decide
/-- Domain condition for `E_2 - E_1`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_lam_cond1 (E_2 E_1 : ℝ) (hdom : E_2 - E_1 ≠ 0) : E_2 - E_1 ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq6_lam_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

end Bespoke
