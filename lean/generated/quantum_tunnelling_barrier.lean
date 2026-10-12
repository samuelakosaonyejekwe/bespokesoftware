import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantum tunnelling through a potential barrier

Machine-checkable statements for this investigation (quantum-tunnelling-barrier).
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
def d_E : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Particle energy [eV]
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Barrier width [nm]
def d_R : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Reflection probability [1]
def d_T : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Transmission probability [1]
def d_V : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Potential energy [J]
def d_V_0 : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Barrier height [eV]
def d_hbar : Dim := ⟨12, 24, -12, 0, 0, 0, 0⟩  -- Reduced Planck constant [J s]
def d_k_1 : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Incident wavenumber [1/m]
def d_kappa : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Decay constant inside the barrier [1/m]
def d_m_e : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Electron mass [kg]
def d_m_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Particle mass in electron masses [1]
def d_psi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Wavefunction (arbitrary normalisation) [1]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position [m]

/-! ## 1. Time-independent Schrödinger equation

    -hbar^2/(2*m_r*m_e)*d2(psi,x) + V*psi = E*psi
-/
/-- Both sides of "Time-independent Schrödinger equation" carry the same physical dimension. -/
theorem eq1_tise_dim : (Dim.mul (Dim.div (Dim.pow d_hbar 2 1) (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e)) (Dim.div d_psi (Dim.pow d_x 2 1))) = (Dim.mul d_E d_psi) := by decide
theorem eq1_tise_term1 : (Dim.mul (Dim.div (Dim.pow d_hbar 2 1) (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e)) (Dim.div d_psi (Dim.pow d_x 2 1))) = (Dim.mul d_V d_psi) := by decide
/-- The denominator `2 * m_r * m_e` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_tise_reg1 (m_r m_e : ℝ) (hm_r : 0 < m_r) (hm_e : 0 < m_e) : (2 : ℝ) * m_r * m_e ≠ 0 := by positivity

/-! ## 2. Incident wavenumber

    k_1 = sqrt(2*m_r*m_e*E)/hbar
-/
/-- Both sides of "Incident wavenumber" carry the same physical dimension. -/
theorem eq2_k1_dim : d_k_1 = (Dim.div (Dim.pow (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e) d_E) 1 2) d_hbar) := by decide
/-- The argument `2 * m_r * m_e * E` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_k1_reg1 (m_r m_e E : ℝ) (hm_r : 0 < m_r) (hm_e : 0 < m_e) (hE : 0 < E) : 0 ≤ (2 : ℝ) * m_r * m_e * E := by positivity
/-- The denominator `hbar` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_k1_reg2 (hbar : ℝ) (hhbar : 0 < hbar) : hbar ≠ 0 := by positivity

/-! ## 3. Decay constant inside the barrier

    kappa = sqrt(2*m_r*m_e*(V_0 - E))/hbar
-/
/-- Both sides of "Decay constant inside the barrier" carry the same physical dimension. -/
theorem eq3_kap_dim : d_kappa = (Dim.div (Dim.pow (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e) d_V_0) 1 2) d_hbar) := by decide
theorem eq3_kap_term1 : d_V_0 = d_E := by decide
/-- Domain condition for `2 * m_r * m_e * (V_0 - E)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_kap_cond1 (m_r m_e V_0 E : ℝ) (hdom : 0 ≤ (2 : ℝ) * m_r * m_e * (V_0 - E)) : 0 ≤ (2 : ℝ) * m_r * m_e * (V_0 - E) := hdom
/-- The denominator `hbar` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_kap_reg2 (hbar : ℝ) (hhbar : 0 < hbar) : hbar ≠ 0 := by positivity
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq3_kap_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 4. Transmission below the barrier top

    T = 1/(1 + V_0^2*sinh(kappa*L)^2/(4*E*(V_0 - E)))
-/
/-- Both sides of "Transmission below the barrier top" carry the same physical dimension. -/
theorem eq4_T_dim : d_T = (Dim.div Dim.one Dim.one) := by decide
theorem eq4_T_term1 : (Dim.mul d_kappa d_L) = Dim.one := by decide
theorem eq4_T_term2 : d_V_0 = d_E := by decide
theorem eq4_T_term3 : Dim.one = (Dim.div (Dim.mul (Dim.pow d_V_0 2 1) (Dim.pow Dim.one 2 1)) (Dim.mul (Dim.mul Dim.one d_E) d_V_0)) := by decide
/-- Domain condition for `4 * E * (V_0 - E)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_T_cond1 (E V_0 : ℝ) (hdom : (4 : ℝ) * E * (V_0 - E) ≠ 0) : (4 : ℝ) * E * (V_0 - E) ≠ 0 := hdom
/-- Domain condition for `1 + V_0^2 * sinh(kappa * L)^2 / (4 * E * (V_0 - E))`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_T_cond2 (V_0 kappa L E : ℝ) (hdom : (1 : ℝ) + V_0 ^ 2 * Real.sinh (kappa * L) ^ 2 / ((4 : ℝ) * E * (V_0 - E)) ≠ 0) : (1 : ℝ) + V_0 ^ 2 * Real.sinh (kappa * L) ^ 2 / ((4 : ℝ) * E * (V_0 - E)) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq4_T_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 5. Conservation of probability current

    R + T = 1
-/
/-- Both sides of "Conservation of probability current" carry the same physical dimension. -/
theorem eq5_flux_dim : d_R = Dim.one := by decide
theorem eq5_flux_term1 : d_R = d_T := by decide

end Bespoke
