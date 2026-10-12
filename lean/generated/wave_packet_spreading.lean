import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Spreading of a free quantum wave packet

Machine-checkable statements for this investigation (wave-packet-spreading).
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
def d_dp : Dim := ⟨12, 12, -12, 0, 0, 0, 0⟩  -- Momentum uncertainty [kg m/s]
def d_hbar : Dim := ⟨12, 24, -12, 0, 0, 0, 0⟩  -- Reduced Planck constant [J s]
def d_i_u : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Imaginary unit [1]
def d_k : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Wavenumber [1/m]
def d_k_0 : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Mean wavenumber [1/m]
def d_m_e : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Electron mass [kg]
def d_m_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Particle mass in electron masses [1]
def d_omega_k : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Angular frequency of a plane-wave component [1/s]
def d_psi : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Wavefunction [1]
def d_sigma_0 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Initial position uncertainty [nm]
def d_sigma_t : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position uncertainty at time t [m]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Elapsed time [fs]
def d_tau_s : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Spreading time [s]
def d_v_g : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Group velocity [m/s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Position [m]

/-! ## 1. Time-dependent Schrödinger equation

    i_u*hbar*pd(psi,t) = -hbar^2/(2*m_r*m_e)*pd2(psi,x)
-/
/-- Both sides of "Time-dependent Schrödinger equation" carry the same physical dimension. -/
theorem eq1_tdse_dim : (Dim.mul (Dim.mul d_i_u d_hbar) (Dim.div d_psi d_t)) = (Dim.mul (Dim.div (Dim.pow d_hbar 2 1) (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e)) (Dim.div d_psi (Dim.pow d_x 2 1))) := by decide
/-- The denominator `2 * m_r * m_e` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_tdse_reg1 (m_r m_e : ℝ) (hm_r : 0 < m_r) (hm_e : 0 < m_e) : (2 : ℝ) * m_r * m_e ≠ 0 := by positivity

/-! ## 2. Dispersion relation

    omega_k = hbar*k^2/(2*m_r*m_e)
-/
/-- Both sides of "Dispersion relation" carry the same physical dimension. -/
theorem eq2_disp_dim : d_omega_k = (Dim.div (Dim.mul d_hbar (Dim.pow d_k 2 1)) (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e)) := by decide
/-- The denominator `2 * m_r * m_e` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_disp_reg1 (m_r m_e : ℝ) (hm_r : 0 < m_r) (hm_e : 0 < m_e) : (2 : ℝ) * m_r * m_e ≠ 0 := by positivity

/-! ## 3. Spreading time

    tau_s = 2*m_r*m_e*sigma_0^2/hbar
-/
/-- Both sides of "Spreading time" carry the same physical dimension. -/
theorem eq3_taus_dim : d_tau_s = (Dim.div (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_r) d_m_e) (Dim.pow d_sigma_0 2 1)) d_hbar) := by decide
/-- The denominator `hbar` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_taus_reg1 (hbar : ℝ) (hhbar : 0 < hbar) : hbar ≠ 0 := by positivity

/-! ## 4. Width of the packet

    sigma_t = sigma_0*sqrt(1 + (t/tau_s)^2)
-/
/-- Both sides of "Width of the packet" carry the same physical dimension. -/
theorem eq4_sig_dim : d_sigma_t = (Dim.mul d_sigma_0 (Dim.pow Dim.one 1 2)) := by decide
theorem eq4_sig_term1 : Dim.one = (Dim.pow (Dim.div d_t d_tau_s) 2 1) := by decide
/-- The denominator `tau_s` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_sig_reg1 (tau_s : ℝ) (htau_s : 0 < tau_s) : tau_s ≠ 0 := by positivity
/-- The argument `1 + (t / tau_s)^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_sig_reg2 (t tau_s : ℝ) (ht : 0 < t) (htau_s : 0 < tau_s) : 0 ≤ (1 : ℝ) + (t / tau_s) ^ 2 := by positivity

/-! ## 5. Group velocity

    v_g = hbar*k_0/(m_r*m_e)
-/
/-- Both sides of "Group velocity" carry the same physical dimension. -/
theorem eq5_vg_dim : d_v_g = (Dim.div (Dim.mul d_hbar d_k_0) (Dim.mul d_m_r d_m_e)) := by decide
/-- The denominator `m_r * m_e` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_vg_reg1 (m_r m_e : ℝ) (hm_r : 0 < m_r) (hm_e : 0 < m_e) : m_r * m_e ≠ 0 := by positivity

/-! ## 6. Momentum uncertainty

    dp = hbar/(2*sigma_0)
-/
/-- Both sides of "Momentum uncertainty" carry the same physical dimension. -/
theorem eq6_dp_dim : d_dp = (Dim.div d_hbar (Dim.mul Dim.one d_sigma_0)) := by decide
/-- The denominator `2 * sigma_0` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_dp_reg1 (sigma_0 : ℝ) (hsigma_0 : 0 < sigma_0) : (2 : ℝ) * sigma_0 ≠ 0 := by positivity

end Bespoke
