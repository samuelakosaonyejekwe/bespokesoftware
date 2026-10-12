import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Charge relaxation with a hypothesised memory kernel

Machine-checkable statements for this investigation (charge-memory-relaxation).
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
def d_A_f : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Fitted amplitude [1]
def d_D_rms : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Root-mean-square difference between the laws [1]
def d_E_f : Dim := ⟨12, 12, -36, -12, 0, 0, 0⟩  -- Electric field [V/m]
def d_J_c : Dim := ⟨0, -24, 0, 12, 0, 0, 0⟩  -- Conduction current density [A/m^2]
def d_K_m : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Memory kernel [1/s]
def d_eps_0 : Dim := ⟨-12, -36, 48, 24, 0, 0, 0⟩  -- Vacuum permittivity [F/m]
def d_eps_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Relative permittivity of the fluid [1]
def d_n_samp : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Number of samples in the record [1]
def d_q : Dim := ⟨0, 0, 12, 12, 0, 0, 0⟩  -- Free charge under the hypothesised law [C]
def d_q_0 : Dim := ⟨0, 0, 12, 12, 0, 0, 0⟩  -- Initial charge [nC]
def d_q_c : Dim := ⟨0, 0, 12, 12, 0, 0, 0⟩  -- Free charge under the conventional law [C]
def d_q_f : Dim := ⟨0, 0, 12, 12, 0, 0, 0⟩  -- Conventional comparison curve [C]
def d_rho_e : Dim := ⟨0, -36, 12, 12, 0, 0, 0⟩  -- Free charge density [C/m^3]
def d_s_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Earlier time (integration variable) [s]
def d_sigma_e : Dim := ⟨-12, -36, 36, 24, 0, 0, 0⟩  -- Electrical conductivity of the fluid [S/m]
def d_sigma_req : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Noise level giving a five-standard-deviation distinction [1]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_tau_M : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Maxwell relaxation time [s]
def d_tau_f : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Fitted time constant [s]
def d_tau_m : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Memory time [s]
def d_theta_c : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Critical memory ratio for oscillation [1]
def d_theta_m : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Memory time as a multiple of the Maxwell time [1]
def d_y_0 : Dim := ⟨0, 0, 12, 12, 0, 0, 0⟩  -- Initial value of the memory variable [C]
def d_y_m : Dim := ⟨0, 0, 12, 12, 0, 0, 0⟩  -- Memory variable: kernel-weighted past charge [C]

/-! ## 1. Charge conservation

    pd(rho_e,t) = -div(J_c)
-/
/-- Both sides of "Charge conservation" carry the same physical dimension. -/
theorem eq1_cons_dim : (Dim.div d_rho_e d_t) = (Dim.div d_J_c d_length) := by decide

/-! ## 2. Ohm's law (conventional)

    J_c = sigma_e*E_f
-/
/-- Both sides of "Ohm's law (conventional)" carry the same physical dimension. -/
theorem eq2_ohm_dim : d_J_c = (Dim.mul d_sigma_e d_E_f) := by decide

/-! ## 3. Gauss's law

    eps_0*eps_r*div(E_f) = rho_e
-/
/-- Both sides of "Gauss's law" carry the same physical dimension. -/
theorem eq3_gauss_dim : (Dim.mul (Dim.mul d_eps_0 d_eps_r) (Dim.div d_E_f d_length)) = d_rho_e := by decide

/-! ## 4. Maxwell relaxation time

    tau_M = eps_0*eps_r/sigma_e
-/
/-- Both sides of "Maxwell relaxation time" carry the same physical dimension. -/
theorem eq4_tau_dim : d_tau_M = (Dim.div (Dim.mul d_eps_0 d_eps_r) d_sigma_e) := by decide
/-- The denominator `sigma_e` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_tau_reg1 (sigma_e : ℝ) (hsigma_e : 0 < sigma_e) : sigma_e ≠ 0 := by positivity

/-! ## 5. Conventional charge relaxation

    d(q_c,t) = -q_c/tau_M
-/
/-- Both sides of "Conventional charge relaxation" carry the same physical dimension. -/
theorem eq5_conv_dim : (Dim.div d_q_c d_t) = (Dim.div d_q_c d_tau_M) := by decide
/-- The denominator `tau_M` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_conv_reg1 (tau_M : ℝ) (htau_M : 0 < tau_M) : tau_M ≠ 0 := by positivity

/-! ## 6. Hypothesised memory law

    d(q,t) = -int(K_m*q, s_t)/tau_M
-/
/-- Both sides of "Hypothesised memory law" carry the same physical dimension. -/
theorem eq6_mem_dim : (Dim.div d_q d_t) = (Dim.div (Dim.mul (Dim.mul d_K_m d_q) d_s_t) d_tau_M) := by decide
/-- The denominator `tau_M` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_mem_reg1 (tau_M : ℝ) (htau_M : 0 < tau_M) : tau_M ≠ 0 := by positivity

/-! ## 7. Hypothesised kernel

    K_m = exp(-(t - s_t)/tau_m)/tau_m
-/
/-- Both sides of "Hypothesised kernel" carry the same physical dimension. -/
theorem eq7_ker_dim : d_K_m = (Dim.div Dim.one d_tau_m) := by decide
theorem eq7_ker_term1 : d_t = d_s_t := by decide
theorem eq7_ker_term2 : (Dim.div d_t d_tau_m) = Dim.one := by decide
/-- The denominator `tau_m` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_ker_reg1 (tau_m : ℝ) (htau_m : 0 < tau_m) : tau_m ≠ 0 := by positivity
/-- The denominator `tau_m` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_ker_reg2 (tau_m : ℝ) (htau_m : 0 < tau_m) : tau_m ≠ 0 := by positivity

/-! ## 8. Memory time

    tau_m = theta_m*tau_M
-/
/-- Both sides of "Memory time" carry the same physical dimension. -/
theorem eq8_tm_dim : d_tau_m = (Dim.mul d_theta_m d_tau_M) := by decide

/-! ## 9. Memory variable

    tau_m*d(y_m,t) = q - y_m
-/
/-- Both sides of "Memory variable" carry the same physical dimension. -/
theorem eq9_aux_dim : (Dim.mul d_tau_m (Dim.div d_y_m d_t)) = d_q := by decide
theorem eq9_aux_term1 : d_q = d_y_m := by decide

/-! ## 10. Decay driven by the memory variable

    d(q,t) = -y_m/tau_M
-/
/-- Both sides of "Decay driven by the memory variable" carry the same physical dimension. -/
theorem eq10_dec_dim : (Dim.div d_q d_t) = (Dim.div d_y_m d_tau_M) := by decide
/-- The denominator `tau_M` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_dec_reg1 (tau_M : ℝ) (htau_M : 0 < tau_M) : tau_M ≠ 0 := by positivity

/-! ## 11. Critical memory ratio

    theta_c = 1/4
-/
/-- Both sides of "Critical memory ratio" carry the same physical dimension. -/
theorem eq11_thc_dim : d_theta_c = (Dim.div Dim.one Dim.one) := by decide
/-- The denominator `4` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_thc_reg1  : (4 : ℝ) ≠ 0 := by positivity

/-! ## 12. Memory variable at the instant of charging

    y_0 = 0*q_0
-/
/-- Both sides of "Memory variable at the instant of charging" carry the same physical dimension. -/
theorem eq12_ic_dim : d_y_0 = (Dim.mul Dim.one d_q_0) := by decide

/-! ## 13. Conventional curve fitted to the data

    q_f = A_f*q_0*exp(-t/tau_f)
-/
/-- Both sides of "Conventional curve fitted to the data" carry the same physical dimension. -/
theorem eq13_fit_dim : d_q_f = (Dim.mul (Dim.mul d_A_f d_q_0) Dim.one) := by decide
theorem eq13_fit_term1 : (Dim.div d_t d_tau_f) = Dim.one := by decide
/-- The denominator `tau_f` stays away from its singular set whenever the quantities are positive. -/
theorem eq13_fit_reg1 (tau_f : ℝ) (htau_f : 0 < tau_f) : tau_f ≠ 0 := by positivity

/-! ## 14. Noise level for a five-standard-deviation distinction

    sigma_req = D_rms*sqrt(n_samp)/5
-/
/-- Both sides of "Noise level for a five-standard-deviation distinction" carry the same physical dimension. -/
theorem eq14_sig_dim : d_sigma_req = (Dim.div (Dim.mul d_D_rms (Dim.pow d_n_samp 1 2)) Dim.one) := by decide
/-- The argument `n_samp` stays away from its singular set whenever the quantities are positive. -/
theorem eq14_sig_reg1 (n_samp : ℝ) (hn_samp : 0 < n_samp) : 0 ≤ n_samp := by positivity
/-- The denominator `5` stays away from its singular set whenever the quantities are positive. -/
theorem eq14_sig_reg2  : (5 : ℝ) ≠ 0 := by positivity

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (A E M O : Prop) (h1 : M → O) (h2 : E → (¬O)) (h3 : O → (M ∨ A)) : (O ∧ (¬A)) → (M ∧ (¬E)) := by tauto

end Bespoke
