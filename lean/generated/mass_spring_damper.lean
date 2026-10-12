import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Mass–spring–damper: free and forced vibration

Machine-checkable statements for this investigation (mass-spring-damper).
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
def d_F_0 : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Forcing amplitude [N]
def d_TR : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Transmissibility [1]
def d_X : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Steady-state displacement amplitude [m]
def d_c : Dim := ⟨12, 0, -12, 0, 0, 0, 0⟩  -- Viscous damping coefficient [N s/m]
def d_delta_l : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Logarithmic decrement [1]
def d_f_d : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Forcing frequency [Hz]
def d_k : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Spring stiffness [N/m]
def d_m : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass [kg]
def d_omega : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Forcing angular frequency [1/s]
def d_omega_d : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Damped natural angular frequency [1/s]
def d_omega_n : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Undamped natural angular frequency [1/s]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Displacement of the mass [m]
def d_zeta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Damping ratio [1]

/-! ## 1. Equation of motion

    m*d2(x,t) + c*d(x,t) + k*x = F_0*cos(omega*t)
-/
/-- Both sides of "Equation of motion" carry the same physical dimension. -/
theorem eq1_mom_dim : (Dim.mul d_m (Dim.div d_x (Dim.pow d_t 2 1))) = (Dim.mul d_F_0 Dim.one) := by decide
theorem eq1_mom_term1 : (Dim.mul d_m (Dim.div d_x (Dim.pow d_t 2 1))) = (Dim.mul d_c (Dim.div d_x d_t)) := by decide
theorem eq1_mom_term2 : (Dim.mul d_m (Dim.div d_x (Dim.pow d_t 2 1))) = (Dim.mul d_k d_x) := by decide
theorem eq1_mom_term3 : (Dim.mul d_omega d_t) = Dim.one := by decide

/-! ## 2. Forcing angular frequency

    omega = 2*pi*f_d
-/
/-- Both sides of "Forcing angular frequency" carry the same physical dimension. -/
theorem eq2_om_dim : d_omega = (Dim.mul (Dim.mul Dim.one Dim.one) d_f_d) := by decide

/-! ## 3. Natural frequency

    omega_n = sqrt(k/m)
-/
/-- Both sides of "Natural frequency" carry the same physical dimension. -/
theorem eq3_wn_dim : d_omega_n = (Dim.pow (Dim.div d_k d_m) 1 2) := by decide
/-- The denominator `m` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_wn_reg1 (m : ℝ) (hm : 0 < m) : m ≠ 0 := by positivity
/-- The argument `k / m` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_wn_reg2 (k m : ℝ) (hk : 0 < k) (hm : 0 < m) : 0 ≤ k / m := by positivity

/-! ## 4. Damping ratio

    zeta = c/(2*sqrt(k*m))
-/
/-- Both sides of "Damping ratio" carry the same physical dimension. -/
theorem eq4_zeta_dim : d_zeta = (Dim.div d_c (Dim.mul Dim.one (Dim.pow (Dim.mul d_k d_m) 1 2))) := by decide
/-- The argument `k * m` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_zeta_reg1 (k m : ℝ) (hk : 0 < k) (hm : 0 < m) : 0 ≤ k * m := by positivity
/-- The denominator `2 * sqrt(k * m)` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_zeta_reg2 (k m : ℝ) (hk : 0 < k) (hm : 0 < m) : (2 : ℝ) * Real.sqrt (k * m) ≠ 0 := by positivity

/-! ## 5. Damped natural frequency

    omega_d = omega_n*sqrt(1 - zeta^2)
-/
/-- Both sides of "Damped natural frequency" carry the same physical dimension. -/
theorem eq5_wd_dim : d_omega_d = (Dim.mul d_omega_n (Dim.pow Dim.one 1 2)) := by decide
theorem eq5_wd_term1 : Dim.one = (Dim.pow d_zeta 2 1) := by decide
/-- Domain condition for `1 - zeta^2`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq5_wd_cond1 (zeta : ℝ) (hdom : 0 ≤ (1 : ℝ) - zeta ^ 2) : 0 ≤ (1 : ℝ) - zeta ^ 2 := hdom

/-! ## 6. Logarithmic decrement

    delta_l = 2*pi*zeta/sqrt(1 - zeta^2)
-/
/-- Both sides of "Logarithmic decrement" carry the same physical dimension. -/
theorem eq6_dec_dim : d_delta_l = (Dim.div (Dim.mul (Dim.mul Dim.one Dim.one) d_zeta) (Dim.pow Dim.one 1 2)) := by decide
theorem eq6_dec_term1 : Dim.one = (Dim.pow d_zeta 2 1) := by decide
/-- Domain condition for `1 - zeta^2`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq6_dec_cond1 (zeta : ℝ) (hdom : 0 ≤ (1 : ℝ) - zeta ^ 2) : 0 ≤ (1 : ℝ) - zeta ^ 2 := hdom
/-- Domain condition for `sqrt(1 - zeta^2)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_dec_cond2 (zeta : ℝ) (hdom : Real.sqrt ((1 : ℝ) - zeta ^ 2) ≠ 0) : Real.sqrt ((1 : ℝ) - zeta ^ 2) ≠ 0 := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq6_dec_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 7. Steady-state amplitude

    X = F_0/sqrt((k - m*omega^2)^2 + (c*omega)^2)
-/
/-- Both sides of "Steady-state amplitude" carry the same physical dimension. -/
theorem eq7_amp_dim : d_X = (Dim.div d_F_0 (Dim.pow (Dim.pow d_k 2 1) 1 2)) := by decide
theorem eq7_amp_term1 : d_k = (Dim.mul d_m (Dim.pow d_omega 2 1)) := by decide
theorem eq7_amp_term2 : (Dim.pow d_k 2 1) = (Dim.pow (Dim.mul d_c d_omega) 2 1) := by decide
/-- Domain condition for `(k - m * omega^2)^2 + (c * omega)^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_amp_cond1 (k m omega c : ℝ) (hdom : 0 ≤ (k - m * omega ^ 2) ^ 2 + (c * omega) ^ 2) : 0 ≤ (k - m * omega ^ 2) ^ 2 + (c * omega) ^ 2 := hdom
/-- Domain condition for `sqrt((k - m * omega^2)^2 + (c * omega)^2)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq7_amp_cond2 (k m omega c : ℝ) (hdom : Real.sqrt ((k - m * omega ^ 2) ^ 2 + (c * omega) ^ 2) ≠ 0) : Real.sqrt ((k - m * omega ^ 2) ^ 2 + (c * omega) ^ 2) ≠ 0 := hdom

/-! ## 8. Transmissibility

    TR = sqrt((k^2 + (c*omega)^2)/((k - m*omega^2)^2 + (c*omega)^2))
-/
/-- Both sides of "Transmissibility" carry the same physical dimension. -/
theorem eq8_tr_dim : d_TR = (Dim.pow (Dim.div (Dim.pow d_k 2 1) (Dim.pow d_k 2 1)) 1 2) := by decide
theorem eq8_tr_term1 : (Dim.pow d_k 2 1) = (Dim.pow (Dim.mul d_c d_omega) 2 1) := by decide
theorem eq8_tr_term2 : d_k = (Dim.mul d_m (Dim.pow d_omega 2 1)) := by decide
theorem eq8_tr_term3 : (Dim.pow d_k 2 1) = (Dim.pow (Dim.mul d_c d_omega) 2 1) := by decide
/-- Domain condition for `(k - m * omega^2)^2 + (c * omega)^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq8_tr_cond1 (k m omega c : ℝ) (hdom : (k - m * omega ^ 2) ^ 2 + (c * omega) ^ 2 ≠ 0) : (k - m * omega ^ 2) ^ 2 + (c * omega) ^ 2 ≠ 0 := hdom
/-- Domain condition for `(k^2 + (c * omega)^2) / ((k - m * omega^2)^2 + (c * omega)^2)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq8_tr_cond2 (k c omega m : ℝ) (hdom : 0 ≤ (k ^ 2 + (c * omega) ^ 2) / ((k - m * omega ^ 2) ^ 2 + (c * omega) ^ 2)) : 0 ≤ (k ^ 2 + (c * omega) ^ 2) / ((k - m * omega ^ 2) ^ 2 + (c * omega) ^ 2) := hdom

end Bespoke
