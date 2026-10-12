import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Double pendulum: chaos and energy conservation

Machine-checkable statements for this investigation (double-pendulum).
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
def d_E : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Mechanical energy [J]
def d_L_1 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Upper length [m]
def d_L_2 : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Lower length [m]
def d_delta_s : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Separation of the twin trajectories [rad]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_lambda : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Finite-time Lyapunov exponent [1/s]
def d_m_1 : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Upper mass [kg]
def d_m_2 : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Lower mass [kg]
def d_omega_1 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Angular velocity of the upper arm [1/s]
def d_omega_2 : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Angular velocity of the lower arm [1/s]
def d_omega_n : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Normal-mode angular frequency (equal masses and lengths) [1/s]
def d_phi_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Angle of the upper arm [rad]
def d_phi_2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Angle of the lower arm [rad]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_theta_1 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Initial angle of the upper arm from the vertical [deg]
def d_theta_2 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Initial angle of the lower arm from the vertical [deg]

/-! ## 1. Upper arm

    (m_1 + m_2)*L_1^2*d(omega_1,t) + m_2*L_1*L_2*cos(phi_1 - phi_2)*d(omega_2,t) = -m_2*L_1*L_2*omega_2^2*sin(phi_1 - phi_2) - (m_1 + m_2)*g*L_1*sin(phi_1)
-/
/-- Both sides of "Upper arm" carry the same physical dimension. -/
theorem eq1_e1_dim : (Dim.mul (Dim.mul d_m_1 (Dim.pow d_L_1 2 1)) (Dim.div d_omega_1 d_t)) = (Dim.mul (Dim.mul (Dim.mul (Dim.mul d_m_2 d_L_1) d_L_2) (Dim.pow d_omega_2 2 1)) Dim.one) := by decide
theorem eq1_e1_term1 : d_m_1 = d_m_2 := by decide
theorem eq1_e1_term2 : d_phi_1 = d_phi_2 := by decide
theorem eq1_e1_term3 : d_phi_1 = Dim.one := by decide
theorem eq1_e1_term4 : (Dim.mul (Dim.mul d_m_1 (Dim.pow d_L_1 2 1)) (Dim.div d_omega_1 d_t)) = (Dim.mul (Dim.mul (Dim.mul (Dim.mul d_m_2 d_L_1) d_L_2) Dim.one) (Dim.div d_omega_2 d_t)) := by decide
theorem eq1_e1_term5 : d_phi_1 = d_phi_2 := by decide
theorem eq1_e1_term6 : d_phi_1 = Dim.one := by decide
theorem eq1_e1_term7 : d_m_1 = d_m_2 := by decide
theorem eq1_e1_term8 : d_phi_1 = Dim.one := by decide
theorem eq1_e1_term9 : (Dim.mul (Dim.mul (Dim.mul (Dim.mul d_m_2 d_L_1) d_L_2) (Dim.pow d_omega_2 2 1)) Dim.one) = (Dim.mul (Dim.mul (Dim.mul d_m_1 d_g) d_L_1) Dim.one) := by decide

/-! ## 2. Lower arm

    m_2*L_1*L_2*cos(phi_1 - phi_2)*d(omega_1,t) + m_2*L_2^2*d(omega_2,t) = m_2*L_1*L_2*omega_1^2*sin(phi_1 - phi_2) - m_2*g*L_2*sin(phi_2)
-/
/-- Both sides of "Lower arm" carry the same physical dimension. -/
theorem eq2_e2_dim : (Dim.mul (Dim.mul (Dim.mul (Dim.mul d_m_2 d_L_1) d_L_2) Dim.one) (Dim.div d_omega_1 d_t)) = (Dim.mul (Dim.mul (Dim.mul (Dim.mul d_m_2 d_L_1) d_L_2) (Dim.pow d_omega_1 2 1)) Dim.one) := by decide
theorem eq2_e2_term1 : d_phi_1 = d_phi_2 := by decide
theorem eq2_e2_term2 : d_phi_1 = Dim.one := by decide
theorem eq2_e2_term3 : (Dim.mul (Dim.mul (Dim.mul (Dim.mul d_m_2 d_L_1) d_L_2) Dim.one) (Dim.div d_omega_1 d_t)) = (Dim.mul (Dim.mul d_m_2 (Dim.pow d_L_2 2 1)) (Dim.div d_omega_2 d_t)) := by decide
theorem eq2_e2_term4 : d_phi_1 = d_phi_2 := by decide
theorem eq2_e2_term5 : d_phi_1 = Dim.one := by decide
theorem eq2_e2_term6 : d_phi_2 = Dim.one := by decide
theorem eq2_e2_term7 : (Dim.mul (Dim.mul (Dim.mul (Dim.mul d_m_2 d_L_1) d_L_2) (Dim.pow d_omega_1 2 1)) Dim.one) = (Dim.mul (Dim.mul (Dim.mul d_m_2 d_g) d_L_2) Dim.one) := by decide

/-! ## 3. Kinematics, upper arm

    d(phi_1,t) = omega_1
-/
/-- Both sides of "Kinematics, upper arm" carry the same physical dimension. -/
theorem eq3_k1_dim : (Dim.div d_phi_1 d_t) = d_omega_1 := by decide

/-! ## 4. Kinematics, lower arm

    d(phi_2,t) = omega_2
-/
/-- Both sides of "Kinematics, lower arm" carry the same physical dimension. -/
theorem eq4_k2_dim : (Dim.div d_phi_2 d_t) = d_omega_2 := by decide

/-! ## 5. Initial upper angle

    phi_1 = theta_1
-/
/-- Both sides of "Initial upper angle" carry the same physical dimension. -/
theorem eq5_i1_dim : d_phi_1 = d_theta_1 := by decide

/-! ## 6. Initial lower angle

    phi_2 = theta_2
-/
/-- Both sides of "Initial lower angle" carry the same physical dimension. -/
theorem eq6_i2_dim : d_phi_2 = d_theta_2 := by decide

/-! ## 7. Mechanical energy

    E = 0.5*(m_1 + m_2)*L_1^2*omega_1^2 + 0.5*m_2*L_2^2*omega_2^2 + m_2*L_1*L_2*cos(phi_1 - phi_2)*omega_1*omega_2 + (m_1 + m_2)*g*L_1*(1 - cos(phi_1)) + m_2*g*L_2*(1 - cos(phi_2))
-/
/-- Both sides of "Mechanical energy" carry the same physical dimension. -/
theorem eq7_en_dim : d_E = (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_1) (Dim.pow d_L_1 2 1)) (Dim.pow d_omega_1 2 1)) := by decide
theorem eq7_en_term1 : d_m_1 = d_m_2 := by decide
theorem eq7_en_term2 : (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_1) (Dim.pow d_L_1 2 1)) (Dim.pow d_omega_1 2 1)) = (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_2) (Dim.pow d_L_2 2 1)) (Dim.pow d_omega_2 2 1)) := by decide
theorem eq7_en_term3 : d_phi_1 = d_phi_2 := by decide
theorem eq7_en_term4 : d_phi_1 = Dim.one := by decide
theorem eq7_en_term5 : (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_1) (Dim.pow d_L_1 2 1)) (Dim.pow d_omega_1 2 1)) = (Dim.mul (Dim.mul (Dim.mul (Dim.mul (Dim.mul d_m_2 d_L_1) d_L_2) Dim.one) d_omega_1) d_omega_2) := by decide
theorem eq7_en_term6 : d_m_1 = d_m_2 := by decide
theorem eq7_en_term7 : d_phi_1 = Dim.one := by decide
theorem eq7_en_term8 : Dim.one = Dim.one := by decide
theorem eq7_en_term9 : (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_1) (Dim.pow d_L_1 2 1)) (Dim.pow d_omega_1 2 1)) = (Dim.mul (Dim.mul (Dim.mul d_m_1 d_g) d_L_1) Dim.one) := by decide
theorem eq7_en_term10 : d_phi_2 = Dim.one := by decide
theorem eq7_en_term11 : Dim.one = Dim.one := by decide
theorem eq7_en_term12 : (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_1) (Dim.pow d_L_1 2 1)) (Dim.pow d_omega_1 2 1)) = (Dim.mul (Dim.mul (Dim.mul d_m_2 d_g) d_L_2) Dim.one) := by decide

/-! ## 8. Normal modes for equal masses and lengths

    omega_n^2 = (2 + sqrt(2))*g/L_1
-/
/-- Both sides of "Normal modes for equal masses and lengths" carry the same physical dimension. -/
theorem eq8_modes_dim : (Dim.pow d_omega_n 2 1) = (Dim.div (Dim.mul Dim.one d_g) d_L_1) := by decide
theorem eq8_modes_term1 : Dim.one = (Dim.pow Dim.one 1 2) := by decide
/-- The argument `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_modes_reg1  : 0 ≤ (2 : ℝ) := by positivity
/-- The denominator `L_1` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_modes_reg2 (L_1 : ℝ) (hL_1 : 0 < L_1) : L_1 ≠ 0 := by positivity

/-! ## 9. Growth of the twin separation

    d(delta_s,t) = lambda*delta_s
-/
/-- Both sides of "Growth of the twin separation" carry the same physical dimension. -/
theorem eq9_lyap_dim : (Dim.div d_delta_s d_t) = (Dim.mul d_lambda d_delta_s) := by decide

end Bespoke
