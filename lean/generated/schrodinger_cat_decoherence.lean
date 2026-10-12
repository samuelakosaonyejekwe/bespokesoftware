import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Schrödinger's cat and environmental decoherence

Machine-checkable statements for this investigation (schrodinger-cat-decoherence).
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
def d_Gamma : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Decoherence rate [1/s]
def d_Lambda_a : Dim := ⟨0, -24, -12, 0, 0, 0, 0⟩  -- Localisation rate from gas collisions [1/(m^2 s)]
def d_Lambda_d : Dim := ⟨0, -24, -12, 0, 0, 0, 0⟩  -- Photon localisation rate of a sphere small compared with the thermal wavelength [1/(m^2 s)]
def d_Lambda_g : Dim := ⟨0, -24, -12, 0, 0, 0, 0⟩  -- Photon localisation rate of a sphere large compared with the thermal wavelength [1/(m^2 s)]
def d_Lambda_p : Dim := ⟨0, -24, -12, 0, 0, 0, 0⟩  -- Localisation rate from thermal photons [1/(m^2 s)]
def d_T : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Temperature of gas and radiation [K]
def d_a : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Radius of the object [um]
def d_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Speed of light [m/s]
def d_dx : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Separation between the two branches of the superposition [nm]
def d_hbar : Dim := ⟨12, 24, -12, 0, 0, 0, 0⟩  -- Reduced Planck constant [J s]
def d_k_B : Dim := ⟨12, 24, -24, 0, -12, 0, 0⟩  -- Boltzmann constant [J/K]
def d_l_air : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Separation at which gas collisions saturate [m]
def d_l_ph : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Separation at which photon scattering saturates [m]
def d_m_g : Dim := ⟨12, 0, 0, 0, 0, 0, 0⟩  -- Mass of a gas molecule [u]
def d_n_g : Dim := ⟨0, -36, 0, 0, 0, 0, 0⟩  -- Number density of the gas [1/m^3]
def d_p : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Gas pressure [Pa]
def d_rho_c : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Off-diagonal element of the density matrix [1]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_tau_D : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Decoherence time [s]
def d_zeta_3 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Riemann zeta function at 3 [1]
def d_zeta_5 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Riemann zeta function at 5 [1]
def d_zeta_9 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Riemann zeta function at 9 [1]

/-! ## 1. Decay of the interference term

    d(rho_c,t) = -Gamma*rho_c
-/
/-- Both sides of "Decay of the interference term" carry the same physical dimension. -/
theorem eq1_rho_dim : (Dim.div d_rho_c d_t) = (Dim.mul d_Gamma d_rho_c) := by decide

/-! ## 2. Gas number density

    n_g = p/(k_B*T)
-/
/-- Both sides of "Gas number density" carry the same physical dimension. -/
theorem eq2_ng_dim : d_n_g = (Dim.div d_p (Dim.mul d_k_B d_T)) := by decide
/-- The denominator `k_B * T` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_ng_reg1 (k_B T : ℝ) (hk_B : 0 < k_B) (hT : 0 < T) : k_B * T ≠ 0 := by positivity

/-! ## 3. Localisation rate from gas collisions

    Lambda_a = 8/(3*hbar^2)*n_g*sqrt(2*pi*m_g)*a^2*(k_B*T)^(3/2)
-/
/-- Both sides of "Localisation rate from gas collisions" carry the same physical dimension. -/
theorem eq3_la_dim : d_Lambda_a = (Dim.mul (Dim.mul (Dim.mul (Dim.mul (Dim.div Dim.one (Dim.mul Dim.one (Dim.pow d_hbar 2 1))) d_n_g) (Dim.pow (Dim.mul (Dim.mul Dim.one Dim.one) d_m_g) 1 2)) (Dim.pow d_a 2 1)) (Dim.pow (Dim.mul d_k_B d_T) 3 2)) := by decide
/-- The denominator `3 * hbar^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_la_reg1 (hbar : ℝ) (hhbar : 0 < hbar) : (3 : ℝ) * hbar ^ 2 ≠ 0 := by positivity
/-- The argument `2 * pi * m_g` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_la_reg2 (m_g : ℝ) (hm_g : 0 < m_g) : 0 ≤ (2 : ℝ) * Real.pi * m_g := by positivity
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_la_reg3  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 4. Riemann zeta function at 9

    zeta_9 = 1.0020083928
-/
/-- Both sides of "Riemann zeta function at 9" carry the same physical dimension. -/
theorem eq4_z9_dim : d_zeta_9 = Dim.one := by decide

/-! ## 5. Riemann zeta function at 5

    zeta_5 = 1.0369277551
-/
/-- Both sides of "Riemann zeta function at 5" carry the same physical dimension. -/
theorem eq5_z5_dim : d_zeta_5 = Dim.one := by decide

/-! ## 6. Photon localisation rate, small sphere

    Lambda_d = 8*40320*zeta_9*c*a^6/(9*pi)*(k_B*T/(hbar*c))^9
-/
/-- Both sides of "Photon localisation rate, small sphere" carry the same physical dimension. -/
theorem eq6_ld_dim : d_Lambda_d = (Dim.mul (Dim.div (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one Dim.one) d_zeta_9) d_c) (Dim.pow d_a 6 1)) (Dim.mul Dim.one Dim.one)) (Dim.pow (Dim.div (Dim.mul d_k_B d_T) (Dim.mul d_hbar d_c)) 9 1)) := by decide
/-- The denominator `9 * pi` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_ld_reg1  : (9 : ℝ) * Real.pi ≠ 0 := by positivity
/-- The denominator `hbar * c` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_ld_reg2 (hbar c : ℝ) (hhbar : 0 < hbar) (hc : 0 < c) : hbar * c ≠ 0 := by positivity

/-! ## 7. Photon localisation rate, large sphere

    Lambda_g = 8*zeta_5*c*a^2/pi*(k_B*T/(hbar*c))^5
-/
/-- Both sides of "Photon localisation rate, large sphere" carry the same physical dimension. -/
theorem eq7_lg_dim : d_Lambda_g = (Dim.mul (Dim.div (Dim.mul (Dim.mul (Dim.mul Dim.one d_zeta_5) d_c) (Dim.pow d_a 2 1)) Dim.one) (Dim.pow (Dim.div (Dim.mul d_k_B d_T) (Dim.mul d_hbar d_c)) 5 1)) := by decide
/-- The denominator `pi` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_lg_reg1  : Real.pi ≠ 0 := by positivity
/-- The denominator `hbar * c` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_lg_reg2 (hbar c : ℝ) (hhbar : 0 < hbar) (hc : 0 < c) : hbar * c ≠ 0 := by positivity

/-! ## 8. Localisation rate from thermal photons

    Lambda_p = Lambda_d*Lambda_g/(Lambda_d + Lambda_g)
-/
/-- Both sides of "Localisation rate from thermal photons" carry the same physical dimension. -/
theorem eq8_lp_dim : d_Lambda_p = (Dim.div (Dim.mul d_Lambda_d d_Lambda_g) d_Lambda_d) := by decide
theorem eq8_lp_term1 : d_Lambda_d = d_Lambda_g := by decide
/-- The denominator `Lambda_d + Lambda_g` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_lp_reg1 (Lambda_d Lambda_g : ℝ) (hLambda_d : 0 < Lambda_d) (hLambda_g : 0 < Lambda_g) : Lambda_d + Lambda_g ≠ 0 := by positivity

/-! ## 9. Separation at which gas collisions saturate

    l_air = hbar*sqrt(3/(4*m_g*k_B*T))
-/
/-- Both sides of "Separation at which gas collisions saturate" carry the same physical dimension. -/
theorem eq9_lair_dim : d_l_air = (Dim.mul d_hbar (Dim.pow (Dim.div Dim.one (Dim.mul (Dim.mul (Dim.mul Dim.one d_m_g) d_k_B) d_T)) 1 2)) := by decide
/-- The denominator `4 * m_g * k_B * T` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_lair_reg1 (m_g k_B T : ℝ) (hm_g : 0 < m_g) (hk_B : 0 < k_B) (hT : 0 < T) : (4 : ℝ) * m_g * k_B * T ≠ 0 := by positivity
/-- The argument `3 / (4 * m_g * k_B * T)` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_lair_reg2 (m_g k_B T : ℝ) (hm_g : 0 < m_g) (hk_B : 0 < k_B) (hT : 0 < T) : 0 ≤ (3 : ℝ) / ((4 : ℝ) * m_g * k_B * T) := by positivity

/-! ## 10. Riemann zeta function at 3

    zeta_3 = 1.2020569032
-/
/-- Both sides of "Riemann zeta function at 3" carry the same physical dimension. -/
theorem eq10_z3_dim : d_zeta_3 = Dim.one := by decide

/-! ## 11. Separation at which photon scattering saturates

    l_ph = sqrt(zeta_3/(4*zeta_5))*hbar*c/(k_B*T)
-/
/-- Both sides of "Separation at which photon scattering saturates" carry the same physical dimension. -/
theorem eq11_lph_dim : d_l_ph = (Dim.div (Dim.mul (Dim.mul (Dim.pow (Dim.div d_zeta_3 (Dim.mul Dim.one d_zeta_5)) 1 2) d_hbar) d_c) (Dim.mul d_k_B d_T)) := by decide
/-- Domain condition for `4 * zeta_5`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq11_lph_cond1 (zeta_5 : ℝ) (hdom : (4 : ℝ) * zeta_5 ≠ 0) : (4 : ℝ) * zeta_5 ≠ 0 := hdom
/-- Domain condition for `zeta_3 / (4 * zeta_5)`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq11_lph_cond2 (zeta_3 zeta_5 : ℝ) (hdom : 0 ≤ zeta_3 / ((4 : ℝ) * zeta_5)) : 0 ≤ zeta_3 / ((4 : ℝ) * zeta_5) := hdom
/-- The denominator `k_B * T` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_lph_reg3 (k_B T : ℝ) (hk_B : 0 < k_B) (hT : 0 < T) : k_B * T ≠ 0 := by positivity

/-! ## 12. Decoherence rate with saturation

    Gamma = Lambda_a*dx^2/(1 + dx^2/l_air^2) + Lambda_p*dx^2/(1 + dx^2/l_ph^2)
-/
/-- Both sides of "Decoherence rate with saturation" carry the same physical dimension. -/
theorem eq12_gam_dim : d_Gamma = (Dim.div (Dim.mul d_Lambda_a (Dim.pow d_dx 2 1)) Dim.one) := by decide
theorem eq12_gam_term1 : Dim.one = (Dim.div (Dim.pow d_dx 2 1) (Dim.pow d_l_air 2 1)) := by decide
theorem eq12_gam_term2 : Dim.one = (Dim.div (Dim.pow d_dx 2 1) (Dim.pow d_l_ph 2 1)) := by decide
theorem eq12_gam_term3 : (Dim.div (Dim.mul d_Lambda_a (Dim.pow d_dx 2 1)) Dim.one) = (Dim.div (Dim.mul d_Lambda_p (Dim.pow d_dx 2 1)) Dim.one) := by decide
/-- The denominator `l_air^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq12_gam_reg1 (l_air : ℝ) (hl_air : 0 < l_air) : l_air ^ 2 ≠ 0 := by positivity
/-- The denominator `1 + dx^2 / l_air^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq12_gam_reg2 (dx l_air : ℝ) (hdx : 0 < dx) (hl_air : 0 < l_air) : (1 : ℝ) + dx ^ 2 / l_air ^ 2 ≠ 0 := by positivity
/-- The denominator `l_ph^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq12_gam_reg3 (l_ph : ℝ) (hl_ph : 0 < l_ph) : l_ph ^ 2 ≠ 0 := by positivity
/-- The denominator `1 + dx^2 / l_ph^2` stays away from its singular set whenever the quantities are positive. -/
theorem eq12_gam_reg4 (dx l_ph : ℝ) (hdx : 0 < dx) (hl_ph : 0 < l_ph) : (1 : ℝ) + dx ^ 2 / l_ph ^ 2 ≠ 0 := by positivity

/-! ## 13. Decoherence time

    tau_D = 1/Gamma
-/
/-- Both sides of "Decoherence time" carry the same physical dimension. -/
theorem eq13_tau_dim : d_tau_D = (Dim.div Dim.one d_Gamma) := by decide
/-- The denominator `Gamma` stays away from its singular set whenever the quantities are positive. -/
theorem eq13_tau_reg1 (Gamma : ℝ) (hGamma : 0 < Gamma) : Gamma ≠ 0 := by positivity

/-! ## Logical structure of the argument -/

/-- The conclusion follows from the premises in classical propositional logic. -/
theorem argument_valid (C D M O U : Prop) (h1 : U → D) (h2 : D → M) (h3 : (M ∧ C) → O) (h4 : U) : M ∧ (C → O) := by tauto

end Bespoke
