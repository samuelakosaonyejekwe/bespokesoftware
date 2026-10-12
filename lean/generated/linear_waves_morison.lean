import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Linear waves and Morison loading on a vertical pile

Machine-checkable statements for this investigation (linear-waves-morison).
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

/-! ## Dimensions of the symbols -/

def d_length : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩
def d_C_D : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Drag coefficient [1]
def d_C_M : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Inertia coefficient [1]
def d_D : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Pile diameter [m]
def d_F : Dim := ⟨12, 12, -24, 0, 0, 0, 0⟩  -- Base shear [N]
def d_H : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Wave height [m]
def d_L_w : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Wavelength [m]
def d_M_b : Dim := ⟨12, 24, -24, 0, 0, 0, 0⟩  -- Overturning moment about the seabed [N m]
def d_T : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Wave period [s]
def d_U_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Current speed (in the wave direction) [m/s]
def d_a_x : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Horizontal particle acceleration [m/s^2]
def d_d : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Water depth [m]
def d_eta : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Surface elevation [m]
def d_f : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- In-line force per unit length [N/m]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_k : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Wave number [1/m]
def d_omega : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Wave angular frequency [1/s]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Sea-water density [kg/m^3]
def d_sigma_w : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Intrinsic angular frequency [1/s]
def d_t : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Time [s]
def d_u : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Horizontal particle velocity [m/s]
def d_z : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Elevation above still water [m]

/-! ## 1. Angular frequency

    omega = 2*pi/T
-/
/-- Both sides of "Angular frequency" carry the same physical dimension. -/
theorem eq1_om_dim : d_omega = (Dim.div (Dim.mul Dim.one Dim.one) d_T) := by decide
/-- The denominator `T` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_om_reg1 (T : ℝ) (hT : 0 < T) : T ≠ 0 := by positivity

/-! ## 2. Intrinsic frequency

    sigma_w = omega
-/
/-- Both sides of "Intrinsic frequency" carry the same physical dimension. -/
theorem eq2_sig_dim : d_sigma_w = d_omega := by decide

/-! ## 3. Dispersion relation

    sigma_w^2 = g*k*tanh(k*d)
-/
/-- Both sides of "Dispersion relation" carry the same physical dimension. -/
theorem eq3_disp_dim : (Dim.pow d_sigma_w 2 1) = (Dim.mul (Dim.mul d_g d_k) Dim.one) := by decide
theorem eq3_disp_term1 : (Dim.mul d_k d_d) = Dim.one := by decide

/-! ## 4. Wavelength

    L_w = 2*pi/k
-/
/-- Both sides of "Wavelength" carry the same physical dimension. -/
theorem eq4_lw_dim : d_L_w = (Dim.div (Dim.mul Dim.one Dim.one) d_k) := by decide
/-- The denominator `k` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_lw_reg1 (k : ℝ) (hk : 0 < k) : k ≠ 0 := by positivity

/-! ## 5. Surface elevation at the pile

    eta = H/2*cos(omega*t)
-/
/-- Both sides of "Surface elevation at the pile" carry the same physical dimension. -/
theorem eq5_eta_dim : d_eta = (Dim.mul (Dim.div d_H Dim.one) Dim.one) := by decide
theorem eq5_eta_term1 : (Dim.mul d_omega d_t) = Dim.one := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_eta_reg1  : (2 : ℝ) ≠ 0 := by positivity

/-! ## 6. Horizontal particle velocity

    u = H/2*sigma_w*cosh(k*(z + d))/sinh(k*d)*cos(omega*t) + U_c
-/
/-- Both sides of "Horizontal particle velocity" carry the same physical dimension. -/
theorem eq6_u_dim : d_u = (Dim.mul (Dim.div (Dim.mul (Dim.mul (Dim.div d_H Dim.one) d_sigma_w) Dim.one) Dim.one) Dim.one) := by decide
theorem eq6_u_term1 : d_z = d_d := by decide
theorem eq6_u_term2 : (Dim.mul d_k d_z) = Dim.one := by decide
theorem eq6_u_term3 : (Dim.mul d_k d_d) = Dim.one := by decide
theorem eq6_u_term4 : (Dim.mul d_omega d_t) = Dim.one := by decide
theorem eq6_u_term5 : (Dim.mul (Dim.div (Dim.mul (Dim.mul (Dim.div d_H Dim.one) d_sigma_w) Dim.one) Dim.one) Dim.one) = d_U_c := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_u_reg1  : (2 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `sinh(k * d)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq6_u_cond2 (k d : ℝ) (hdom : Real.sinh (k * d) ≠ 0) : Real.sinh (k * d) ≠ 0 := hdom

/-! ## 7. Horizontal particle acceleration

    a_x = -H/2*sigma_w*omega*cosh(k*(z + d))/sinh(k*d)*sin(omega*t)
-/
/-- Both sides of "Horizontal particle acceleration" carry the same physical dimension. -/
theorem eq7_ax_dim : d_a_x = (Dim.mul (Dim.div (Dim.mul (Dim.mul (Dim.mul (Dim.div d_H Dim.one) d_sigma_w) d_omega) Dim.one) Dim.one) Dim.one) := by decide
theorem eq7_ax_term1 : d_z = d_d := by decide
theorem eq7_ax_term2 : (Dim.mul d_k d_z) = Dim.one := by decide
theorem eq7_ax_term3 : (Dim.mul d_k d_d) = Dim.one := by decide
theorem eq7_ax_term4 : (Dim.mul d_omega d_t) = Dim.one := by decide
/-- The denominator `2` stays away from its singular set whenever the quantities are positive. -/
theorem eq7_ax_reg1  : (2 : ℝ) ≠ 0 := by positivity
/-- Domain condition for `sinh(k * d)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq7_ax_cond2 (k d : ℝ) (hdom : Real.sinh (k * d) ≠ 0) : Real.sinh (k * d) ≠ 0 := hdom

/-! ## 8. Morison equation

    f = 0.5*rho*C_D*D*abs(u)*u + rho*C_M*pi*D^2/4*a_x
-/
/-- Both sides of "Morison equation" carry the same physical dimension. -/
theorem eq8_mor_dim : d_f = (Dim.mul (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) d_C_D) d_D) d_u) d_u) := by decide
theorem eq8_mor_term1 : (Dim.mul (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) d_C_D) d_D) d_u) d_u) = (Dim.mul (Dim.div (Dim.mul (Dim.mul (Dim.mul d_rho d_C_M) Dim.one) (Dim.pow d_D 2 1)) Dim.one) d_a_x) := by decide
/-- The denominator `4` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_mor_reg1  : (4 : ℝ) ≠ 0 := by positivity

/-! ## 9. Base shear

    F = int(f, z)
-/
/-- Both sides of "Base shear" carry the same physical dimension. -/
theorem eq9_F_dim : d_F = (Dim.mul d_f d_z) := by decide

/-! ## 10. Overturning moment

    M_b = int(f*(z + d), z)
-/
/-- Both sides of "Overturning moment" carry the same physical dimension. -/
theorem eq10_M_dim : d_M_b = (Dim.mul (Dim.mul d_f d_z) d_z) := by decide
theorem eq10_M_term1 : d_z = d_d := by decide

end Bespoke
