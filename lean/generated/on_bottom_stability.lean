import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# On-bottom stability of a subsea pipeline

Machine-checkable statements for this investigation (on-bottom-stability).
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
def d_A_c : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Concrete cross-section [m^2]
def d_A_i : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Bore area [m^2]
def d_A_s : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Steel cross-section [m^2]
def d_C_D : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Drag coefficient [1]
def d_C_L : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Lift coefficient [1]
def d_C_M : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Inertia coefficient [1]
def d_D_h : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Hydrodynamic outer diameter [m]
def d_D_s : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Steel outer diameter [mm]
def d_F_D : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Drag force per unit length [N/m]
def d_F_I : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Inertia force per unit length [N/m]
def d_F_L : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Lift force per unit length [N/m]
def d_H : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Design wave height [m]
def d_SF : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Factor of safety against sliding [1]
def d_T : Dim := ⟨0, 0, 12, 0, 0, 0, 0⟩  -- Wave period [s]
def d_U_c : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Current speed perpendicular to the pipe [m/s]
def d_U_e : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Effective current over the pipe [m/s]
def d_a_w : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Near-bed orbital acceleration amplitude [m/s^2]
def d_d : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Water depth [m]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_gamma_sc : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Safety factor on hydrodynamic load [1]
def d_k : Dim := ⟨0, -12, 0, 0, 0, 0, 0⟩  -- Wave number [1/m]
def d_mu_s : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Pipe–soil friction coefficient [1]
def d_omega : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Wave angular frequency [1/s]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Sea-water density [kg/m^3]
def d_rho_c : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Concrete density [kg/m^3]
def d_rho_i : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Density of pipe contents [kg/m^3]
def d_rho_s : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Steel density [kg/m^3]
def d_t_c : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Concrete coating thickness [mm]
def d_theta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Wave phase [rad]
def d_u_w : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Near-bed orbital velocity amplitude [m/s]
def d_w_req : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Required submerged weight per unit length [N/m]
def d_w_s : Dim := ⟨12, 0, -24, 0, 0, 0, 0⟩  -- Submerged weight per unit length [N/m]

/-! ## 1. Angular frequency

    omega = 2*pi/T
-/
/-- Both sides of "Angular frequency" carry the same physical dimension. -/
theorem eq1_om_dim : d_omega = (Dim.div (Dim.mul Dim.one Dim.one) d_T) := by decide
/-- The denominator `T` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_om_reg1 (T : ℝ) (hT : 0 < T) : T ≠ 0 := by positivity

/-! ## 2. Dispersion relation

    omega^2 = g*k*tanh(k*d)
-/
/-- Both sides of "Dispersion relation" carry the same physical dimension. -/
theorem eq2_disp_dim : (Dim.pow d_omega 2 1) = (Dim.mul (Dim.mul d_g d_k) Dim.one) := by decide
theorem eq2_disp_term1 : (Dim.mul d_k d_d) = Dim.one := by decide

/-! ## 3. Near-bed orbital velocity

    u_w = pi*H/(T*sinh(k*d))
-/
/-- Both sides of "Near-bed orbital velocity" carry the same physical dimension. -/
theorem eq3_uw_dim : d_u_w = (Dim.div (Dim.mul Dim.one d_H) (Dim.mul d_T Dim.one)) := by decide
theorem eq3_uw_term1 : (Dim.mul d_k d_d) = Dim.one := by decide
/-- Domain condition for `T * sinh(k * d)`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq3_uw_cond1 (T k d : ℝ) (hdom : T * Real.sinh (k * d) ≠ 0) : T * Real.sinh (k * d) ≠ 0 := hdom

/-! ## 4. Near-bed orbital acceleration

    a_w = omega*u_w
-/
/-- Both sides of "Near-bed orbital acceleration" carry the same physical dimension. -/
theorem eq4_aw_dim : d_a_w = (Dim.mul d_omega d_u_w) := by decide

/-! ## 5. Hydrodynamic diameter

    D_h = D_s + 2*t_c
-/
/-- Both sides of "Hydrodynamic diameter" carry the same physical dimension. -/
theorem eq5_dh_dim : d_D_h = d_D_s := by decide
theorem eq5_dh_term1 : d_D_s = (Dim.mul Dim.one d_t_c) := by decide

/-! ## 6. Effective current

    U_e = U_c
-/
/-- Both sides of "Effective current" carry the same physical dimension. -/
theorem eq6_ue_dim : d_U_e = d_U_c := by decide

/-! ## 7. Drag force

    F_D = 0.5*rho*D_h*C_D*abs(u_w*cos(theta) + U_e)*(u_w*cos(theta) + U_e)
-/
/-- Both sides of "Drag force" carry the same physical dimension. -/
theorem eq7_fd_dim : d_F_D = (Dim.mul (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) d_D_h) d_C_D) (Dim.mul d_u_w Dim.one)) (Dim.mul d_u_w Dim.one)) := by decide
theorem eq7_fd_term1 : d_theta = Dim.one := by decide
theorem eq7_fd_term2 : (Dim.mul d_u_w Dim.one) = d_U_e := by decide
theorem eq7_fd_term3 : d_theta = Dim.one := by decide
theorem eq7_fd_term4 : (Dim.mul d_u_w Dim.one) = d_U_e := by decide

/-! ## 8. Inertia force

    F_I = -pi*rho*D_h^2/4*C_M*a_w*sin(theta)
-/
/-- Both sides of "Inertia force" carry the same physical dimension. -/
theorem eq8_fi_dim : d_F_I = (Dim.mul (Dim.mul (Dim.mul (Dim.div (Dim.mul (Dim.mul Dim.one d_rho) (Dim.pow d_D_h 2 1)) Dim.one) d_C_M) d_a_w) Dim.one) := by decide
theorem eq8_fi_term1 : d_theta = Dim.one := by decide
/-- The denominator `4` stays away from its singular set whenever the quantities are positive. -/
theorem eq8_fi_reg1  : (4 : ℝ) ≠ 0 := by positivity

/-! ## 9. Lift force

    F_L = 0.5*rho*D_h*C_L*(u_w*cos(theta) + U_e)^2
-/
/-- Both sides of "Lift force" carry the same physical dimension. -/
theorem eq9_fl_dim : d_F_L = (Dim.mul (Dim.mul (Dim.mul (Dim.mul Dim.one d_rho) d_D_h) d_C_L) (Dim.pow (Dim.mul d_u_w Dim.one) 2 1)) := by decide
theorem eq9_fl_term1 : d_theta = Dim.one := by decide
theorem eq9_fl_term2 : (Dim.mul d_u_w Dim.one) = d_U_e := by decide

/-! ## 10. Submerged weight

    w_s = g*(rho_s*A_s + rho_i*A_i + rho_c*A_c - rho*pi*D_h^2/4)
-/
/-- Both sides of "Submerged weight" carry the same physical dimension. -/
theorem eq10_ws_dim : d_w_s = (Dim.mul d_g (Dim.mul d_rho_s d_A_s)) := by decide
theorem eq10_ws_term1 : (Dim.mul d_rho_s d_A_s) = (Dim.mul d_rho_i d_A_i) := by decide
theorem eq10_ws_term2 : (Dim.mul d_rho_s d_A_s) = (Dim.mul d_rho_c d_A_c) := by decide
theorem eq10_ws_term3 : (Dim.mul d_rho_s d_A_s) = (Dim.div (Dim.mul (Dim.mul d_rho Dim.one) (Dim.pow d_D_h 2 1)) Dim.one) := by decide
/-- The denominator `4` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_ws_reg1  : (4 : ℝ) ≠ 0 := by positivity

/-! ## 11. Required submerged weight

    w_req = gamma_sc*(abs(F_D + F_I)/mu_s + F_L)
-/
/-- Both sides of "Required submerged weight" carry the same physical dimension. -/
theorem eq11_req_dim : d_w_req = (Dim.mul d_gamma_sc (Dim.div d_F_D d_mu_s)) := by decide
theorem eq11_req_term1 : d_F_D = d_F_I := by decide
theorem eq11_req_term2 : (Dim.div d_F_D d_mu_s) = d_F_L := by decide
/-- The denominator `mu_s` stays away from its singular set whenever the quantities are positive. -/
theorem eq11_req_reg1 (mu_s : ℝ) (hmu_s : 0 < mu_s) : mu_s ≠ 0 := by positivity

/-! ## 12. Factor of safety against sliding

    SF = (mu_s*w_s)/(abs(F_D + F_I) + mu_s*F_L)
-/
/-- Both sides of "Factor of safety against sliding" carry the same physical dimension. -/
theorem eq12_sf_dim : d_SF = (Dim.div (Dim.mul d_mu_s d_w_s) d_F_D) := by decide
theorem eq12_sf_term1 : d_F_D = d_F_I := by decide
theorem eq12_sf_term2 : d_F_D = (Dim.mul d_mu_s d_F_L) := by decide
/-- Domain condition for `abs(F_D + F_I) + mu_s * F_L`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq12_sf_cond1 (F_D F_I mu_s F_L : ℝ) (hdom : abs (F_D + F_I) + mu_s * F_L ≠ 0) : abs (F_D + F_I) + mu_s * F_L ≠ 0 := hdom

end Bespoke
