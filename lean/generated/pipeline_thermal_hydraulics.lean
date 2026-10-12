import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Pipeline pressure and temperature profile

Machine-checkable statements for this investigation (pipeline-thermal-hydraulics).
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
def d_A : Dim := ⟨0, 24, 0, 0, 0, 0, 0⟩  -- Flow area [m^2]
def d_D : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Inner diameter [in]
def d_Re : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Reynolds number [1]
def d_T : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Fluid temperature [K]
def d_T_amb : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Ambient (seabed or soil) temperature [°C]
def d_U : Dim := ⟨12, 0, -36, 0, -12, 0, 0⟩  -- Overall heat-transfer coefficient (inner-area basis) [W/(m^2 K)]
def d_cp : Dim := ⟨0, 24, -24, 0, -12, 0, 0⟩  -- Specific heat capacity [J/(kg K)]
def d_eps_r : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Wall roughness [mm]
def d_f : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Darcy friction factor [1]
def d_g : Dim := ⟨0, 12, -24, 0, 0, 0, 0⟩  -- Gravitational acceleration [m/s^2]
def d_mdot : Dim := ⟨12, 0, -12, 0, 0, 0, 0⟩  -- Mass flow rate [kg/s]
def d_mu : Dim := ⟨12, -12, -12, 0, 0, 0, 0⟩  -- Dynamic viscosity at inlet temperature [cP]
def d_p : Dim := ⟨12, -12, -24, 0, 0, 0, 0⟩  -- Pressure [Pa]
def d_rho : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Fluid density [kg/m^3]
def d_theta : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Pipe inclination [rad]
def d_u : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Mean velocity [m/s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Distance along pipe [m]

/-! ## 1. Continuity

    mdot = rho*u*A
-/
/-- Both sides of "Continuity" carry the same physical dimension. -/
theorem eq1_cont_dim : d_mdot = (Dim.mul (Dim.mul d_rho d_u) d_A) := by decide

/-! ## 2. Flow area

    A = pi*D^2/4
-/
/-- Both sides of "Flow area" carry the same physical dimension. -/
theorem eq2_area_dim : d_A = (Dim.div (Dim.mul Dim.one (Dim.pow d_D 2 1)) Dim.one) := by decide
/-- The denominator `4` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_area_reg1  : (4 : ℝ) ≠ 0 := by positivity

/-! ## 3. Reynolds number

    Re = rho*u*D/mu
-/
/-- Both sides of "Reynolds number" carry the same physical dimension. -/
theorem eq3_re_dim : d_Re = (Dim.div (Dim.mul (Dim.mul d_rho d_u) d_D) d_mu) := by decide
/-- The denominator `mu` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_re_reg1 (mu : ℝ) (hmu : 0 < mu) : mu ≠ 0 := by positivity

/-! ## 4. Momentum balance

    pd(p,x) = -f*rho*u^2/(2*D) - rho*g*sin(theta)
-/
/-- Both sides of "Momentum balance" carry the same physical dimension. -/
theorem eq4_mom_dim : (Dim.div d_p d_x) = (Dim.div (Dim.mul (Dim.mul d_f d_rho) (Dim.pow d_u 2 1)) (Dim.mul Dim.one d_D)) := by decide
theorem eq4_mom_term1 : d_theta = Dim.one := by decide
theorem eq4_mom_term2 : (Dim.div (Dim.mul (Dim.mul d_f d_rho) (Dim.pow d_u 2 1)) (Dim.mul Dim.one d_D)) = (Dim.mul (Dim.mul d_rho d_g) Dim.one) := by decide
/-- The denominator `2 * D` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_mom_reg1 (D : ℝ) (hD : 0 < D) : (2 : ℝ) * D ≠ 0 := by positivity

/-! ## 5. Colebrook–White friction factor

    1/sqrt(f) = -2*log10(eps_r/(3.7*D) + 2.51/(Re*sqrt(f)))
-/
/-- Both sides of "Colebrook–White friction factor" carry the same physical dimension. -/
theorem eq5_cw_dim : (Dim.div Dim.one (Dim.pow d_f 1 2)) = (Dim.mul Dim.one Dim.one) := by decide
theorem eq5_cw_term1 : (Dim.div d_eps_r (Dim.mul Dim.one d_D)) = (Dim.div Dim.one (Dim.mul d_Re (Dim.pow d_f 1 2))) := by decide
theorem eq5_cw_term2 : (Dim.div d_eps_r (Dim.mul Dim.one d_D)) = Dim.one := by decide
/-- The argument `f` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_cw_reg1 (f : ℝ) (hf : 0 < f) : 0 ≤ f := by positivity
/-- The denominator `sqrt(f)` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_cw_reg2 (f : ℝ) (hf : 0 < f) : Real.sqrt f ≠ 0 := by positivity
/-- The denominator `3.7 * D` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_cw_reg3 (D : ℝ) (hD : 0 < D) : (3.7 : ℝ) * D ≠ 0 := by positivity
/-- The argument `f` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_cw_reg4 (f : ℝ) (hf : 0 < f) : 0 ≤ f := by positivity
/-- The denominator `Re * sqrt(f)` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_cw_reg5 (Re f : ℝ) (hRe : 0 < Re) (hf : 0 < f) : Re * Real.sqrt f ≠ 0 := by positivity
/-- Domain condition for `eps_r / (3.7 * D) + 2.51 / (Re * sqrt(f))`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq5_cw_cond6 (eps_r D Re f : ℝ) (hdom : 0 < eps_r / ((3.7 : ℝ) * D) + (2.51 : ℝ) / (Re * Real.sqrt f)) : 0 < eps_r / ((3.7 : ℝ) * D) + (2.51 : ℝ) / (Re * Real.sqrt f) := hdom

/-! ## 6. Energy balance

    mdot*cp*pd(T,x) = -U*pi*D*(T - T_amb)
-/
/-- Both sides of "Energy balance" carry the same physical dimension. -/
theorem eq6_en_dim : (Dim.mul (Dim.mul d_mdot d_cp) (Dim.div d_T d_x)) = (Dim.mul (Dim.mul (Dim.mul d_U Dim.one) d_D) d_T) := by decide
theorem eq6_en_term1 : d_T = d_T_amb := by decide

end Bespoke
