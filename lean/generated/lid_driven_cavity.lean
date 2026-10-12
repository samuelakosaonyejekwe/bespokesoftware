import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Lid-driven cavity flow

Machine-checkable statements for this investigation (lid-driven-cavity).
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
def d_L : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Cavity side length [m]
def d_Re : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Reynolds number U L/ν [1]
def d_U_l : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Lid speed [m/s]
def d_U_w : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Tangential wall speed [m/s]
def d_h_g : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Grid spacing [m]
def d_nu : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Kinematic viscosity [m^2/s]
def d_omega : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Vorticity [1/s]
def d_omega_w : Dim := ⟨0, 0, -12, 0, 0, 0, 0⟩  -- Wall vorticity [1/s]
def d_psi : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Streamfunction [m^2/s]
def d_psi_1 : Dim := ⟨0, 24, -12, 0, 0, 0, 0⟩  -- Streamfunction one node in from the wall [m^2/s]
def d_u : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Horizontal velocity [m/s]
def d_v : Dim := ⟨0, 12, -12, 0, 0, 0, 0⟩  -- Vertical velocity [m/s]
def d_x : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Horizontal coordinate [m]
def d_y : Dim := ⟨0, 12, 0, 0, 0, 0, 0⟩  -- Vertical coordinate [m]

/-! ## 1. Reynolds number

    Re = U_l*L/nu
-/
/-- Both sides of "Reynolds number" carry the same physical dimension. -/
theorem eq1_re_dim : d_Re = (Dim.div (Dim.mul d_U_l d_L) d_nu) := by decide
/-- The denominator `nu` stays away from its singular set whenever the quantities are positive. -/
theorem eq1_re_reg1 (nu : ℝ) (hnu : 0 < nu) : nu ≠ 0 := by positivity

/-! ## 2. Horizontal velocity

    u = pd(psi,y)
-/
/-- Both sides of "Horizontal velocity" carry the same physical dimension. -/
theorem eq2_u_dim : d_u = (Dim.div d_psi d_y) := by decide

/-! ## 3. Vertical velocity

    v = -pd(psi,x)
-/
/-- Both sides of "Vertical velocity" carry the same physical dimension. -/
theorem eq3_v_dim : d_v = (Dim.div d_psi d_x) := by decide

/-! ## 4. Streamfunction equation

    lap(psi) = -omega
-/
/-- Both sides of "Streamfunction equation" carry the same physical dimension. -/
theorem eq4_poisson_dim : (Dim.div d_psi (Dim.pow d_length 2 1)) = d_omega := by decide

/-! ## 5. Vorticity transport

    u*pd(omega,x) + v*pd(omega,y) = nu*lap(omega)
-/
/-- Both sides of "Vorticity transport" carry the same physical dimension. -/
theorem eq5_vort_dim : (Dim.mul d_u (Dim.div d_omega d_x)) = (Dim.mul d_nu (Dim.div d_omega (Dim.pow d_length 2 1))) := by decide
theorem eq5_vort_term1 : (Dim.mul d_u (Dim.div d_omega d_x)) = (Dim.mul d_v (Dim.div d_omega d_y)) := by decide

/-! ## 6. Wall vorticity

    omega_w = -2*psi_1/h_g^2 - 2*U_w/h_g
-/
/-- Both sides of "Wall vorticity" carry the same physical dimension. -/
theorem eq6_wall_dim : d_omega_w = (Dim.div (Dim.mul Dim.one d_psi_1) (Dim.pow d_h_g 2 1)) := by decide
theorem eq6_wall_term1 : (Dim.div (Dim.mul Dim.one d_psi_1) (Dim.pow d_h_g 2 1)) = (Dim.div (Dim.mul Dim.one d_U_w) d_h_g) := by decide
/-- Domain condition for `h_g^2`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_wall_cond1 (h_g : ℝ) (hdom : h_g ^ 2 ≠ 0) : h_g ^ 2 ≠ 0 := hdom
/-- Domain condition for `h_g`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_wall_cond2 (h_g : ℝ) (hdom : h_g ≠ 0) : h_g ≠ 0 := hdom

end Bespoke
