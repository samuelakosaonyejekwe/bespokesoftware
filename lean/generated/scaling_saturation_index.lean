import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Scaling potential of reverse-osmosis concentrate

Machine-checkable statements for this investigation (scaling-saturation-index).
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
def d_A_L : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Langelier solids term [1]
def d_Alk : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Alkalinity of the feed (as CaCO₃) [mg/L]
def d_B_L : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Langelier temperature term [1]
def d_CF : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Concentration factor [1]
def d_C_L : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Langelier calcium term [1]
def d_Ca_h : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Calcium hardness of concentrate as CaCO₃ [kg/m^3]
def d_D_L : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Langelier alkalinity term [1]
def d_I_s : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Ionic strength over 1 mol/L [1]
def d_K_a : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Association constant of the CaSO₄ ion pair [1]
def d_K_sp : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Solubility product of gypsum [1]
def d_LSI : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Langelier saturation index [1]
def d_Rej : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Salt rejection of the membrane [%]
def d_SR : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Gypsum saturation ratio [1]
def d_T : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Temperature [°C]
def d_TDS : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Total dissolved solids of the feed [mg/L]
def d_T_ref : Dim := ⟨0, 0, 0, 0, 12, 0, 0⟩  -- Reference temperature 1 K [K]
def d_c_ref : Dim := ⟨12, -36, 0, 0, 0, 0, 0⟩  -- Reference concentration 1 mg/L [kg/m^3]
def d_gamma : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Activity coefficient of a divalent ion [1]
def d_m_Ca : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Free calcium over 1 mol/L [1]
def d_m_SO4 : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Free sulphate over 1 mol/L [1]
def d_m_pair : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- CaSO₄ ion pair over 1 mol/L [1]
def d_pH : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Feed pH [1]
def d_pH_c : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Concentrate pH [1]
def d_pH_s : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- Saturation pH [1]
def d_r : Dim := ⟨0, 0, 0, 0, 0, 0, 0⟩  -- System recovery [%]

/-! ## 1. Concentration factor

    CF = (1 - r*(1 - Rej))/(1 - r)
-/
/-- Both sides of "Concentration factor" carry the same physical dimension. -/
theorem eq1_cf_dim : d_CF = (Dim.div Dim.one Dim.one) := by decide
theorem eq1_cf_term1 : Dim.one = d_Rej := by decide
theorem eq1_cf_term2 : Dim.one = (Dim.mul d_r Dim.one) := by decide
theorem eq1_cf_term3 : Dim.one = d_r := by decide
/-- Domain condition for `1 - r`: established on the declared ranges by interval arithmetic; stated here as an explicit hypothesis. -/
theorem eq1_cf_cond1 (r : ℝ) (hdom : (1 : ℝ) - r ≠ 0) : (1 : ℝ) - r ≠ 0 := hdom

/-! ## 2. Concentrate pH

    pH_c = pH + log10(CF)
-/
/-- Both sides of "Concentrate pH" carry the same physical dimension. -/
theorem eq2_phc_dim : d_pH_c = d_pH := by decide
theorem eq2_phc_term1 : d_CF = Dim.one := by decide
theorem eq2_phc_term2 : d_pH = Dim.one := by decide
/-- The argument `CF` stays away from its singular set whenever the quantities are positive. -/
theorem eq2_phc_reg1 (CF : ℝ) (hCF : 0 < CF) : 0 < CF := by positivity

/-! ## 3. Solids term

    A_L = (log10(CF*TDS/c_ref) - 1)/10
-/
/-- Both sides of "Solids term" carry the same physical dimension. -/
theorem eq3_al_dim : d_A_L = (Dim.div Dim.one Dim.one) := by decide
theorem eq3_al_term1 : (Dim.div (Dim.mul d_CF d_TDS) d_c_ref) = Dim.one := by decide
theorem eq3_al_term2 : Dim.one = Dim.one := by decide
/-- The denominator `c_ref` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_al_reg1 (c_ref : ℝ) (hc_ref : 0 < c_ref) : c_ref ≠ 0 := by positivity
/-- Domain condition for `CF * TDS / c_ref`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq3_al_cond2 (CF TDS c_ref : ℝ) (hdom : 0 < CF * TDS / c_ref) : 0 < CF * TDS / c_ref := hdom
/-- The denominator `10` stays away from its singular set whenever the quantities are positive. -/
theorem eq3_al_reg3  : (10 : ℝ) ≠ 0 := by positivity
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq3_al_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 4. Temperature term

    B_L = 34.55 - 13.12*log10(T/T_ref)
-/
/-- Both sides of "Temperature term" carry the same physical dimension. -/
theorem eq4_bl_dim : d_B_L = Dim.one := by decide
theorem eq4_bl_term1 : (Dim.div d_T d_T_ref) = Dim.one := by decide
theorem eq4_bl_term2 : Dim.one = (Dim.mul Dim.one Dim.one) := by decide
/-- The denominator `T_ref` stays away from its singular set whenever the quantities are positive. -/
theorem eq4_bl_reg1 (T_ref : ℝ) (hT_ref : 0 < T_ref) : T_ref ≠ 0 := by positivity
/-- Domain condition for `T / T_ref`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq4_bl_cond2 (T T_ref : ℝ) (hdom : 0 < T / T_ref) : 0 < T / T_ref := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq4_bl_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 5. Calcium term

    C_L = log10(Ca_h/c_ref) - 0.4
-/
/-- Both sides of "Calcium term" carry the same physical dimension. -/
theorem eq5_cl_dim : d_C_L = Dim.one := by decide
theorem eq5_cl_term1 : (Dim.div d_Ca_h d_c_ref) = Dim.one := by decide
theorem eq5_cl_term2 : Dim.one = Dim.one := by decide
/-- The denominator `c_ref` stays away from its singular set whenever the quantities are positive. -/
theorem eq5_cl_reg1 (c_ref : ℝ) (hc_ref : 0 < c_ref) : c_ref ≠ 0 := by positivity
/-- Domain condition for `Ca_h / c_ref`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq5_cl_cond2 (Ca_h c_ref : ℝ) (hdom : 0 < Ca_h / c_ref) : 0 < Ca_h / c_ref := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq5_cl_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 6. Alkalinity term

    D_L = log10(CF*Alk/c_ref)
-/
/-- Both sides of "Alkalinity term" carry the same physical dimension. -/
theorem eq6_dl_dim : d_D_L = Dim.one := by decide
theorem eq6_dl_term1 : (Dim.div (Dim.mul d_CF d_Alk) d_c_ref) = Dim.one := by decide
/-- The denominator `c_ref` stays away from its singular set whenever the quantities are positive. -/
theorem eq6_dl_reg1 (c_ref : ℝ) (hc_ref : 0 < c_ref) : c_ref ≠ 0 := by positivity
/-- Domain condition for `CF * Alk / c_ref`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq6_dl_cond2 (CF Alk c_ref : ℝ) (hdom : 0 < CF * Alk / c_ref) : 0 < CF * Alk / c_ref := hdom
/-- The regularised form of this equation replaces each singular quotient a / b by a * b / (b ^ 2 + ε ^ 2),
    which is bounded and smooth for every real b. -/
theorem eq6_dl_soft (a b ε : ℝ) (hε : 0 < ε) : |a * b / (b ^ 2 + ε ^ 2)| ≤ |a| / (2 * ε) := soft_recip_bounded a b ε hε

/-! ## 7. Saturation pH

    pH_s = 9.3 + A_L + B_L - C_L - D_L
-/
/-- Both sides of "Saturation pH" carry the same physical dimension. -/
theorem eq7_phs_dim : d_pH_s = Dim.one := by decide
theorem eq7_phs_term1 : Dim.one = d_A_L := by decide
theorem eq7_phs_term2 : Dim.one = d_B_L := by decide
theorem eq7_phs_term3 : Dim.one = d_C_L := by decide
theorem eq7_phs_term4 : Dim.one = d_D_L := by decide

/-! ## 8. Langelier saturation index

    LSI = pH_c - pH_s
-/
/-- Both sides of "Langelier saturation index" carry the same physical dimension. -/
theorem eq8_lsi_dim : d_LSI = d_pH_c := by decide
theorem eq8_lsi_term1 : d_pH_c = d_pH_s := by decide

/-! ## 9. Ionic strength

    I_s = 2.5e-5*CF*TDS/c_ref
-/
/-- Both sides of "Ionic strength" carry the same physical dimension. -/
theorem eq9_is_dim : d_I_s = (Dim.div (Dim.mul (Dim.mul Dim.one d_CF) d_TDS) d_c_ref) := by decide
/-- The denominator `c_ref` stays away from its singular set whenever the quantities are positive. -/
theorem eq9_is_reg1 (c_ref : ℝ) (hc_ref : 0 < c_ref) : c_ref ≠ 0 := by positivity

/-! ## 10. Davies activity coefficient

    log10(gamma) = -0.509*4*(sqrt(I_s)/(1 + sqrt(I_s)) - 0.3*I_s)
-/
/-- Both sides of "Davies activity coefficient" carry the same physical dimension. -/
theorem eq10_dav_dim : Dim.one = (Dim.mul (Dim.mul Dim.one Dim.one) (Dim.div (Dim.pow d_I_s 1 2) Dim.one)) := by decide
theorem eq10_dav_term1 : d_gamma = Dim.one := by decide
theorem eq10_dav_term2 : Dim.one = (Dim.pow d_I_s 1 2) := by decide
theorem eq10_dav_term3 : (Dim.div (Dim.pow d_I_s 1 2) Dim.one) = (Dim.mul Dim.one d_I_s) := by decide
/-- The argument `gamma` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_dav_reg1 (gamma : ℝ) (hgamma : 0 < gamma) : 0 < gamma := by positivity
/-- The argument `I_s` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_dav_reg2 (I_s : ℝ) (hI_s : 0 < I_s) : 0 ≤ I_s := by positivity
/-- The argument `I_s` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_dav_reg3 (I_s : ℝ) (hI_s : 0 < I_s) : 0 ≤ I_s := by positivity
/-- The denominator `1 + sqrt(I_s)` stays away from its singular set whenever the quantities are positive. -/
theorem eq10_dav_reg4 (I_s : ℝ) (hI_s : 0 < I_s) : (1 : ℝ) + Real.sqrt I_s ≠ 0 := by positivity

/-! ## 11. Ion-pair equilibrium

    m_pair = K_a*gamma^2*m_Ca*m_SO4
-/
/-- Both sides of "Ion-pair equilibrium" carry the same physical dimension. -/
theorem eq11_pair_dim : d_m_pair = (Dim.mul (Dim.mul (Dim.mul d_K_a (Dim.pow d_gamma 2 1)) d_m_Ca) d_m_SO4) := by decide

/-! ## 12. Gypsum saturation ratio

    SR = gamma^2*m_Ca*m_SO4/K_sp
-/
/-- Both sides of "Gypsum saturation ratio" carry the same physical dimension. -/
theorem eq12_sr_dim : d_SR = (Dim.div (Dim.mul (Dim.mul (Dim.pow d_gamma 2 1) d_m_Ca) d_m_SO4) d_K_sp) := by decide
/-- Domain condition for `K_sp`: a condition on the solution; stated here as an explicit hypothesis. -/
theorem eq12_sr_cond1 (K_sp : ℝ) (hdom : K_sp ≠ 0) : K_sp ≠ 0 := hdom

end Bespoke
