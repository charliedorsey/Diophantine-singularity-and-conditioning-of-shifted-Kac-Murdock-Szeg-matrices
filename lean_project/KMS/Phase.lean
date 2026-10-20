import KMS.Secular
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Gate 2.0 / 2.1 — the real Blaschke phase `ψ_a`

The phase is defined by an explicit, globally smooth real formula (no `Complex.arg` branch):

  `ψ_a(θ) = θ + 2 arctan (a sin θ / (1 - a cos θ))`,

which is the boundary argument of `b_a(z) = (z - a)/(1 - a z)` written as
`arg z + arg(1 - a z̄) - arg(1 - a z)`; for `0 < a < 1` the denominator `1 - a cos θ` is positive
for every real `θ`.  We then prove it IS the manuscript's phase:

* `cos_psi`, `sin_psi`: `R cos ψ = D`, `R sin ψ = E`;
* `psi_eq_arg`: on `(0, π)`, `ψ_a θ = Complex.arg (D + E i)` — manuscript eq. `(psi)`;
* `psi_zero`, `psi_pi`, `continuous_psi`: continuous on `ℝ` with `ψ(0) = 0`, `ψ(π) = π`;
* `lem_phase`: `S_N(θ) = R(θ) sin(Nθ + ψ_a(θ))` (every real `θ`);
* `hasDerivAt_psi`: `ψ_a' = μ_a` (every real `θ`);
* `blaschke_phase`: `e^{iψ} = b_a(e^{iθ})`; `normSq_one_sub`: `|1 - a e^{iθ}|² = R`.
-/

open Real Set

namespace ShiftedKMS

/-- `D(θ) = (1 + a²) cos θ - 2a`, manuscript eq. `(DE)`. -/
noncomputable def Da (a θ : ℝ) : ℝ := (1 + a ^ 2) * Real.cos θ - 2 * a
/-- `E(θ) = (1 - a²) sin θ`, manuscript eq. `(DE)`. -/
noncomputable def Ea (a θ : ℝ) : ℝ := (1 - a ^ 2) * Real.sin θ
/-- `R(θ) = 1 - 2a cos θ + a²`. -/
noncomputable def Ra (a θ : ℝ) : ℝ := 1 - 2 * a * Real.cos θ + a ^ 2
/-- The real Blaschke phase `ψ_a`. -/
noncomputable def psi (a θ : ℝ) : ℝ := θ + 2 * Real.arctan (a * Real.sin θ / (1 - a * Real.cos θ))
/-- `G_N(θ) = Nθ + ψ_a(θ)`, manuscript eq. `(G)`. -/
noncomputable def Gph (N : ℕ) (a θ : ℝ) : ℝ := N * θ + psi a θ

lemma symbol_eq_div_Ra (a θ : ℝ) : symbol a θ = (1 - a ^ 2) / Ra a θ := rfl

lemma one_sub_a_cos_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    0 < 1 - a * Real.cos θ := by
  have := Real.cos_le_one θ
  nlinarith

lemma Ra_eq (a θ : ℝ) : Ra a θ = (1 - a * Real.cos θ) ^ 2 + (a * Real.sin θ) ^ 2 := by
  unfold Ra; linear_combination (-a ^ 2) * Real.sin_sq_add_cos_sq θ

lemma Ra_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) : 0 < Ra a θ := by
  rw [Ra_eq]; have := one_sub_a_cos_pos ha0 ha1 θ; positivity

/-- `R² = D² + E²`, hence `R = √(D² + E²)` (manuscript definition of `R`). -/
lemma Ra_sq (a θ : ℝ) : Ra a θ ^ 2 = Da a θ ^ 2 + Ea a θ ^ 2 := by
  unfold Ra Da Ea
  linear_combination (-(a - 1) ^ 2 * (a + 1) ^ 2) * Real.sin_sq_add_cos_sq θ

lemma Ra_eq_sqrt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    Ra a θ = Real.sqrt (Da a θ ^ 2 + Ea a θ ^ 2) := by
  rw [← Ra_sq, Real.sqrt_sq (Ra_pos ha0 ha1 θ).le]

lemma symbol_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) : 0 < symbol a θ := by
  rw [symbol_eq_div_Ra]
  exact div_pos (by nlinarith) (Ra_pos ha0 ha1 θ)

lemma Ra_ge {a : ℝ} (ha0 : 0 < a) (θ : ℝ) : (1 - a) ^ 2 ≤ Ra a θ := by
  unfold Ra; have := Real.cos_le_one θ; nlinarith

lemma Ra_le {a : ℝ} (ha0 : 0 < a) (θ : ℝ) : Ra a θ ≤ (1 + a) ^ 2 := by
  unfold Ra; have := Real.neg_one_le_cos θ; nlinarith

lemma lowerEdge_eq {a : ℝ} (ha0 : 0 < a) : lowerEdge a = (1 - a ^ 2) / (1 + a) ^ 2 := by
  have : (1 + a) ≠ 0 := by positivity
  unfold lowerEdge
  rw [eq_div_iff (pow_ne_zero 2 this)]
  field_simp
  ring

/-- `μ₋ ≤ μ_a(θ)`. -/
lemma lowerEdge_le_symbol {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    lowerEdge a ≤ symbol a θ := by
  rw [lowerEdge_eq ha0, symbol_eq_div_Ra]
  exact div_le_div_of_nonneg_left (by nlinarith) (Ra_pos ha0 ha1 θ) (Ra_le ha0 θ)

/-- `μ_a(θ) ≤ μ₊`. -/
lemma symbol_le_upperEdge {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    symbol a θ ≤ upperEdge a := by
  have h1 : (1 - a) ≠ 0 := by intro h; linarith
  have e : upperEdge a = (1 - a ^ 2) / (1 - a) ^ 2 := by
    unfold upperEdge
    rw [eq_div_iff (pow_ne_zero 2 h1)]
    field_simp
    ring
  rw [e, symbol_eq_div_Ra]
  exact div_le_div_of_nonneg_left (by nlinarith) (by positivity) (Ra_ge ha0 θ)

/-! ### `R cos ψ = D`, `R sin ψ = E` -/

lemma phase_alg {a c s Cp Sp : ℝ} (hw : 1 - a * c ≠ 0) (h1 : Sp * (1 - a * c) = a * s * Cp)
    (h2 : Cp ^ 2 * ((1 - a * c) ^ 2 + a ^ 2 * s ^ 2) = (1 - a * c) ^ 2) (h3 : s ^ 2 + c ^ 2 = 1) :
    (1 - 2 * a * c + a ^ 2) * (c * (2 * Cp ^ 2 - 1) - s * (2 * Sp * Cp)) = (1 + a ^ 2) * c - 2 * a ∧
    (1 - 2 * a * c + a ^ 2) * (s * (2 * Cp ^ 2 - 1) + c * (2 * Sp * Cp)) = (1 - a ^ 2) * s := by
  constructor
  · apply mul_left_cancel₀ hw
    linear_combination (-2 * (1 - 2 * a * c + a ^ 2) * s * Cp) * h1 +
      (2 * ((1 - a * c) * c - a * s ^ 2)) * h2 +
      (-2 * a ^ 2 * Cp ^ 2 * ((1 - a * c) * c - a * s ^ 2) - 2 * a * (1 - a * c) ^ 2) * h3
  · apply mul_left_cancel₀ hw
    linear_combination (2 * (1 - 2 * a * c + a ^ 2) * c * Cp) * h1 +
      (2 * ((1 - a * c) * s + a * c * s)) * h2 +
      (-2 * a ^ 2 * Cp ^ 2 * ((1 - a * c) * s + a * c * s)) * h3

lemma psi_trig {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    Ra a θ * Real.cos (psi a θ) = Da a θ ∧ Ra a θ * Real.sin (psi a θ) = Ea a θ := by
  have hw := one_sub_a_cos_pos ha0 ha1 θ
  set u := a * Real.sin θ / (1 - a * Real.cos θ) with hu
  set φ := Real.arctan u with hφ
  have hCp : 0 < Real.cos φ := Real.cos_arctan_pos u
  have h1 : Real.sin φ * (1 - a * Real.cos θ) = a * Real.sin θ * Real.cos φ := by
    have ht : Real.tan φ = u := Real.tan_arctan u
    rw [Real.tan_eq_sin_div_cos, div_eq_iff hCp.ne'] at ht
    rw [ht, hu]; field_simp
  have h2 : Real.cos φ ^ 2 * ((1 - a * Real.cos θ) ^ 2 + a ^ 2 * Real.sin θ ^ 2) =
      (1 - a * Real.cos θ) ^ 2 := by
    rw [hφ, Real.cos_sq_arctan, hu]
    field_simp
  have hpsi : psi a θ = θ + 2 * φ := rfl
  rw [hpsi, Real.cos_add, Real.sin_add, Real.cos_two_mul, Real.sin_two_mul]
  obtain ⟨hc, hs⟩ := phase_alg hw.ne' h1 h2 (Real.sin_sq_add_cos_sq θ)
  refine ⟨?_, ?_⟩
  · unfold Ra Da; rw [← hc]
  · unfold Ra Ea; rw [← hs]

lemma cos_psi {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    Ra a θ * Real.cos (psi a θ) = Da a θ := (psi_trig ha0 ha1 θ).1

lemma sin_psi {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    Ra a θ * Real.sin (psi a θ) = Ea a θ := (psi_trig ha0 ha1 θ).2

/-- **`lem:phase` (first claim)**: `S_N(θ) = R(θ) sin(Nθ + ψ_a(θ))`, for every real `θ`. -/
theorem lem_phase {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) (θ : ℝ) :
    secular N a θ = Ra a θ * Real.sin (N * θ + psi a θ) := by
  rw [secular_eq_DE, Real.sin_add]
  have hc := cos_psi ha0 ha1 θ
  have hs := sin_psi ha0 ha1 θ
  unfold Da at hc; unfold Ea at hs
  rw [← hc, ← hs]; ring

/-! ### Endpoints, continuity, derivative, monotonicity -/

@[simp] lemma psi_zero (a : ℝ) : psi a 0 = 0 := by simp [psi]

@[simp] lemma psi_pi (a : ℝ) : psi a π = π := by simp [psi]

lemma Gph_zero (N : ℕ) (a : ℝ) : Gph N a 0 = 0 := by simp only [Gph, mul_zero, psi_zero, add_zero]

lemma Gph_pi (N : ℕ) (a : ℝ) : Gph N a π = (N + 1) * π := by simp only [Gph, psi_pi]; ring

/-- **`prop:blaschke`, eq. `(psiprime)`**: `ψ_a'(θ) = μ_a(θ)` for every real `θ`. -/
theorem hasDerivAt_psi {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    HasDerivAt (psi a) (symbol a θ) θ := by
  have hw := one_sub_a_cos_pos ha0 ha1 θ
  have hu : HasDerivAt (fun x => a * Real.sin x / (1 - a * Real.cos x))
      ((a * Real.cos θ * (1 - a * Real.cos θ) - a * Real.sin θ * (a * Real.sin θ)) /
        (1 - a * Real.cos θ) ^ 2) θ := by
    have h1 := (Real.hasDerivAt_sin θ).const_mul a
    have h2 := ((Real.hasDerivAt_cos θ).const_mul a).const_sub 1
    convert h1.div h2 hw.ne' using 1
    ring
  have h := (hasDerivAt_id θ).add ((hu.arctan).const_mul 2)
  convert h using 1
  · funext x; rfl
  have hR := Ra_pos ha0 ha1 θ
  have hR' : Ra a θ = (1 - a * Real.cos θ) ^ 2 + (a * Real.sin θ) ^ 2 := Ra_eq a θ
  have hden : (1 + (a * Real.sin θ / (1 - a * Real.cos θ)) ^ 2) =
      Ra a θ / (1 - a * Real.cos θ) ^ 2 := by
    rw [hR']; field_simp
  rw [hden, symbol_eq_div_Ra]
  field_simp
  unfold Ra
  linear_combination (2 * a ^ 2) * Real.sin_sq_add_cos_sq θ

theorem hasDerivAt_Gph {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) (θ : ℝ) :
    HasDerivAt (Gph N a) (N + symbol a θ) θ := by
  have h := ((hasDerivAt_id θ).const_mul (N : ℝ)).add (hasDerivAt_psi ha0 ha1 θ)
  convert h using 1
  · funext x; simp only [Gph, id_eq, Pi.add_apply]
  · simp only [mul_one]

lemma continuous_psi {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : Continuous (psi a) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_psi ha0 ha1 x).continuousAt

lemma continuous_Gph {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) : Continuous (Gph N a) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_Gph ha0 ha1 N x).continuousAt

lemma strictMono_psi {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : StrictMono (psi a) :=
  strictMono_of_hasDerivAt_pos (fun x => hasDerivAt_psi ha0 ha1 x) (fun x => symbol_pos ha0 ha1 x)

/-- `G_N' = N + μ_a > 0`, manuscript eq. `(Gprime)`; hence `G_N` is strictly increasing. -/
lemma strictMono_Gph {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) : StrictMono (Gph N a) :=
  strictMono_of_hasDerivAt_pos (fun x => hasDerivAt_Gph ha0 ha1 N x)
    (fun x => by have := symbol_pos ha0 ha1 x; positivity)

/-- `ψ_a` maps `(0, π)` into `(0, π)` (the manuscript's range in eq. `(psi)`). -/
lemma psi_mem_Ioo {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    psi a θ ∈ Ioo 0 π := by
  have hm := strictMono_psi ha0 ha1
  constructor
  · have := hm hθ.1; rwa [psi_zero] at this
  · have := hm hθ.2; rwa [psi_pi] at this

/-- `θ < ψ_a(θ)` on `(0, π)`. -/
lemma lt_psi {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) : θ < psi a θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hw := one_sub_a_cos_pos ha0 ha1 θ
  have : 0 < Real.arctan (a * Real.sin θ / (1 - a * Real.cos θ)) :=
    Real.arctan_pos.2 (by positivity)
  unfold psi; linarith

/-! ### Bridge to the manuscript's `arg` definition and the Blaschke form -/

/-- **Manuscript eq. `(psi)`**: on `(0, π)`, `ψ_a(θ) = arg (D(θ) + i E(θ))`. -/
theorem psi_eq_arg {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    psi a θ = Complex.arg ((Da a θ : ℂ) + (Ea a θ : ℂ) * Complex.I) := by
  have hR := Ra_pos ha0 ha1 θ
  have e : (Da a θ : ℂ) + (Ea a θ : ℂ) * Complex.I =
      (Ra a θ : ℂ) * (Complex.cos (psi a θ) + Complex.sin (psi a θ) * Complex.I) := by
    rw [← cos_psi ha0 ha1 θ, ← sin_psi ha0 ha1 θ, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  rw [e, Complex.arg_real_mul _ hR, Complex.arg_cos_add_sin_mul_I]
  have h := psi_mem_Ioo ha0 ha1 hθ
  exact ⟨by linarith [h.1, Real.pi_pos], h.2.le⟩

lemma normSq_one_sub {a : ℝ} (θ : ℝ) :
    Complex.normSq (1 - (a : ℂ) * Complex.exp (θ * Complex.I)) = Ra a θ := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  unfold Ra
  linear_combination a ^ 2 * Real.sin_sq_add_cos_sq θ

/-- `ψ_a'(θ) = (1 - a²) / |1 - a e^{iθ}|² = μ_a(θ)` (manuscript eq. `(psiprime)`). -/
theorem hasDerivAt_psi_poisson {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    HasDerivAt (psi a)
      ((1 - a ^ 2) / Complex.normSq (1 - (a : ℂ) * Complex.exp (θ * Complex.I))) θ := by
  rw [normSq_one_sub]; exact hasDerivAt_psi ha0 ha1 θ

/-- **`prop:blaschke`, eq. `(blaschkephase)`**: `e^{iψ_a(θ)} = b_a(e^{iθ})`, every real `θ`. -/
theorem blaschke_phase {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    Complex.exp (psi a θ * Complex.I) =
      (Complex.exp (θ * Complex.I) - a) / (1 - a * Complex.exp (θ * Complex.I)) := by
  have hR := Ra_pos ha0 ha1 θ
  have hden : (1 - (a : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 := by
    intro h
    have := congrArg Complex.normSq h
    rw [normSq_one_sub, map_zero] at this
    linarith
  rw [eq_div_iff hden]
  have hc := cos_psi ha0 ha1 θ
  have hs := sin_psi ha0 ha1 θ
  unfold Da Ra at hc; unfold Ea Ra at hs
  rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.sub_im, Complex.one_im]
    apply mul_left_cancel₀ hR.ne'
    unfold Ra
    linear_combination (1 - a * Real.cos θ) * hc + a * Real.sin θ * hs +
      (-a * (a - 1) * (a + 1)) * Real.sin_sq_add_cos_sq θ
  · simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.sub_im, Complex.one_im]
    apply mul_left_cancel₀ hR.ne'
    unfold Ra
    linear_combination (1 - a * Real.cos θ) * hs - a * Real.sin θ * hc

/-! ### Gate 2.2 — exact quantization `G_N(θ_k) = kπ` -/

/-- Existence and uniqueness of the `k`-th eigenangle (`1 ≤ k ≤ N`). -/
theorem eigAngle_existsUnique {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ N) : ∃! θ, θ ∈ Ioo 0 π ∧ Gph N a θ = k * π := by
  have hm := strictMono_Gph ha0 ha1 N
  have hpi := Real.pi_pos
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
  obtain ⟨θ, hθ, hG⟩ : ∃ θ ∈ Icc 0 π, Gph N a θ = k * π := by
    have hivt := intermediate_value_Icc Real.pi_pos.le (continuous_Gph ha0 ha1 N).continuousOn
    apply hivt
    rw [Gph_zero, Gph_pi]
    constructor <;> nlinarith
  refine ⟨θ, ⟨⟨?_, ?_⟩, hG⟩, ?_⟩
  · rcases hθ.1.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, Gph_zero] at hG; nlinarith
  · rcases hθ.2.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h, Gph_pi] at hG; nlinarith
  · rintro θ' ⟨-, hG'⟩
    exact hm.injective (hG'.trans hG.symm)

/-- The `k`-th eigenangle `θ_k` (meaningful for `1 ≤ k ≤ N`, `0 < a < 1`). -/
noncomputable def eigAngle (N : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  Classical.epsilon fun θ => θ ∈ Ioo 0 π ∧ Gph N a θ = k * π

lemma eigAngle_spec {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    eigAngle N a k ∈ Ioo 0 π ∧ Gph N a (eigAngle N a k) = k * π :=
  Classical.epsilon_spec (eigAngle_existsUnique ha0 ha1 hk1 hkN).exists

lemma eq_eigAngle {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (hG : Gph N a θ = k * π) : θ = eigAngle N a k :=
  (eigAngle_existsUnique ha0 ha1 hk1 hkN).unique ⟨hθ, hG⟩ (eigAngle_spec ha0 ha1 hk1 hkN)

/-- `0 < θ_1 < ⋯ < θ_N < π`. -/
lemma eigAngle_lt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N k l : ℕ} (hk1 : 1 ≤ k) (hkl : k < l)
    (hlN : l ≤ N) : eigAngle N a k < eigAngle N a l := by
  have h1 := (eigAngle_spec ha0 ha1 hk1 (by omega : k ≤ N)).2
  have h2 := (eigAngle_spec ha0 ha1 (by omega : 1 ≤ l) hlN).2
  rw [← (strictMono_Gph ha0 ha1 N).lt_iff_lt, h1, h2]
  have : (k : ℝ) < l := by exact_mod_cast hkl
  nlinarith [Real.pi_pos]

/-- **`thm:quant`, eq. `(quant)`**: the zeros of the secular function in `(0, π)` are exactly
the `N` eigenangles `θ_1, …, θ_N`. -/
theorem secular_eq_zero_iff {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) :
    secular N a θ = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ θ = eigAngle N a k := by
  have hR := Ra_pos ha0 ha1 θ
  have hm := strictMono_Gph ha0 ha1 N
  rw [lem_phase ha0 ha1, mul_eq_zero, or_iff_right hR.ne', Real.sin_eq_zero_iff]
  have hlo : 0 < Gph N a θ := by have := hm hθ.1; rwa [Gph_zero] at this
  have hhi : Gph N a θ < (N + 1) * π := by have := hm hθ.2; rwa [Gph_pi] at this
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨n, hn⟩
    have hG : Gph N a θ = n * π := by rw [Gph]; exact hn.symm
    have hn1 : (0 : ℝ) < n := by
      by_contra h; push_neg at h; nlinarith
    have hn2 : (n : ℝ) < N + 1 := by
      by_contra h; push_neg at h; nlinarith
    have hn1' : 0 < n := by exact_mod_cast hn1
    have hn2' : n < N + 1 := by exact_mod_cast hn2
    refine ⟨n.toNat, by omega, by omega, ?_⟩
    apply eq_eigAngle ha0 ha1 (by omega) (by omega) hθ
    rw [hG]; congr 1
    have : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn1'.le
    exact_mod_cast this.symm
  · rintro ⟨k, hk1, hkN, rfl⟩
    refine ⟨k, ?_⟩
    have := (eigAngle_spec ha0 ha1 hk1 hkN).2
    rw [Gph] at this
    push_cast; exact this.symm

/-- **`thm:quant`, eq. `(spacing)`**: `π/(N + μ₊) ≤ θ_{k+1} - θ_k ≤ π/(N + μ₋)`. -/
theorem eigAngle_spacing {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k + 1 ≤ N) :
    π / (N + upperEdge a) ≤ eigAngle N a (k + 1) - eigAngle N a k ∧
      eigAngle N a (k + 1) - eigAngle N a k ≤ π / (N + lowerEdge a) := by
  have hlt := eigAngle_lt ha0 ha1 hk1 (Nat.lt_succ_self k) hkN
  have h1 := (eigAngle_spec ha0 ha1 hk1 (by omega : k ≤ N)).2
  have h2 := (eigAngle_spec ha0 ha1 (by omega : 1 ≤ k + 1) hkN).2
  obtain ⟨ξ, -, hξ⟩ := exists_hasDerivAt_eq_slope (Gph N a) (fun x => (N : ℝ) + symbol a x) hlt
    (continuous_Gph ha0 ha1 N).continuousOn (fun x _ => hasDerivAt_Gph ha0 ha1 N x)
  rw [h1, h2] at hξ
  push_cast at hξ
  set Δ := eigAngle N a (k + 1) - eigAngle N a k with hΔ
  have hΔpos : 0 < Δ := by rw [hΔ]; linarith
  have hslope : ((N : ℝ) + symbol a ξ) * Δ = π := by
    rw [hξ]; field_simp; ring
  have hlo := lowerEdge_le_symbol ha0 ha1 ξ
  have hhi := symbol_le_upperEdge ha0 ha1 ξ
  have hlo0 : 0 < lowerEdge a := by unfold lowerEdge; apply div_pos <;> linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  constructor
  · rw [div_le_iff₀ (by linarith)]
    nlinarith
  · rw [le_div_iff₀ (by linarith)]
    nlinarith

/-! ### Gate 2.2 — the source sine eigenvectors -/

open Matrix

/-- Manuscript eq. `(eigs)`: `v_j = sin((j+1)θ) - a sin(jθ)`. -/
noncomputable def eigVecF (a θ : ℝ) (j : ℕ) : ℝ := Real.sin ((j + 1) * θ) - a * Real.sin (j * θ)

/-- The eigenvector `v = (v_0, …, v_{N-1})`. -/
noncomputable def eigVec (N : ℕ) (a θ : ℝ) : Fin N → ℝ := fun j => eigVecF a θ j.val

lemma sin_sub_add (x θ : ℝ) :
    Real.sin (x - θ) + Real.sin (x + θ) = 2 * Real.cos θ * Real.sin x := by
  rw [Real.sin_sub, Real.sin_add]; ring

/-- Three-term recurrence `v_m + v_{m+2} = 2 cos θ · v_{m+1}`. -/
lemma eigVecF_rec (a θ : ℝ) (m : ℕ) :
    eigVecF a θ m + eigVecF a θ (m + 2) = 2 * Real.cos θ * eigVecF a θ (m + 1) := by
  unfold eigVecF
  have h1 := sin_sub_add (((m : ℝ) + 2) * θ) θ
  have h2 := sin_sub_add (((m : ℝ) + 1) * θ) θ
  rw [show ((m : ℝ) + 2) * θ - θ = ((m : ℝ) + 1) * θ by ring,
    show ((m : ℝ) + 2) * θ + θ = ((m : ℝ) + 2 + 1) * θ by ring] at h1
  rw [show ((m : ℝ) + 1) * θ - θ = (m : ℝ) * θ by ring,
    show ((m : ℝ) + 1) * θ + θ = ((m : ℝ) + 2) * θ by ring] at h2
  push_cast
  rw [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring]
  linear_combination h1 - a * h2

lemma eigVecF_zero (a θ : ℝ) : eigVecF a θ 0 = Real.sin θ := by simp only [eigVecF, CharP.cast_eq_zero, zero_add, one_mul, zero_mul, sin_zero, mul_zero, sub_zero]

lemma eigVecF_one (a θ : ℝ) :
    eigVecF a θ 1 = 2 * Real.sin θ * Real.cos θ - a * Real.sin θ := by
  simp only [eigVecF, Nat.cast_one, one_mul]
  rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.sin_two_mul]

/-- `S_N = v_N - a v_{N-1}` (the boundary defect of the recurrence). -/
lemma secular_eq_eigVecF (a θ : ℝ) (n : ℕ) :
    secular (n + 1) a θ = eigVecF a θ (n + 1) - a * eigVecF a θ n := by
  unfold secular eigVecF
  push_cast
  rw [show (n : ℝ) + 1 - 1 = n by ring, show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
  ring

lemma triDiag_mulVec_apply {R : Type*} [CommRing R] {n : ℕ} (b : R) (D : Fin n → R)
    (v : Fin n → R) (i : Fin n) :
    (triDiag b D *ᵥ v) i =
      D i * v i + b * (∑ k : Fin n, if k.val + 1 = i.val then v k else 0) +
        b * (∑ k : Fin n, if i.val + 1 = k.val then v k else 0) := by
  simp only [Matrix.mulVec, dotProduct]
  have hpt : ∀ k : Fin n, triDiag b D i k * v k =
      (if k = i then D i * v i else 0) + b * (if k.val + 1 = i.val then v k else 0) +
        b * (if i.val + 1 = k.val then v k else 0) := by
    intro k
    rw [triDiag_apply]
    by_cases h : k = i
    · subst h
      simp only [↓reduceIte, Nat.add_eq_left, one_ne_zero, mul_zero, add_zero]
    · have hv : k.val ≠ i.val := fun e => h (Fin.ext e)
      rw [if_neg (Ne.symm h), if_neg h]
      split_ifs <;> first | ring1 | (exfalso; omega)
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma eig_entry (a θ : ℝ) {N i : ℕ} (hN : 2 ≤ N) (hi : i < N) :
    (if i = 0 then 1 else if i + 1 = N then 1 else 1 + a ^ 2) * eigVecF a θ i +
      -a * (if 1 ≤ i then eigVecF a θ (i - 1) else 0) +
      -a * (if i + 1 < N then eigVecF a θ (i + 1) else 0) =
      Ra a θ * eigVecF a θ i + (if i + 1 = N then a * secular N a θ else 0) := by
  rcases i with _ | m
  · rw [if_pos (rfl : (0 : ℕ) = 0), if_neg (show ¬ (1 ≤ 0) by omega),
      if_pos (show 0 + 1 < N by omega), if_neg (show ¬ (0 + 1 = N) by omega), eigVecF_zero,
      show 0 + 1 = 1 from rfl, eigVecF_one]
    unfold Ra; ring
  · have hrec := eigVecF_rec a θ m
    rw [if_neg (show ¬ (m + 1 = 0) by omega), if_pos (show 1 ≤ m + 1 by omega),
      show m + 1 - 1 = m from rfl]
    by_cases hb : m + 1 + 1 = N
    · subst hb
      rw [if_pos rfl, if_pos rfl, if_neg (lt_irrefl _), secular_eq_eigVecF]
      unfold Ra
      linear_combination (-a) * hrec
    · rw [if_neg hb, if_pos (show m + 1 + 1 < N by omega), if_neg hb]
      unfold Ra
      linear_combination (-a) * hrec

/-- `M · v = R v + a S_N e_{N-1}`, with `M = kmsInvTri`. -/
theorem kmsInvTri_mulVec_eigVec {N : ℕ} (hN : 2 ≤ N) (a θ : ℝ) (i : Fin N) :
    (kmsInvTri N a *ᵥ eigVec N a θ) i =
      Ra a θ * eigVec N a θ i + (if i.val + 1 = N then a * secular N a θ else 0) := by
  rw [kmsInvTri, triDiag_mulVec_apply]
  simp only [eigVec]
  rw [sum_fin_pred (n := N) i.isLt.le (eigVecF a θ), sum_fin_succ' (n := N) i.val (eigVecF a θ)]
  have h := eig_entry a θ hN i.isLt
  simp only [endMat]
  convert h using 2

/-- **`thm:quant`, eq. `(eigs)`** (eigenpair form): whenever `S_N(θ) = 0`,
`T_N(a) v(θ) = μ_a(θ) v(θ)`. -/
theorem kms_mulVec_eigVec {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) {θ : ℝ}
    (hS : secular N a θ = 0) :
    kms N a *ᵥ eigVec N a θ = symbol a θ • eigVec N a θ := by
  have hR := Ra_pos ha0 ha1 θ
  have hM : kmsInvTri N a *ᵥ eigVec N a θ = Ra a θ • eigVec N a θ := by
    funext i
    rw [kmsInvTri_mulVec_eigVec hN, hS, mul_zero, ite_self, add_zero, Pi.smul_apply, smul_eq_mul]
  have key : Ra a θ • (kms N a *ᵥ eigVec N a θ) = (1 - a ^ 2) • eigVec N a θ := by
    rw [← Matrix.mulVec_smul, ← hM, Matrix.mulVec_mulVec, kms_mul_kmsInvTri hN,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [symbol_eq_div_Ra]
  funext i
  have := congrFun key i
  simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
  field_simp
  linarith

lemma eigVec_ne_zero {N : ℕ} (hN : 1 ≤ N) (a : ℝ) {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    eigVec N a θ ≠ 0 := by
  intro h
  have := congrFun h ⟨0, hN⟩
  simp only [eigVec, eigVecF_zero, Pi.zero_apply] at this
  exact hs this

/-- **`thm:quant`, eqs. `(eigs)`, `(shiftedeigs)`**: for `1 ≤ k ≤ N`, `θ_k` gives a KMS
eigenpair `(μ_a(θ_k), v^{(k)})` with `v^{(k)} ≠ 0`, and `B_N v^{(k)} = (μ_a(θ_k) - τ) v^{(k)}`. -/
theorem kms_eigenpair {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N k : ℕ} (hN : 2 ≤ N) (hk1 : 1 ≤ k)
    (hkN : k ≤ N) :
    kms N a *ᵥ eigVec N a (eigAngle N a k) =
        symbol a (eigAngle N a k) • eigVec N a (eigAngle N a k) ∧
      eigVec N a (eigAngle N a k) ≠ 0 := by
  have hmem := (eigAngle_spec ha0 ha1 hk1 hkN).1
  have hS : secular N a (eigAngle N a k) = 0 :=
    (secular_eq_zero_iff ha0 ha1 hmem).2 ⟨k, hk1, hkN, rfl⟩
  exact ⟨kms_mulVec_eigVec ha0 ha1 hN hS,
    eigVec_ne_zero (by omega) a (Real.sin_pos_of_pos_of_lt_pi hmem.1 hmem.2).ne'⟩

theorem shifted_eigenpair {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N k : ℕ} (hN : 2 ≤ N)
    (hk1 : 1 ≤ k) (hkN : k ≤ N) (τ : ℝ) :
    shifted N a τ *ᵥ eigVec N a (eigAngle N a k) =
      (symbol a (eigAngle N a k) - τ) • eigVec N a (eigAngle N a k) := by
  rw [shifted, Matrix.sub_mulVec, (kms_eigenpair ha0 ha1 hN hk1 hkN).1, sub_smul]
  congr 1
  funext i
  simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

/-- **`prop:blaschke`, eq. `(blaschkequant)`**: at every eigenangle, `z_k^N b_a(z_k) = (-1)^k`. -/
theorem blaschke_quant {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N k : ℕ} (hk1 : 1 ≤ k)
    (hkN : k ≤ N) :
    Complex.exp (eigAngle N a k * Complex.I) ^ N *
        ((Complex.exp (eigAngle N a k * Complex.I) - a) /
          (1 - a * Complex.exp (eigAngle N a k * Complex.I))) = (-1) ^ k := by
  have hG := (eigAngle_spec ha0 ha1 hk1 hkN).2
  rw [← blaschke_phase ha0 ha1, ← Complex.exp_nat_mul, ← Complex.exp_add]
  have e : (N : ℂ) * (eigAngle N a k * Complex.I) + psi a (eigAngle N a k) * Complex.I =
      (k : ℂ) * (π * Complex.I) := by
    have : ((Gph N a (eigAngle N a k) : ℝ) : ℂ) = ((k * π : ℝ) : ℂ) := by rw [hG]
    unfold Gph at this
    push_cast at this
    linear_combination Complex.I * this
  rw [e, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-! ### Gate 2.2 — spectral completeness: the `N` eigenangles give the whole spectrum -/

/-- `μ_a` is injective on `[0, π]`; in particular the `N` eigenvalues are simple. -/
lemma symbol_injOn {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : InjOn (symbol a) (Icc 0 π) := by
  intro x hx y hy hxy
  apply Real.injOn_cos hx hy
  rw [symbol_eq_div_Ra, symbol_eq_div_Ra,
    div_eq_div_iff (Ra_pos ha0 ha1 x).ne' (Ra_pos ha0 ha1 y).ne'] at hxy
  unfold Ra at hxy
  have h1 : (1 - a ^ 2) * (2 * a) ≠ 0 := mul_ne_zero (by nlinarith) (by positivity)
  apply mul_left_cancel₀ h1
  linear_combination hxy

/-- The `k`-th eigenvector, indexed by `Fin N` (`k ↦ θ_{k+1}`). -/
noncomputable def eigVecK (N : ℕ) (a : ℝ) (k : Fin N) : Fin N → ℝ :=
  eigVec N a (eigAngle N a (k.val + 1))

/-- The `k`-th eigenvalue `μ_a(θ_{k+1})`. -/
noncomputable def eigValK (N : ℕ) (a : ℝ) (k : Fin N) : ℝ := symbol a (eigAngle N a (k.val + 1))

lemma eigValK_injective {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) :
    Function.Injective (eigValK N a) := by
  intro k l hkl
  have mem : ∀ j : Fin N, eigAngle N a (j.val + 1) ∈ Icc 0 π := fun j =>
    let h := (eigAngle_spec ha0 ha1 (by omega : 1 ≤ j.val + 1) (by omega : j.val + 1 ≤ N)).1
    ⟨h.1.le, h.2.le⟩
  have := symbol_injOn ha0 ha1 (mem k) (mem l) hkl
  by_contra hne
  have hv : k.val ≠ l.val := fun e => hne (Fin.ext e)
  rcases Nat.lt_or_gt_of_ne hv with h | h
  · have := eigAngle_lt ha0 ha1 (by omega : 1 ≤ k.val + 1) (by omega : k.val + 1 < l.val + 1)
      (by omega : l.val + 1 ≤ N)
    linarith
  · have := eigAngle_lt ha0 ha1 (by omega : 1 ≤ l.val + 1) (by omega : l.val + 1 < k.val + 1)
      (by omega : k.val + 1 ≤ N)
    linarith

theorem eigVecK_linearIndependent {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) :
    LinearIndependent ℝ (eigVecK N a) := by
  apply Module.End.eigenvectors_linearIndependent' (Matrix.toLin' (kms N a)) (eigValK N a)
    (eigValK_injective ha0 ha1 N)
  intro k
  obtain ⟨h1, h2⟩ := kms_eigenpair ha0 ha1 hN (by omega : 1 ≤ k.val + 1) (by omega : k.val + 1 ≤ N)
  refine ⟨?_, h2⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact h1

/-- **`thm:quant` (completeness)**: every eigenvalue of `T_N(a)` is `μ_a(θ_k)` for some
`1 ≤ k ≤ N`.  Together with `kms_eigenpair` and `eigValK_injective`, the spectrum of `T_N(a)` is
exactly `{μ_a(θ_1), …, μ_a(θ_N)}`, all simple. -/
theorem kms_spectrum {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) {lam : ℝ}
    {x : Fin N → ℝ} (hx0 : x ≠ 0) (hx : kms N a *ᵥ x = lam • x) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ lam = symbol a (eigAngle N a k) := by
  have hli := eigVecK_linearIndependent ha0 ha1 hN
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card])
  have hxmem : x ∈ Submodule.span ℝ (Set.range (eigVecK N a)) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hxmem
  have hT : Matrix.toLin' (kms N a) x = ∑ k, (c k * eigValK N a k) • eigVecK N a k := by
    rw [← hc, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, Matrix.toLin'_apply]
    obtain ⟨h1, -⟩ := kms_eigenpair ha0 ha1 hN (by omega : 1 ≤ k.val + 1)
      (by omega : k.val + 1 ≤ N)
    rw [eigVecK, h1, smul_smul, eigValK]
  rw [Matrix.toLin'_apply, hx, ← hc, Finset.smul_sum] at hT
  have hzero : ∑ k, (c k * eigValK N a k - lam * c k) • eigVecK N a k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, smul_smul] at hT ⊢
    rw [← hT, sub_self]
  have hcoef := (Fintype.linearIndependent_iff.1 hli) _ hzero
  obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hx0
    rw [← hc]
    simp only [hall, zero_smul, Finset.sum_const_zero]
  refine ⟨k.val + 1, by omega, by omega, ?_⟩
  have := hcoef k
  have : c k * (eigValK N a k - lam) = 0 := by linear_combination this
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hk
  · unfold eigValK at h; linarith

end ShiftedKMS
