import KMS.Spikes
import Mathlib.NumberTheory.Niven
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Gate 5.5 — worked examples and the hollow-slice collapses

* `example_golden`: "A recurrent non-hollow family" (`α = 1/5`, `β = 3/5`):
  `a = (3-√5)/2`, `τ = (1+√5)/2`, singular exactly at `N ≡ 3 (mod 5)`.
* `example_incompat`: "A rational-incompatible family" (`α = 1/3`, `β = 1/2`):
  `a = 2-√3`, `τ = 2/√3`, no singular dimension, `d_N ∈ {1/2, 1/6}`, `γ = 2/3`,
  `M = 1/√3`, `C = √3/(2π)`, and `κ₂/N → √3/π` (`N ≡ 0`), `3√3/π` (`N ≡ 1, 2`).
* `example_isolated`: "An isolated irrational singularity" (`a = 1/2`, `τ = 3/2`): `N = 2` is
  singular, `cos θ_τ = 3/4`, `α = arccos(3/4)/π` is irrational (Niven), `β = 2α`, `N = 2` is the
  only singular dimension, and `d_N = ‖(N-2)α‖`.
* `hollow_constants` (eqs. `(hollowgamma)`, `(hollowC)`), `hollow_kappa` (eq. `(hollowkappa)`),
  `hollow_kernel_vector` (two-sine nullvector `= sin θ_τ · (cos jθ_τ)_j`, first-kind Chebyshev),
  `hollow_det` (single-Chebyshev determinant `det(T_N - I) = (-1)^{N+1} a^N U_{N-2}(a)`).
-/

open Real Set Filter Topology

namespace ShiftedKMS

lemma sqrt5_sq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
lemma sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-! ### A recurrent non-hollow family -/

lemma golden_a : aOf (1 / 5) (3 / 5) = (3 - √5) / 2 := by
  have hc := Real.cos_pi_div_five
  have h1 : π * (1 / 5 + 3 / 5) / 2 = 2 * (π / 5) := by ring
  have h2 : π * (1 / 5 - 3 / 5) / 2 = -(π / 5) := by ring
  have hpos : 0 < 1 + √5 := by positivity
  rw [aOf, h1, h2, Real.cos_neg, Real.cos_two_mul, hc, div_eq_iff (by positivity)]
  have := sqrt5_sq
  nlinarith

lemma golden_tau : tauOf (1 / 5) (3 / 5) = (1 + √5) / 2 := by
  have hs : 0 < Real.sin (π / 5) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have h1 : π * (3 / 5) = π - 2 * (π / 5) := by ring
  rw [tauOf, h1, Real.sin_pi_sub, Real.sin_two_mul, show π * (1 / 5) = π / 5 by ring,
    Real.cos_pi_div_five, div_eq_iff hs.ne']
  ring

/-- **"A recurrent non-hollow family"**: `α = 1/5`, `β = 3/5` give `a = (3-√5)/2`,
`τ = φ = (1+√5)/2`, and `B_N` is singular exactly at `N ≡ 3 (mod 5)`. -/
theorem example_golden :
    InteriorParam ((3 - √5) / 2) ((1 + √5) / 2) ∧
      alphaOf ((3 - √5) / 2) ((1 + √5) / 2) = 1 / 5 ∧
      betaOf ((3 - √5) / 2) ((1 + √5) / 2) = 3 / 5 ∧
      ∀ N : ℕ, 2 ≤ N → (N ∈ singDims ((3 - √5) / 2) ((1 + √5) / 2) ↔ N % 5 = 3) := by
  obtain ⟨hint, hα, hβ⟩ := triangle_inverse (α := 1 / 5) (β := 3 / 5) ⟨by norm_num, by norm_num,
    by norm_num⟩
  rw [golden_a, golden_tau] at hint hα hβ
  refine ⟨hint, hα, hβ, fun N hN => ?_⟩
  have hα' : alphaOf ((3 - √5) / 2) ((1 + √5) / 2) = ((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ) := by
    rw [hα]; norm_num
  have hr : ((5 : ℕ) : ℝ) * betaOf ((3 - √5) / 2) ((1 + √5) / 2) = ((3 : ℤ) : ℝ) := by
    rw [hβ]; norm_num
  rw [(thm_rational_congr hint hα' hr).2.2 N hN, Int.ModEq]
  omega

/-! ### A rational-incompatible family -/

lemma incomp_a : aOf (1 / 3) (1 / 2) = 2 - √3 := by
  have h1 : π * (1 / 3 + 1 / 2) / 2 = 5 * π / 12 := by ring
  have h2 : π * (1 / 3 - 1 / 2) / 2 = -(π / 12) := by ring
  rw [aOf, h1, h2, Real.cos_neg]
  have hpi := Real.pi_pos
  have hc1 : 0 < Real.cos (π / 12) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hc2 : 0 < Real.cos (5 * π / 12) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs1 : Real.cos (π / 12) ^ 2 = 1 / 2 + √3 / 4 := by
    rw [Real.cos_sq, show 2 * (π / 12) = π / 6 by ring, Real.cos_pi_div_six]; ring
  have hs2 : Real.cos (5 * π / 12) ^ 2 = 1 / 2 - √3 / 4 := by
    rw [Real.cos_sq, show 2 * (5 * π / 12) = π - π / 6 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_six]; ring
  have h3 := sqrt3_sq
  have h3lt : √3 < 2 := by nlinarith [Real.sqrt_nonneg 3]
  rw [← pow_left_inj₀ (div_pos hc2 hc1).le (by linarith) two_ne_zero, div_pow, hs2, hs1,
    div_eq_iff (by positivity)]
  nlinarith

lemma incomp_tau : tauOf (1 / 3) (1 / 2) = 2 / √3 := by
  rw [tauOf, show π * (1 / 2) = π / 2 by ring, show π * (1 / 3) = π / 3 by ring,
    Real.sin_pi_div_two, Real.sin_pi_div_three]
  field_simp

lemma distZ_of_abs_lt {x : ℝ} (h1 : -(1 / 2) ≤ x) (h2 : x < 1 / 2) : distZ x = |x| := by
  rw [distZ, round_eq_zero_iff.2 ⟨h1, h2⟩, Int.cast_zero, sub_zero]

/-- **"A rational-incompatible family"**: `α = 1/3`, `β = 1/2`. -/
theorem example_incompat :
    let a := 2 - √3
    let τ := 2 / √3
    InteriorParam a τ ∧ alphaOf a τ = 1 / 3 ∧ betaOf a τ = 1 / 2 ∧
      (∀ N : ℕ, 2 ≤ N → Nonsingular N a τ) ∧
      (∀ N : ℕ, dN N a τ = if N % 3 = 0 then 1 / 2 else 1 / 6) ∧
      gam a τ = 2 / 3 ∧ Mband a τ = 1 / √3 ∧ Cint a τ = √3 / (2 * π) ∧
      Tendsto (fun k : ℕ => kappa (3 * k) a τ / ((3 * k : ℕ) : ℝ)) atTop (𝓝 (√3 / π)) ∧
      Tendsto (fun k : ℕ => kappa (1 + 3 * k) a τ / ((1 + 3 * k : ℕ) : ℝ)) atTop
        (𝓝 (3 * √3 / π)) ∧
      Tendsto (fun k : ℕ => kappa (2 + 3 * k) a τ / ((2 + 3 * k : ℕ) : ℝ)) atTop
        (𝓝 (3 * √3 / π)) := by
  intro a τ
  obtain ⟨hint, hα, hβ⟩ := triangle_inverse (α := 1 / 3) (β := 1 / 2) ⟨by norm_num, by norm_num,
    by norm_num⟩
  rw [incomp_a, incomp_tau] at hint hα hβ
  have h3 := sqrt3_sq
  have h3p : 0 < √3 := by positivity
  have h3lt : √3 < 2 := by nlinarith
  have hpi := Real.pi_pos
  have hα' : alphaOf a τ = ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) := by rw [hα]; norm_num
  have hincomp : ∀ z : ℤ, ((3 : ℕ) : ℝ) * betaOf a τ ≠ z := by
    intro z hz
    rw [hβ] at hz
    have : (2 : ℝ) * z = 3 := by push_cast at hz; linarith
    have : (2 : ℤ) * z = 3 := by exact_mod_cast this
    omega
  obtain ⟨hdpos, hns, -⟩ := thm_rational_laws_incompat hint hα' hincomp
  -- the residue distances
  have hd : ∀ r : ℕ, r < 3 → dRes a τ 1 3 r = if r = 0 then 1 / 2 else 1 / 6 := by
    intro r hr
    unfold dRes
    rw [hβ]
    interval_cases r
    · rw [distZ_of_abs_lt (by norm_num) (by norm_num)]; norm_num
    · rw [distZ_of_abs_lt (by norm_num) (by norm_num)]; norm_num
    · rw [distZ_of_abs_lt (by norm_num) (by norm_num)]; norm_num
  have hdN : ∀ N : ℕ, dN N a τ = if N % 3 = 0 then 1 / 2 else 1 / 6 := by
    intro N
    rw [dN_eq_dRes hα' (by norm_num), hd _ (Nat.mod_lt _ (by norm_num))]
  -- the constants
  have hγ : gam a τ = 2 / 3 := by
    rw [gam_form hint, hα, show π * (1 / 3) = π / 3 by ring, Real.sin_pi_div_three]
    show 2 * (2 - √3) * (2 / √3) ^ 2 * (√3 / 2) / (1 - (2 - √3) ^ 2) = 2 / 3
    have hden : 1 - (2 - √3) ^ 2 = 2 * √3 * (2 - √3) := by nlinarith
    rw [hden, div_eq_iff (by positivity)]
    field_simp
    nlinarith
  have hup : upperEdge a = √3 := by
    show (1 + (2 - √3)) / (1 - (2 - √3)) = √3
    rw [div_eq_iff (by nlinarith)]; nlinarith
  have hlow : lowerEdge a = 1 / √3 := by
    show (1 - (2 - √3)) / (1 + (2 - √3)) = 1 / √3
    rw [div_eq_div_iff (by nlinarith) h3p.ne']; nlinarith
  have hM : Mband a τ = 1 / √3 := by
    rw [Mband, hup, hlow]
    have e1 : √3 - 2 / √3 = 1 / √3 := by field_simp; nlinarith
    have e2 : 2 / √3 - 1 / √3 = 1 / √3 := by ring
    rw [show τ = 2 / √3 from rfl, e1, e2, max_self]
  have hC : Cint a τ = √3 / (2 * π) := by
    rw [Cint, hM, hγ]; field_simp; linarith [h3]
  refine ⟨hint, hα, hβ, hns, hdN, hγ, hM, hC, ?_, ?_, ?_⟩
  · have := kappa_div_tendsto_class hint hα' (by norm_num) (r := 0) (by norm_num) (hdpos 0)
    rw [hd 0 (by norm_num), ite_eq_left rfl, hC] at this
    simp only [zero_add] at this
    convert this using 2
    field_simp
    try ring
  · have := kappa_div_tendsto_class hint hα' (by norm_num) (r := 1) (by norm_num) (hdpos 1)
    rw [hd 1 (by norm_num), ite_eq_right one_ne_zero, hC] at this
    convert this using 2
    field_simp
    try ring
  · have := kappa_div_tendsto_class hint hα' (by norm_num) (r := 2) (by norm_num) (hdpos 2)
    rw [hd 2 (by norm_num), ite_eq_right two_ne_zero, hC] at this
    convert this using 2
    field_simp
    try ring

/-! ### An isolated irrational singularity -/

lemma isolated_interior : InteriorParam (1 / 2) (3 / 2) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> simp only [lowerEdge, upperEdge] <;> norm_num

lemma isolated_crossCos : crossCos (1 / 2) (3 / 2) = 3 / 4 := by
  simp only [crossCos]; norm_num

lemma isolated_alpha : alphaOf (1 / 2) (3 / 2) = Real.arccos (3 / 4) / π := by
  rw [alphaOf, crossAngle, isolated_crossCos]

/-- `arccos(3/4)/π` is irrational (Niven's theorem, Mathlib). -/
lemma irrational_arccos_three_quarters : Irrational (Real.arccos (3 / 4) / π) := by
  rintro ⟨r, hr⟩
  have hθ : Real.arccos (3 / 4) = r * π := by
    rw [hr]; field_simp
  have hcos : Real.cos (Real.arccos (3 / 4)) = 3 / 4 :=
    Real.cos_arccos (by norm_num) (by norm_num)
  have hmem := niven (θ := Real.arccos (3 / 4)) ⟨r, hθ⟩ ⟨3 / 4, by rw [hcos]; norm_num⟩
  rw [hcos] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h <;> norm_num at h

/-- **"An isolated irrational singularity"**: `a = 1/2`, `τ = 3/2`. -/
theorem example_isolated :
    InteriorParam (1 / 2) (3 / 2) ∧
      (shifted 2 (1 / 2) (3 / 2)).det = 0 ∧
      Real.cos (crossAngle (1 / 2) (3 / 2)) = 3 / 4 ∧
      Irrational (alphaOf (1 / 2) (3 / 2)) ∧
      betaOf (1 / 2) (3 / 2) = 2 * alphaOf (1 / 2) (3 / 2) ∧
      singDims (1 / 2) (3 / 2) = {2} ∧
      ∀ N : ℕ, dN N (1 / 2) (3 / 2) = distZ (((N : ℝ) - 2) * alphaOf (1 / 2) (3 / 2)) := by
  have hint := isolated_interior
  have hdet : (shifted 2 (1 / 2) (3 / 2)).det = 0 := by
    rw [Matrix.det_fin_two]
    simp only [shifted_apply]
    simp only [one_div, Nat.dist, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, tsub_self, add_zero, pow_zero, ↓reduceIte, Nat.mod_succ, zero_tsub, tsub_zero, zero_add, pow_one, zero_ne_one, one_ne_zero]
    norm_num
  have hirr : Irrational (alphaOf (1 / 2) (3 / 2)) := by
    rw [isolated_alpha]; exact irrational_arccos_three_quarters
  have h2mem : (2 : ℕ) ∈ singDims (1 / 2) (3 / 2) := ⟨le_rfl, hdet⟩
  obtain ⟨-, z, hz⟩ := (mem_singDims hint 2).1 h2mem
  obtain ⟨⟨hα0, hβ0, hαβ⟩, -, -⟩ := triangle_forward hint
  -- `α < 1/2`, since `cos θ_τ = 3/4 > 0`
  have hαhalf : alphaOf (1 / 2) (3 / 2) < 1 / 2 := by
    rw [isolated_alpha, div_lt_iff₀ Real.pi_pos]
    have := Real.arccos_lt_pi_div_two.2 (show (0 : ℝ) < 3 / 4 by norm_num)
    linarith
  have hz0 : z = 0 := by
    have h1 : (z : ℝ) < 1 := by push_cast at hz; linarith
    have h2 : (-1 : ℝ) < z := by push_cast at hz; linarith
    have : z < 1 := by exact_mod_cast h1
    have : -1 < z := by exact_mod_cast h2
    omega
  have hβ : betaOf (1 / 2) (3 / 2) = 2 * alphaOf (1 / 2) (3 / 2) := by
    rw [hz0] at hz; push_cast at hz; linarith
  refine ⟨hint, hdet, ?_, hirr, hβ, ?_, ?_⟩
  · rw [crossAngle, isolated_crossCos]; exact Real.cos_arccos (by norm_num) (by norm_num)
  · ext N
    simp only [Set.mem_singleton_iff]
    exact ⟨fun hN => singDims_subsingleton_of_irrational hint hirr hN h2mem, fun hN => hN ▸ h2mem⟩
  · intro N
    have := prop_affinecollapse (a := 1 / 2) (τ := 3 / 2) (r := 2) (m := 0)
      (by rw [hβ]; push_cast; ring) N
    simpa only [Nat.cast_ofNat] using this

/-! ### The hollow slice `τ = 1` -/

section Hollow

variable {a : ℝ}

lemma hollow_interior (ha0 : 0 < a) (ha1 : a < 1) : InteriorParam a 1 := by
  refine ⟨ha0, ha1, ?_, ?_⟩
  · simp only [lowerEdge]; rw [div_lt_one (by linarith)]; linarith
  · simp only [upperEdge]; rw [one_lt_div (by linarith)]; linarith

lemma hollow_crossCos (ha0 : 0 < a) : crossCos a 1 = a := by
  simp only [crossCos]; field_simp; ring

/-- On `τ = 1`, `a = cos(πα)` and the exact constants of eqs. `(hollowgamma)`, `(hollowC)`:
`γ(a,1) = 2a/√(1-a²)`, `M(a,1) = 2a/(1-a)`, `C(a,1) = π⁻¹ √((1+a)/(1-a))`. -/
theorem hollow_constants (ha0 : 0 < a) (ha1 : a < 1) :
    Real.cos (π * alphaOf a 1) = a ∧
      gam a 1 = 2 * a / √(1 - a ^ 2) ∧
      Mband a 1 = 2 * a / (1 - a) ∧
      Cint a 1 = 1 / π * √((1 + a) / (1 - a)) := by
  have h := hollow_interior ha0 ha1
  have hpi := Real.pi_pos
  have hcos : Real.cos (π * alphaOf a 1) = a := by
    rw [alphaOf, crossAngle, hollow_crossCos ha0, mul_div_cancel₀ _ hpi.ne']
    exact Real.cos_arccos (by linarith) ha1.le
  have h1a : 0 < 1 - a ^ 2 := by nlinarith
  have hsin : Real.sin (π * alphaOf a 1) = √(1 - a ^ 2) := by
    have hs := sin_pi_alpha_pos h
    have : Real.sin (π * alphaOf a 1) ^ 2 = 1 - a ^ 2 := by
      rw [Real.sin_sq, hcos]
    rw [← this, Real.sqrt_sq hs.le]
  have hsq : 0 < √(1 - a ^ 2) := Real.sqrt_pos.2 h1a
  have hγ : gam a 1 = 2 * a / √(1 - a ^ 2) := by
    rw [gam_form h, hsin, one_pow, mul_one, div_eq_div_iff h1a.ne' hsq.ne']
    have := Real.mul_self_sqrt h1a.le
    linear_combination (2 * a) * this
  have hM : Mband a 1 = 2 * a / (1 - a) := by
    rw [Mband, upperEdge, lowerEdge]
    have e1 : (1 + a) / (1 - a) - 1 = 2 * a / (1 - a) := by
      field_simp [show (1 - a) ≠ 0 by linarith]; ring
    have e2 : 1 - (1 - a) / (1 + a) = 2 * a / (1 + a) := by
      field_simp [show (1 + a) ≠ 0 by linarith]; ring
    rw [e1, e2, max_eq_left]
    exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  refine ⟨hcos, hγ, hM, ?_⟩
  rw [Cint, hM, hγ]
  have hfac : √(1 - a ^ 2) = √(1 + a) * √(1 - a) := by
    rw [← Real.sqrt_mul (by linarith)]; ring_nf
  have hp : 0 < √(1 + a) := Real.sqrt_pos.2 (by linarith)
  have hm : 0 < √(1 - a) := Real.sqrt_pos.2 (by linarith)
  rw [Real.sqrt_div (by linarith), hfac]
  set s := √(1 - a) with hs
  set t := √(1 + a) with ht
  have hm2 : s ^ 2 = 1 - a := Real.sq_sqrt (by linarith)
  rw [show (1 : ℝ) - a = s ^ 2 from hm2.symm]
  field_simp

/-- **eq. `(hollowkappa)`**: on `τ = 1`, at nonsingular `N ≥ n₂(a,1)`,
`κ₂(T_N - I) = π⁻¹√((1+a)/(1-a)) (N+1)/‖(N-1)α‖ · (1 + O(N⁻¹))`, two-sided and explicit. -/
theorem hollow_kappa (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : n2 a 1 ≤ N)
    (hns : Nonsingular N a 1) :
    (1 - Kkap a 1 / N) * (1 / π * √((1 + a) / (1 - a)) * (N + 1) /
        distZ (((N : ℝ) - 1) * alphaOf a 1)) ≤ kappa N a 1 ∧
      kappa N a 1 ≤ (1 + Kkap a 1 / N) * (1 / π * √((1 + a) / (1 - a)) * (N + 1) /
        distZ (((N : ℝ) - 1) * alphaOf a 1)) := by
  have h := hollow_interior ha0 ha1
  have hk := thm_kappa_relative h hN hns
  rwa [(hollow_constants ha0 ha1).2.2.2, cor_hollowdich_dN h rfl] at hk

/-- The two-sine nullvector collapses on `τ = 1`: `sin((j+1)θ) - a sin(jθ) = sin θ · cos(jθ)` when
`a = cos θ`, i.e. the kernel vector is `sin θ_τ · (T_j(a))_j` (first-kind Chebyshev). -/
theorem hollow_kernel_vector (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) (j : Fin N) :
    eigVec N a (crossAngle a 1) j =
      Real.sin (crossAngle a 1) * (Polynomial.Chebyshev.T ℝ (j : ℕ)).eval a := by
  have hc : Real.cos (crossAngle a 1) = a := by
    rw [crossAngle, hollow_crossCos ha0]; exact Real.cos_arccos (by linarith) ha1.le
  set θ := crossAngle a 1
  rw [← hc, Polynomial.Chebyshev.T_real_cos]
  simp only [eigVec, eigVecF]
  rw [add_mul, one_mul, Real.sin_add]
  push_cast
  ring

/-- The determinant collapses on `τ = 1` to the single-Chebyshev formula
`det(T_N - I) = (-1)^{N+1} a^N U_{N-2}(a)`. -/
theorem hollow_det (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) :
    (shifted N a 1).det =
      (-1) ^ (N + 1) * a ^ N * (Polynomial.Chebyshev.U ℝ ((N : ℤ) - 2)).eval a := by
  have h := hollow_interior ha0 ha1
  have hβ := (thm_resonance h).1.1 rfl
  have hcos := (hollow_constants ha0 ha1).1
  have hs := sin_pi_alpha_pos h
  rw [thm_det h hN, hβ, one_pow, mul_one]
  have hU := Polynomial.Chebyshev.U_real_cos (π * alphaOf a 1) ((N : ℤ) - 2)
  rw [hcos] at hU
  have e : (((N : ℤ) - 2 : ℤ) : ℝ) + 1 = (N : ℝ) - 1 := by push_cast; ring
  rw [e] at hU
  rw [show π * ((N : ℝ) * alphaOf a 1 - alphaOf a 1) = ((N : ℝ) - 1) * (π * alphaOf a 1) by ring,
    ← hU]
  field_simp

end Hollow

end ShiftedKMS
