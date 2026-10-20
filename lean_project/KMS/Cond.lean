import KMS.Arith
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Gate 4.0 – 4.2 — singular values, localization, and the uniform RELATIVE `σ_min` estimate

* G4.0: `lam`, `sigmaMin`, `sigmaMax` (via `|eigenvalues|` of the symmetric `B_N`), `kappa`, the
  `Nonsingular` predicate, and the bridge to the matrix (`det = 0 ↔ some λ_k = 0`,
  `σ_min ≤ |λ| ≤ σ_max` for every eigenvalue).
* G4.1: `thm_localization` (eq. `(localization)`) with explicit `n0`, and the relative
  `O(N^{-2})` form `thm_local_asymp` (eq. `(local-asymp)`).
* G4.2: `thm_smin_relative` — for ALL `N ≥ n1(a,τ)`, singular or not, with explicit `K(a,τ)`:
  `(1 - K/N) A_N ≤ σ_min(B_N) ≤ (1 + K/N) A_N`,  `A_N = π γ d_N / (N + τ)`.
  The bound is multiplicative in `d_N`, so it covers arbitrarily small `d_N` and the near-tie
  `d_N ≈ 1/2`.
-/

open Real Set Matrix

namespace ShiftedKMS

/-! ### Derivatives of the symbol -/

/-- `μ_a'(θ) = -2a(1-a²) sin θ / R(θ)²`. -/
noncomputable def dmu (a θ : ℝ) : ℝ := -(2 * a * (1 - a ^ 2) * Real.sin θ) / Ra a θ ^ 2

/-- `μ_a''(θ) = -2a(1-a²) (cos θ R(θ) - 4a sin²θ) / R(θ)³`. -/
noncomputable def d2mu (a θ : ℝ) : ℝ :=
  -(2 * a * (1 - a ^ 2) * (Real.cos θ * Ra a θ - 4 * a * Real.sin θ ^ 2)) / Ra a θ ^ 3

lemma hasDerivAt_Ra (a θ : ℝ) : HasDerivAt (Ra a) (2 * a * Real.sin θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).const_mul (2 * a)).const_sub 1 |>.add_const (a ^ 2)
  convert h using 1
  · funext x; simp only [Ra]
  · ring

theorem hasDerivAt_symbol {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    HasDerivAt (symbol a) (dmu a θ) θ := by
  have hR := Ra_pos ha0 ha1 θ
  have h := ((hasDerivAt_Ra a θ).inv hR.ne').const_mul (1 - a ^ 2)
  convert h using 1
  · funext x; simp only [symbol_eq_div_Ra, div_eq_mul_inv, Pi.inv_apply]
  · unfold dmu; field_simp

theorem hasDerivAt_dmu {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    HasDerivAt (dmu a) (d2mu a θ) θ := by
  have hR := Ra_pos ha0 ha1 θ
  have h := (((Real.hasDerivAt_sin θ).const_mul (-(2 * a * (1 - a ^ 2)))).div
    ((hasDerivAt_Ra a θ).pow 2) (pow_ne_zero 2 hR.ne'))
  convert h using 1
  · funext x; simp only [dmu, Pi.div_apply, Pi.pow_apply]; ring
  · simp only [Pi.pow_apply]; unfold d2mu; field_simp; ring

/-- Lipschitz constant of `μ_a`: `|μ_a'| ≤ 2a(1-a²)/(1-a)⁴`. -/
noncomputable def Lmu (a : ℝ) : ℝ := 2 * a * (1 - a ^ 2) / (1 - a) ^ 4

/-- Bound on `|μ_a''|`: `2a(1-a²)((1+a)² + 4a)/(1-a)⁶`. -/
noncomputable def L2mu (a : ℝ) : ℝ := 2 * a * (1 - a ^ 2) * ((1 + a) ^ 2 + 4 * a) / (1 - a) ^ 6

lemma abs_dmu_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) : |dmu a θ| ≤ Lmu a := by
  have hR := Ra_pos ha0 ha1 θ
  have hRge := Ra_ge ha0 θ
  have hc : 0 ≤ 2 * a * (1 - a ^ 2) := by nlinarith
  have h1a : 0 < (1 - a) ^ 4 := by have : 0 < 1 - a := by linarith
                                   positivity
  unfold dmu Lmu
  rw [abs_div, abs_neg, abs_mul, abs_of_nonneg hc, abs_of_pos (by positivity : 0 < Ra a θ ^ 2)]
  have hs := Real.abs_sin_le_one θ
  have hR4 : (1 - a) ^ 4 ≤ Ra a θ ^ 2 := by
    have : (1 - a) ^ 4 = ((1 - a) ^ 2) ^ 2 := by ring
    rw [this]; exact pow_le_pow_left₀ (by positivity) hRge 2
  calc 2 * a * (1 - a ^ 2) * |Real.sin θ| / Ra a θ ^ 2
      ≤ 2 * a * (1 - a ^ 2) * 1 / Ra a θ ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hs hc
    _ ≤ 2 * a * (1 - a ^ 2) * 1 / (1 - a) ^ 4 :=
        div_le_div_of_nonneg_left (by positivity) h1a hR4
    _ = 2 * a * (1 - a ^ 2) / (1 - a) ^ 4 := by ring

lemma abs_d2mu_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) : |d2mu a θ| ≤ L2mu a := by
  have hR := Ra_pos ha0 ha1 θ
  have hRge := Ra_ge ha0 θ
  have hRle := Ra_le ha0 θ
  have hc : 0 ≤ 2 * a * (1 - a ^ 2) := by nlinarith
  have h1a : 0 < (1 - a) ^ 6 := by have : 0 < 1 - a := by linarith
                                   positivity
  have hnum : |Real.cos θ * Ra a θ - 4 * a * Real.sin θ ^ 2| ≤ (1 + a) ^ 2 + 4 * a := by
    have hcos := Real.abs_cos_le_one θ
    have hsin2 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have h1 : |Real.cos θ * Ra a θ| ≤ (1 + a) ^ 2 := by
      rw [abs_mul, abs_of_pos hR]
      calc |Real.cos θ| * Ra a θ ≤ 1 * Ra a θ := mul_le_mul_of_nonneg_right hcos hR.le
        _ ≤ (1 + a) ^ 2 := by linarith
    have h2 : |4 * a * Real.sin θ ^ 2| ≤ 4 * a := by
      rw [abs_of_nonneg (by positivity)]; nlinarith [sq_nonneg (Real.sin θ)]
    calc |Real.cos θ * Ra a θ - 4 * a * Real.sin θ ^ 2|
        ≤ |Real.cos θ * Ra a θ| + |4 * a * Real.sin θ ^ 2| := abs_sub _ _
      _ ≤ (1 + a) ^ 2 + 4 * a := add_le_add h1 h2
  have hR6 : (1 - a) ^ 6 ≤ Ra a θ ^ 3 := by
    have : (1 - a) ^ 6 = ((1 - a) ^ 2) ^ 3 := by ring
    rw [this]; exact pow_le_pow_left₀ (by positivity) hRge 3
  unfold d2mu L2mu
  rw [abs_div, abs_neg, abs_mul, abs_of_nonneg hc, abs_of_pos (by positivity : 0 < Ra a θ ^ 3)]
  calc 2 * a * (1 - a ^ 2) * |Real.cos θ * Ra a θ - 4 * a * Real.sin θ ^ 2| / Ra a θ ^ 3
      ≤ 2 * a * (1 - a ^ 2) * ((1 + a) ^ 2 + 4 * a) / Ra a θ ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hnum hc
    _ ≤ 2 * a * (1 - a ^ 2) * ((1 + a) ^ 2 + 4 * a) / (1 - a) ^ 6 :=
        div_le_div_of_nonneg_left (by positivity) h1a hR6

/-- A Lipschitz bound from a derivative bound (real line). -/
lemma abs_sub_le_of_deriv {f f' : ℝ → ℝ} {L : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hb : ∀ x, |f' x| ≤ L) (x y : ℝ) : |f x - f y| ≤ L * |x - y| := by
  rcases lt_trichotomy x y with h | h | h
  · obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope f f' h
      (fun z _ => (hf z).continuousAt.continuousWithinAt) (fun z _ => hf z)
    have hxy : 0 < y - x := by linarith
    rw [eq_div_iff hxy.ne'] at hc
    rw [abs_sub_comm (f x), ← hc, abs_mul, abs_sub_comm x, abs_of_pos hxy]
    exact mul_le_mul_of_nonneg_right (hb c) hxy.le
  · subst h; simp
  · obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope f f' h
      (fun z _ => (hf z).continuousAt.continuousWithinAt) (fun z _ => hf z)
    have hxy : 0 < x - y := by linarith
    rw [eq_div_iff hxy.ne'] at hc
    rw [← hc, abs_mul, abs_of_pos hxy]
    exact mul_le_mul_of_nonneg_right (hb c) hxy.le

lemma symbol_lipschitz {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (x y : ℝ) :
    |symbol a x - symbol a y| ≤ Lmu a * |x - y| :=
  abs_sub_le_of_deriv (hasDerivAt_symbol ha0 ha1) (abs_dmu_le ha0 ha1) x y

lemma dmu_lipschitz {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (x y : ℝ) :
    |dmu a x - dmu a y| ≤ L2mu a * |x - y| :=
  abs_sub_le_of_deriv (hasDerivAt_dmu ha0 ha1) (abs_d2mu_le ha0 ha1) x y

/-- Mean value theorem with the intermediate point bounded by the endpoints. -/
lemma mvt_between {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (x y : ℝ) :
    ∃ c, |c - y| ≤ |x - y| ∧ f x - f y = f' c * (x - y) := by
  rcases lt_trichotomy x y with h | h | h
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope f f' h
      (fun z _ => (hf z).continuousAt.continuousWithinAt) (fun z _ => hf z)
    refine ⟨c, ?_, ?_⟩
    · rw [abs_of_neg (by linarith [hc.2]), abs_of_neg (by linarith)]; linarith [hc.1]
    · have hxy : y - x ≠ 0 := by linarith
      rw [hc']; field_simp; ring
  · subst h; exact ⟨x, by simp, by simp⟩
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope f f' h
      (fun z _ => (hf z).continuousAt.continuousWithinAt) (fun z _ => hf z)
    refine ⟨c, ?_, ?_⟩
    · rw [abs_of_pos (by linarith [hc.1]), abs_of_pos (by linarith)]; linarith [hc.2]
    · have hxy : x - y ≠ 0 := by linarith
      rw [hc']; field_simp

/-! ### G4.0 — singular values and the condition number -/

/-- The eigenvalues `λ_k = μ_a(θ_k) - τ` of `B_N(a,τ)` (`k = 1, …, N`; Gate 2 shows these are
all of them, each simple). -/
noncomputable def lam (N : ℕ) (a τ : ℝ) (k : ℕ) : ℝ := symbol a (eigAngle N a k) - τ

/-- `σ_min(B_N) = min_k |λ_k|` (singular values of a real symmetric matrix). -/
noncomputable def sigmaMin (N : ℕ) (a τ : ℝ) : ℝ :=
  if h : (Finset.Icc 1 N).Nonempty then (Finset.Icc 1 N).inf' h fun k => |lam N a τ k| else 0

/-- `σ_max(B_N) = max_k |λ_k|`. -/
noncomputable def sigmaMax (N : ℕ) (a τ : ℝ) : ℝ :=
  if h : (Finset.Icc 1 N).Nonempty then (Finset.Icc 1 N).sup' h fun k => |lam N a τ k| else 0

/-- Nonsingularity predicate; the condition number is only asserted under it. -/
def Nonsingular (N : ℕ) (a τ : ℝ) : Prop := (shifted N a τ).det ≠ 0

/-- `κ₂(B_N) = σ_max/σ_min` — meaningful only under `Nonsingular N a τ`. -/
noncomputable def kappa (N : ℕ) (a τ : ℝ) : ℝ := sigmaMax N a τ / sigmaMin N a τ

lemma Icc_nonempty {N : ℕ} (hN : 1 ≤ N) : (Finset.Icc 1 N).Nonempty := ⟨1, by simp; omega⟩

lemma sigmaMin_le {N : ℕ} (a τ : ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    sigmaMin N a τ ≤ |lam N a τ k| := by
  unfold sigmaMin
  rw [dif_pos (Icc_nonempty (by omega))]
  exact Finset.inf'_le _ (by simp; omega)

lemma le_sigmaMin {N : ℕ} (hN : 1 ≤ N) (a τ : ℝ) {c : ℝ}
    (h : ∀ k, 1 ≤ k → k ≤ N → c ≤ |lam N a τ k|) : c ≤ sigmaMin N a τ := by
  unfold sigmaMin
  rw [dif_pos (Icc_nonempty hN)]
  exact Finset.le_inf' _ _ (fun k hk => by simp at hk; exact h k hk.1 hk.2)

lemma le_sigmaMax {N : ℕ} (a τ : ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    |lam N a τ k| ≤ sigmaMax N a τ := by
  unfold sigmaMax
  rw [dif_pos (Icc_nonempty (by omega))]
  exact Finset.le_sup' (fun k => |lam N a τ k|) (by simp; omega)

lemma sigmaMax_le {N : ℕ} (hN : 1 ≤ N) (a τ : ℝ) {c : ℝ}
    (h : ∀ k, 1 ≤ k → k ≤ N → |lam N a τ k| ≤ c) : sigmaMax N a τ ≤ c := by
  unfold sigmaMax
  rw [dif_pos (Icc_nonempty hN)]
  exact Finset.sup'_le _ _ (fun k hk => by simp at hk; exact h k hk.1 hk.2)

lemma sigmaMin_nonneg {N : ℕ} (hN : 1 ≤ N) (a τ : ℝ) : 0 ≤ sigmaMin N a τ :=
  le_sigmaMin hN a τ (fun _ _ _ => abs_nonneg _)

/-- Bridge to the matrix: `det B_N = 0` iff some `λ_k = 0` (`0 < a < 1`, `N ≥ 2`, any `τ`). -/
theorem det_eq_zero_iff_lam {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) (τ : ℝ) :
    (shifted N a τ).det = 0 ↔ ∃ k, 1 ≤ k ∧ k ≤ N ∧ lam N a τ k = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨x, hx0, hx⟩
    have hT : kms N a *ᵥ x = τ • x := by
      rw [shifted, Matrix.sub_mulVec, sub_eq_zero] at hx
      rw [hx]; funext i; simp [Matrix.mulVec_diagonal]
    obtain ⟨k, hk1, hkN, hk⟩ := kms_spectrum ha0 ha1 hN hx0 hT
    exact ⟨k, hk1, hkN, by rw [lam, ← hk, sub_self]⟩
  · rintro ⟨k, hk1, hkN, hk⟩
    refine ⟨eigVec N a (eigAngle N a k), (kms_eigenpair ha0 ha1 hN hk1 hkN).2, ?_⟩
    rw [shifted_eigenpair ha0 ha1 hN hk1 hkN, ← lam, hk, zero_smul]

/-- `Nonsingular ↔ σ_min > 0`. -/
theorem nonsingular_iff_sigmaMin_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N)
    (τ : ℝ) : Nonsingular N a τ ↔ 0 < sigmaMin N a τ := by
  unfold Nonsingular
  rw [ne_eq, det_eq_zero_iff_lam ha0 ha1 hN]
  constructor
  · intro h
    unfold sigmaMin
    rw [dif_pos (Icc_nonempty (by omega)), Finset.lt_inf'_iff]
    intro k hk
    simp at hk
    exact abs_pos.2 (fun h0 => h ⟨k, hk.1, hk.2, h0⟩)
  · rintro hpos ⟨k, hk1, hkN, hk⟩
    have := sigmaMin_le (N := N) a τ hk1 hkN
    rw [hk, abs_zero] at this
    linarith

/-- Every eigenvalue `λ` of `B_N` satisfies `σ_min ≤ |λ| ≤ σ_max` (so these are the extreme
singular values of the symmetric matrix `B_N`). -/
theorem sigma_bounds_eigen {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) (τ : ℝ)
    {l : ℝ} {x : Fin N → ℝ} (hx0 : x ≠ 0) (hx : shifted N a τ *ᵥ x = l • x) :
    sigmaMin N a τ ≤ |l| ∧ |l| ≤ sigmaMax N a τ := by
  have hT : kms N a *ᵥ x = (l + τ) • x := by
    rw [shifted, Matrix.sub_mulVec] at hx
    have hd : (diagonal fun _ : Fin N => τ) *ᵥ x = τ • x := by
      funext i; simp [Matrix.mulVec_diagonal]
    rw [hd, sub_eq_iff_eq_add] at hx
    rw [hx, add_smul]
  obtain ⟨k, hk1, hkN, hk⟩ := kms_spectrum ha0 ha1 hN hx0 hT
  have hl : l = lam N a τ k := by rw [lam, ← hk]; ring
  rw [hl]
  exact ⟨sigmaMin_le a τ hk1 hkN, le_sigmaMax a τ hk1 hkN⟩

/-! ### G4.1 — nonasymptotic localization -/

section Interior

variable {a τ : ℝ}

/-- The residual `X_N = Nα - β`; `G_N(θ_τ) = π(X_N + 1)`. -/
noncomputable def resid (N : ℕ) (a τ : ℝ) : ℝ := N * alphaOf a τ - betaOf a τ

/-- The nearest phase index `k_N = round(X_N) + 1` (manuscript: nearest integer to `X_N + 1`). -/
noncomputable def nearIdx (N : ℕ) (a τ : ℝ) : ℕ := (round (resid N a τ) + 1).toNat

/-- Explicit threshold `n₀(a,τ) = ⌈β/α⌉ + ⌈1/(1-α)⌉ + 2`. -/
noncomputable def n0 (a τ : ℝ) : ℕ :=
  ⌈betaOf a τ / alphaOf a τ⌉₊ + ⌈1 / (1 - alphaOf a τ)⌉₊ + 2

lemma n0_spec (h : InteriorParam a τ) {N : ℕ} (hN : n0 a τ ≤ N) :
    2 ≤ N ∧ 0 ≤ resid N a τ ∧ resid N a τ ≤ N - 1 - betaOf a τ := by
  obtain ⟨hα, hβ, hαβ⟩ := alpha_beta_bounds h
  have h1 := Nat.le_ceil (betaOf a τ / alphaOf a τ)
  have h2 := Nat.le_ceil (1 / (1 - alphaOf a τ))
  have hNr : (⌈betaOf a τ / alphaOf a τ⌉₊ : ℝ) + ⌈1 / (1 - alphaOf a τ)⌉₊ + 2 ≤ N := by
    exact_mod_cast hN
  have h1a : 0 < 1 - alphaOf a τ := by linarith
  have hc1 : (0 : ℝ) ≤ ⌈1 / (1 - alphaOf a τ)⌉₊ := Nat.cast_nonneg _
  have hc2 : (0 : ℝ) ≤ ⌈betaOf a τ / alphaOf a τ⌉₊ := Nat.cast_nonneg _
  refine ⟨by unfold n0 at hN; omega, ?_, ?_⟩
  · have : betaOf a τ / alphaOf a τ ≤ N := by linarith
    rw [div_le_iff₀ hα] at this
    unfold resid; linarith
  · have : 1 / (1 - alphaOf a τ) ≤ N := by linarith
    rw [div_le_iff₀ h1a] at this
    unfold resid; nlinarith

lemma nearIdx_mem (h : InteriorParam a τ) {N : ℕ} (hN : n0 a τ ≤ N) :
    1 ≤ nearIdx N a τ ∧ nearIdx N a τ ≤ N ∧ ((nearIdx N a τ : ℕ) : ℝ) = round (resid N a τ) + 1 := by
  obtain ⟨hN2, hX0, hX1⟩ := n0_spec h hN
  have hβ := (alpha_beta_bounds h).2.1
  have hr0 : 0 ≤ round (resid N a τ) := by
    rw [round_eq]; apply Int.floor_nonneg.2; linarith
  have hr1 : round (resid N a τ) ≤ N - 1 := by
    have := abs_sub_round (resid N a τ)
    have h3 : (round (resid N a τ) : ℝ) < N - 1 + 1 / 2 := by
      rw [abs_le] at this; linarith [this.1]
    have h4 : (round (resid N a τ) : ℝ) < ((N : ℤ) - 1 : ℤ) + 1 := by push_cast; linarith
    exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast h4)
  have e : (((round (resid N a τ) + 1).toNat : ℕ) : ℤ) = round (resid N a τ) + 1 :=
    Int.toNat_of_nonneg (by omega)
  refine ⟨by unfold nearIdx; omega, by unfold nearIdx; omega, ?_⟩
  unfold nearIdx
  exact_mod_cast e

/-- `|G_N(θ_{k}) - G_N(θ_τ)| = π |k - 1 - X_N|`. -/
lemma Gph_eig_sub_cross (h : InteriorParam a τ) {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Gph N a (eigAngle N a k) - Gph N a (crossAngle a τ) = π * ((k : ℝ) - 1 - resid N a τ) := by
  rw [(eigAngle_spec h.1 h.2.1 hk1 hkN).2, Gph_crossAngle h, resid]; ring

/-- Two-sided angular displacement from phase displacement. -/
lemma angle_bounds_of_phase (h : InteriorParam a τ) (N : ℕ) (x : ℝ) :
    |Gph N a x - Gph N a (crossAngle a τ)| / (N + upperEdge a) ≤ |x - crossAngle a τ| ∧
      |x - crossAngle a τ| ≤ |Gph N a x - Gph N a (crossAngle a τ)| / (N + lowerEdge a) := by
  have ha0 := h.1
  have ha1 := h.2.1
  obtain ⟨ξ, -, hξ⟩ := mvt_between (hasDerivAt_Gph ha0 ha1 N) x (crossAngle a τ)
  have hlo := lowerEdge_le_symbol ha0 ha1 ξ
  have hhi := symbol_le_upperEdge ha0 ha1 ξ
  have hl0 := lowerEdge_pos ha0 ha1
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [hξ, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < N + symbol a ξ)]
  set u := |x - crossAngle a τ|
  have hu := abs_nonneg (x - crossAngle a τ)
  constructor
  · rw [div_le_iff₀ (by linarith)]; nlinarith
  · rw [le_div_iff₀ (by linarith)]; nlinarith

/-- **`thm:localization`, eq. `(localization)`**: for all `N ≥ n₀(a,τ)`, the nearest-phase index
`k_N ∈ {1,…,N}` and `π d_N/(N+μ₊) ≤ |θ_{k_N} - θ_τ| ≤ π d_N/(N+μ₋)`. -/
theorem thm_localization (h : InteriorParam a τ) {N : ℕ} (hN : n0 a τ ≤ N) :
    1 ≤ nearIdx N a τ ∧ nearIdx N a τ ≤ N ∧
      π * dN N a τ / (N + upperEdge a) ≤ |eigAngle N a (nearIdx N a τ) - crossAngle a τ| ∧
      |eigAngle N a (nearIdx N a τ) - crossAngle a τ| ≤ π * dN N a τ / (N + lowerEdge a) := by
  obtain ⟨hk1, hkN, hk⟩ := nearIdx_mem h hN
  have hG := Gph_eig_sub_cross h hk1 hkN
  rw [hk] at hG
  have hd : |Gph N a (eigAngle N a (nearIdx N a τ)) - Gph N a (crossAngle a τ)| = π * dN N a τ := by
    rw [hG, abs_mul, abs_of_pos Real.pi_pos, dN, distZ, ← resid]
    congr 1
    rw [show (round (resid N a τ) : ℝ) + 1 - 1 - resid N a τ =
      -(resid N a τ - round (resid N a τ)) by ring, abs_neg]
  obtain ⟨b1, b2⟩ := angle_bounds_of_phase h N (eigAngle N a (nearIdx N a τ))
  rw [hd] at b1 b2
  exact ⟨hk1, hkN, b1, b2⟩

/-- **`thm:localization`, eq. `(local-asymp)`** (relative `O(N^{-2})`, explicit constant):
`(1 - c/N²) π d_N/(N+τ) ≤ |θ_{k_N} - θ_τ| ≤ (1 + c/N²) π d_N/(N+τ)`, `c = π Lμ/2`. -/
theorem thm_local_asymp (h : InteriorParam a τ) {N : ℕ} (hN : n0 a τ ≤ N) :
    (1 - π * Lmu a / 2 / N ^ 2) * (π * dN N a τ / (N + τ)) ≤
        |eigAngle N a (nearIdx N a τ) - crossAngle a τ| ∧
      |eigAngle N a (nearIdx N a τ) - crossAngle a τ| ≤
        (1 + π * Lmu a / 2 / N ^ 2) * (π * dN N a τ / (N + τ)) := by
  have ha0 := h.1
  have ha1 := h.2.1
  have hτ := h.tau_pos
  obtain ⟨hk1, hkN, hk⟩ := nearIdx_mem h hN
  obtain ⟨hN2, -, -⟩ := n0_spec h hN
  set θk := eigAngle N a (nearIdx N a τ)
  set θτ := crossAngle a τ
  have hG := Gph_eig_sub_cross h hk1 hkN
  rw [hk] at hG
  obtain ⟨ξ, hξ, hmvt⟩ := mvt_between (hasDerivAt_Gph ha0 ha1 N) θk θτ
  set u := |θk - θτ| with hu
  have hd : π * ((round (resid N a τ) : ℝ) + 1 - 1 - resid N a τ) =
      -(π * (resid N a τ - round (resid N a τ))) := by ring
  -- `(N + μ(ξ)) · u = π d_N`
  have hpos : (0 : ℝ) < N + symbol a ξ := by have := symbol_pos ha0 ha1 ξ; positivity
  have key : (N + symbol a ξ) * u = π * dN N a τ := by
    have := congrArg abs (hmvt.symm.trans hG)
    rw [abs_mul, abs_mul, abs_of_pos hpos, abs_of_pos Real.pi_pos] at this
    rw [hu, this, dN, distZ, resid]
    congr 1
    rw [show (round (↑N * alphaOf a τ - betaOf a τ) : ℝ) + 1 - 1 - (↑N * alphaOf a τ - betaOf a τ) =
      -((↑N * alphaOf a τ - betaOf a τ) - round (↑N * alphaOf a τ - betaOf a τ)) by ring, abs_neg]
  have hdN := distZ_le_half (resid N a τ)
  have hd0 := distZ_nonneg (resid N a τ)
  have hl0 := lowerEdge_pos ha0 ha1
  have hlo := lowerEdge_le_symbol ha0 ha1 ξ
  have hN1 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  -- `u ≤ π/(2N)` and `|μ(ξ) - τ| ≤ Lμ u`
  have hu0 : 0 ≤ u := abs_nonneg _
  have hub : u ≤ π / (2 * N) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (N + symbol a ξ) * u ≤ π * (1 / 2) := by
      rw [key, dN]; exact mul_le_mul_of_nonneg_left hdN Real.pi_pos.le
    have h2 : (N : ℝ) * u ≤ (N + symbol a ξ) * u :=
      mul_le_mul_of_nonneg_right (by linarith [symbol_pos ha0 ha1 ξ]) hu0
    linarith
  have hLm : 0 ≤ Lmu a := le_trans (abs_nonneg _) (abs_dmu_le ha0 ha1 0)
  have hμξ : |symbol a ξ - τ| ≤ Lmu a * u := by
    have := symbol_lipschitz ha0 ha1 ξ θτ
    rw [symbol_crossAngle h] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hξ.trans le_rfl) hLm)
  -- write `u = (π d/(N+τ)) · ρ` with `ρ = (N+τ)/(N+μ(ξ))`, `|ρ - 1| ≤ c/N²`
  set A := π * dN N a τ / (N + τ) with hA
  have hA0 : 0 ≤ A := by rw [hA, dN]; positivity
  have huA : u = A * ((N + τ) / (N + symbol a ξ)) := by
    rw [hA, ← key]; field_simp
  have hρ : |(N + τ) / (N + symbol a ξ) - 1| ≤ π * Lmu a / 2 / N ^ 2 := by
    rw [show (N + τ) / (N + symbol a ξ) - 1 = (τ - symbol a ξ) / (N + symbol a ξ) by
      field_simp; ring, abs_div, abs_of_pos hpos, abs_sub_comm]
    rw [div_le_iff₀ hpos]
    calc |symbol a ξ - τ| ≤ Lmu a * u := hμξ
      _ ≤ Lmu a * (π / (2 * N)) := mul_le_mul_of_nonneg_left hub hLm
      _ = π * Lmu a / 2 / N ^ 2 * N := by field_simp
      _ ≤ π * Lmu a / 2 / N ^ 2 * (N + symbol a ξ) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [abs_le] at hρ
  constructor
  · rw [huA]; nlinarith
  · rw [huA]; nlinarith

end Interior

/-! ### G4.2 — the uniform RELATIVE smallest-singular-value estimate -/

section SminRel

variable {a τ : ℝ}

/-- `γ(a,τ) = |μ_a'(θ_τ)|`, manuscript eq. `(gamma)`. -/
noncomputable def gam (a τ : ℝ) : ℝ := |dmu a (crossAngle a τ)|

lemma gam_pos (h : InteriorParam a τ) : 0 < gam a τ := by
  have hθ := crossAngle_mem h
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hR := Ra_pos h.1 h.2.1 (crossAngle a τ)
  have hc : 0 < 2 * a * (1 - a ^ 2) := by have := h.1; have := h.2.1; nlinarith
  unfold gam dmu
  rw [abs_pos, neg_div, neg_ne_zero]
  positivity

/-- **eq. `(gamma-form)`**: `γ(a,τ) = 2aτ² sin(πα)/(1 - a²)`. -/
theorem gam_form (h : InteriorParam a τ) :
    gam a τ = 2 * a * τ ^ 2 * Real.sin (π * alphaOf a τ) / (1 - a ^ 2) := by
  have hθ := crossAngle_mem h
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have h1a : 0 < 1 - a ^ 2 := by have := h.1; have := h.2.1; nlinarith
  have hτ := h.tau_pos
  unfold gam dmu
  rw [Ra_crossAngle h, ← crossAngle_eq_pi_alpha h, abs_div, abs_neg,
    abs_of_pos (by have := h.1; positivity), abs_of_pos (by positivity)]
  field_simp

/-- The relative constant `K(a,τ) = c₁ + c₂ + c₁c₂`, `c₁ = π L₂/γ`, `c₂ = π Lμ`. -/
noncomputable def Ksm (a τ : ℝ) : ℝ :=
  π * L2mu a / gam a τ + π * Lmu a + (π * L2mu a / gam a τ) * (π * Lmu a)

lemma Lmu_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 ≤ Lmu a :=
  le_trans (abs_nonneg _) (abs_dmu_le ha0 ha1 0)

lemma L2mu_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 ≤ L2mu a :=
  le_trans (abs_nonneg _) (abs_d2mu_le ha0 ha1 0)

lemma Ksm_nonneg (h : InteriorParam a τ) : 0 ≤ Ksm a τ := by
  have := Lmu_nonneg h.1 h.2.1
  have := L2mu_nonneg h.1 h.2.1
  have := gam_pos h
  have := Real.pi_pos
  unfold Ksm; positivity

/-- Product of two relative perturbations. -/
lemma prod_rel {ρ₁ ρ₂ x y : ℝ} (h1 : |ρ₁ - 1| ≤ x) (h2 : |ρ₂ - 1| ≤ y) (hρ₁ : 0 ≤ ρ₁)
    (hρ₂ : 0 ≤ ρ₂) :
    1 - (x + y) ≤ ρ₁ * ρ₂ ∧ ρ₁ * ρ₂ ≤ 1 + (x + y + x * y) := by
  rw [abs_le] at h1 h2
  constructor
  · rcases le_or_gt 0 (1 - x) with hx | hx
    · rcases le_or_gt 0 (1 - y) with hy | hy
      · have : (1 - x) * (1 - y) ≤ ρ₁ * ρ₂ := mul_le_mul (by linarith) (by linarith) hy hρ₁
        nlinarith
      · nlinarith [mul_nonneg hρ₁ hρ₂]
    · nlinarith [mul_nonneg hρ₁ hρ₂]
  · have : ρ₁ * ρ₂ ≤ (1 + x) * (1 + y) :=
      mul_le_mul (by linarith) (by linarith) hρ₂ (by linarith)
    nlinarith

/-- **Core relative displacement lemma.**  If the phase of `x` is `π r` away from the crossing
(`0 ≤ r ≤ 1`), then `|μ_a(x) - τ|` equals `π γ r/(N+τ)` up to a relative factor `1 ± K/N`,
UNIFORMLY in `r` (the bound is multiplicative in `r`). -/
theorem rel_disp (h : InteriorParam a τ) {N : ℕ} (hN1 : 1 ≤ N) {x r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hG : |Gph N a x - Gph N a (crossAngle a τ)| = π * r) :
    (1 - Ksm a τ / N) * (π * gam a τ * r / (N + τ)) ≤ |symbol a x - τ| ∧
      |symbol a x - τ| ≤ (1 + Ksm a τ / N) * (π * gam a τ * r / (N + τ)) := by
  have ha0 := h.1
  have ha1 := h.2.1
  have hτ := h.tau_pos
  have hγ := gam_pos h
  have hpi := Real.pi_pos
  have hLm := Lmu_nonneg ha0 ha1
  have hL2 := L2mu_nonneg ha0 ha1
  set θτ := crossAngle a τ with hθτ
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  -- MVT on `G_N` and on `μ_a`
  obtain ⟨ξ, hξ, hG'⟩ := mvt_between (hasDerivAt_Gph ha0 ha1 N) x θτ
  obtain ⟨η, hη, hμ'⟩ := mvt_between (hasDerivAt_symbol ha0 ha1) x θτ
  set u := |x - θτ| with hu
  have hu0 : 0 ≤ u := abs_nonneg _
  have hpos : (0 : ℝ) < N + symbol a ξ := by have := symbol_pos ha0 ha1 ξ; positivity
  have key : (N + symbol a ξ) * u = π * r := by
    rw [← hG, hG', abs_mul, abs_of_pos hpos]
  have hdisp : |symbol a x - τ| = |dmu a η| * u := by
    rw [← symbol_crossAngle h, hμ', abs_mul]
  -- `u ≤ π/N`
  have hub : u ≤ π / N := by
    rw [le_div_iff₀ (by linarith)]
    have h1 : (N : ℝ) * u ≤ (N + symbol a ξ) * u :=
      mul_le_mul_of_nonneg_right (by linarith [symbol_pos ha0 ha1 ξ]) hu0
    have h2 : π * r ≤ π := by nlinarith
    linarith [mul_comm u (N : ℝ)]
  -- the two relative factors
  set ρ₁ := |dmu a η| / gam a τ with hρ₁
  set ρ₂ := (N + τ) / (N + symbol a ξ) with hρ₂
  have hρ₁0 : 0 ≤ ρ₁ := by positivity
  have hρ₂0 : 0 ≤ ρ₂ := by positivity
  have e1 : |ρ₁ - 1| ≤ π * L2mu a / gam a τ / N := by
    rw [hρ₁, show |dmu a η| / gam a τ - 1 = (|dmu a η| - gam a τ) / gam a τ by field_simp,
      abs_div, abs_of_pos hγ, div_le_iff₀ hγ,
      show π * L2mu a / gam a τ / N * gam a τ = π * L2mu a / N by field_simp]
    have hl := dmu_lipschitz ha0 ha1 η θτ
    have hab := abs_abs_sub_abs_le_abs_sub (dmu a η) (dmu a θτ)
    calc |(|dmu a η| - gam a τ)| ≤ L2mu a * |η - θτ| := hab.trans hl
      _ ≤ L2mu a * u := mul_le_mul_of_nonneg_left hη hL2
      _ ≤ L2mu a * (π / N) := mul_le_mul_of_nonneg_left hub hL2
      _ = π * L2mu a / N := by ring
  have e2 : |ρ₂ - 1| ≤ π * Lmu a / N := by
    rw [hρ₂, show (N + τ) / (N + symbol a ξ) - 1 = (τ - symbol a ξ) / (N + symbol a ξ) by
      field_simp; ring, abs_div, abs_of_pos hpos, abs_sub_comm]
    have hl := symbol_lipschitz ha0 ha1 ξ θτ
    rw [show symbol a θτ = τ from symbol_crossAngle h] at hl
    rw [div_le_iff₀ hpos]
    calc |symbol a ξ - τ| ≤ Lmu a * |ξ - θτ| := hl
      _ ≤ Lmu a * u := mul_le_mul_of_nonneg_left hξ hLm
      _ ≤ Lmu a * (π / N) := mul_le_mul_of_nonneg_left hub hLm
      _ = π * Lmu a / N * 1 := by ring
      _ ≤ π * Lmu a / N * (N + symbol a ξ) := by
          apply mul_le_mul_of_nonneg_left (by linarith [symbol_pos ha0 ha1 ξ]) (by positivity)
  obtain ⟨plo, phi⟩ := prod_rel e1 e2 hρ₁0 hρ₂0
  -- `|μ(x) - τ| = A ρ₁ ρ₂`
  set A := π * gam a τ * r / (N + τ) with hA
  have hA0 : 0 ≤ A := by positivity
  have hfac : |symbol a x - τ| = A * (ρ₁ * ρ₂) := by
    rw [hdisp, hA, hρ₁, hρ₂]
    have hu' : u = π * r / (N + symbol a ξ) := by rw [← key]; field_simp
    rw [hu']; field_simp
  -- collect the constants
  have hK : π * L2mu a / gam a τ / N + π * Lmu a / N +
      π * L2mu a / gam a τ / N * (π * Lmu a / N) ≤ Ksm a τ / N := by
    unfold Ksm
    have hc1 : 0 ≤ π * L2mu a / gam a τ := by positivity
    have hc2 : 0 ≤ π * Lmu a := by positivity
    have : π * L2mu a / gam a τ / N * (π * Lmu a / N) ≤ π * L2mu a / gam a τ * (π * Lmu a) / N := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_nonneg hc1 hc2
      nlinarith [mul_le_mul_of_nonneg_left (show (N : ℝ) ≤ N * N by nlinarith) this]
    rw [add_div, add_div]
    linarith
  have hK' : π * L2mu a / gam a τ / N + π * Lmu a / N ≤ Ksm a τ / N := by
    have : 0 ≤ π * L2mu a / gam a τ / N * (π * Lmu a / N) := by positivity
    linarith
  constructor
  · rw [hfac]
    calc (1 - Ksm a τ / N) * A = A * (1 - Ksm a τ / N) := mul_comm _ _
      _ ≤ A * (ρ₁ * ρ₂) := mul_le_mul_of_nonneg_left (by linarith) hA0
  · rw [hfac]
    calc A * (ρ₁ * ρ₂) ≤ A * (1 + Ksm a τ / N) := mul_le_mul_of_nonneg_left (by linarith) hA0
      _ = (1 + Ksm a τ / N) * A := mul_comm _ _

/-- Threshold for the relative estimate: `n₁ = n₀ + ⌈K⌉`. -/
noncomputable def n1 (a τ : ℝ) : ℕ := n0 a τ + ⌈Ksm a τ⌉₊

/-- **G4.2 — `thm:smin`, eq. `(smin)`, in uniform RELATIVE form.**  For every `N ≥ n₁(a,τ)`
(singular or not):
`(1 - K/N) · πγ d_N/(N+τ) ≤ σ_min(B_N) ≤ (1 + K/N) · πγ d_N/(N+τ)`. -/
theorem thm_smin_relative (h : InteriorParam a τ) {N : ℕ} (hN : n1 a τ ≤ N) :
    (1 - Ksm a τ / N) * (π * gam a τ * dN N a τ / (N + τ)) ≤ sigmaMin N a τ ∧
      sigmaMin N a τ ≤ (1 + Ksm a τ / N) * (π * gam a τ * dN N a τ / (N + τ)) := by
  have ha0 := h.1
  have ha1 := h.2.1
  have hτ := h.tau_pos
  have hγ := gam_pos h
  have hpi := Real.pi_pos
  have hN0 : n0 a τ ≤ N := le_trans (Nat.le_add_right _ _) hN
  obtain ⟨hN2, hX0, hX1⟩ := n0_spec h hN0
  have hβ := (alpha_beta_bounds h).2.1
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hKN : Ksm a τ / N ≤ 1 := by
    rw [div_le_one (by linarith)]
    have := Nat.le_ceil (Ksm a τ)
    have : (⌈Ksm a τ⌉₊ : ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_add_left _ _) hN
    linarith
  have hK0 := Ksm_nonneg h
  set X := resid N a τ with hX
  have hdX : dN N a τ = distZ X := rfl
  by_cases hint : ∃ z : ℤ, X = z
  · -- singular dimension: `d_N = 0 = σ_min`
    obtain ⟨z, hz⟩ := hint
    have hd0 : dN N a τ = 0 := by rw [hdX, (distZ_eq_zero_iff X).2 ⟨z, hz⟩]
    have hsing : (shifted N a τ).det = 0 := (thm_sing h hN2).2 ⟨z, by rw [← hz]; rfl⟩
    obtain ⟨k, hk1, hkN, hk⟩ := (det_eq_zero_iff_lam ha0 ha1 hN2 τ).1 hsing
    have hs0 : sigmaMin N a τ = 0 := le_antisymm
      (by have := sigmaMin_le (N := N) a τ hk1 hkN; rwa [hk, abs_zero] at this)
      (sigmaMin_nonneg (by omega) a τ)
    rw [hd0, hs0]; simp
  · push_neg at hint
    -- bracketing indices `j = ⌊X⌋ + 1`, `j + 1`
    have hfl0 : 0 ≤ ⌊X⌋ := Int.floor_nonneg.2 hX0
    have hflt : (⌊X⌋ : ℝ) < X := lt_of_le_of_ne (Int.floor_le X) (fun e => hint _ e.symm)
    have hfl1 : ⌊X⌋ ≤ N - 2 := by
      have : (⌊X⌋ : ℝ) < N - 1 := by linarith
      have : ⌊X⌋ < (N : ℤ) - 1 := by exact_mod_cast this
      omega
    set j := (⌊X⌋ + 1).toNat with hj
    have hjz : (j : ℤ) = ⌊X⌋ + 1 := Int.toNat_of_nonneg (by omega)
    have hjr : (j : ℝ) = ⌊X⌋ + 1 := by exact_mod_cast hjz
    have hj1 : 1 ≤ j := by omega
    have hjN : j + 1 ≤ N := by omega
    set r₁ := X - ⌊X⌋ with hr₁
    set r₂ := (⌊X⌋ : ℝ) + 1 - X with hr₂
    have hr₁0 : 0 ≤ r₁ := by linarith
    have hr₂0 : 0 ≤ r₂ := by linarith [Int.lt_floor_add_one X]
    have hr₁1 : r₁ ≤ 1 := by linarith [Int.lt_floor_add_one X]
    have hr₂1 : r₂ ≤ 1 := by linarith
    have hfr : Int.fract X = r₁ := rfl
    have hdmin : dN N a τ = min r₁ r₂ := by
      rw [hdX, distZ, abs_sub_round_eq_min, hfr, hr₂]; congr 1; ring
    have hG1 : |Gph N a (eigAngle N a j) - Gph N a (crossAngle a τ)| = π * r₁ := by
      rw [Gph_eig_sub_cross h hj1 (by omega), ← hX, hjr,
        show π * ((⌊X⌋ : ℝ) + 1 - 1 - X) = -(π * r₁) by rw [hr₁]; ring, abs_neg,
        abs_of_nonneg (by positivity)]
    have hG2 : |Gph N a (eigAngle N a (j + 1)) - Gph N a (crossAngle a τ)| = π * r₂ := by
      rw [Gph_eig_sub_cross h (by omega) hjN, ← hX]
      push_cast
      rw [hjr, show π * ((⌊X⌋ : ℝ) + 1 + 1 - 1 - X) = π * r₂ by rw [hr₂]; ring,
        abs_of_nonneg (by positivity)]
    obtain ⟨l1, u1⟩ := rel_disp h (by omega) hr₁0 hr₁1 hG1
    obtain ⟨l2, u2⟩ := rel_disp h (by omega) hr₂0 hr₂1 hG2
    -- monotonicity: the minimum is attained at `j` or `j + 1`
    have hanti := symbol_strictAntiOn ha0 ha1
    have memI : ∀ k, 1 ≤ k → k ≤ N → eigAngle N a k ∈ Icc 0 π := fun k hk1 hkN =>
      let hk := (eigAngle_spec ha0 ha1 hk1 hkN).1; ⟨hk.1.le, hk.2.le⟩
    have hθτI : crossAngle a τ ∈ Icc 0 π := let hθ := crossAngle_mem h; ⟨hθ.1.le, hθ.2.le⟩
    have hj_lt : eigAngle N a j < crossAngle a τ := by
      rw [← (strictMono_Gph ha0 ha1 N).lt_iff_lt, (eigAngle_spec ha0 ha1 hj1 (by omega)).2,
        Gph_crossAngle h, show (N : ℝ) * alphaOf a τ - betaOf a τ = X from rfl, hjr]
      nlinarith
    have hj1_gt : crossAngle a τ < eigAngle N a (j + 1) := by
      rw [← (strictMono_Gph ha0 ha1 N).lt_iff_lt, (eigAngle_spec ha0 ha1 (by omega) hjN).2,
        Gph_crossAngle h, show (N : ℝ) * alphaOf a τ - betaOf a τ = X from rfl]
      push_cast; rw [hjr]
      nlinarith [Int.lt_floor_add_one X]
    have hmono : ∀ k, 1 ≤ k → k ≤ N →
        min |lam N a τ j| |lam N a τ (j + 1)| ≤ |lam N a τ k| := by
      intro k hk1 hkN
      rcases le_or_gt k j with hkj | hkj
      · apply min_le_of_left_le
        have hθ : eigAngle N a k ≤ eigAngle N a j := by
          rcases hkj.lt_or_eq with hl | he
          · exact (eigAngle_lt ha0 ha1 hk1 hl (by omega)).le
          · rw [he]
        have h1 : symbol a (eigAngle N a j) ≤ symbol a (eigAngle N a k) :=
          hanti.antitoneOn (memI k hk1 hkN) (memI j hj1 (by omega)) hθ
        have h2 : τ < symbol a (eigAngle N a j) := by
          rw [← symbol_crossAngle h]; exact hanti (memI j hj1 (by omega)) hθτI hj_lt
        unfold lam
        rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
        linarith
      · apply min_le_of_right_le
        have hθ : eigAngle N a (j + 1) ≤ eigAngle N a k := by
          rcases (Nat.succ_le_of_lt hkj).lt_or_eq with hl | he
          · exact (eigAngle_lt ha0 ha1 (by omega) hl hkN).le
          · subst he; exact le_rfl
        have h1 : symbol a (eigAngle N a k) ≤ symbol a (eigAngle N a (j + 1)) :=
          hanti.antitoneOn (memI (j + 1) (by omega) hjN) (memI k hk1 hkN) hθ
        have h2 : symbol a (eigAngle N a (j + 1)) < τ := by
          rw [← symbol_crossAngle h]; exact hanti hθτI (memI (j + 1) (by omega) hjN) hj1_gt
        unfold lam
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
        linarith
    have hB : 0 ≤ π * gam a τ / (N + τ) := by positivity
    have hKl : 0 ≤ 1 - Ksm a τ / N := by linarith
    constructor
    · -- lower bound: both bracketing eigenvalues are ≥ (1 - K/N) A
      apply le_sigmaMin (by omega) a τ
      intro k hk1 hkN
      refine le_trans ?_ (hmono k hk1 hkN)
      apply le_min
      · refine le_trans ?_ l1
        rw [hdmin]
        have := min_le_left r₁ r₂
        have : π * gam a τ * min r₁ r₂ / (N + τ) ≤ π * gam a τ * r₁ / (N + τ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left this (by positivity)
        exact mul_le_mul_of_nonneg_left this hKl
      · refine le_trans ?_ l2
        rw [hdmin]
        have := min_le_right r₁ r₂
        have : π * gam a τ * min r₁ r₂ / (N + τ) ≤ π * gam a τ * r₂ / (N + τ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left this (by positivity)
        exact mul_le_mul_of_nonneg_left this hKl
    · -- upper bound: σ_min ≤ the bracketing eigenvalue realising `d_N` (ties allowed)
      rw [hdmin]
      rcases le_total r₁ r₂ with hle | hle
      · rw [min_eq_left hle]
        exact (sigmaMin_le a τ hj1 (by omega)).trans u1
      · rw [min_eq_right hle]
        exact (sigmaMin_le a τ (by omega) hjN).trans u2

/-- Corollary: at nonsingular `N ≥ n₁`, `|σ_min / A_N - 1| ≤ K/N`. -/
theorem smin_ratio (h : InteriorParam a τ) {N : ℕ} (hN : n1 a τ ≤ N) (hns : Nonsingular N a τ) :
    |sigmaMin N a τ / (π * gam a τ * dN N a τ / (N + τ)) - 1| ≤ Ksm a τ / N := by
  have hN0 : n0 a τ ≤ N := le_trans (Nat.le_add_right _ _) hN
  obtain ⟨hN2, -, -⟩ := n0_spec h hN0
  have hd : 0 < dN N a τ := by
    rcases (distZ_nonneg (resid N a τ)).lt_or_eq with hl | he
    · exact hl
    · exfalso; apply hns
      exact (thm_sing h hN2).2 ((distZ_eq_zero_iff _).1 he.symm)
  have hA : 0 < π * gam a τ * dN N a τ / (N + τ) := by
    have := gam_pos h; have := h.tau_pos; have := Real.pi_pos; positivity
  obtain ⟨lo, hi⟩ := thm_smin_relative h hN
  rw [abs_le, le_sub_iff_add_le, sub_le_iff_le_add, le_div_iff₀ hA, div_le_iff₀ hA]
  constructor <;> nlinarith

end SminRel

end ShiftedKMS
