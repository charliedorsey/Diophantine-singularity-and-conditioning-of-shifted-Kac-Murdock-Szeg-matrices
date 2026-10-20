import KMS.Paper
import KMS.MatrixBridge
import KMS.Sharpen

/-!
# Corresponding formal statements for the numbered results of the paper

Reference manuscript: `manuscript/shifted_kms.tex` in this public companion.

For every labeled theorem-like environment of the accompanying manuscript there is exactly one theorem
`ShiftedKMS.PaperStatement.<label>` (`:`/`-` replaced by `_`) whose statement carries **every
clause** of the environment. Conventions:

* matrices are the actual Mathlib matrices `kms N a = [a^{|i-j|}]`, `shifted N a τ = T_N(a) - τ I`,
  in the paper's range `N ≥ 2` (eq. `(Tdef)`);
* `κ₂(B_N)` is `kappaMat N a τ = ‖B_N‖₂ · ‖B_N⁻¹‖₂` with Mathlib's induced `ℓ²→ℓ²` operator norm
  (`Matrix.Norms.L2Operator`); `σ_min(B_N) = sigmaMinMat = inf_{‖x‖₂=1} ‖B_N x‖₂`,
  `σ_max(B_N) = sigmaMaxMat = ‖B_N‖₂`. Where the paper needs `κ₂ = +∞` at a singular dimension the
  value is `kappaMatE : EReal`, which is `⊤` exactly when `B_N` is not invertible;
* `F = X (1 + O(N^{-p}))` "for all sufficiently large `N` [with property `P`]" is
  `RelBigO p P F X := ∃ K > 0, ∃ N₀, ∀ N ≥ N₀, P N → |F N - X N| ≤ K / N^p · |X N|`
  (constants depend on the fixed `(a, τ)`, as the paper states);
* weak convergence of measures is `WeakLim` (convergence of integrals of every bounded continuous
  test function), the definition of weak convergence.
-/

open Real Set Filter Topology MeasureTheory Matrix Finset
open scoped Matrix.Norms.L2Operator ENNReal BoundedContinuousFunction RealInnerProductSpace
open Classical

namespace ShiftedKMS

/-! ## Matrix-level spectral quantities -/

/-- `σ_max(B_N) = ‖B_N‖₂` (induced operator 2-norm). -/
noncomputable def sigmaMaxMat (N : ℕ) (a τ : ℝ) : ℝ := ‖shifted N a τ‖

/-- `σ_min(B_N) = inf_{‖x‖₂ = 1} ‖B_N x‖₂`. -/
noncomputable def sigmaMinMat (N : ℕ) (a τ : ℝ) : ℝ :=
  ⨅ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
    ‖(Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) x‖

/-- `κ₂(B_N) = ‖B_N‖₂ ‖B_N⁻¹‖₂` (real-valued; Mathlib's `B⁻¹ = 0` at a singular `B`). -/
noncomputable def kappaMat (N : ℕ) (a τ : ℝ) : ℝ := ‖shifted N a τ‖ * ‖(shifted N a τ)⁻¹‖

/-- `κ₂(B_N) ∈ (-∞, +∞]`: the operator-norm condition number, `+∞` at a singular dimension. -/
noncomputable def kappaMatE (N : ℕ) (a τ : ℝ) : EReal :=
  if IsUnit (shifted N a τ) then ((kappaMat N a τ : ℝ) : EReal) else ⊤

/-- Paper-shaped relative error: `F = X (1 + O(N^{-p}))` for all sufficiently large `N`
satisfying `P`. -/
def RelBigO (p : ℕ) (P : ℕ → Prop) (F X : ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → P N → |F N - X N| ≤ K / (N : ℝ) ^ p * |X N|

/-- Paper-shaped absolute error: `F = X + O(N^{-p})` for all sufficiently large `N`. -/
def AbsBigO (p : ℕ) (F X : ℕ → ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |F N - X N| ≤ K / (N : ℝ) ^ p

namespace PaperStatement

variable {a τ : ℝ}

/-! ### Bridges (all `N ≥ 2`) -/

lemma isUnit_iff_nonsingular {N : ℕ} : IsUnit (shifted N a τ) ↔ Nonsingular N a τ := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]; rfl

lemma sigmaMaxMat_eq (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) :
    sigmaMaxMat N a τ = sigmaMax N a τ :=
  (sigmaMax_eq_opNorm ha0 ha1 hN τ).symm

lemma sigmaMinMat_eq (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) :
    sigmaMinMat N a τ = sigmaMin N a τ :=
  (sigmaMin_eq_iInf_sphere ha0 ha1 hN τ).symm

lemma kappaMat_eq (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) :
    kappaMat N a τ = kappa N a τ := by
  by_cases hns : Nonsingular N a τ
  · exact (kappa_eq_operator_twoNorm_conditionNumber ha0 ha1 hN τ hns).symm
  · have h0 : sigmaMin N a τ = 0 := by
      have := sigmaMin_nonneg (N := N) (by omega) a τ
      have h' : ¬ 0 < sigmaMin N a τ := fun h => hns ((nonsingular_iff_sigmaMin_pos ha0 ha1 hN τ).2 h)
      linarith [not_lt.1 h']
    have hinv : (shifted N a τ)⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rw [isUnit_iff_ne_zero]; exact hns)
    rw [kappaMat, kappa, hinv, h0, norm_zero, mul_zero, div_zero]

lemma kappaMatE_eq (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) :
    kappaMatE N a τ = if Nonsingular N a τ then ((kappa N a τ : ℝ) : EReal) else ⊤ := by
  rw [kappaMatE, kappaMat_eq ha0 ha1 hN]
  simp only [isUnit_iff_nonsingular]

lemma sigmaMinMat_eq_zero_of_singular (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N)
    (hs : (shifted N a τ).det = 0) : sigmaMinMat N a τ = 0 := by
  rw [sigmaMinMat_eq ha0 ha1 hN]
  have := sigmaMin_nonneg (N := N) (by omega) a τ
  have h' : ¬ 0 < sigmaMin N a τ := fun h => (nonsingular_iff_sigmaMin_pos ha0 ha1 hN τ).2 h hs
  linarith [not_lt.1 h']

/-! ### `RelBigO` toolkit -/

lemma relBigO_of_two_sided {p : ℕ} {P : ℕ → Prop} {F X : ℕ → ℝ} {c : ℝ} {N₀ : ℕ}
    (h : ∀ N, N₀ ≤ N → P N → 0 ≤ X N ∧
      (1 - c / (N : ℝ) ^ p) * X N ≤ F N ∧ F N ≤ (1 + c / (N : ℝ) ^ p) * X N) :
    RelBigO p P F X := by
  refine ⟨max c 1, lt_of_lt_of_le one_pos (le_max_right _ _), N₀, fun N hN hP => ?_⟩
  obtain ⟨hX, h1, h2⟩ := h N hN hP
  rw [abs_of_nonneg hX]
  have hpow : 0 ≤ (N : ℝ) ^ p := by positivity
  have hcK : c / (N : ℝ) ^ p ≤ max c 1 / (N : ℝ) ^ p :=
    div_le_div_of_nonneg_right (le_max_left _ _) hpow
  have hb : |F N - X N| ≤ c / (N : ℝ) ^ p * X N := by
    rw [abs_le]; constructor <;> nlinarith
  exact hb.trans (mul_le_mul_of_nonneg_right hcK hX)

lemma relBigO_of_abs {p : ℕ} {P : ℕ → Prop} {F X : ℕ → ℝ} {c : ℝ} {N₀ : ℕ}
    (h : ∀ N, N₀ ≤ N → P N → 0 ≤ X N ∧ |F N - X N| ≤ c / (N : ℝ) ^ p * X N) :
    RelBigO p P F X := by
  refine relBigO_of_two_sided (c := c) (N₀ := N₀) fun N hN hP => ?_
  obtain ⟨hX, hb⟩ := h N hN hP
  rw [abs_le] at hb
  exact ⟨hX, by nlinarith [hb.1], by nlinarith [hb.2]⟩

lemma RelBigO.congr {p : ℕ} {P : ℕ → Prop} {F G X : ℕ → ℝ} (h : RelBigO p P F X) (M : ℕ)
    (hFG : ∀ N, M ≤ N → P N → F N = G N) : RelBigO p P G X := by
  obtain ⟨K, hK, N₀, hN₀⟩ := h
  exact ⟨K, hK, max N₀ M, fun N hN hP =>
    hFG N (le_of_max_le_right hN) hP ▸ hN₀ N (le_of_max_le_left hN) hP⟩

lemma RelBigO.mono {p : ℕ} {P Q : ℕ → Prop} {F X : ℕ → ℝ} (h : RelBigO p P F X)
    (hQP : ∀ N, Q N → P N) : RelBigO p Q F X := by
  obtain ⟨K, hK, N₀, hN₀⟩ := h
  exact ⟨K, hK, N₀, fun N hN hQ => hN₀ N hN (hQP N hQ)⟩

/-! ### Empirical-measure congruences (only the window `N ≥ 2` is ever sampled) -/

lemma empMeasure_congr {X : Type*} [MeasurableSpace X] {x y : ℕ → X}
    (h : ∀ N, 2 ≤ N → x N = y N) : empMeasure x = empMeasure y := by
  funext L
  unfold empMeasure
  congr 1
  refine Finset.sum_congr rfl fun N hN => ?_
  rw [h N (Finset.mem_Icc.1 hN).1]

lemma empMeasureStar_congr {x y : ℕ → ℝ} (h : ∀ N, 2 ≤ N → x N = y N) :
    empMeasureStar a τ x = empMeasureStar a τ y := by
  funext L
  unfold empMeasureStar
  congr 1
  refine Finset.sum_congr rfl fun N hN => ?_
  rw [h N (Finset.mem_Icc.1 (Finset.mem_filter.1 hN).1).1]


/-! ## Auxiliary identities used by the canonical statements -/

/-- `‖x‖ = dist(x, ℤ)` (manuscript eq. `(dN)`): `distZ` is the distance to the integers. -/
lemma distZ_eq_infDist (x : ℝ) : distZ x = Metric.infDist x (Set.range ((↑) : ℤ → ℝ)) := by
  apply le_antisymm
  · rw [Metric.le_infDist (show (Set.range ((↑) : ℤ → ℝ)).Nonempty from ⟨0, 0, by simp⟩)]
    rintro _ ⟨z, rfl⟩
    rw [Real.dist_eq, distZ]
    exact round_le x z
  · refine (Metric.infDist_le_dist_of_mem
      (show ((round x : ℤ) : ℝ) ∈ Set.range ((↑) : ℤ → ℝ) from ⟨round x, rfl⟩)).trans (le_of_eq ?_)
    rw [Real.dist_eq, distZ]

/-- The crossing angle is the **unique** `θ ∈ (0,π)` with `μ_a(θ) = τ` (eq. `(crossing)`). -/
lemma crossing_unique (h : InteriorParam a τ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (hs : symbol a θ = τ) :
    θ = crossAngle a τ := by
  have hc := crossAngle_mem h
  have e := hs.trans (symbol_crossAngle h).symm
  have hR1 := Ra_pos h.1 h.2.1 θ
  have hR2 := Ra_pos h.1 h.2.1 (crossAngle a τ)
  rw [symbol_eq_div_Ra, symbol_eq_div_Ra, div_eq_div_iff hR1.ne' hR2.ne'] at e
  have h1a : (1 - a ^ 2) ≠ 0 := by nlinarith [h.1, h.2.1]
  have hR : Ra a (crossAngle a τ) = Ra a θ := mul_left_cancel₀ h1a e
  unfold Ra at hR
  have hcos : Real.cos θ = Real.cos (crossAngle a τ) :=
    mul_left_cancel₀ (show (2 * a) ≠ 0 by have := h.1; positivity) (by linarith)
  exact Real.injOn_cos ⟨hθ.1.le, hθ.2.le⟩ ⟨hc.1.le, hc.2.le⟩ hcos

lemma upperEdge_pos' (ha0 : 0 < a) (ha1 : a < 1) : 0 < upperEdge a :=
  (lowerEdge_pos ha0 ha1).trans (edges_lt ha0 ha1)

/-! ## §2 KMS quantization and Blaschke phase -/

/-- **`lem:phase`** (with `ψ_a(θ) = arg(D + iE)` and `R = √(D² + E²)` exactly as in the
manuscript): `R = 1 - 2a cos θ + a²`; `ψ_a(θ) ∈ (0,π)`; `S_N(θ) = R(θ) sin(Nθ + ψ_a(θ))` on `(0,π)`;
and `ψ_a` extends continuously to `[0,π]` with `ψ_a(0) = 0`, `ψ_a(π) = π`. -/
theorem lem_phase (ha0 : 0 < a) (ha1 : a < 1) :
    (∀ θ : ℝ, Real.sqrt (Da a θ ^ 2 + Ea a θ ^ 2) = 1 - 2 * a * Real.cos θ + a ^ 2) ∧
    (∀ θ ∈ Ioo 0 π, Complex.arg ((Da a θ : ℂ) + (Ea a θ : ℂ) * Complex.I) ∈ Ioo 0 π) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Ioo 0 π,
      secular N a θ = Real.sqrt (Da a θ ^ 2 + Ea a θ ^ 2) *
        Real.sin (N * θ + Complex.arg ((Da a θ : ℂ) + (Ea a θ : ℂ) * Complex.I))) ∧
    ∃ g : ℝ → ℝ, ContinuousOn g (Icc 0 π) ∧
      (∀ θ ∈ Ioo 0 π, g θ = Complex.arg ((Da a θ : ℂ) + (Ea a θ : ℂ) * Complex.I)) ∧
      g 0 = 0 ∧ g π = π := by
  refine ⟨fun θ => (Ra_eq_sqrt ha0 ha1 θ).symm, fun θ hθ => ?_, fun N _ θ hθ => ?_,
    psi a, (continuous_psi ha0 ha1).continuousOn, fun θ hθ => psi_eq_arg ha0 ha1 hθ,
    psi_zero a, psi_pi a⟩
  · rw [← psi_eq_arg ha0 ha1 hθ]; exact psi_mem_Ioo ha0 ha1 hθ
  · rw [← psi_eq_arg ha0 ha1 hθ, ← Ra_eq_sqrt ha0 ha1]; exact ShiftedKMS.lem_phase ha0 ha1 N θ

/-- **`prop:blaschke`**: `e^{iψ_a(θ)} = b_a(e^{iθ})` on `(0,π)` (eq. `(blaschkephase)`);
`ψ_a'(θ) = (1-a²)/|1-ae^{iθ}|² = μ_a(θ)` (eq. `(psiprime)`); and `z_k^N b_a(z_k) = (-1)^k` at every
eigenangle (eq. `(blaschkequant)`). -/
theorem prop_blaschke (ha0 : 0 < a) (ha1 : a < 1) :
    (∀ θ ∈ Ioo 0 π,
      Complex.exp (((Complex.arg ((Da a θ : ℂ) + (Ea a θ : ℂ) * Complex.I) : ℝ) : ℂ) * Complex.I) =
        (Complex.exp (θ * Complex.I) - a) / (1 - a * Complex.exp (θ * Complex.I))) ∧
    (∀ θ ∈ Ioo 0 π,
      HasDerivAt (fun t : ℝ => Complex.arg ((Da a t : ℂ) + (Ea a t : ℂ) * Complex.I))
        ((1 - a ^ 2) / ‖1 - (a : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2) θ ∧
      (1 - a ^ 2) / ‖1 - (a : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 = symbol a θ) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ k : ℕ, 1 ≤ k → k ≤ N →
      Complex.exp (eigAngle N a k * Complex.I) ^ N *
        ((Complex.exp (eigAngle N a k * Complex.I) - a) /
          (1 - a * Complex.exp (eigAngle N a k * Complex.I))) = (-1) ^ k) := by
  refine ⟨fun θ hθ => ?_, fun θ hθ => ?_, fun N _ k hk1 hkN => blaschke_quant ha0 ha1 hk1 hkN⟩
  · rw [← psi_eq_arg ha0 ha1 hθ]; exact blaschke_phase ha0 ha1 θ
  · have hn : ‖1 - (a : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 = Ra a θ := by
      rw [← Complex.normSq_eq_norm_sq, normSq_one_sub]
    rw [hn]
    refine ⟨?_, rfl⟩
    refine (hasDerivAt_psi ha0 ha1 θ).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with t ht using (psi_eq_arg ha0 ha1 ht).symm

/-- **`thm:quant`** (`N ≥ 2`): on `(0,π)`, `G_N(θ) = Nθ + ψ_a(θ)` with `ψ_a = arg(D+iE)` (eq. `(G)`); each `θ_k` is the unique point of `(0,π)` with `G_N(θ) = kπ`;
`0 < θ_1 < ⋯ < θ_N < π`; these give the whole spectrum of `T_N(a)`; every eigenvalue is simple;
the spacing law `(spacing)`; the eigenpairs `(eigs)`; and the eigenvalues of `B_N(a,τ)`, as
Mathlib's eigenvalue multiset of the symmetric matrix, are `μ_a(θ_k) - τ` (eq. `(shiftedeigs)`). -/
theorem thm_quant (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) :
    (∀ θ ∈ Ioo 0 π, Gph N a θ = N * θ + Complex.arg ((Da a θ : ℂ) + (Ea a θ : ℂ) * Complex.I)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ N → ∃! θ, θ ∈ Ioo 0 π ∧ Gph N a θ = k * π) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ N → eigAngle N a k ∈ Ioo 0 π ∧ Gph N a (eigAngle N a k) = k * π) ∧
    (∀ k : ℕ, 1 ≤ k → k + 1 ≤ N → eigAngle N a k < eigAngle N a (k + 1)) ∧
    spectrum ℝ (kms N a) = {μ | ∃ k, 1 ≤ k ∧ k ≤ N ∧ μ = symbol a (eigAngle N a k)} ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ N →
      Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' (kms N a))
        (symbol a (eigAngle N a k))) = 1) ∧
    (∀ k l : ℕ, 1 ≤ k → k ≤ N → 1 ≤ l → l ≤ N →
      symbol a (eigAngle N a k) = symbol a (eigAngle N a l) → k = l) ∧
    (∀ k : ℕ, 1 ≤ k → k + 1 ≤ N →
      π / (N + upperEdge a) ≤ eigAngle N a (k + 1) - eigAngle N a k ∧
        eigAngle N a (k + 1) - eigAngle N a k ≤ π / (N + lowerEdge a)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ N →
      (fun j : Fin N => Real.sin ((((j : ℕ) : ℝ) + 1) * eigAngle N a k) -
          a * Real.sin (((j : ℕ) : ℝ) * eigAngle N a k)) ≠ 0 ∧
      (kms N a) *ᵥ (fun j : Fin N => Real.sin ((((j : ℕ) : ℝ) + 1) * eigAngle N a k) -
          a * Real.sin (((j : ℕ) : ℝ) * eigAngle N a k)) =
        symbol a (eigAngle N a k) • (fun j : Fin N => Real.sin ((((j : ℕ) : ℝ) + 1) * eigAngle N a k) -
          a * Real.sin (((j : ℕ) : ℝ) * eigAngle N a k))) ∧
    (∀ τ : ℝ, Multiset.map (shifted_isHermitian N a τ).eigenvalues Finset.univ.val =
      Multiset.map (fun k : Fin N => symbol a (eigAngle N a (k.val + 1)) - τ) Finset.univ.val) := by
  refine ⟨fun θ hθ => by rw [Gph, psi_eq_arg ha0 ha1 hθ],
    fun k hk1 hkN => eigAngle_existsUnique ha0 ha1 hk1 hkN,
    fun k hk1 hkN => eigAngle_spec ha0 ha1 hk1 hkN, fun k hk1 hk2 => ?_, spectrum_kms ha0 ha1 hN,
    fun k hk1 hkN => kms_eigenspace_finrank_one ha0 ha1 hN hk1 hkN,
    fun k l hk1 hkN hl1 hlN hkl => ?_, fun k hk1 hk2 => eigAngle_spacing ha0 ha1 hk1 hk2,
    fun k hk1 hkN => ⟨(kms_eigenpair ha0 ha1 hN hk1 hkN).2, (kms_eigenpair ha0 ha1 hN hk1 hkN).1⟩,
    fun τ => eigenvalues_multiset ha0 ha1 hN τ⟩
  · have hsp := (eigAngle_spacing ha0 ha1 hk1 hk2).1
    have : 0 < π / (N + upperEdge a) := by
      have := upperEdge_pos' ha0 ha1; positivity
    linarith
  · have := lamF_injective ha0 ha1 N 0 (a₁ := ⟨k - 1, by omega⟩) (a₂ := ⟨l - 1, by omega⟩)
      (by simp only [lamF, lam]; rw [show k - 1 + 1 = k by omega, show l - 1 + 1 = l by omega, hkl])
    have := congrArg Fin.val this
    simp only at this
    omega

/-! ## §3 The Diophantine triangle and the determinant -/

/-- **`thm:triangle`** together with the section's standing definitions: the crossing angle is the
unique `θ_τ ∈ (0,π)` with `μ_a(θ_τ) = τ` and satisfies `(costheta)`; `α = θ_τ/π`,
`β = 1 - ψ_a(θ_τ)/π` with `ψ_a = arg(D+iE)`; `(a,τ) ↦ (α,β)` is a bijection of the interior region
onto the open triangle `𝒟`; and the inverse is `(inverse)`. -/
theorem thm_triangle :
    (∀ a τ : ℝ, InteriorParam a τ →
      crossAngle a τ ∈ Ioo 0 π ∧ symbol a (crossAngle a τ) = τ ∧
      (∀ θ ∈ Ioo 0 π, symbol a θ = τ → θ = crossAngle a τ) ∧
      Real.cos (crossAngle a τ) = (1 + a ^ 2 - (1 - a ^ 2) / τ) / (2 * a) ∧
      alphaOf a τ = crossAngle a τ / π ∧
      betaOf a τ = 1 - Complex.arg ((Da a (crossAngle a τ) : ℂ) +
        (Ea a (crossAngle a τ) : ℂ) * Complex.I) / π) ∧
    Set.BijOn (fun p : ℝ × ℝ => (alphaOf p.1 p.2, betaOf p.1 p.2))
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1 ∧ lowerEdge p.1 < p.2 ∧ p.2 < upperEdge p.1}
      {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1} ∧
    (∀ a τ : ℝ, InteriorParam a τ →
      τ = Real.sin (π * betaOf a τ) / Real.sin (π * alphaOf a τ) ∧
      a = Real.cos (π * (alphaOf a τ + betaOf a τ) / 2) /
        Real.cos (π * (alphaOf a τ - betaOf a τ) / 2)) ∧
    (∀ α β : ℝ, 0 < α → 0 < β → α + β < 1 →
      InteriorParam (Real.cos (π * (α + β) / 2) / Real.cos (π * (α - β) / 2))
        (Real.sin (π * β) / Real.sin (π * α)) ∧
      alphaOf (Real.cos (π * (α + β) / 2) / Real.cos (π * (α - β) / 2))
        (Real.sin (π * β) / Real.sin (π * α)) = α ∧
      betaOf (Real.cos (π * (α + β) / 2) / Real.cos (π * (α - β) / 2))
        (Real.sin (π * β) / Real.sin (π * α)) = β) := by
  refine ⟨fun a τ h => ⟨crossAngle_mem h, symbol_crossAngle h, fun θ hθ hs => crossing_unique h hθ hs,
    cos_crossAngle h, rfl, ?_⟩, triangle_bijOn, fun a τ h => ⟨(triangle_forward h).2.1,
    (triangle_forward h).2.2⟩, fun α β h0 h1 h2 => triangle_inverse ⟨h0, h1, h2⟩⟩
  rw [← psi_eq_arg h.1 h.2.1 (crossAngle_mem h)]; rfl

/-- **`lem:chebshift`** (eqs. `(chebshift)`, `(xdef)`). -/
theorem lem_chebshift {N : ℕ} (hN : 2 ≤ N) (ha0 : 0 < a) (ha1 : a < 1) (hτ : τ ≠ 0) :
    (kms N a - τ • (1 : Matrix (Fin N) (Fin N) ℝ)).det =
      (τ * a) ^ N / (1 - a ^ 2) *
        (Polynomial.eval ((1 - a ^ 2 - τ * (1 + a ^ 2)) / (2 * τ * a))
            (Polynomial.Chebyshev.U ℝ (N : ℤ)) +
          2 * a * Polynomial.eval ((1 - a ^ 2 - τ * (1 + a ^ 2)) / (2 * τ * a))
            (Polynomial.Chebyshev.U ℝ ((N : ℤ) - 1)) +
          a ^ 2 * Polynomial.eval ((1 - a ^ 2 - τ * (1 + a ^ 2)) / (2 * τ * a))
            (Polynomial.Chebyshev.U ℝ ((N : ℤ) - 2))) := by
  have e : kms N a - τ • (1 : Matrix (Fin N) (Fin N) ℝ) = shifted N a τ := by
    rw [shifted]; congr 1; ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]
  rw [e]
  exact ShiftedKMS.lem_chebshift hN ha0 ha1 hτ

/-- **`thm:det`**: eq. `(det)` for every interior pair and `N ≥ 2`; `d_N = dist(Nα - β, ℤ)`
(eq. `(dN)`); and eq. `(detdepth)`. -/
theorem thm_det (h : InteriorParam a τ) :
    (∀ N : ℕ, 2 ≤ N → (shifted N a τ).det =
      (-1) ^ (N + 1) * a ^ N * τ ^ (N - 1) * Real.sin (π * (N * alphaOf a τ - betaOf a τ)) /
        Real.sin (π * alphaOf a τ)) ∧
    (∀ N : ℕ, dN N a τ = Metric.infDist ((N : ℝ) * alphaOf a τ - betaOf a τ)
      (Set.range ((↑) : ℤ → ℝ))) ∧
    (∀ N : ℕ, 2 ≤ N → |(shifted N a τ).det| =
      a ^ N * τ ^ (N - 1) * Real.sin (π * dN N a τ) / Real.sin (π * alphaOf a τ)) :=
  ⟨fun _ hN => ShiftedKMS.thm_det h hN, fun _ => distZ_eq_infDist _,
    fun _ hN => thm_detdepth h hN⟩

/-! ## §4 Exact singularity geometry and recurrence -/

/-- **`thm:sing`**: for an interior pair and every `N ≥ 2`, `B_N` is singular iff `Nα - β ∈ ℤ`
(eq. `(sing)`), and at a singular dimension the nullity is exactly one. -/
theorem thm_sing (h : InteriorParam a τ) :
    ∀ N : ℕ, 2 ≤ N →
      ((shifted N a τ).det = 0 ↔ ∃ z : ℤ, (N : ℝ) * alphaOf a τ - betaOf a τ = z) ∧
      ((shifted N a τ).det = 0 →
        Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (shifted N a τ))) = 1) :=
  fun _ hN => ⟨ShiftedKMS.thm_sing h hN, shifted_nullity_one h hN⟩

lemma rational_q_bounds {p q : ℕ} (h : InteriorParam a τ) (hα : alphaOf a τ = p / q) :
    0 < p ∧ p < q := by
  obtain ⟨hα0, hβ0, hαβ⟩ := alpha_beta_bounds h
  rw [hα] at hα0 hαβ
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; simp at hα0
    · exact hq
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hp : (0 : ℝ) < p := by
    by_contra hc; push Not at hc
    have : (p : ℝ) / q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hqr.le
    linarith
  have hpq : (p : ℝ) < q := by
    have : (p : ℝ) / q < 1 := by linarith
    rwa [div_lt_one hqr] at this
  exact ⟨by exact_mod_cast hp, by exact_mod_cast hpq⟩

/-- **`thm:rational`** (`α = p/q` in lowest terms): singularity occurs for some dimension iff
`qβ ∈ ℤ` (eq. `(compat)`); if `r = qβ ∈ ℤ` then `0 < r < q - p` and the singular dimensions are
exactly `Np ≡ r (mod q)` (eq. `(congruence)`), which is one residue class of `N` mod `q`, and
recurs infinitely often; if `qβ ∉ ℤ` there are no singular dimensions. -/
theorem thm_rational {p q : ℕ} (h : InteriorParam a τ) (hpq : p.Coprime q)
    (hα : alphaOf a τ = p / q) :
    ((∃ N : ℕ, 2 ≤ N ∧ (shifted N a τ).det = 0) ↔ ∃ r : ℤ, (q : ℝ) * betaOf a τ = r) ∧
    (∀ r : ℤ, (q : ℝ) * betaOf a τ = r →
      0 < r ∧ r < (q : ℤ) - p ∧
      (∀ N : ℕ, 2 ≤ N → ((shifted N a τ).det = 0 ↔ (N : ℤ) * p ≡ r [ZMOD q])) ∧
      (∃ c : ℤ, 0 ≤ c ∧ c < q ∧ ∀ N : ℤ, N * p ≡ r [ZMOD q] ↔ N ≡ c [ZMOD q]) ∧
      {N : ℕ | 2 ≤ N ∧ (shifted N a τ).det = 0}.Infinite) ∧
    ((¬ ∃ r : ℤ, (q : ℝ) * betaOf a τ = r) → ∀ N : ℕ, 2 ≤ N → (shifted N a τ).det ≠ 0) := by
  obtain ⟨hp, hpq'⟩ := rational_q_bounds h hα
  refine ⟨thm_rational_exists h hpq hα, fun r hr => ?_, fun hno N hN hd => ?_⟩
  · obtain ⟨h0, h1, hc⟩ := thm_rational_congr h hα hr
    refine ⟨h0, h1, fun N hN => ?_, thm_rational_one_class hpq (by omega) r,
      singDims_infinite h hpq hα hr⟩
    have e : N ∈ singDims a τ ↔ 2 ≤ N ∧ (shifted N a τ).det = 0 := Iff.rfl
    rw [← hc N hN, e]
    exact ⟨fun hd => ⟨hN, hd⟩, fun hd => hd.2⟩
  · have hmem : N ∈ singDims a τ := ⟨hN, hd⟩
    rw [singDims_empty h hα hno] at hmem
    exact hmem

/-- **`cor:param`** (both directions of the complete recurrent parametrization). -/
theorem cor_param :
    (∀ a τ : ℝ, InteriorParam a τ → {N : ℕ | 2 ≤ N ∧ (shifted N a τ).det = 0}.Infinite →
      ∃ p q r : ℕ, 0 < p ∧ 0 < r ∧ p + r < q ∧ p.Coprime q ∧
        alphaOf a τ = p / q ∧ betaOf a τ = r / q ∧
        τ = Real.sin (r * π / q) / Real.sin (p * π / q) ∧
        a = Real.cos ((p + r) * π / (2 * q)) / Real.cos (((p : ℝ) - r) * π / (2 * q)) ∧
        ∀ N : ℕ, 2 ≤ N → ((shifted N a τ).det = 0 ↔ (N : ℤ) * p ≡ r [ZMOD q])) ∧
    (∀ p q r : ℕ, 0 < p → 0 < r → p + r < q → p.Coprime q →
      InteriorParam (Real.cos ((p + r) * π / (2 * q)) / Real.cos (((p : ℝ) - r) * π / (2 * q)))
        (Real.sin (r * π / q) / Real.sin (p * π / q)) ∧
      alphaOf (Real.cos ((p + r) * π / (2 * q)) / Real.cos (((p : ℝ) - r) * π / (2 * q)))
        (Real.sin (r * π / q) / Real.sin (p * π / q)) = p / q ∧
      betaOf (Real.cos ((p + r) * π / (2 * q)) / Real.cos (((p : ℝ) - r) * π / (2 * q)))
        (Real.sin (r * π / q) / Real.sin (p * π / q)) = r / q ∧
      {N : ℕ | 2 ≤ N ∧ (shifted N (Real.cos ((p + r) * π / (2 * q)) /
        Real.cos (((p : ℝ) - r) * π / (2 * q))) (Real.sin (r * π / q) / Real.sin (p * π / q))).det
          = 0}.Infinite ∧
      ∀ N : ℕ, 2 ≤ N → ((shifted N (Real.cos ((p + r) * π / (2 * q)) /
        Real.cos (((p : ℝ) - r) * π / (2 * q))) (Real.sin (r * π / q) / Real.sin (p * π / q))).det
          = 0 ↔ (N : ℤ) * p ≡ r [ZMOD q])) := by
  refine ⟨fun a τ h hinf => ?_, fun p q r hp hr hpqr hcop => ?_⟩
  · obtain ⟨p, q, r, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ShiftedKMS.cor_param h hinf
    refine ⟨p, q, r, h1, h2, h3, h4, h5, h6, h7, h8, fun N hN => ?_⟩
    have e : N ∈ singDims a τ ↔ 2 ≤ N ∧ (shifted N a τ).det = 0 := Iff.rfl
    rw [← h9 N hN, e]
    exact ⟨fun hd => ⟨hN, hd⟩, fun hd => hd.2⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := cor_param_converse hp hr hpqr hcop
    refine ⟨h1, h2, h3, h4, fun N hN => ?_⟩
    rw [← h5 N hN]
    exact ⟨fun hd => ⟨hN, hd⟩, fun hd => hd.2⟩

/-- **`thm:zeroinf`**: irrational `α` ⇒ at most one singular dimension; and for every interior
pair `#{N ≥ 2 : B_N singular} ∈ {0, 1, ∞}` (eq. `(card)`). -/
theorem thm_zeroinf :
    (∀ a τ : ℝ, InteriorParam a τ → Irrational (alphaOf a τ) →
      {N : ℕ | 2 ≤ N ∧ (shifted N a τ).det = 0}.Subsingleton) ∧
    (∀ a τ : ℝ, InteriorParam a τ →
      {N : ℕ | 2 ≤ N ∧ (shifted N a τ).det = 0}.encard ∈ ({0, 1, ⊤} : Set ℕ∞)) := by
  refine ⟨fun a τ h hα => singDims_subsingleton_of_irrational h hα, fun a τ h => ?_⟩
  rcases ShiftedKMS.thm_zeroinf h with e | e | e
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)

/-- **`thm:dense-strata`**: in `𝒟` and in `𝒫`, `S_0, S_1, S_∞` are dense; `S_0` has full measure;
`S_1` is uncountable and null; `S_∞` is countable and null. -/
theorem thm_dense_strata :
    ((triangleSet ⊆ closure (strat 0) ∧ triangleSet ⊆ closure (strat 1) ∧
        triangleSet ⊆ closure (strat ⊤)) ∧
      volume (triangleSet \ strat 0) = 0 ∧
      (¬ (strat 1).Countable ∧ volume (strat 1) = 0) ∧
      (strat ⊤).Countable ∧ volume (strat ⊤) = 0) ∧
    ((regionSet ⊆ closure (physStrat 0) ∧ regionSet ⊆ closure (physStrat 1) ∧
        regionSet ⊆ closure (physStrat ⊤)) ∧
      volume (regionSet \ physStrat 0) = 0 ∧
      (¬ (physStrat 1).Countable ∧ volume (physStrat 1) = 0) ∧
      (physStrat ⊤).Countable ∧ volume (physStrat ⊤) = 0) :=
  ⟨thm_dense_strata_triangle, thm_dense_strata_physical⟩

/-- **`prop:inertia`** with multiplicity, for Mathlib's eigenvalues of the symmetric matrix
`B_N`: `n₊ = ⌈Nα - β⌉` (eq. `(inertia)`); exactly one zero eigenvalue iff `Nα - β ∈ ℤ`, otherwise
none; `n₋` is the remainder. -/
theorem prop_inertia (h : InteriorParam a τ) {N : ℕ} (hN : 2 ≤ N) :
    (Fintype.card {i // 0 < (shifted_isHermitian N a τ).eigenvalues i} : ℤ) =
      ⌈(N : ℝ) * alphaOf a τ - betaOf a τ⌉ ∧
    Fintype.card {i // (shifted_isHermitian N a τ).eigenvalues i = 0} =
      (if ∃ z : ℤ, (N : ℝ) * alphaOf a τ - betaOf a τ = z then 1 else 0) ∧
    Fintype.card {i // (shifted_isHermitian N a τ).eigenvalues i < 0} =
      N - Fintype.card {i // 0 < (shifted_isHermitian N a τ).eigenvalues i} -
        Fintype.card {i // (shifted_isHermitian N a τ).eigenvalues i = 0} := by
  rw [inertia_pos h.1 h.2.1 hN τ, inertia_zero h.1 h.2.1 hN τ, inertia_neg h.1 h.2.1 hN τ]
  refine ⟨thm_inertia h hN, thm_zeroCount h hN, ?_⟩
  have := thm_inertia_sum h N
  omega

/-- **`prop:kernel`**: at a singular dimension the kernel is spanned by
`(sin((j+1)θ_τ) - a sin(jθ_τ))_{j=0}^{N-1}` (eq. `(kernel)`). -/
theorem prop_kernel (h : InteriorParam a τ) {N : ℕ} (hN : 2 ≤ N) (hs : (shifted N a τ).det = 0) :
    LinearMap.ker (Matrix.toLin' (shifted N a τ)) =
      Submodule.span ℝ {fun j : Fin N => Real.sin ((((j : ℕ) : ℝ) + 1) * crossAngle a τ) -
        a * Real.sin (((j : ℕ) : ℝ) * crossAngle a τ)} :=
  shifted_ker_eq_span h hN hs

/-! ## §5 Conditioning across the symbol band -/

/-- `k` is a nearest integer to `x`. -/
def IsNearestInt (k : ℤ) (x : ℝ) : Prop := ∀ m : ℤ, |(k : ℝ) - x| ≤ |(m : ℝ) - x|

lemma Gph_cross_div_pi (h : InteriorParam a τ) (N : ℕ) :
    Gph N a (crossAngle a τ) / π = N * alphaOf a τ + 1 - betaOf a τ := by
  rw [Gph_crossAngle h]; field_simp; ring

lemma nearest_dist (h : InteriorParam a τ) {N k : ℕ}
    (hk : IsNearestInt k (Gph N a (crossAngle a τ) / π)) :
    |(k : ℝ) - 1 - resid N a τ| = dN N a τ := by
  rw [Gph_cross_div_pi h] at hk
  have hx : (N : ℝ) * alphaOf a τ + 1 - betaOf a τ = resid N a τ + 1 := by unfold resid; ring
  rw [hx] at hk
  have e1 : |(k : ℝ) - 1 - resid N a τ| = |((k : ℤ) : ℝ) - (resid N a τ + 1)| := by
    push_cast; ring_nf
  rw [e1, dN, distZ, ← resid]
  apply le_antisymm
  · refine (hk (round (resid N a τ) + 1)).trans (le_of_eq ?_)
    push_cast
    rw [show (round (resid N a τ) : ℝ) + 1 - (resid N a τ + 1) =
      -(resid N a τ - round (resid N a τ)) by ring, abs_neg]
  · refine (round_le (resid N a τ) ((k : ℤ) - 1)).trans (le_of_eq ?_)
    push_cast
    rw [show resid N a τ - ((k : ℝ) - 1) = -((k : ℝ) - (resid N a τ + 1)) by ring, abs_neg]

lemma nearIdx_isNearest (h : InteriorParam a τ) {N : ℕ} (hN : n0 a τ ≤ N) :
    IsNearestInt (nearIdx N a τ) (Gph N a (crossAngle a τ) / π) := by
  obtain ⟨-, -, hk⟩ := nearIdx_mem h hN
  intro m
  rw [Gph_cross_div_pi h]
  have hx : (N : ℝ) * alphaOf a τ + 1 - betaOf a τ = resid N a τ + 1 := by unfold resid; ring
  rw [hx]
  have e : (((nearIdx N a τ : ℕ) : ℤ) : ℝ) = round (resid N a τ) + 1 := by
    rw [Int.cast_natCast]; exact hk
  rw [e, show (round (resid N a τ) : ℝ) + 1 - (resid N a τ + 1) =
      -(resid N a τ - round (resid N a τ)) by ring, abs_neg]
  refine (round_le (resid N a τ) (m - 1)).trans (le_of_eq ?_)
  push_cast
  rw [show resid N a τ - ((m : ℝ) - 1) = -((m : ℝ) - (resid N a τ + 1)) by ring, abs_neg]

lemma localization_general (h : InteriorParam a τ) {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (hk : |(k : ℝ) - 1 - resid N a τ| = dN N a τ) :
    π * dN N a τ / (N + upperEdge a) ≤ |eigAngle N a k - crossAngle a τ| ∧
      |eigAngle N a k - crossAngle a τ| ≤ π * dN N a τ / (N + lowerEdge a) := by
  have hG := Gph_eig_sub_cross h hk1 hkN
  have hd : |Gph N a (eigAngle N a k) - Gph N a (crossAngle a τ)| = π * dN N a τ := by
    rw [hG, abs_mul, abs_of_pos Real.pi_pos, hk]
  obtain ⟨b1, b2⟩ := angle_bounds_of_phase h N (eigAngle N a k)
  rw [hd] at b1 b2
  exact ⟨b1, b2⟩

lemma local_asymp_general (h : InteriorParam a τ) {N k : ℕ} (hN2 : 2 ≤ N) (hk1 : 1 ≤ k)
    (hkN : k ≤ N) (hk : |(k : ℝ) - 1 - resid N a τ| = dN N a τ) :
    (1 - π * Lmu a / 2 / N ^ 2) * (π * dN N a τ / (N + τ)) ≤ |eigAngle N a k - crossAngle a τ| ∧
      |eigAngle N a k - crossAngle a τ| ≤ (1 + π * Lmu a / 2 / N ^ 2) * (π * dN N a τ / (N + τ)) := by
  have ha0 := h.1
  have ha1 := h.2.1
  have hτ := h.tau_pos
  set θk := eigAngle N a k
  set θτ := crossAngle a τ
  have hG := Gph_eig_sub_cross h hk1 hkN
  obtain ⟨ξ, hξ, hmvt⟩ := mvt_between (hasDerivAt_Gph ha0 ha1 N) θk θτ
  set u := |θk - θτ| with hu
  have hpos : (0 : ℝ) < N + symbol a ξ := by have := symbol_pos ha0 ha1 ξ; positivity
  have key : (N + symbol a ξ) * u = π * dN N a τ := by
    have := congrArg abs (hmvt.symm.trans hG)
    rw [abs_mul, abs_mul, abs_of_pos hpos, abs_of_pos Real.pi_pos, hk] at this
    exact this
  have hdN : dN N a τ ≤ 1 / 2 := distZ_le_half _
  have hd0 : 0 ≤ dN N a τ := distZ_nonneg _
  have hlo := lowerEdge_le_symbol ha0 ha1 ξ
  have hl0 := lowerEdge_pos ha0 ha1
  have hN1 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hu0 : 0 ≤ u := abs_nonneg _
  have hub : u ≤ π / (2 * N) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (N + symbol a ξ) * u ≤ π * (1 / 2) := by
      rw [key]; exact mul_le_mul_of_nonneg_left hdN Real.pi_pos.le
    have h2 : (N : ℝ) * u ≤ (N + symbol a ξ) * u :=
      mul_le_mul_of_nonneg_right (by linarith [symbol_pos ha0 ha1 ξ]) hu0
    linarith
  have hLm : 0 ≤ Lmu a := le_trans (abs_nonneg _) (abs_dmu_le ha0 ha1 0)
  have hμξ : |symbol a ξ - τ| ≤ Lmu a * u := by
    have := symbol_lipschitz ha0 ha1 ξ θτ
    rw [symbol_crossAngle h] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hξ.trans le_rfl) hLm)
  set A := π * dN N a τ / (N + τ) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
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

lemma abs_sub_le_of_two_sided {c t X F : ℝ} (ht : 0 ≤ t) (hX : 0 ≤ X)
    (h1 : (1 - c * t) * X ≤ F) (h2 : F ≤ (1 + c * t) * X) :
    |F - X| ≤ max c 1 * t * |X| := by
  rw [abs_of_nonneg hX, abs_le]
  have : c * t * X ≤ max c 1 * t * X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) ht) hX
  constructor <;> nlinarith

/-- **`thm:localization`**: `G_N(θ_τ)/π = Nα + 1 - β`; for all large `N` a nearest integer `k_N`
to it lies in `{1,…,N}`; for **every** such nearest choice, eq. `(localization)` holds for all
large `N`, and at nonsingular dimensions eq. `(local-asymp)` holds with a relative `O(N^{-2})`. -/
theorem thm_localization (h : InteriorParam a τ) :
    (∀ N : ℕ, Gph N a (crossAngle a τ) / π = N * alphaOf a τ + 1 - betaOf a τ) ∧
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ IsNearestInt k (Gph N a (crossAngle a τ) / π)) ∧
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℕ, 1 ≤ k → k ≤ N →
      IsNearestInt k (Gph N a (crossAngle a τ) / π) →
      π * dN N a τ / (N + upperEdge a) ≤ |eigAngle N a k - crossAngle a τ| ∧
        |eigAngle N a k - crossAngle a τ| ≤ π * dN N a τ / (N + lowerEdge a)) ∧
    (∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Nonsingular N a τ → ∀ k : ℕ, 1 ≤ k → k ≤ N →
      IsNearestInt k (Gph N a (crossAngle a τ) / π) →
      abs (|eigAngle N a k - crossAngle a τ| - π * dN N a τ / (N + τ)) ≤
        K / (N : ℝ) ^ 2 * |π * dN N a τ / (N + τ)|) := by
  refine ⟨Gph_cross_div_pi h, ⟨n0 a τ, fun N hN => ⟨nearIdx N a τ, (nearIdx_mem h hN).1,
    (nearIdx_mem h hN).2.1, nearIdx_isNearest h hN⟩⟩,
    ⟨n0 a τ, fun N _ k hk1 hkN hk => localization_general h hk1 hkN (nearest_dist h hk)⟩, ?_⟩
  refine ⟨max (π * Lmu a / 2) 1, lt_of_lt_of_le one_pos (le_max_right _ _), n0 a τ,
    fun N hN _ k hk1 hkN hk => ?_⟩
  have hN2 := (n0_spec h hN).1
  obtain ⟨b1, b2⟩ := local_asymp_general h hN2 hk1 hkN (nearest_dist h hk)
  have hX : 0 ≤ π * dN N a τ / (N + τ) := by
    have := h.tau_pos; have := distZ_nonneg (N * alphaOf a τ - betaOf a τ)
    rw [dN]; positivity
  have e : ∀ c : ℝ, c / (N : ℝ) ^ 2 = c * (1 / (N : ℝ) ^ 2) := fun c => by ring
  rw [e] at b1 b2
  have := abs_sub_le_of_two_sided (by positivity) hX b1 b2
  rw [e]
  linarith [this, le_of_eq (mul_assoc (max (π * Lmu a / 2) 1) (1 / (N : ℝ) ^ 2)
    |π * dN N a τ / (N + τ)|)]

lemma interior_X_nonneg (h : InteriorParam a τ) (N : ℕ) :
    0 ≤ π * gam a τ * dN N a τ / (N + τ) := by
  have := gam_pos h; have := h.tau_pos
  have := distZ_nonneg (N * alphaOf a τ - betaOf a τ)
  rw [dN]; positivity

lemma interior_Y_nonneg (h : InteriorParam a τ) (N : ℕ) :
    0 ≤ Cint a τ * (N + τ) / dN N a τ := by
  have := Cint_pos h; have := h.tau_pos
  have := distZ_nonneg (N * alphaOf a τ - betaOf a τ)
  rw [dN]; positivity

/-- **`thm:smin`**: at every sufficiently large nonsingular dimension
`σ_min(B_N) = π γ d_N/(N+τ) (1 + O(N^{-1}))` (eq. `(smin)`); at an exact singular dimension
`σ_min = 0`. -/
theorem thm_smin (h : InteriorParam a τ) :
    RelBigO 1 (fun N => Nonsingular N a τ) (fun N => sigmaMinMat N a τ)
      (fun N => π * gam a τ * dN N a τ / (N + τ)) ∧
    ∀ N : ℕ, 2 ≤ N → (shifted N a τ).det = 0 → sigmaMinMat N a τ = 0 := by
  refine ⟨?_, fun N hN hs => sigmaMinMat_eq_zero_of_singular h.1 h.2.1 hN hs⟩
  refine RelBigO.congr (relBigO_of_two_sided (c := Ksm a τ) (N₀ := n1 a τ) fun N hN _ => ?_) 2
    fun N hN _ => (sigmaMinMat_eq h.1 h.2.1 hN).symm
  simp only [pow_one]
  exact ⟨interior_X_nonneg h N, thm_smin_relative h hN⟩

/-- **`thm:kappa`**: `γ = |μ_a'(θ_τ)|` (eq. `(gamma)`), `M = max{μ₊-τ, τ-μ₋}` (eq. `(M)`),
`C = M/(πγ)` (eq. `(C)`), and at every sufficiently large nonsingular `N`,
`κ₂(B_N) = C (N+τ)/d_N (1 + O(N^{-1}))` (eq. `(kappa)`). -/
theorem thm_kappa (h : InteriorParam a τ) :
    gam a τ = |deriv (symbol a) (crossAngle a τ)| ∧
    Mband a τ = max (upperEdge a - τ) (τ - lowerEdge a) ∧
    Cint a τ = Mband a τ / (π * gam a τ) ∧
    RelBigO 1 (fun N => Nonsingular N a τ) (fun N => kappaMat N a τ)
      (fun N => Cint a τ * (N + τ) / dN N a τ) := by
  refine ⟨by rw [(hasDerivAt_symbol h.1 h.2.1 _).deriv]; rfl, rfl, rfl, ?_⟩
  refine RelBigO.congr (relBigO_of_two_sided (c := Kkap a τ) (N₀ := n2 a τ) fun N hN hns => ?_) 2
    fun N hN _ => (kappaMat_eq h.1 h.2.1 hN).symm
  simp only [pow_one]
  exact ⟨interior_Y_nonneg h N, thm_kappa_relative h hN hns⟩

/-- **`thm:outside`**: below / above the band, `κ₂(B_N)` is finite (`B_N` invertible) and strictly
below the limit for every `N ≥ 2`, converges to it (eqs. `(outside-lower)`, `(outside-upper)`),
and in particular is uniformly bounded in `N`. -/
theorem thm_outside (ha0 : 0 < a) (ha1 : a < 1) :
    (∀ τ : ℝ, τ < lowerEdge a →
      (∀ N : ℕ, 2 ≤ N → IsUnit (shifted N a τ) ∧
        kappaMat N a τ < (upperEdge a - τ) / (lowerEdge a - τ)) ∧
      Tendsto (fun N => kappaMat N a τ) atTop (𝓝 ((upperEdge a - τ) / (lowerEdge a - τ))) ∧
      ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N → kappaMat N a τ ≤ B) ∧
    (∀ τ : ℝ, upperEdge a < τ →
      (∀ N : ℕ, 2 ≤ N → IsUnit (shifted N a τ) ∧
        kappaMat N a τ < (τ - lowerEdge a) / (τ - upperEdge a)) ∧
      Tendsto (fun N => kappaMat N a τ) atTop (𝓝 ((τ - lowerEdge a) / (τ - upperEdge a))) ∧
      ∃ B : ℝ, ∀ N : ℕ, 2 ≤ N → kappaMat N a τ ≤ B) := by
  constructor
  · intro τ hτ
    obtain ⟨h1, h2⟩ := thm_outside_lower ha0 ha1 hτ
    have hb : ∀ N : ℕ, 2 ≤ N → IsUnit (shifted N a τ) ∧
        kappaMat N a τ < (upperEdge a - τ) / (lowerEdge a - τ) := fun N hN =>
      ⟨isUnit_iff_nonsingular.2 (h1 N hN).1, (kappaMat_eq ha0 ha1 hN).symm ▸ (h1 N hN).2⟩
    refine ⟨hb, h2.congr' ?_, _, fun N hN => (hb N hN).2.le⟩
    filter_upwards [eventually_ge_atTop 2] with N hN using (kappaMat_eq ha0 ha1 hN).symm
  · intro τ hτ
    obtain ⟨h1, h2⟩ := thm_outside_upper ha0 ha1 hτ
    have hb : ∀ N : ℕ, 2 ≤ N → IsUnit (shifted N a τ) ∧
        kappaMat N a τ < (τ - lowerEdge a) / (τ - upperEdge a) := fun N hN =>
      ⟨isUnit_iff_nonsingular.2 (h1 N hN).1, (kappaMat_eq ha0 ha1 hN).symm ▸ (h1 N hN).2⟩
    refine ⟨hb, h2.congr' ?_, _, fun N hN => (hb N hN).2.le⟩
    filter_upwards [eventually_ge_atTop 2] with N hN using (kappaMat_eq ha0 ha1 hN).symm

lemma nE_ge_two (a : ℝ) : 2 ≤ nE a := by unfold nE; omega

/-- **`thm:edges`** in the manuscript's literal constants (eqs. `(edge-up-smin)`,
`(edge-up-kappa)`, `(edge-low-smin)`, `(edge-low-kappa)`); `B_N` is invertible at both edges for
all large `N`. -/
theorem thm_edges (ha0 : 0 < a) (ha1 : a < 1) :
    RelBigO 2 (fun _ => True) (fun N => sigmaMinMat N a (upperEdge a))
      (fun N => π ^ 2 * a * (1 + a) / (1 - a) ^ 3 * (1 / (N + upperEdge a) ^ 2)) ∧
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → IsUnit (shifted N a (upperEdge a))) ∧
    RelBigO 2 (fun _ => True) (fun N => kappaMat N a (upperEdge a))
      (fun N => 4 * lowerEdge a ^ 2 / π ^ 2 * (N + upperEdge a) ^ 2) ∧
    RelBigO 2 (fun _ => True) (fun N => sigmaMinMat N a (lowerEdge a))
      (fun N => π ^ 2 * a * (1 - a) / (1 + a) ^ 3 * (1 / (N + lowerEdge a) ^ 2)) ∧
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → IsUnit (shifted N a (lowerEdge a))) ∧
    RelBigO 2 (fun _ => True) (fun N => kappaMat N a (lowerEdge a))
      (fun N => 4 * upperEdge a ^ 2 / π ^ 2 * (N + lowerEdge a) ^ 2) := by
  have hu := upperEdge_pos' ha0 ha1
  have hl := lowerEdge_pos ha0 ha1
  have h1a : 0 < 1 - a := by linarith
  refine ⟨?_, ⟨nE a, fun N hN => isUnit_iff_nonsingular.2 (thm_edge_upper_kappa ha0 ha1 hN).1⟩,
    ?_, ?_, ⟨nE a, fun N hN => isUnit_iff_nonsingular.2 (thm_edge_lower_kappa ha0 ha1 hN).1⟩, ?_⟩
  · refine RelBigO.congr (relBigO_of_abs (c := KeU a) (N₀ := nE a) fun N hN _ => ?_) 2
      fun N hN _ => (sigmaMinMat_eq ha0 ha1 hN).symm
    have e : π ^ 2 * a * (1 + a) / (1 - a) ^ 3 * (1 / (N + upperEdge a) ^ 2) =
        kapU a * (π / (N + upperEdge a)) ^ 2 := by unfold kapU; rw [div_pow]; ring
    rw [e]
    exact ⟨by unfold kapU; positivity, thm_edge_upper_smin ha0 ha1 hN⟩
  · refine RelBigO.congr (relBigO_of_abs (c := KkU a) (N₀ := nE a) fun N hN _ => ?_) 2
      fun N hN _ => (kappaMat_eq ha0 ha1 hN).symm
    have e : 4 * lowerEdge a ^ 2 / π ^ 2 * (N + upperEdge a) ^ 2 =
        4 * lowerEdge a ^ 2 * ((N + upperEdge a) / π) ^ 2 := by ring
    rw [e]
    exact ⟨by positivity, (thm_edge_upper_kappa ha0 ha1 hN).2⟩
  · refine RelBigO.congr (relBigO_of_abs (c := KeL a) (N₀ := nE a) fun N hN _ => ?_) 2
      fun N hN _ => (sigmaMinMat_eq ha0 ha1 hN).symm
    have e : π ^ 2 * a * (1 - a) / (1 + a) ^ 3 * (1 / (N + lowerEdge a) ^ 2) =
        kapL a * (π / (N + lowerEdge a)) ^ 2 := by unfold kapL; rw [div_pow]; ring
    rw [e]
    exact ⟨by unfold kapL; positivity, thm_edge_lower_smin ha0 ha1 hN⟩
  · refine RelBigO.congr (relBigO_of_abs (c := KkL a) (N₀ := nE a) fun N hN _ => ?_) 2
      fun N hN _ => (kappaMat_eq ha0 ha1 hN).symm
    have e : 4 * upperEdge a ^ 2 / π ^ 2 * (N + lowerEdge a) ^ 2 =
        4 * upperEdge a ^ 2 * ((N + lowerEdge a) / π) ^ 2 := by ring
    rw [e]
    exact ⟨by positivity, (thm_edge_lower_kappa ha0 ha1 hN).2⟩

/-! ### Non-uniformity of the interior error terms near a band edge -/

lemma sigmaMin_ge_sub {N : ℕ} (hN : 1 ≤ N) (τ τ' : ℝ) :
    sigmaMin N a τ' - |τ - τ'| ≤ sigmaMin N a τ := by
  have hne := Icc_nonempty (N := N) hN
  obtain ⟨k, hk, hkmin⟩ := Finset.exists_mem_eq_inf' hne fun k => |lam N a τ k|
  rw [Finset.mem_Icc] at hk
  have h1 : sigmaMin N a τ = |lam N a τ k| := by simp only [sigmaMin, hne, ↓reduceDIte]; exact hkmin
  have h2 := sigmaMin_le (N := N) a τ' hk.1 hk.2
  rw [h1]
  have := abs_sub_abs_le_abs_sub (lam N a τ' k) (lam N a τ k)
  have e : lam N a τ' k - lam N a τ k = τ - τ' := by unfold lam; ring
  rw [e] at this
  linarith

lemma sigmaMax_band_le (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ}
    (h1 : lowerEdge a ≤ τ) (h2 : τ ≤ upperEdge a) :
    sigmaMax N a τ ≤ upperEdge a - lowerEdge a :=
  sigmaMax_le hN a τ fun k _ _ => by
    have := lowerEdge_le_symbol ha0 ha1 (eigAngle N a k)
    have := symbol_le_upperEdge ha0 ha1 (eigAngle N a k)
    unfold lam; rw [abs_le]; constructor <;> linarith

lemma sigmaMin_upperEdge_pos (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) :
    0 < sigmaMin N a (upperEdge a) := by
  rw [← nonsingular_iff_sigmaMin_pos ha0 ha1 hN]
  unfold Nonsingular
  rw [ne_eq, det_eq_zero_iff_lam ha0 ha1 hN]
  rintro ⟨k, hk1, hkN, hk⟩
  have := (symbol_strict_bounds ha0 ha1 (eigAngle_spec ha0 ha1 hk1 hkN).1).2
  unfold lam at hk; linarith

/-- Near the upper edge, at a fixed `N ≥ 2`, `σ_min(B_N(a,τ)) ≥ s₀/2` and `B_N` is invertible. -/
lemma sigmaMin_lowerEdge_pos (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) :
    0 < sigmaMin N a (lowerEdge a) := by
  rw [← nonsingular_iff_sigmaMin_pos ha0 ha1 hN]
  unfold Nonsingular
  rw [ne_eq, det_eq_zero_iff_lam ha0 ha1 hN]
  rintro ⟨k, hk1, hkN, hk⟩
  have := (symbol_strict_bounds ha0 ha1 (eigAngle_spec ha0 ha1 hk1 hkN).1).1
  unfold lam at hk; linarith

/-- Near the upper edge, at a fixed `N ≥ 2`, `σ_min(B_N(a,τ)) ≥ s₀/2` and `B_N` is invertible. -/
lemma near_upper_edge (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) :
    ∀ᶠ τ in 𝓝[<] upperEdge a, InteriorParam a τ ∧
      sigmaMin N a (upperEdge a) / 2 ≤ sigmaMin N a τ ∧ IsUnit (shifted N a τ) := by
  set s₀ := sigmaMin N a (upperEdge a)
  have hs₀ := sigmaMin_upperEdge_pos ha0 ha1 hN
  have hlt : max (lowerEdge a) (upperEdge a - s₀ / 2) < upperEdge a :=
    max_lt (edges_lt ha0 ha1) (by linarith)
  filter_upwards [Ioo_mem_nhdsLT hlt] with τ hτ
  have hl : lowerEdge a < τ := lt_of_le_of_lt (le_max_left _ _) hτ.1
  have hs : upperEdge a - s₀ / 2 < τ := lt_of_le_of_lt (le_max_right _ _) hτ.1
  have hσ := sigmaMin_ge_sub (a := a) (N := N) (by omega) τ (upperEdge a)
  rw [abs_of_neg (by linarith [hτ.2])] at hσ
  have hσ' : s₀ / 2 ≤ sigmaMin N a τ := by linarith [hτ.2]
  refine ⟨⟨ha0, ha1, hl, hτ.2⟩, hσ', ?_⟩
  rw [isUnit_iff_nonsingular, nonsingular_iff_sigmaMin_pos ha0 ha1 hN]
  linarith

/-- Near the lower edge, at a fixed `N ≥ 2`, `σ_min(B_N(a,τ)) ≥ s₀/2` and `B_N` is invertible. -/
lemma near_lower_edge (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) :
    ∀ᶠ τ in 𝓝[>] lowerEdge a, InteriorParam a τ ∧
      sigmaMin N a (lowerEdge a) / 2 ≤ sigmaMin N a τ ∧ IsUnit (shifted N a τ) := by
  set s₀ := sigmaMin N a (lowerEdge a)
  have hs₀ := sigmaMin_lowerEdge_pos ha0 ha1 hN
  have hlt : lowerEdge a < min (upperEdge a) (lowerEdge a + s₀ / 2) :=
    lt_min (edges_lt ha0 ha1) (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hlt] with τ hτ
  have hu : τ < upperEdge a := lt_of_lt_of_le hτ.2 (min_le_left _ _)
  have hs : τ < lowerEdge a + s₀ / 2 := lt_of_lt_of_le hτ.2 (min_le_right _ _)
  have hσ := sigmaMin_ge_sub (a := a) (N := N) (by omega) τ (lowerEdge a)
  rw [abs_of_pos (by linarith [hτ.1])] at hσ
  have hσ' : s₀ / 2 ≤ sigmaMin N a τ := by linarith [hτ.1]
  refine ⟨⟨ha0, ha1, hτ.1, hu⟩, hσ', ?_⟩
  rw [isUnit_iff_nonsingular, nonsingular_iff_sigmaMin_pos ha0 ha1 hN]
  linarith

lemma exists_large_N (K : ℝ) (N₀ : ℕ) : ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧ K / N ≤ 1 / 2 := by
  refine ⟨N₀ + 2 + ⌈2 * K⌉₊, by omega, by omega, ?_⟩
  have hc := Nat.le_ceil (2 * K)
  have hN : ((N₀ + 2 + ⌈2 * K⌉₊ : ℕ) : ℝ) = N₀ + 2 + ⌈2 * K⌉₊ := by push_cast; ring
  have hpos : (0 : ℝ) < ((N₀ + 2 + ⌈2 * K⌉₊ : ℕ) : ℝ) := by rw [hN]; positivity
  rw [div_le_iff₀ hpos, hN]
  have : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
  linarith

/-- One fixed `N`, one level `τ` with `σ_min ≥ s/2` and `C(a,τ)` large: the relative `κ₂` bound
with `K/N ≤ 1/2` is impossible. -/
lemma kappa_contra (ha0 : 0 < a) (ha1 : a < 1) {K : ℝ} {N : ℕ} (hN2 : 2 ≤ N)
    (hKN : K / N ≤ 1 / 2) {s : ℝ} (hs : 0 < s) (h : InteriorParam a τ)
    (hσ : s / 2 ≤ sigmaMin N a τ) (hU : IsUnit (shifted N a τ))
    (hC : (upperEdge a - lowerEdge a) / (s / 2) < Cint a τ)
    (hb : |kappaMat N a τ - Cint a τ * (N + τ) / dN N a τ| ≤
      K / N * |Cint a τ * (N + τ) / dN N a τ|) : False := by
  rw [kappaMat_eq ha0 ha1 hN2] at hb
  have hW : 0 ≤ upperEdge a - lowerEdge a := (sub_pos.2 (edges_lt ha0 ha1)).le
  have hκB : kappa N a τ ≤ (upperEdge a - lowerEdge a) / (s / 2) := by
    unfold kappa
    calc sigmaMax N a τ / sigmaMin N a τ ≤ (upperEdge a - lowerEdge a) / sigmaMin N a τ :=
          div_le_div_of_nonneg_right
            (sigmaMax_band_le ha0 ha1 (by omega) h.2.2.1.le h.2.2.2.le) (by linarith)
      _ ≤ (upperEdge a - lowerEdge a) / (s / 2) := div_le_div_of_nonneg_left hW (by linarith) hσ
  have hns : Nonsingular N a τ := isUnit_iff_nonsingular.1 hU
  have hd0 : 0 < dN N a τ := by
    have := distZ_nonneg (N * alphaOf a τ - betaOf a τ)
    rcases (show (0 : ℝ) ≤ dN N a τ from this).lt_or_eq with h' | h'
    · exact h'
    · exact absurd ((thm_sing_dN h hN2).2 h'.symm) hns
  have hdh : dN N a τ ≤ 1 / 2 := distZ_le_half _
  have hCp := Cint_pos h
  have hτ := h.tau_pos
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  set X := Cint a τ * (N + τ) / dN N a τ
  have hX : 2 * (Cint a τ * (N + τ)) ≤ X := by
    have := div_le_div_of_nonneg_left (by positivity : 0 ≤ Cint a τ * (N + τ)) hd0 hdh
    rw [div_div_eq_mul_div, div_one] at this
    linarith
  have hX0 : 0 ≤ X := by positivity
  rw [abs_of_nonneg hX0, abs_le] at hb
  have hKX : K / N * X ≤ 1 / 2 * X := mul_le_mul_of_nonneg_right hKN hX0
  have : Cint a τ ≤ Cint a τ * (N + τ) := le_mul_of_one_le_right hCp.le (by linarith)
  linarith [hb.1]

/-- One fixed `N`, one level `τ` with `σ_min ≥ s/2` and `γ(a,τ)` small: the relative `σ_min` bound
with `K/N ≤ 1/2` is impossible. -/
lemma sigma_contra (ha0 : 0 < a) (ha1 : a < 1) {K : ℝ} {N : ℕ} (hN2 : 2 ≤ N)
    (hKN : K / N ≤ 1 / 2) {s : ℝ} (hs : 0 < s) (h : InteriorParam a τ)
    (hσ : s / 2 ≤ sigmaMin N a τ) (hγ : gam a τ < s / (2 * π))
    (hb : |sigmaMinMat N a τ - π * gam a τ * dN N a τ / (N + τ)| ≤
      K / N * |π * gam a τ * dN N a τ / (N + τ)|) : False := by
  rw [sigmaMinMat_eq ha0 ha1 hN2] at hb
  have hτ := h.tau_pos
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hγ0 := (gam_pos h).le
  have hdh : dN N a τ ≤ 1 / 2 := distZ_le_half _
  set Y := π * gam a τ * dN N a τ / (N + τ)
  have hY0 : 0 ≤ Y := interior_X_nonneg h N
  have hY : Y ≤ π * gam a τ / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have : π * gam a τ * dN N a τ ≤ π * gam a τ * (1 / 2) :=
      mul_le_mul_of_nonneg_left hdh (by positivity)
    have : π * gam a τ / 4 * 2 ≤ π * gam a τ / 4 * (N + τ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  rw [abs_of_nonneg hY0, abs_le] at hb
  have hKY : K / N * Y ≤ 1 / 2 * Y := mul_le_mul_of_nonneg_right hKN hY0
  have hγ' : π * gam a τ < s / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hγ; nlinarith [Real.pi_pos]
  nlinarith [hb.2, Real.pi_pos]

/-- A relative `O(N^{-1})` law `F = X (1 + O(N^{-1}))` holding **uniformly** for the levels
`τ ∈ S` (one constant `K` and one threshold `N₀` for all `τ ∈ S`), at invertible `B_N`. -/
def UniformRelO1 (a : ℝ) (S : Set ℝ) (F X : ℝ → ℕ → ℝ) : Prop :=
  ∃ K : ℝ, ∃ N₀ : ℕ, ∀ τ ∈ S, ∀ N : ℕ, N₀ ≤ N → IsUnit (shifted N a τ) →
    |F τ N - X τ N| ≤ K / N * |X τ N|

/-- **Non-uniformity at the upper edge**: on every interior one-sided neighbourhood
`(μ₊ - δ, μ₊)`, neither the `σ_min` law nor the `κ₂` law holds uniformly in `τ`. -/
theorem nonuniform_upper (ha0 : 0 < a) (ha1 : a < 1) {δ : ℝ} (hδ : 0 < δ) :
    ¬ UniformRelO1 a (Ioo (upperEdge a - δ) (upperEdge a) ∩ Ioo (lowerEdge a) (upperEdge a))
        (fun τ N => sigmaMinMat N a τ) (fun τ N => π * gam a τ * dN N a τ / (N + τ)) ∧
    ¬ UniformRelO1 a (Ioo (upperEdge a - δ) (upperEdge a) ∩ Ioo (lowerEdge a) (upperEdge a))
        (fun τ N => kappaMat N a τ) (fun τ N => Cint a τ * (N + τ) / dN N a τ) := by
  have hW : ∀ᶠ τ in 𝓝[<] upperEdge a, τ ∈ Ioo (upperEdge a - δ) (upperEdge a) :=
    Ioo_mem_nhdsLT (by linarith)
  constructor
  · rintro ⟨K, N₀, hK⟩
    obtain ⟨N, hN₀, hN2, hKN⟩ := exists_large_N K N₀
    have hs₀ := sigmaMin_upperEdge_pos ha0 ha1 hN2
    have hg : ∀ᶠ τ in 𝓝[<] upperEdge a, gam a τ < sigmaMin N a (upperEdge a) / (2 * π) :=
      ((gam_tendsto_zero_upper ha0 ha1).mono_left nhdsWithin_le_nhds).eventually
        (gt_mem_nhds (by positivity))
    obtain ⟨τ, ⟨⟨h, hσ, hU⟩, hγ⟩, hw⟩ := (((near_upper_edge ha0 ha1 hN2).and hg).and hW).exists
    exact sigma_contra ha0 ha1 hN2 hKN hs₀ h hσ hγ
      (hK τ ⟨hw, h.2.2.1, h.2.2.2⟩ N hN₀ hU)
  · rintro ⟨K, N₀, hK⟩
    obtain ⟨N, hN₀, hN2, hKN⟩ := exists_large_N K N₀
    have hs₀ := sigmaMin_upperEdge_pos ha0 ha1 hN2
    obtain ⟨τ, ⟨⟨h, hσ, hU⟩, hC⟩, hw⟩ := (((near_upper_edge ha0 ha1 hN2).and
      ((Cint_tendsto_atTop_upper ha0 ha1).eventually_gt_atTop
        ((upperEdge a - lowerEdge a) / (sigmaMin N a (upperEdge a) / 2)))).and hW).exists
    exact kappa_contra ha0 ha1 hN2 hKN hs₀ h hσ hU hC (hK τ ⟨hw, h.2.2.1, h.2.2.2⟩ N hN₀ hU)

/-- **Non-uniformity at the lower edge**: on every interior one-sided neighbourhood
`(μ₋, μ₋ + δ)`, neither the `σ_min` law nor the `κ₂` law holds uniformly in `τ`. -/
theorem nonuniform_lower (ha0 : 0 < a) (ha1 : a < 1) {δ : ℝ} (hδ : 0 < δ) :
    ¬ UniformRelO1 a (Ioo (lowerEdge a) (lowerEdge a + δ) ∩ Ioo (lowerEdge a) (upperEdge a))
        (fun τ N => sigmaMinMat N a τ) (fun τ N => π * gam a τ * dN N a τ / (N + τ)) ∧
    ¬ UniformRelO1 a (Ioo (lowerEdge a) (lowerEdge a + δ) ∩ Ioo (lowerEdge a) (upperEdge a))
        (fun τ N => kappaMat N a τ) (fun τ N => Cint a τ * (N + τ) / dN N a τ) := by
  have hW : ∀ᶠ τ in 𝓝[>] lowerEdge a, τ ∈ Ioo (lowerEdge a) (lowerEdge a + δ) :=
    Ioo_mem_nhdsGT (by linarith)
  constructor
  · rintro ⟨K, N₀, hK⟩
    obtain ⟨N, hN₀, hN2, hKN⟩ := exists_large_N K N₀
    have hs₀ := sigmaMin_lowerEdge_pos ha0 ha1 hN2
    have hg : ∀ᶠ τ in 𝓝[>] lowerEdge a, gam a τ < sigmaMin N a (lowerEdge a) / (2 * π) :=
      ((gam_tendsto_zero_lower ha0 ha1).mono_left nhdsWithin_le_nhds).eventually
        (gt_mem_nhds (by positivity))
    obtain ⟨τ, ⟨⟨h, hσ, hU⟩, hγ⟩, hw⟩ := (((near_lower_edge ha0 ha1 hN2).and hg).and hW).exists
    exact sigma_contra ha0 ha1 hN2 hKN hs₀ h hσ hγ
      (hK τ ⟨hw, h.2.2.1, h.2.2.2⟩ N hN₀ hU)
  · rintro ⟨K, N₀, hK⟩
    obtain ⟨N, hN₀, hN2, hKN⟩ := exists_large_N K N₀
    have hs₀ := sigmaMin_lowerEdge_pos ha0 ha1 hN2
    obtain ⟨τ, ⟨⟨h, hσ, hU⟩, hC⟩, hw⟩ := (((near_lower_edge ha0 ha1 hN2).and
      ((Cint_tendsto_atTop_lower ha0 ha1).eventually_gt_atTop
        ((upperEdge a - lowerEdge a) / (sigmaMin N a (lowerEdge a) / 2)))).and hW).exists
    exact kappa_contra ha0 ha1 hN2 hKN hs₀ h hσ hU hC (hK τ ⟨hw, h.2.2.1, h.2.2.2⟩ N hN₀ hU)

/-- **`thm:main-conditioning`**, all five regimes with the operator-norm `κ₂(B_N)` and
`σ_min(B_N)`, plus the closing sentence: the interior error terms are **not** uniform as `τ` approaches a band
edge — at either edge, on every one-sided interior neighbourhood, for both `σ_min` and `κ₂`, no
single pair `(K, N₀)` serves all `τ`. -/
theorem thm_main_conditioning (ha0 : 0 < a) (ha1 : a < 1) :
    (∀ τ : ℝ, τ < lowerEdge a →
      (∀ N : ℕ, 2 ≤ N → IsUnit (shifted N a τ) ∧
        kappaMat N a τ < (upperEdge a - τ) / (lowerEdge a - τ)) ∧
      Tendsto (fun N => kappaMat N a τ) atTop (𝓝 ((upperEdge a - τ) / (lowerEdge a - τ)))) ∧
    ((∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → IsUnit (shifted N a (lowerEdge a))) ∧
      RelBigO 2 (fun _ => True) (fun N => kappaMat N a (lowerEdge a))
        (fun N => 4 * upperEdge a ^ 2 / π ^ 2 * (N + lowerEdge a) ^ 2)) ∧
    (∀ τ : ℝ, lowerEdge a < τ → τ < upperEdge a →
      RelBigO 1 (fun N => Nonsingular N a τ) (fun N => sigmaMinMat N a τ)
        (fun N => π * gam a τ * dN N a τ / (N + τ)) ∧
      RelBigO 1 (fun N => Nonsingular N a τ) (fun N => kappaMat N a τ)
        (fun N => Cint a τ * (N + τ) / dN N a τ)) ∧
    ((∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → IsUnit (shifted N a (upperEdge a))) ∧
      RelBigO 2 (fun _ => True) (fun N => kappaMat N a (upperEdge a))
        (fun N => 4 * lowerEdge a ^ 2 / π ^ 2 * (N + upperEdge a) ^ 2)) ∧
    (∀ τ : ℝ, upperEdge a < τ →
      (∀ N : ℕ, 2 ≤ N → IsUnit (shifted N a τ) ∧
        kappaMat N a τ < (τ - lowerEdge a) / (τ - upperEdge a)) ∧
      Tendsto (fun N => kappaMat N a τ) atTop (𝓝 ((τ - lowerEdge a) / (τ - upperEdge a)))) ∧
    (∀ δ : ℝ, 0 < δ →
      ¬ UniformRelO1 a (Ioo (upperEdge a - δ) (upperEdge a) ∩ Ioo (lowerEdge a) (upperEdge a))
          (fun τ N => sigmaMinMat N a τ) (fun τ N => π * gam a τ * dN N a τ / (N + τ)) ∧
      ¬ UniformRelO1 a (Ioo (upperEdge a - δ) (upperEdge a) ∩ Ioo (lowerEdge a) (upperEdge a))
          (fun τ N => kappaMat N a τ) (fun τ N => Cint a τ * (N + τ) / dN N a τ) ∧
      ¬ UniformRelO1 a (Ioo (lowerEdge a) (lowerEdge a + δ) ∩ Ioo (lowerEdge a) (upperEdge a))
          (fun τ N => sigmaMinMat N a τ) (fun τ N => π * gam a τ * dN N a τ / (N + τ)) ∧
      ¬ UniformRelO1 a (Ioo (lowerEdge a) (lowerEdge a + δ) ∩ Ioo (lowerEdge a) (upperEdge a))
          (fun τ N => kappaMat N a τ) (fun τ N => Cint a τ * (N + τ) / dN N a τ)) := by
  obtain ⟨hlo, hhi⟩ := thm_outside ha0 ha1
  obtain ⟨-, hU, hUk, -, hL, hLk⟩ := thm_edges ha0 ha1
  refine ⟨fun τ hτ => ⟨(hlo τ hτ).1, (hlo τ hτ).2.1⟩, ⟨hL, hLk⟩, fun τ h1 h2 => ?_, ⟨hU, hUk⟩,
    fun τ hτ => ⟨(hhi τ hτ).1, (hhi τ hτ).2.1⟩, fun δ hδ =>
    ⟨(nonuniform_upper ha0 ha1 hδ).1, (nonuniform_upper ha0 ha1 hδ).2,
      (nonuniform_lower ha0 ha1 hδ).1, (nonuniform_lower ha0 ha1 hδ).2⟩⟩
  have h : InteriorParam a τ := ⟨ha0, ha1, h1, h2⟩
  exact ⟨(thm_smin h).1, (thm_kappa h).2.2.2⟩

/-! ## §6 Arithmetic laws for interior conditioning -/

lemma ratLaw_top {p q : ℕ} (h1 : ∃! r : ℕ, r < q ∧ dRes a τ p q r = 0) :
    ratLaw a τ p q {⊤} = (q : ℝ≥0∞)⁻¹ := by
  rw [ratLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  have e : ∀ r, Measure.dirac (atomVal (Cint a τ) (dRes a τ p q r)) {⊤} =
      if dRes a τ p q r = 0 then 1 else 0 := by
    intro r
    rw [Measure.dirac_apply' _ (measurableSet_singleton _)]
    unfold atomVal
    split_ifs with hd
    · simp
    · simp
  simp_rw [e]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc : ((range q).filter fun r => dRes a τ p q r = 0).card = 1 := by
    rw [Finset.card_eq_one]
    obtain ⟨r, ⟨hr, hr0⟩, huniq⟩ := h1
    refine ⟨r, ?_⟩
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    exact ⟨fun hs => huniq s hs, fun hs => hs ▸ ⟨hr, hr0⟩⟩
  rw [hc, Nat.cast_one, smul_eq_mul, mul_one]

lemma kappaMat_seq (ha0 : 0 < a) (ha1 : a < 1) {q : ℕ} (hq : 1 ≤ q) (r : ℕ) :
    (fun k : ℕ => kappa (r + q * k) a τ / ((r + q * k : ℕ) : ℝ)) =ᶠ[atTop]
      (fun k : ℕ => kappaMat (r + q * k) a τ / ((r + q * k : ℕ) : ℝ)) := by
  filter_upwards [eventually_ge_atTop 2] with k hk
  have : 2 ≤ r + q * k := by nlinarith
  rw [kappaMat_eq ha0 ha1 this]

/-- **`thm:rational-laws`** (`α = p/q` in lowest terms, `d_r = ‖rp/q - β‖`, eq. `(dr)`).
Incompatible case `qβ ∉ ℤ`: every `d_r > 0`, every `B_N` is invertible, `κ₂(B_N)/N → C/d_r` along
`N ≡ r (mod q)` (eq. `(rat-incompat)`), and the empirical law of `κ₂/N` converges weakly to
`q⁻¹ ∑_{r<q} δ_{C/d_r}` (eq. `(rat-measure)`). Compatible case `qβ ∈ ℤ`: exactly one residue class
has `d_r = 0` and it is singular; the other classes obey `(rat-incompat)`; with `κ₂ = +∞` at singular
`N`, the empirical law (on `[-∞, +∞]`) converges weakly to the atomic law with one atom of mass
`1/q` at `+∞` and the finite atoms `C/d_r` on the remaining classes. -/
theorem thm_rational_laws {p q : ℕ} (h : InteriorParam a τ) (hpq : p.Coprime q)
    (hα : alphaOf a τ = p / q) :
    (∀ r : ℕ, dRes a τ p q r = distZ (r * p / q - betaOf a τ)) ∧
    ((¬ ∃ z : ℤ, (q : ℝ) * betaOf a τ = z) →
      (∀ r : ℕ, r < q → 0 < dRes a τ p q r) ∧
      (∀ N : ℕ, 2 ≤ N → IsUnit (shifted N a τ)) ∧
      (∀ r : ℕ, r < q → Tendsto (fun k : ℕ => kappaMat (r + q * k) a τ / ((r + q * k : ℕ) : ℝ))
        atTop (𝓝 (Cint a τ / dRes a τ p q r))) ∧
      WeakLim (empMeasure fun N => kappaMat N a τ / N)
        (((q : ℝ≥0∞)⁻¹) • ∑ r ∈ range q, Measure.dirac (Cint a τ / dRes a τ p q r))) ∧
    ((∃ z : ℤ, (q : ℝ) * betaOf a τ = z) →
      (∃! r : ℕ, r < q ∧ dRes a τ p q r = 0) ∧
      (∀ r : ℕ, r < q → dRes a τ p q r = 0 → ∀ N : ℕ, 2 ≤ N → N % q = r →
        ¬ IsUnit (shifted N a τ)) ∧
      (∀ r : ℕ, r < q → 0 < dRes a τ p q r →
        Tendsto (fun k : ℕ => kappaMat (r + q * k) a τ / ((r + q * k : ℕ) : ℝ))
          atTop (𝓝 (Cint a τ / dRes a τ p q r))) ∧
      WeakLim (empMeasure fun N =>
          if IsUnit (shifted N a τ) then ((kappaMat N a τ / N : ℝ) : EReal) else (⊤ : EReal))
        (((q : ℝ≥0∞)⁻¹) • ∑ r ∈ range q, Measure.dirac
          (if dRes a τ p q r = 0 then (⊤ : EReal) else ((Cint a τ / dRes a τ p q r : ℝ) : EReal))) ∧
      (((q : ℝ≥0∞)⁻¹) • ∑ r ∈ range q, Measure.dirac
          (if dRes a τ p q r = 0 then (⊤ : EReal) else ((Cint a τ / dRes a τ p q r : ℝ) : EReal)))
        {⊤} = (q : ℝ≥0∞)⁻¹) := by
  have ha0 := h.1
  have ha1 := h.2.1
  obtain ⟨hp, hpq'⟩ := rational_q_bounds h hα
  have hq1 : 1 ≤ q := by omega
  obtain ⟨hsing, hlim, hweak⟩ := ShiftedKMS.thm_rational_laws h hα
  refine ⟨fun r => rfl, fun hno => ?_, fun hz => ?_⟩
  · have hno' : ∀ z : ℤ, (q : ℝ) * betaOf a τ ≠ z := fun z hz => hno ⟨z, hz⟩
    obtain ⟨hd, hns, hw⟩ := thm_rational_laws_incompat h hα hno'
    refine ⟨fun r _ => hd r, fun N hN => isUnit_iff_nonsingular.2 (hns N hN),
      fun r hr => (hlim r hr (hd r)).congr' (kappaMat_seq ha0 ha1 hq1 r), ?_⟩
    rw [empMeasure_congr (y := fun N => kappa N a τ / N) fun N hN => by rw [kappaMat_eq ha0 ha1 hN]]
    exact hw
  · obtain ⟨z, hz⟩ := hz
    have hu := thm_rational_laws_compat h hpq hα hz
    refine ⟨hu, fun r hr hr0 N hN hNr hU => hsing r hr hr0 N hN hNr (isUnit_iff_nonsingular.1 hU),
      fun r hr hr0 => (hlim r hr hr0).congr' (kappaMat_seq ha0 ha1 hq1 r), ?_,
      ratLaw_top (a := a) (τ := τ) hu⟩
    rw [empMeasure_congr (y := kapNormE a τ) fun N hN => by
      unfold kapNormE; rw [kappaMat_eq ha0 ha1 hN]; simp only [isUnit_iff_nonsingular]]
    exact hweak

/-- `𝓘_L^*` as the paper writes it: the window indices with `d_N > 0`. -/
lemma windowStar_eq_dN (h : InteriorParam a τ) (L : ℕ) :
    windowStar a τ L = (window L).filter (fun N => 0 < dN N a τ) := by
  unfold windowStar
  refine Finset.filter_congr fun N hN => ?_
  have hN2 := (Finset.mem_Icc.1 hN).1
  rw [Nonsingular, ne_eq, thm_sing_dN h hN2]
  exact ⟨fun h' => lt_of_le_of_ne (distZ_nonneg _) (Ne.symm h'), fun h' => h'.ne'⟩

lemma card_windowStar_exact (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    (∀ L : ℕ, (windowStar a τ L).card = L) ∨
      ∃ N₁ : ℕ, 2 ≤ N₁ ∧ ∀ L : ℕ, (windowStar a τ L).card = if N₁ ≤ L + 1 then L - 1 else L := by
  have hsplit : ∀ L, (windowStar a τ L).card +
      ((window L).filter (fun N => ¬ Nonsingular N a τ)).card = L := by
    intro L
    have e := Finset.card_filter_add_card_filter_not (s := window L)
      (p := fun N => Nonsingular N a τ)
    rw [card_window] at e
    unfold windowStar
    convert e using 3
  by_cases hs : ∃ N₁, 2 ≤ N₁ ∧ ¬ Nonsingular N₁ a τ
  · obtain ⟨N₁, hN₁, hsg⟩ := hs
    refine Or.inr ⟨N₁, hN₁, fun L => ?_⟩
    have := hsplit L
    split_ifs with hL
    · have h1 : ((window L).filter (fun N => ¬ Nonsingular N a τ)).card = 1 := by
        apply le_antisymm (card_sing_le h hα L)
        apply Finset.card_pos.2
        exact ⟨N₁, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hN₁, hL⟩, hsg⟩⟩
      omega
    · have h0 : ((window L).filter (fun N => ¬ Nonsingular N a τ)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro N hN hns
        have hNw := Finset.mem_Icc.1 hN
        have : N = N₁ := singDims_subsingleton_of_irrational h hα
          ⟨hNw.1, not_not.1 hns⟩ ⟨hN₁, not_not.1 hsg⟩
        omega
      omega
  · refine Or.inl fun L => ?_
    push Not at hs
    have h0 : ((window L).filter (fun N => ¬ Nonsingular N a τ)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro N hN hns
      exact hns (hs N (Finset.mem_Icc.1 hN).1)
    have := hsplit L
    omega

/-- **`thm:irr-laws`** (irrational `α`; `𝓘_L = {2,…,L+1}`, `𝓘_L^* = {N ∈ 𝓘_L : d_N > 0}`):
`L^* = L` for all `L`, or there is one singular `N₁` and `L^* = L - 1` exactly for `L ≥ N₁ - 1`;
eq. `(uniformlaw)`; eq. `(paretolaw)` with `Law(C/U)`, `U ~ U[0,1/2]`; Pareto tail of index one
(eq. `(paretotail)`, for `t > 0`, where `2C/t` is defined); and eq. `(cesaro)` over `𝓘_L^*` with
denominator `L`. -/
theorem thm_irr_laws (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    (∀ L : ℕ, window L = Finset.Icc 2 (L + 1) ∧
      windowStar a τ L = (window L).filter (fun N => 0 < dN N a τ)) ∧
    ((∀ L : ℕ, (windowStar a τ L).card = L) ∨
      ∃ N₁ : ℕ, 2 ≤ N₁ ∧ ∀ L : ℕ, (windowStar a τ L).card = if N₁ ≤ L + 1 then L - 1 else L) ∧
    IsProbabilityMeasure (unif 0 (π * gam a τ / 2)) ∧
    WeakLim (empMeasure fun N => (N : ℝ) * sigmaMinMat N a τ) (unif 0 (π * gam a τ / 2)) ∧
    paretoLaw (Cint a τ) = (unif 0 (1 / 2)).map (fun u => Cint a τ / u) ∧
    IsProbabilityMeasure (paretoLaw (Cint a τ)) ∧
    WeakLim (empMeasureStar a τ fun N => kappaMat N a τ / N) (paretoLaw (Cint a τ)) ∧
    (∀ t : ℝ, 0 < t → paretoLaw (Cint a τ) (Ioi t) = ENNReal.ofReal (min 1 (2 * Cint a τ / t))) ∧
    Tendsto (fun L : ℕ => (L : ℝ)⁻¹ * ∑ N ∈ windowStar a τ L, kappaMat N a τ / N) atTop atTop := by
  have ha0 := h.1
  have ha1 := h.2.1
  refine ⟨fun L => ⟨rfl, windowStar_eq_dN h L⟩, card_windowStar_exact h hα,
    isProbabilityMeasure_unif (by have := gam_pos h; positivity), ?_, rfl,
    isProbabilityMeasure_paretoLaw _, ?_, fun t ht => paretoLaw_tail (Cint_pos h) ht, ?_⟩
  · rw [empMeasure_congr (y := fun N => (N : ℝ) * sigmaMin N a τ) fun N hN => by
      rw [sigmaMinMat_eq ha0 ha1 hN]]
    exact thm_irr_laws_uniform h hα
  · rw [empMeasureStar_congr (y := fun N => kappa N a τ / N) fun N hN => by
      rw [kappaMat_eq ha0 ha1 hN]]
    exact thm_irr_laws_pareto h hα
  · refine (thm_irr_laws_cesaro h hα).congr fun L => ?_
    congr 1
    refine Finset.sum_congr rfl fun N hN => ?_
    rw [kappaMat_eq ha0 ha1 (Finset.mem_Icc.1 (Finset.mem_filter.1 hN).1).1]

/-- For irrational `α`, `B_N` is invertible for all large `N` (the isolated singular dimension,
if any, is deleted). -/
lemma eventually_isUnit (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    ∀ᶠ N in atTop, IsUnit (shifted N a τ) := by
  by_cases hs : ∃ N₁, 2 ≤ N₁ ∧ ¬ Nonsingular N₁ a τ
  · obtain ⟨N₁, hN₁, hsg⟩ := hs
    filter_upwards [eventually_ge_atTop (N₁ + 1)] with N hN
    rw [isUnit_iff_nonsingular]
    intro hns
    have : N = N₁ := singDims_subsingleton_of_irrational h hα
      ⟨by omega, hns⟩ ⟨hN₁, not_not.1 hsg⟩
    omega
  · push Not at hs
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact isUnit_iff_nonsingular.2 (hs N hN)

lemma deleted_eq_atTop (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    atTop ⊓ 𝓟 {N : ℕ | IsUnit (shifted N a τ)} = atTop :=
  inf_eq_left.2 (le_principal_iff.2 (eventually_isUnit h hα))

/-- **`thm:quadratic-envelope`** (with `𝓜₊ = liminf N ‖Nα - β‖`, eq. `(Mplus)`): after deleting
the (at most one) singular dimension, `limsup κ₂(B_N)/N² = C/𝓜₊`, with `C/0 = +∞`. -/
theorem thm_quadratic_envelope (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    Mplus (alphaOf a τ) (betaOf a τ) =
      liminf (fun N : ℕ => ENNReal.ofReal (N * dN N a τ)) atTop ∧
    (∀ᶠ N in atTop, IsUnit (shifted N a τ)) ∧
    limsup (fun N : ℕ => ENNReal.ofReal (kappaMat N a τ / (N : ℝ) ^ 2))
        (atTop ⊓ 𝓟 {N : ℕ | IsUnit (shifted N a τ)}) =
      ENNReal.ofReal (Cint a τ) / Mplus (alphaOf a τ) (betaOf a τ) ∧
    (Mplus (alphaOf a τ) (betaOf a τ) = 0 →
      ENNReal.ofReal (Cint a τ) / Mplus (alphaOf a τ) (betaOf a τ) = ⊤) := by
  refine ⟨rfl, eventually_isUnit h hα, ?_, fun h0 => ?_⟩
  · rw [deleted_eq_atTop h hα, ← ShiftedKMS.thm_quadratic_envelope h hα]
    refine limsup_congr ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [kappaMat_eq h.1 h.2.1 hN]
  · rw [h0]; exact ENNReal.div_zero (ENNReal.ofReal_pos.2 (Cint_pos h)).ne'

/-- **`def:wplus`**: `w₊(α,β) = sup {w ≥ 0 : ‖Nα - β‖ < N^{-w} for infinitely many N ∈ ℕ}`, and the
set is nonempty (it contains `w = 0`). -/
theorem def_wplus (α β : ℝ) :
    wplus α β = sSup ((fun w : NNReal => (w : ℝ≥0∞)) ''
      {w : NNReal | {N : ℕ | distZ (N * α - β) < (N : ℝ) ^ (-(w : ℝ))}.Infinite}) ∧
    (0 : NNReal) ∈ {w : NNReal | {N : ℕ | distZ (N * α - β) < (N : ℝ) ^ (-(w : ℝ))}.Infinite} := by
  refine ⟨?_, ?_⟩
  · unfold wplus
    rw [sSup_image]
    refine iSup_congr fun w => ?_
    exact iSup_congr_Prop Nat.frequently_atTop_iff_infinite (fun _ => rfl)
  · show {N : ℕ | distZ (N * α - β) < (N : ℝ) ^ (-((0 : NNReal) : ℝ))}.Infinite
    have : {N : ℕ | distZ (N * α - β) < (N : ℝ) ^ (-((0 : NNReal) : ℝ))} = Set.univ := by
      ext N
      simp only [NNReal.coe_zero, neg_zero, Real.rpow_zero, Set.mem_ofPred_eq, Set.mem_univ,
        iff_true]
      linarith [distZ_le_half (N * α - β)]
    rw [this]
    exact Set.infinite_univ

/-- **`thm:exponent`**: after deleting the singular dimension,
`limsup log κ₂(B_N)/log N = 1 + w₊(α,β)` (eq. `(condexp)`). -/
theorem thm_exponent (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    limsup (fun N : ℕ => ENNReal.ofReal (Real.log (kappaMat N a τ) / Real.log N))
        (atTop ⊓ 𝓟 {N : ℕ | IsUnit (shifted N a τ)}) =
      1 + wplus (alphaOf a τ) (betaOf a τ) := by
  rw [deleted_eq_atTop h hα, ← ShiftedKMS.thm_exponent h hα]
  refine limsup_congr ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [kappaMat_eq h.1 h.2.1 hN]

/-- **`thm:generic`** (fixed irrational `α`, which for an interior pair lies in `(0,1)`): for a.e.
`β`, `𝓜₊ = 0` and `w₊ = 1` (eq. `(genericM)`); and for a.e. `0 < β < 1 - α`, the corresponding pair
`(a,τ)` of `thm:triangle` satisfies eq. `(genericcond)` (singular dimension deleted). -/
theorem thm_generic {α : ℝ} (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ᵐ β : ℝ, Mplus α β = 0 ∧ wplus α β = 1) ∧
    ∀ᵐ β : ℝ, β ∈ Ioo 0 (1 - α) →
      InteriorParam (aOf α β) (tauOf α β) ∧
      alphaOf (aOf α β) (tauOf α β) = α ∧ betaOf (aOf α β) (tauOf α β) = β ∧
      limsup (fun N : ℕ => ENNReal.ofReal
          (Real.log (kappaMat N (aOf α β) (tauOf α β)) / Real.log N))
        (atTop ⊓ 𝓟 {N : ℕ | IsUnit (shifted N (aOf α β) (tauOf α β))}) = 2 ∧
      limsup (fun N : ℕ => ENNReal.ofReal (kappaMat N (aOf α β) (tauOf α β) / (N : ℝ) ^ 2))
        (atTop ⊓ 𝓟 {N : ℕ | IsUnit (shifted N (aOf α β) (tauOf α β))}) = ⊤ := by
  refine ⟨(ae_Mplus_eq_zero hα).and (ae_wplus_eq_one hα), ?_⟩
  filter_upwards [thm_generic_triangle hα hα0 hα1] with β hβ hmem
  have htri : (α, β) ∈ triangleSet := ⟨hα0, hmem.1, by linarith [hmem.2]⟩
  obtain ⟨hI, hA, hB⟩ := triangle_inverse htri
  obtain ⟨-, -, hlog, hsq⟩ := hβ htri
  have hirr : Irrational (alphaOf (aOf α β) (tauOf α β)) := by rw [hA]; exact hα
  refine ⟨hI, hA, hB, ?_, ?_⟩
  · rw [deleted_eq_atTop hI hirr, ← hlog]
    refine limsup_congr ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [kappaMat_eq hI.1 hI.2.1 hN]
  · rw [deleted_eq_atTop hI hirr, ← hsq]
    refine limsup_congr ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [kappaMat_eq hI.1 hI.2.1 hN]

/-! ## §7 The resonant hollow slice -/

/-- **`thm:resonance`**: within the interior triangle `τ = 1 ⇔ β = α` (eq. `(resonance)`), and
`β > α ⇔ τ > 1`, `β < α ⇔ τ < 1` (eq. `(tau-regions)`). -/
theorem thm_resonance (h : InteriorParam a τ) :
    (τ = 1 ↔ betaOf a τ = alphaOf a τ) ∧ (alphaOf a τ < betaOf a τ ↔ 1 < τ) ∧
      (betaOf a τ < alphaOf a τ ↔ τ < 1) :=
  ShiftedKMS.thm_resonance h

lemma kms_sub_one (N : ℕ) (a : ℝ) : kms N a - 1 = shifted N a 1 := by
  rw [shifted, Matrix.diagonal_one]

/-- **`cor:hollowdich`** (`τ = 1`, an interior level for every `0 < a < 1`): `d_N = ‖(N-1)α‖`
(eq. `(hollowd)`); for `α = p/q` in lowest terms `T_N(a) - I_N` is singular exactly when
`N ≡ 1 (mod q)` (eq. `(hollowcong)`); irrational `α` gives no singular dimension. -/
theorem cor_hollowdich (ha0 : 0 < a) (ha1 : a < 1) :
    InteriorParam a 1 ∧
    (∀ N : ℕ, dN N a 1 = distZ (((N : ℝ) - 1) * alphaOf a 1)) ∧
    (∀ p q : ℕ, p.Coprime q → alphaOf a 1 = p / q → ∀ N : ℕ, 2 ≤ N →
      ((kms N a - 1).det = 0 ↔ (N : ℤ) ≡ 1 [ZMOD q])) ∧
    (Irrational (alphaOf a 1) → ∀ N : ℕ, 2 ≤ N → (kms N a - 1).det ≠ 0) := by
  have h := hollow_interior ha0 ha1
  refine ⟨h, cor_hollowdich_dN h rfl, fun p q hpq hα N hN => ?_, fun hα N hN hd => ?_⟩
  · rw [kms_sub_one, ← cor_hollowdich_rational h rfl hpq hα N hN]
    exact ⟨fun hd => ⟨hN, hd⟩, fun hd => hd.2⟩
  · have hmem : N ∈ singDims a 1 := ⟨hN, by rw [← kms_sub_one]; exact hd⟩
    rw [cor_hollowdich_irrational h rfl hα] at hmem
    exact hmem

/-- **`prop:affinecollapse`**: if `β ≡ rα (mod 1)` for a fixed integer `r ≥ 1`, then
`d_N = ‖(N - r)α‖` (eq. `(affinehom)`) and `𝓜₊(α,β) = liminf_q q‖qα‖` (eq. `(Mhom)`). -/
theorem prop_affinecollapse (r : ℕ) (_hr : 1 ≤ r)
    (hβ : ∃ m : ℤ, betaOf a τ = r * alphaOf a τ - m) :
    (∀ N : ℕ, dN N a τ = distZ (((N : ℝ) - r) * alphaOf a τ)) ∧
    Mplus (alphaOf a τ) (betaOf a τ) =
      liminf (fun q : ℕ => ENNReal.ofReal (q * distZ (q * alphaOf a τ))) atTop := by
  obtain ⟨m, hm⟩ := hβ
  refine ⟨ShiftedKMS.prop_affinecollapse hm, ?_⟩
  rw [hm, prop_affinecollapse_Mplus]
  simp only [Mplus, sub_zero]

end PaperStatement

/-! ## Scope and equation ledger

Displayed equations and in-text claims of the accompanying manuscript that are not themselves labeled
environments, each as a theorem on the actual matrices. -/

namespace PaperLedger

open PaperStatement

variable {a τ : ℝ}

/-- eq. `(smax)`: `σ_max(B_N) = M(a,τ) + O(N^{-2})` for interior `(a,τ)`, `M = max{μ₊-τ, τ-μ₋}`
(eq. `(M)`). -/
theorem eq_smax (h : InteriorParam a τ) :
    AbsBigO 2 (fun N => sigmaMaxMat N a τ) (fun _ => max (upperEdge a - τ) (τ - lowerEdge a)) := by
  refine ⟨max (L2mu a * π ^ 2) 1, lt_of_lt_of_le one_pos (le_max_right _ _), 2, fun N hN => ?_⟩
  dsimp only
  rw [sigmaMaxMat_eq h.1 h.2.1 hN]
  exact (thm_smax h (N := N) (by omega)).trans
    (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))

/-- eq. `(cassels)`: for fixed irrational `α` and every `c > 0`, `‖Nα - β‖ < c/N` has infinitely many
positive solutions for almost every `β` (Cassels' theorem, proved in `KMS.Cassels`). -/
theorem eq_cassels (α : ℝ) (hα : Irrational α) (c : ℝ) (hc : 0 < c) :
    ∀ᵐ β : ℝ, {N : ℕ | 0 < N ∧ distZ (N * α - β) < c / N}.Infinite := by
  filter_upwards [casselsSupplier α hα c hc] with β hβ
  rw [← Nat.frequently_atTop_iff_infinite]
  refine (hβ.and_eventually (eventually_gt_atTop 0)).mono fun N hN => ⟨hN.2, ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN.2
  rw [lt_div_iff₀ hN0, mul_comm]
  exact hN.1

/-- Weyl's equidistribution theorem in the form used (`{Nα - β}` equidistributed mod 1 for
irrational `α`, every target `β`), proved in `KMS.Suppliers`. -/
theorem weyl : WeylSupplier := weyl_equidistribution

/-- The first Borel–Cantelli step of the generic argument. -/
theorem borel_cantelli (α : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ β : ℝ, ∀ᶠ N : ℕ in atTop, ¬ distZ (N * α - β) < (N : ℝ) ^ (-(1 + ε)) :=
  ae_eventually_not_lt_rpow α hε

/-- eq. `(paretotail)` on its domain `t > 0`, together with the trivial range `t ≤ 0`. -/
theorem eq_paretotail {C : ℝ} (hC : 0 < C) :
    (∀ t : ℝ, 0 < t → paretoLaw C (Ioi t) = ENNReal.ofReal (min 1 (2 * C / t))) ∧
    (∀ t : ℝ, t ≤ 0 → paretoLaw C (Ioi t) = 1) :=
  ⟨fun _ ht => paretoLaw_tail hC ht, fun _ ht => paretoLaw_tail_nonpos hC ht⟩

/-- Hollow slice `τ = 1`: `a = cos(πα)`, eqs. `(hollowgamma)`, `(hollowC)`, eq. `(hollowkappa)`
for the operator-norm `κ₂(T_N(a) - I_N)`, the hollow determinant and kernel vector. -/
theorem hollow_identities (ha0 : 0 < a) (ha1 : a < 1) :
    Real.cos (π * alphaOf a 1) = a ∧ gam a 1 = 2 * a / √(1 - a ^ 2) ∧
    max (upperEdge a - 1) (1 - lowerEdge a) = 2 * a / (1 - a) ∧
    Cint a 1 = 1 / π * √((1 + a) / (1 - a)) ∧
    RelBigO 1 (fun N => Nonsingular N a 1) (fun N => ‖kms N a - 1‖ * ‖(kms N a - 1)⁻¹‖)
      (fun N => 1 / π * √((1 + a) / (1 - a)) * (N + 1) / distZ (((N : ℝ) - 1) * alphaOf a 1)) ∧
    (∀ N : ℕ, 2 ≤ N → (kms N a - 1).det =
      (-1) ^ (N + 1) * a ^ N * Polynomial.eval a (Polynomial.Chebyshev.U ℝ ((N : ℤ) - 2))) ∧
    (∀ (N : ℕ) (j : Fin N), Real.sin ((((j : ℕ) : ℝ) + 1) * crossAngle a 1) -
        a * Real.sin (((j : ℕ) : ℝ) * crossAngle a 1) =
      Real.sin (crossAngle a 1) * Polynomial.eval a (Polynomial.Chebyshev.T ℝ ((j : ℕ) : ℤ))) := by
  obtain ⟨h1, h2, h3, h4⟩ := hollow_constants ha0 ha1
  refine ⟨h1, h2, h3, h4, ?_, fun N hN => by rw [kms_sub_one]; exact hollow_det ha0 ha1 hN,
    fun N j => hollow_kernel_vector ha0 ha1 N j⟩
  simp_rw [kms_sub_one]
  refine RelBigO.congr (relBigO_of_two_sided (c := Kkap a 1) (N₀ := n2 a 1)
    fun N hN hns => ?_) 2 fun N hN _ => kappaMat_eq ha0 ha1 hN |>.symm
  simp only [pow_one]
  refine ⟨?_, hollow_kappa ha0 ha1 hN hns⟩
  have := distZ_nonneg (((N : ℝ) - 1) * alphaOf a 1)
  positivity

lemma tendsto_kappaMat_of (ha0 : 0 < a) (ha1 : a < 1) {f : ℕ → ℕ} (hf : ∀ᶠ k in atTop, 2 ≤ f k)
    {L : ℝ} (h : Tendsto (fun k => kappa (f k) a τ / (f k : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun k => kappaMat (f k) a τ / (f k : ℝ)) atTop (𝓝 L) := by
  refine h.congr' ?_
  filter_upwards [hf] with k hk
  rw [kappaMat_eq ha0 ha1 hk]

/-- §4 example (golden recurrent non-hollow point). -/
theorem example_recurrent_nonhollow :
    InteriorParam ((3 - √5) / 2) ((1 + √5) / 2) ∧
    alphaOf ((3 - √5) / 2) ((1 + √5) / 2) = 1 / 5 ∧
    betaOf ((3 - √5) / 2) ((1 + √5) / 2) = 3 / 5 ∧
    ∀ N : ℕ, 2 ≤ N → ((shifted N ((3 - √5) / 2) ((1 + √5) / 2)).det = 0 ↔ N % 5 = 3) := by
  obtain ⟨h1, h2, h3, h4⟩ := example_golden
  refine ⟨h1, h2, h3, fun N hN => ?_⟩
  rw [← h4 N hN]
  exact ⟨fun hd => ⟨hN, hd⟩, fun hd => hd.2⟩

/-- §6 example: the incompatible rational crossing `a = 2 - √3`, `τ = 2/√3`, with the operator-norm
`κ₂`. -/
theorem example_rational_incompatible :
    InteriorParam (2 - √3) (2 / √3) ∧
    alphaOf (2 - √3) (2 / √3) = 1 / 3 ∧ betaOf (2 - √3) (2 / √3) = 1 / 2 ∧
    (∀ N : ℕ, 2 ≤ N → IsUnit (shifted N (2 - √3) (2 / √3))) ∧
    (∀ N : ℕ, dN N (2 - √3) (2 / √3) = if N % 3 = 0 then 1 / 2 else 1 / 6) ∧
    gam (2 - √3) (2 / √3) = 2 / 3 ∧
    max (upperEdge (2 - √3) - 2 / √3) (2 / √3 - lowerEdge (2 - √3)) = 1 / √3 ∧
    Cint (2 - √3) (2 / √3) = √3 / (2 * π) ∧
    Tendsto (fun k : ℕ => kappaMat (3 * k) (2 - √3) (2 / √3) / ((3 * k : ℕ) : ℝ)) atTop
      (𝓝 (√3 / π)) ∧
    Tendsto (fun k : ℕ => kappaMat (1 + 3 * k) (2 - √3) (2 / √3) / ((1 + 3 * k : ℕ) : ℝ)) atTop
      (𝓝 (3 * √3 / π)) ∧
    Tendsto (fun k : ℕ => kappaMat (2 + 3 * k) (2 - √3) (2 / √3) / ((2 + 3 * k : ℕ) : ℝ)) atTop
      (𝓝 (3 * √3 / π)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := example_incompat
  have ha0 := h1.1
  have ha1 := h1.2.1
  refine ⟨h1, h2, h3, fun N hN => isUnit_iff_nonsingular.2 (h4 N hN), h5, h6, h7, h8,
    tendsto_kappaMat_of ha0 ha1 (f := fun k => 3 * k) ?_ h9,
    tendsto_kappaMat_of ha0 ha1 (f := fun k => 1 + 3 * k) ?_ h10,
    tendsto_kappaMat_of ha0 ha1 (f := fun k => 2 + 3 * k) ?_ h11⟩ <;>
  · filter_upwards [eventually_ge_atTop 1] with k hk
    omega

/-- §7 example: the isolated irrational singular point `a = 1/2`, `τ = 3/2`. -/
theorem example_isolated_irrational :
    InteriorParam (1 / 2) (3 / 2) ∧ (shifted 2 (1 / 2) (3 / 2)).det = 0 ∧
    Real.cos (crossAngle (1 / 2) (3 / 2)) = 3 / 4 ∧ Irrational (alphaOf (1 / 2) (3 / 2)) ∧
    betaOf (1 / 2) (3 / 2) = 2 * alphaOf (1 / 2) (3 / 2) ∧
    {N : ℕ | 2 ≤ N ∧ (shifted N (1 / 2) (3 / 2)).det = 0} = {2} ∧
    ∀ N : ℕ, dN N (1 / 2) (3 / 2) = distZ (((N : ℝ) - 2) * alphaOf (1 / 2) (3 / 2)) :=
  example_isolated

/-- eq. `(gamma-form)`. -/
theorem eq_gamma_form (h : InteriorParam a τ) :
    gam a τ = 2 * a * τ ^ 2 * Real.sin (π * alphaOf a τ) / (1 - a ^ 2) :=
  gam_form h

/-- eq. `(gamma-phase)`, with the sign resolved: `τ(cot πα - τ cot π(1-β)) = -μ_a'(θ_τ) = γ > 0`. -/
theorem eq_gamma_phase (h : InteriorParam a τ) :
    gam a τ = τ * (Real.cot (π * alphaOf a τ) - τ * Real.cot (π * (1 - betaOf a τ))) := by
  have ha0 := h.1; have ha1 := h.2.1
  have hθ := crossAngle_mem h
  have e1 : π * alphaOf a τ = crossAngle a τ := by unfold alphaOf; field_simp
  have e2 : π * (1 - betaOf a τ) = psi a (crossAngle a τ) := by unfold betaOf; field_simp; ring
  rw [e1, e2, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  have hτ : τ = (1 - a ^ 2) / Ra a (crossAngle a τ) := (symbol_crossAngle h).symm
  unfold gam
  generalize crossAngle a τ = θ at hθ hτ ⊢
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hR := Ra_pos ha0 ha1 θ
  have hc := cos_psi ha0 ha1 θ
  have hsn := sin_psi ha0 ha1 θ
  have hsψ : Real.sin (psi a θ) = Ea a θ / Ra a θ := by field_simp; linarith [hsn]
  have hcψ : Real.cos (psi a θ) = Da a θ / Ra a θ := by field_simp; linarith [hc]
  rw [hsψ, hcψ]
  have h1a : 0 < 1 - a ^ 2 := by nlinarith
  have hneg : dmu a θ < 0 := by
    unfold dmu; apply div_neg_of_neg_of_pos _ (by positivity)
    have : 0 < 2 * a * (1 - a ^ 2) * Real.sin θ := by positivity
    linarith
  rw [abs_of_neg hneg, hτ]
  unfold dmu Ea Da
  have hsc := Real.sin_sq_add_cos_sq θ
  have hRd : Ra a θ = 1 - 2 * a * Real.cos θ + a ^ 2 := rfl
  field_simp
  rw [hRd]
  linear_combination (2 * a) * hsc

/-- eq. `(factor)`: `D + iE = e^{-iθ}(e^{iθ} - a)²`. -/
theorem eq_factor (a θ : ℝ) :
    ((Da a θ : ℂ) + (Ea a θ : ℂ) * Complex.I) =
      Complex.exp (-(θ * Complex.I)) * (Complex.exp (θ * Complex.I) - a) ^ 2 := by
  have e1 : Complex.exp (-(θ * Complex.I)) = Real.cos θ - Real.sin θ * Complex.I := by
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.exp_mul_I]; push_cast
    rw [Complex.cos_neg, Complex.sin_neg]; ring
  have e2 : Complex.exp (θ * Complex.I) = Real.cos θ + Real.sin θ * Complex.I := by
    rw [Complex.exp_mul_I]; push_cast; ring
  rw [e1, e2]
  have hcs : ((Real.cos θ : ℂ)) ^ 2 + ((Real.sin θ : ℂ)) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.cos_sq_add_sin_sq,
      Complex.ofReal_one]
  have hI := Complex.I_sq
  simp only [Da, Ea, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  linear_combination (-((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I - 2 * a)) * hcs +
    (((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I - 2 * a) * (Real.sin θ : ℂ) ^ 2) * hI

/-- eq. `(Tinv)`: `T_N(a)⁻¹ = (1-a²)⁻¹ · tridiag(-a; 1, 1+a², …, 1+a², 1)`. -/
theorem eq_Tinv (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) :
    (kms N a)⁻¹ = (1 - a ^ 2)⁻¹ • kmsInvTri N a := by
  have h : (1 - a ^ 2) ≠ 0 := by nlinarith
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, kms_mul_kmsInvTri hN, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- The symbol band: `μ₋ ≤ μ_a(θ) ≤ μ₊`. -/
theorem symbol_band (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    lowerEdge a ≤ symbol a θ ∧ symbol a θ ≤ upperEdge a :=
  ⟨lowerEdge_le_symbol ha0 ha1 θ, symbol_le_upperEdge ha0 ha1 θ⟩

/-- Introduction: `σ_min(B_N)` is the distance from `τ` to the spectrum of `T_N(a)`. -/
theorem sigmaMin_eq_dist_spectrum (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) (τ : ℝ) :
    sigmaMinMat N a τ = Metric.infDist τ (spectrum ℝ (kms N a)) := by
  rw [sigmaMinMat_eq ha0 ha1 hN]; exact sigmaMin_eq_infDist ha0 ha1 hN τ

/-- Introduction: `B_N` is singular exactly when `d_N = 0`. -/
theorem singular_iff_dN (h : InteriorParam a τ) {N : ℕ} (hN : 2 ≤ N) :
    (shifted N a τ).det = 0 ↔ dN N a τ = 0 :=
  thm_sing_dN h hN

/-- `κ₂ ∈ (-∞,+∞]`: `kappaMatE = +∞` exactly at the singular dimensions; elsewhere it is the
operator-norm condition number. -/
theorem kappaMatE_spec (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) :
    (kappaMatE N a τ = ⊤ ↔ (shifted N a τ).det = 0) ∧
    ((shifted N a τ).det ≠ 0 → kappaMatE N a τ = ((‖shifted N a τ‖ * ‖(shifted N a τ)⁻¹‖ : ℝ) : EReal)) := by
  have _ := hN; have _ := ha0; have _ := ha1
  constructor
  · unfold kappaMatE
    by_cases hU : IsUnit (shifted N a τ)
    · simp only [hU, ↓reduceIte]
      exact ⟨fun h' => absurd h' (EReal.coe_ne_top _), fun h' => absurd h' (isUnit_iff_nonsingular.1 hU)⟩
    · simp only [hU, ↓reduceIte]
      exact ⟨fun _ => not_not.1 (fun h' => hU (isUnit_iff_nonsingular.2 h')), fun _ => trivial⟩
  · intro hns
    unfold kappaMatE
    simp only [isUnit_iff_nonsingular.2 hns, ↓reduceIte]
    rfl

/-- Weak convergence in Mathlib's topology of probability measures (supplement to `thm:irr-laws`):
the starred empirical laws of `κ₂(B_N)/N`, indexed `L ↦ 𝓘_{L+2}^*`, converge to `Law(C/U)`. -/
theorem irr_laws_probability_measures (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    Tendsto (empProbStar h hα (fun N => kappaMat N a τ / N)) atTop (𝓝 (paretoProb (Cint a τ))) := by
  have e : empProbStar h hα (fun N => kappaMat N a τ / N) =
      empProbStar h hα (fun N => kappa N a τ / N) := by
    funext L
    apply Subtype.ext
    show empMeasureStar a τ _ (L + 2) = empMeasureStar a τ _ (L + 2)
    rw [empMeasureStar_congr (a := a) (τ := τ) (x := fun N => kappaMat N a τ / N)
      (y := fun N => kappa N a τ / N) fun N hN => by rw [kappaMat_eq h.1 h.2.1 hN]]
  rw [e]
  exact thm_irr_laws_pareto_prob h hα

/-- An alternative Cesàro indexing `∑_{N ≤ L}` with the singular term removed (supplementary
to the corresponding manuscript theorem; its main form is the last conjunct of
`PaperStatement.thm_irr_laws`). -/
theorem cesaro_le_variant (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    Tendsto (fun L : ℕ => (L : ℝ)⁻¹ *
      ∑ N ∈ (Finset.Icc 2 L).filter (fun N => Nonsingular N a τ), kappaMat N a τ / N)
      atTop atTop := by
  refine (thm_irr_laws_cesaro_le h hα).congr fun L => ?_
  congr 1
  refine Finset.sum_congr rfl fun N hN => ?_
  rw [kappaMat_eq h.1 h.2.1 (Finset.mem_Icc.1 (Finset.mem_filter.1 hN).1).1]

/-- eq. `(Gprime)`: `G_N'(θ) = N + μ_a(θ) > 0`. -/
theorem eq_Gprime (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) (θ : ℝ) :
    HasDerivAt (Gph N a) (N + symbol a θ) θ ∧ 0 < N + symbol a θ :=
  ⟨hasDerivAt_Gph ha0 ha1 N θ, by have := symbol_pos ha0 ha1 θ; positivity⟩

/-- Band-edge degeneration of the interior constants: `γ → 0` and `C → +∞` at both edges. -/
theorem edge_degeneration (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (gam a) (𝓝 (upperEdge a)) (𝓝 0) ∧ Tendsto (gam a) (𝓝 (lowerEdge a)) (𝓝 0) ∧
    Tendsto (Cint a) (𝓝[<] upperEdge a) atTop ∧ Tendsto (Cint a) (𝓝[>] lowerEdge a) atTop :=
  ⟨gam_tendsto_zero_upper ha0 ha1, gam_tendsto_zero_lower ha0 ha1,
    Cint_tendsto_atTop_upper ha0 ha1, Cint_tendsto_atTop_lower ha0 ha1⟩

end PaperLedger

end ShiftedKMS
