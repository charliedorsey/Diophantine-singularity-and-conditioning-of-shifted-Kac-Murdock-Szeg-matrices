import KMS.Cond
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The matrix-to-spectral bridge

Everything here is about the **actual** real symmetric matrix `B_N = shifted N a τ` and Mathlib's
own objects:

* `Matrix.IsHermitian.eigenvalues` / `eigenvectorBasis` (spectral theorem, eigenvalues with
  multiplicity, an orthonormal eigenbasis of `EuclideanSpace ℝ (Fin N)`);
* the induced `2 → 2` operator norm: Mathlib's `Matrix.Norms.L2Operator` norm, i.e. the operator
  norm of `Matrix.toEuclideanCLM B : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)`
  (`Matrix.l2_opNorm_toEuclideanCLM`, definitional);
* `spectrum ℝ (kms N a)` and `Metric.infDist`.

Main results (for `0 < a < 1`, `N ≥ 2`, any real `τ`):

* `eigenvalues_multiset`: Mathlib's eigenvalue multiset of `B_N` is exactly
  `{μ_a(θ_k) - τ : k = 1, …, N}`, each with multiplicity one;
* `inertia_pos/zero/neg`: `n₊, n₀, n₋` counted **with multiplicity** from
  `IsHermitian.eigenvalues` equal `posCount, zeroCount, negCount`;
* `kms_eigenspace_finrank_one`: every eigenvalue of `T_N(a)` is simple (eigenspace dimension 1);
* `sigmaMax_eq_opNorm`: `σ_max = ‖B_N‖₂`;
* `sigmaMin_eq_iInf_sphere`: `σ_min = inf_{‖x‖₂ = 1} ‖B_N x‖₂`;
* `sigmaMin_eq_inv_opNorm_inv`: at a nonsingular dimension `σ_min = ‖B_N⁻¹‖₂⁻¹`;
* **`kappa_eq_operator_twoNorm_conditionNumber`**: `κ₂ = ‖B_N‖₂ · ‖B_N⁻¹‖₂`;
* `spectrum_kms`, `sigmaMin_eq_infDist`: `σ_min(B_N) = dist(τ, spec T_N(a))`.
-/

open Real Set Matrix Finset
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

namespace ShiftedKMS

variable {a τ : ℝ} {N : ℕ}

/-! ### Symmetry and the eigenvalue list -/

lemma shifted_isHermitian (N : ℕ) (a τ : ℝ) : (shifted N a τ).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, star_trivial, shifted_apply, Nat.dist_comm, eq_comm]

/-- The eigenvalue list of `B_N`, indexed by `Fin N`: `k ↦ μ_a(θ_{k+1}) - τ`. -/
noncomputable def lamF (N : ℕ) (a τ : ℝ) (k : Fin N) : ℝ := lam N a τ (k.val + 1)

lemma lamF_injective (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) (τ : ℝ) :
    Function.Injective (lamF N a τ) := by
  intro k l h
  apply eigValK_injective ha0 ha1 N
  simp only [lamF, lam] at h
  simp only [eigValK]
  linarith

lemma shifted_mulVec_eigVecK (ha0 : 0 < a) (ha1 : a < 1) (hN : 2 ≤ N) (τ : ℝ) (k : Fin N) :
    shifted N a τ *ᵥ eigVecK N a k = lamF N a τ k • eigVecK N a k := by
  simp only [eigVecK, lamF, lam]
  exact shifted_eigenpair ha0 ha1 hN (by omega) (by omega) τ

lemma eigVecK_ne_zero (ha0 : 0 < a) (ha1 : a < 1) (hN : 2 ≤ N) (k : Fin N) : eigVecK N a k ≠ 0 :=
  (kms_eigenpair ha0 ha1 hN (k := k.val + 1) (by omega) (by omega)).2

/-- Any eigenvalue of `B_N` (real eigenvector) is some `lamF k`. -/
lemma eigen_shifted_mem (ha0 : 0 < a) (ha1 : a < 1) (hN : 2 ≤ N) {l : ℝ} {x : Fin N → ℝ}
    (hx0 : x ≠ 0) (hx : shifted N a τ *ᵥ x = l • x) : ∃ k : Fin N, l = lamF N a τ k := by
  have hT : kms N a *ᵥ x = (l + τ) • x := by
    rw [shifted, Matrix.sub_mulVec, sub_eq_iff_eq_add] at hx
    rw [hx]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
    ring
  obtain ⟨k, hk1, hkN, hk⟩ := kms_spectrum ha0 ha1 hN hx0 hT
  refine ⟨⟨k - 1, by omega⟩, ?_⟩
  simp only [lamF, lam, show k - 1 + 1 = k by omega]
  linarith

/-! ### Mathlib's spectral data for `B_N` -/

section Spectral

variable (ha0 : 0 < a) (ha1 : a < 1) (hN : 2 ≤ N) (τ : ℝ)


include ha0 ha1 hN

lemma T_bas (i : Fin N) : (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) ((shifted_isHermitian N a τ).eigenvectorBasis i) = (shifted_isHermitian N a τ).eigenvalues i • (shifted_isHermitian N a τ).eigenvectorBasis i := by
  apply WithLp.ofLp_injective
  rw [ofLp_toEuclideanCLM, WithLp.ofLp_smul]
  exact (shifted_isHermitian N a τ).mulVec_eigenvectorBasis i

omit ha0 ha1 hN in
lemma T_symm (x y : EuclideanSpace ℝ (Fin N)) : ⟪(Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) x, y⟫ = ⟪x, (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) y⟫ :=
  (isSymmetric_toEuclideanLin_iff.mpr (shifted_isHermitian N a τ)) x y

lemma inner_bas_T (i : Fin N) (x : EuclideanSpace ℝ (Fin N)) : ⟪(shifted_isHermitian N a τ).eigenvectorBasis i, (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) x⟫ = (shifted_isHermitian N a τ).eigenvalues i * ⟪(shifted_isHermitian N a τ).eigenvectorBasis i, x⟫ := by
  rw [← T_symm, T_bas ha0 ha1 hN, real_inner_smul_left]

omit ha0 ha1 hN in
lemma norm_sq_eq_sum (x : EuclideanSpace ℝ (Fin N)) : ‖x‖ ^ 2 = ∑ i, ⟪(shifted_isHermitian N a τ).eigenvectorBasis i, x⟫ ^ 2 := by
  rw [← ((shifted_isHermitian N a τ).eigenvectorBasis).repr.norm_map x, EuclideanSpace.real_norm_sq_eq]
  simp only [OrthonormalBasis.repr_apply_apply]

lemma norm_T_sq_eq_sum (x : EuclideanSpace ℝ (Fin N)) :
    ‖(Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) x‖ ^ 2 = ∑ i, ((shifted_isHermitian N a τ).eigenvalues i) ^ 2 * ⟪(shifted_isHermitian N a τ).eigenvectorBasis i, x⟫ ^ 2 := by
  rw [norm_sq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_bas_T ha0 ha1 hN]; ring

/-- Every `lamF k` is one of Mathlib's eigenvalues. -/
lemma lamF_mem_range (k : Fin N) : ∃ i, (shifted_isHermitian N a τ).eigenvalues i = lamF N a τ k := by
  set v : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (eigVecK N a k)
  have hv0 : v ≠ 0 := by
    intro h
    apply eigVecK_ne_zero ha0 ha1 hN k
    have := congrArg WithLp.ofLp h
    simpa only [v, WithLp.ofLp_toLp, WithLp.ofLp_zero] using this
  have hTv : (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) v = lamF N a τ k • v := by
    apply WithLp.ofLp_injective
    rw [ofLp_toEuclideanCLM, WithLp.ofLp_smul]
    simp only [v, WithLp.ofLp_toLp]
    exact shifted_mulVec_eigVecK ha0 ha1 hN τ k
  by_contra hne
  push Not at hne
  apply hv0
  have hcoef : ∀ i, ⟪(shifted_isHermitian N a τ).eigenvectorBasis i, v⟫ = 0 := by
    intro i
    have h1 := inner_bas_T ha0 ha1 hN τ i v
    rw [hTv, real_inner_smul_right] at h1
    have h2 : (lamF N a τ k - (shifted_isHermitian N a τ).eigenvalues i) * ⟪(shifted_isHermitian N a τ).eigenvectorBasis i, v⟫ = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (sub_eq_zero.1 h).symm (hne i)
    · exact h
  have := norm_sq_eq_sum (N := N) (a := a) (τ := τ) v
  simp only [hcoef, zero_pow two_ne_zero, Finset.sum_const_zero] at this
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

/-- Every Mathlib eigenvalue is some `lamF k`. -/
lemma ev_mem_range (i : Fin N) : ∃ k, (shifted_isHermitian N a τ).eigenvalues i = lamF N a τ k := by
  have hb := T_bas ha0 ha1 hN τ i
  have hne : (WithLp.ofLp ((shifted_isHermitian N a τ).eigenvectorBasis i) : Fin N → ℝ) ≠ 0 := by
    intro h
    have : (shifted_isHermitian N a τ).eigenvectorBasis i = 0 := by simpa only [WithLp.ofLp_eq_zero] using h
    exact ((shifted_isHermitian N a τ).eigenvectorBasis).orthonormal.ne_zero i this
  exact eigen_shifted_mem ha0 ha1 hN hne ((shifted_isHermitian N a τ).mulVec_eigenvectorBasis i)

/-- **Mathlib's eigenvalue multiset of `B_N` is exactly `{μ_a(θ_k) - τ}`, each simple.** -/
theorem eigenvalues_multiset :
    Multiset.map (shifted_isHermitian N a τ).eigenvalues Finset.univ.val = Multiset.map (lamF N a τ) Finset.univ.val := by
  have hnd : (Multiset.map (lamF N a τ) Finset.univ.val).Nodup :=
    Multiset.Nodup.map (lamF_injective ha0 ha1 N τ) Finset.univ.nodup
  symm
  apply Multiset.eq_of_le_of_card_le
  · rw [Multiset.le_iff_subset hnd]
    intro x hx
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨i, hi⟩ := lamF_mem_range ha0 ha1 hN τ k
    exact Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, hi⟩
  · simp only [Multiset.card_map, Finset.card_val, Finset.card_univ]
    exact le_rfl

lemma card_eigenvalues_filter (P : ℝ → Prop) [DecidablePred P] :
    Fintype.card {i // P ((shifted_isHermitian N a τ).eigenvalues i)} = (Finset.univ.filter fun k => P (lamF N a τ k)).card := by
  rw [Fintype.card_subtype]
  have h := congrArg (fun s => (Multiset.filter P s).card) (eigenvalues_multiset ha0 ha1 hN τ)
  simp only [Multiset.filter_map, Multiset.card_map] at h
  exact h

end Spectral

/-! ### Inertia with multiplicity -/

lemma card_filter_lamF (P : ℝ → Prop) [DecidablePred P] :
    (Finset.univ.filter fun k : Fin N => P (lamF N a τ k)).card =
      ((Finset.Icc 1 N).filter fun k => P (lam N a τ k)).card := by
  refine Finset.card_bij (fun k _ => k.val + 1) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hk⟩
  · intro k _ l _ h
    exact Fin.ext (by simpa using h)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    refine ⟨⟨m - 1, by omega⟩, ?_, by simp only; omega⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [lamF]
    rw [show m - 1 + 1 = m by omega]
    exact hm.2

/-- **`prop:inertia`, matrix form**: `n₊(B_N)` counted with multiplicity (Mathlib's
`IsHermitian.eigenvalues`) is `posCount`. -/
theorem inertia_pos (ha0 : 0 < a) (ha1 : a < 1) (hN : 2 ≤ N) (τ : ℝ) :
    Fintype.card {i // 0 < (shifted_isHermitian N a τ).eigenvalues i} = posCount N a τ := by
  rw [card_eigenvalues_filter ha0 ha1 hN τ (fun x => 0 < x)]
  refine (card_filter_lamF (N := N) (a := a) (τ := τ) (fun x => 0 < x)).trans ?_
  rw [posCount]
  congr 1
  ext k
  simp only [Finset.mem_filter, lam, sub_pos]

theorem inertia_zero (ha0 : 0 < a) (ha1 : a < 1) (hN : 2 ≤ N) (τ : ℝ) :
    Fintype.card {i // (shifted_isHermitian N a τ).eigenvalues i = 0} = zeroCount N a τ := by
  rw [card_eigenvalues_filter ha0 ha1 hN τ (fun x => x = 0)]
  refine (card_filter_lamF (N := N) (a := a) (τ := τ) (fun x => x = 0)).trans ?_
  rw [zeroCount]
  congr 1
  ext k
  simp only [Finset.mem_filter, lam, sub_eq_zero]

theorem inertia_neg (ha0 : 0 < a) (ha1 : a < 1) (hN : 2 ≤ N) (τ : ℝ) :
    Fintype.card {i // (shifted_isHermitian N a τ).eigenvalues i < 0} = negCount N a τ := by
  rw [card_eigenvalues_filter ha0 ha1 hN τ (fun x => x < 0)]
  refine (card_filter_lamF (N := N) (a := a) (τ := τ) (fun x => x < 0)).trans ?_
  rw [negCount]
  congr 1
  ext k
  simp only [Finset.mem_filter, lam, sub_neg]

/-! ### Extreme singular values and the operator 2-norm -/

section Norms

variable (ha0 : 0 < a) (ha1 : a < 1) (hN : 2 ≤ N) (τ : ℝ)


include ha0 ha1 hN

lemma abs_ev_bounds (i : Fin N) : sigmaMin N a τ ≤ |(shifted_isHermitian N a τ).eigenvalues i| ∧ |(shifted_isHermitian N a τ).eigenvalues i| ≤ sigmaMax N a τ := by
  obtain ⟨k, hk⟩ := ev_mem_range ha0 ha1 hN τ i
  rw [hk, lamF]
  exact ⟨sigmaMin_le a τ (by omega) (by omega), le_sigmaMax a τ (by omega) (by omega)⟩

lemma exists_ev_sigmaMax : ∃ i, |(shifted_isHermitian N a τ).eigenvalues i| = sigmaMax N a τ := by
  have hne := Icc_nonempty (N := N) (by omega)
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_mem_eq_sup' hne fun k => |lam N a τ k|
  rw [Finset.mem_Icc] at hk
  obtain ⟨i, hi⟩ := lamF_mem_range ha0 ha1 hN τ ⟨k - 1, by omega⟩
  refine ⟨i, ?_⟩
  rw [hi, sigmaMax, dif_pos hne, hkmax, lamF, show k - 1 + 1 = k by omega]

lemma exists_ev_sigmaMin : ∃ i, |(shifted_isHermitian N a τ).eigenvalues i| = sigmaMin N a τ := by
  have hne := Icc_nonempty (N := N) (by omega)
  obtain ⟨k, hk, hkmin⟩ := Finset.exists_mem_eq_inf' hne fun k => |lam N a τ k|
  rw [Finset.mem_Icc] at hk
  obtain ⟨i, hi⟩ := lamF_mem_range ha0 ha1 hN τ ⟨k - 1, by omega⟩
  refine ⟨i, ?_⟩
  rw [hi, sigmaMin, dif_pos hne, hkmin, lamF, show k - 1 + 1 = k by omega]

lemma norm_T_le (x : EuclideanSpace ℝ (Fin N)) : ‖(Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) x‖ ≤ sigmaMax N a τ * ‖x‖ := by
  have hs : 0 ≤ sigmaMax N a τ := (abs_nonneg _).trans (le_sigmaMax (N := N) a τ le_rfl (by omega))
  rw [← abs_of_nonneg (norm_nonneg ((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) x)), ← abs_of_nonneg (mul_nonneg hs (norm_nonneg x)),
    ← sq_le_sq, mul_pow, norm_T_sq_eq_sum ha0 ha1 hN, norm_sq_eq_sum (N := N) (a := a) (τ := τ) x,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hb := abs_ev_bounds ha0 ha1 hN τ i
  have : ((shifted_isHermitian N a τ).eigenvalues i) ^ 2 ≤ sigmaMax N a τ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb.2 2
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

lemma le_norm_T (x : EuclideanSpace ℝ (Fin N)) : sigmaMin N a τ * ‖x‖ ≤ ‖(Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) x‖ := by
  have hs : 0 ≤ sigmaMin N a τ := sigmaMin_nonneg (by omega) a τ
  rw [← abs_of_nonneg (norm_nonneg ((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) x)), ← abs_of_nonneg (mul_nonneg hs (norm_nonneg x)),
    ← sq_le_sq, mul_pow, norm_T_sq_eq_sum ha0 ha1 hN, norm_sq_eq_sum (N := N) (a := a) (τ := τ) x,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hb := abs_ev_bounds ha0 ha1 hN τ i
  have : sigmaMin N a τ ^ 2 ≤ ((shifted_isHermitian N a τ).eigenvalues i) ^ 2 := by
    rw [← sq_abs ((shifted_isHermitian N a τ).eigenvalues i)]; exact pow_le_pow_left₀ hs hb.1 2
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

lemma norm_T_bas (i : Fin N) : ‖(Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) ((shifted_isHermitian N a τ).eigenvectorBasis i)‖ = |(shifted_isHermitian N a τ).eigenvalues i| := by
  rw [T_bas ha0 ha1 hN, norm_smul, ((shifted_isHermitian N a τ).eigenvectorBasis).orthonormal.1 i, mul_one, Real.norm_eq_abs]

/-- **`σ_max(B_N) = ‖B_N‖₂`** (Mathlib's induced `2 → 2` operator norm). -/
theorem sigmaMax_eq_opNorm : sigmaMax N a τ = ‖shifted N a τ‖ := by
  rw [← l2_opNorm_toEuclideanCLM]
  apply le_antisymm
  · obtain ⟨i, hi⟩ := exists_ev_sigmaMax ha0 ha1 hN τ
    rw [← hi, ← norm_T_bas ha0 ha1 hN]
    calc ‖(Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) ((shifted_isHermitian N a τ).eigenvectorBasis i)‖ ≤ ‖(Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ))‖ * ‖(shifted_isHermitian N a τ).eigenvectorBasis i‖ := ((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ))).le_opNorm _
      _ = ‖(Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ))‖ := by rw [((shifted_isHermitian N a τ).eigenvectorBasis).orthonormal.1 i, mul_one]
  · exact ((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ))).opNorm_le_bound ((abs_nonneg _).trans (le_sigmaMax (N := N) a τ le_rfl (by omega))) (norm_T_le ha0 ha1 hN τ)

/-- **`σ_min(B_N) = inf_{‖x‖₂ = 1} ‖B_N x‖₂`** (the unit sphere is nonempty since `N ≥ 2`). -/
theorem sigmaMin_eq_iInf_sphere :
    sigmaMin N a τ = ⨅ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1, ‖(Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) x‖ := by
  have hsph : ∀ i, (shifted_isHermitian N a τ).eigenvectorBasis i ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 := fun i => by
    rw [mem_sphere_zero_iff_norm]; exact ((shifted_isHermitian N a τ).eigenvectorBasis).orthonormal.1 i
  haveI : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :=
    ⟨⟨(shifted_isHermitian N a τ).eigenvectorBasis ⟨0, by omega⟩, hsph _⟩⟩
  apply le_antisymm
  · apply le_ciInf
    rintro ⟨x, hx⟩
    have := le_norm_T ha0 ha1 hN τ x
    rwa [mem_sphere_zero_iff_norm.1 hx, mul_one] at this
  · obtain ⟨i, hi⟩ := exists_ev_sigmaMin ha0 ha1 hN τ
    refine (ciInf_le ⟨0, ?_⟩ ⟨(shifted_isHermitian N a τ).eigenvectorBasis i, hsph i⟩).trans ?_
    · rintro _ ⟨y, rfl⟩; exact norm_nonneg _
    · rw [norm_T_bas ha0 ha1 hN, hi]

/-- `σ_min > 0 ↔ B_N` invertible (as a matrix). -/
theorem sigmaMin_pos_iff_isUnit : 0 < sigmaMin N a τ ↔ IsUnit (shifted N a τ) := by
  rw [← nonsingular_iff_sigmaMin_pos ha0 ha1 hN, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rfl

/-- **`σ_min(B_N) = ‖B_N⁻¹‖₂⁻¹`** at a nonsingular dimension. -/
theorem sigmaMin_eq_inv_opNorm_inv (hns : Nonsingular N a τ) :
    sigmaMin N a τ = ‖(shifted N a τ)⁻¹‖⁻¹ := by
  have hpos : 0 < sigmaMin N a τ := (nonsingular_iff_sigmaMin_pos ha0 ha1 hN τ).1 hns
  have hdet : IsUnit (shifted N a τ).det := isUnit_iff_ne_zero.2 hns
  set S := Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)⁻¹
  have hTS : ∀ y, (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) (S y) = y := by
    intro y
    apply WithLp.ofLp_injective
    rw [ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hnormS : ‖S‖ = (sigmaMin N a τ)⁻¹ := by
    apply le_antisymm
    · refine S.opNorm_le_bound (by positivity) fun y => ?_
      have := le_norm_T ha0 ha1 hN τ (S y)
      rw [hTS] at this
      rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
      exact this
    · obtain ⟨i, hi⟩ := exists_ev_sigmaMin ha0 ha1 hN τ
      have hev0 : (shifted_isHermitian N a τ).eigenvalues i ≠ 0 := by
        intro h0; rw [h0, abs_zero] at hi; linarith
      have hSb : S ((shifted_isHermitian N a τ).eigenvectorBasis i) = ((shifted_isHermitian N a τ).eigenvalues i)⁻¹ • (shifted_isHermitian N a τ).eigenvectorBasis i := by
        have h1 := hTS ((shifted_isHermitian N a τ).eigenvectorBasis i)
        have h2 : (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) (((shifted_isHermitian N a τ).eigenvalues i)⁻¹ • (shifted_isHermitian N a τ).eigenvectorBasis i) = (shifted_isHermitian N a τ).eigenvectorBasis i := by
          rw [map_smul, T_bas ha0 ha1 hN, smul_smul, inv_mul_cancel₀ hev0, one_smul]
        -- `T` is injective (it has the left inverse coming from `S`)
        have hinj : Function.Injective (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) := by
          intro u w huw
          have hST : ∀ z, S ((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (shifted N a τ)) z) = z := by
            intro z
            apply WithLp.ofLp_injective
            rw [ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, Matrix.mulVec_mulVec,
              Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
          rw [← hST u, ← hST w, huw]
        exact hinj (h1.trans h2.symm)
      calc (sigmaMin N a τ)⁻¹ = ‖S ((shifted_isHermitian N a τ).eigenvectorBasis i)‖ := by
            rw [hSb, norm_smul, ((shifted_isHermitian N a τ).eigenvectorBasis).orthonormal.1 i, mul_one, norm_inv, Real.norm_eq_abs, hi]
        _ ≤ ‖S‖ * ‖(shifted_isHermitian N a τ).eigenvectorBasis i‖ := S.le_opNorm _
        _ = ‖S‖ := by rw [((shifted_isHermitian N a τ).eigenvectorBasis).orthonormal.1 i, mul_one]
  rw [← l2_opNorm_toEuclideanCLM, hnormS, inv_inv]

/-- **The condition-number bridge**: at a nonsingular dimension, the eigenvalue-ratio `kappa`
is the standard spectral condition number `‖B_N‖₂ · ‖B_N⁻¹‖₂` (Mathlib's induced `2 → 2`
operator norm). -/
theorem kappa_eq_operator_twoNorm_conditionNumber (hns : Nonsingular N a τ) :
    kappa N a τ = ‖shifted N a τ‖ * ‖(shifted N a τ)⁻¹‖ := by
  rw [kappa, sigmaMax_eq_opNorm ha0 ha1 hN τ, sigmaMin_eq_inv_opNorm_inv ha0 ha1 hN τ hns,
    div_inv_eq_mul]

end Norms

/-! ### Spectrum of `T_N(a)`, simplicity, and spectral distance -/

lemma mem_spectrum_iff_exists_eigvec {M : Matrix (Fin N) (Fin N) ℝ} {μ : ℝ} :
    μ ∈ spectrum ℝ M ↔ ∃ x : Fin N → ℝ, x ≠ 0 ∧ M *ᵥ x = μ • x := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨x, hx0, hx⟩
    refine ⟨x, hx0, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero] at hx
    exact hx.symm
  · rintro ⟨x, hx0, hx⟩
    refine ⟨x, hx0, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hx, sub_self]

/-- `spec T_N(a) = {μ_a(θ_k) : k = 1, …, N}` (Mathlib's `spectrum` of the matrix). -/
theorem spectrum_kms (ha0 : 0 < a) (ha1 : a < 1) (hN : 2 ≤ N) :
    spectrum ℝ (kms N a) = {μ | ∃ k, 1 ≤ k ∧ k ≤ N ∧ μ = symbol a (eigAngle N a k)} := by
  ext μ
  rw [mem_spectrum_iff_exists_eigvec, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx0, hx⟩
    exact kms_spectrum ha0 ha1 hN hx0 hx
  · rintro ⟨k, hk1, hkN, rfl⟩
    exact ⟨_, (kms_eigenpair ha0 ha1 hN hk1 hkN).2, (kms_eigenpair ha0 ha1 hN hk1 hkN).1⟩

/-- **Scope-section identity**: `σ_min(B_N) = dist(τ, spec T_N(a))` (ordinary absolute distance on
`ℝ`, `Metric.infDist`, over the finite set `spectrum ℝ (kms N a)`). -/
theorem sigmaMin_eq_infDist (ha0 : 0 < a) (ha1 : a < 1) (hN : 2 ≤ N) (τ : ℝ) :
    sigmaMin N a τ = Metric.infDist τ (spectrum ℝ (kms N a)) := by
  rw [spectrum_kms ha0 ha1 hN]
  have hne : ({μ | ∃ k, 1 ≤ k ∧ k ≤ N ∧ μ = symbol a (eigAngle N a k)} : Set ℝ).Nonempty :=
    ⟨symbol a (eigAngle N a 1), ⟨1, le_rfl, by omega, rfl⟩⟩
  apply le_antisymm
  · rw [Metric.le_infDist hne]
    rintro _ ⟨k, hk1, hkN, rfl⟩
    rw [Real.dist_eq, abs_sub_comm]
    exact sigmaMin_le a τ hk1 hkN
  · have hne' := Icc_nonempty (N := N) (by omega)
    obtain ⟨k, hk, hkmin⟩ := Finset.exists_mem_eq_inf' hne' fun k => |lam N a τ k|
    rw [Finset.mem_Icc] at hk
    refine (Metric.infDist_le_dist_of_mem (y := symbol a (eigAngle N a k))
      (show symbol a (eigAngle N a k) ∈ {μ | ∃ k, 1 ≤ k ∧ k ≤ N ∧ μ = symbol a (eigAngle N a k)} from
        ⟨k, hk.1, hk.2, rfl⟩)).trans (le_of_eq ?_)
    rw [Real.dist_eq, abs_sub_comm]
    simp only [sigmaMin, hne', ↓reduceDIte]
    rw [hkmin, lam]

/-- **`thm:quant`, simplicity**: every eigenvalue `μ_a(θ_k)` of `T_N(a)` has a one-dimensional
eigenspace. -/
theorem kms_eigenspace_finrank_one (ha0 : 0 < a) (ha1 : a < 1) (hN : 2 ≤ N) {k : ℕ}
    (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' (kms N a))
      (symbol a (eigAngle N a k))) = 1 := by
  set μ := symbol a (eigAngle N a k)
  have hθ := (eigAngle_spec ha0 ha1 hk1 hkN).1
  have hint : InteriorParam a μ := ⟨ha0, ha1, (symbol_strict_bounds ha0 ha1 hθ).1,
    (symbol_strict_bounds ha0 ha1 hθ).2⟩
  have hsing : (shifted N a μ).det = 0 :=
    (det_eq_zero_iff_lam ha0 ha1 hN μ).2 ⟨k, hk1, hkN, by simp only [lam, μ, sub_self]⟩
  have heq : Module.End.eigenspace (Matrix.toLin' (kms N a)) μ =
      LinearMap.ker (Matrix.toLin' (shifted N a μ)) := by
    ext x
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, Matrix.toLin'_apply,
      Matrix.toLin'_apply, shifted, Matrix.sub_mulVec, sub_eq_zero]
    constructor <;> intro h
    · rw [h]; funext i; simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
    · rw [h]; funext i; simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
  rw [heq]
  exact shifted_nullity_one hint hN hsing

end ShiftedKMS
