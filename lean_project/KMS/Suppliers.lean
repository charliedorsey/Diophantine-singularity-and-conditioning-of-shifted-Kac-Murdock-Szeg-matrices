import KMS.Laws
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd

/-!
# Gate 5 — the arithmetic suppliers (Weyl, Cassels), stated exactly

The manuscript imports two classical theorems in `sec:dioph`. This file fixes their **exact**
formal statements, with the conventions of the paper:

* distances are nearest-integer distances `‖x‖ = |x - round x|` (`distZ`, = the norm of
  `AddCircle 1`);
* time is **positive**: `N ∈ ℕ`, `N → ∞` (no `|N|`, no two-sided orbit);
* `α` is a fixed irrational, the target `β` varies.

`WeylSupplier`: for irrational `α` and **every** `β`, `{Nα - β}` is equidistributed mod 1, in the
form used by `thm:irr-laws` (window `N = 2, …, L+1`).

`CasselsSupplier`: for irrational `α` and every `c > 0`, for Lebesgue-a.e. `β`,
`‖Nα - β‖ < c/N` (i.e. `N‖Nα - β‖ < c`) for infinitely many positive `N` (eq. `(cassels)`).

Status (Mathlib v4.34.0): **neither statement is in Mathlib.**
* `WeylSupplier` is **proved in this file** (`weyl_equidistribution`) from Mathlib's density of
  trigonometric polynomials in `C(AddCircle, ℂ)` (`span_fourier_closure_eq_top`), Fourier
  orthonormality (`fourierCoeff_fourier`) and the geometric-sum bound.
* `CasselsSupplier` is stated here only. The Mathlib inputs for its proof are ergodicity of an
  irrational rotation (`AddCircle.ergodic_add_left`, re-exported as
  `ergodic_irrational_rotation`), Dirichlet/Legendre-type approximation
  (`Real.exists_rat_abs_sub_lt_and_lt_of_irrational`) and `AddCircle.volume_closedBall`.
-/

open Real Set Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace ShiftedKMS

/-- Weyl equidistribution of the affine orbit `Nα - β` (positive times, window `2, …, L+1`),
tested against every continuous function on `ℝ/ℤ`. -/
def WeylSupplier : Prop :=
  ∀ α : ℝ, Irrational α → ∀ β : ℝ, ∀ f : C(AddCircle (1 : ℝ), ℂ),
    Tendsto (fun L : ℕ => (L : ℂ)⁻¹ * ∑ N ∈ window L, f ((N * α - β : ℝ) : AddCircle (1 : ℝ)))
      atTop (𝓝 (∫ x, f x))

/-- Cassels' metric inhomogeneous theorem, positive-time, nearest-integer, fixed irrational `α`,
almost every target `β` (eq. `(cassels)`). -/
def CasselsSupplier : Prop :=
  ∀ α : ℝ, Irrational α → ∀ c : ℝ, 0 < c →
    ∀ᵐ β : ℝ, ∃ᶠ N : ℕ in atTop, (N : ℝ) * distZ (N * α - β) < c

/-- The nearest-integer distance is the norm of `ℝ/ℤ`. -/
lemma norm_addCircle_one (x : ℝ) : ‖(x : AddCircle (1 : ℝ))‖ = distZ x := by
  rw [AddCircle.norm_eq, distZ]
  simp only [inv_one, one_mul, mul_one]

/-- An irrational rotation of `ℝ/ℤ` has infinite order. -/
lemma addOrderOf_irrational {α : ℝ} (hα : Irrational α) :
    addOrderOf (α : AddCircle (1 : ℝ)) = 0 := by
  rw [addOrderOf_eq_zero_iff']
  intro n hn h
  rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  apply hα.ne_rat (k / n : ℚ)
  push_cast
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hk
  field_simp
  linarith

/-- Mathlib supplier: ergodicity of the irrational rotation `x ↦ α + x` on `ℝ/ℤ`. -/
theorem ergodic_irrational_rotation {α : ℝ} (hα : Irrational α) :
    Ergodic (fun x : AddCircle (1 : ℝ) => (α : AddCircle (1 : ℝ)) + x) :=
  AddCircle.ergodic_add_left.2 (addOrderOf_irrational hα)

/-! ### Weyl equidistribution (proved here; not in Mathlib) -/

section Weyl

variable {α β : ℝ}

lemma integrable_of_continuousMap (f : C(UnitAddCircle, ℂ)) : Integrable f (volume : Measure UnitAddCircle) :=
  f.continuous.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

/-- The Weyl average along the orbit. -/
noncomputable def weylAvg (α β : ℝ) (f : UnitAddCircle → ℂ) (L : ℕ) : ℂ :=
  (L : ℂ)⁻¹ * ∑ N ∈ window L, f ((N * α - β : ℝ) : UnitAddCircle)

lemma norm_weylAvg_le (f : C(UnitAddCircle, ℂ)) (L : ℕ) : ‖weylAvg α β f L‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp only [weylAvg, CharP.cast_eq_zero, inv_zero, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_nat_mul, zero_mul, norm_zero, norm_nonneg]
  unfold weylAvg
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  rw [inv_mul_le_iff₀ hLr]
  calc ‖∑ N ∈ window L, f ((N * α - β : ℝ) : UnitAddCircle)‖
      ≤ ∑ N ∈ window L, ‖f ((N * α - β : ℝ) : UnitAddCircle)‖ := norm_sum_le _ _
    _ ≤ ∑ _N ∈ window L, ‖f‖ := Finset.sum_le_sum fun N _ => f.norm_coe_le_norm _
    _ = L * ‖f‖ := by rw [Finset.sum_const, card_window, nsmul_eq_mul]

lemma norm_integral_le (f : C(UnitAddCircle, ℂ)) : ‖∫ x, f x‖ ≤ ‖f‖ := by
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure UnitAddCircle))
    (Eventually.of_forall fun x => f.norm_coe_le_norm x)
  rwa [measureReal_def, UnitAddCircle.measure_univ, ENNReal.toReal_one, mul_one] at this

lemma weylAvg_sub (f g : C(UnitAddCircle, ℂ)) (L : ℕ) :
    weylAvg α β f L - weylAvg α β g L = weylAvg α β ⇑(f - g) L := by
  simp only [weylAvg, ContinuousMap.coe_sub, Pi.sub_apply, Finset.sum_sub_distrib, mul_sub]

/-- The test functions with the Weyl property. -/
def weylSet (α β : ℝ) : Set C(UnitAddCircle, ℂ) :=
  {f | Tendsto (weylAvg α β f) atTop (𝓝 (∫ x, f x))}

lemma weylSet_isClosed : IsClosed (weylSet α β) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  rw [Metric.mem_closure_iff] at hf
  show Tendsto (weylAvg α β f) atTop (𝓝 (∫ x, f x))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := hf (ε / 3) (by positivity)
  obtain ⟨L0, hL0⟩ := Metric.tendsto_atTop.1 hg (ε / 3) (by positivity)
  refine ⟨L0, fun L hL => ?_⟩
  have h1 : ‖weylAvg α β f L - weylAvg α β g L‖ ≤ ‖f - g‖ := by
    rw [weylAvg_sub]; exact norm_weylAvg_le _ _
  have h2 : ‖(∫ x, g x) - ∫ x, f x‖ ≤ ‖f - g‖ := by
    rw [← integral_sub (integrable_of_continuousMap g) (integrable_of_continuousMap f),
      ← norm_neg, ← integral_neg]
    have := norm_integral_le (f - g)
    simpa only [ContinuousMap.coe_sub, Pi.sub_apply, neg_sub] using this
  have h3 := hL0 L hL
  rw [dist_eq_norm] at h3 ⊢
  rw [dist_eq_norm] at hfg
  calc ‖weylAvg α β f L - ∫ x, f x‖
      = ‖(weylAvg α β f L - weylAvg α β g L) + (weylAvg α β g L - ∫ x, g x) +
          ((∫ x, g x) - ∫ x, f x)‖ := by ring_nf
    _ ≤ ‖weylAvg α β f L - weylAvg α β g L‖ + ‖weylAvg α β g L - ∫ x, g x‖ +
          ‖(∫ x, g x) - ∫ x, f x‖ := norm_add₃_le
    _ < ε := by linarith

lemma weylSet_add {f g : C(UnitAddCircle, ℂ)} (hf : f ∈ weylSet α β) (hg : g ∈ weylSet α β) :
    f + g ∈ weylSet α β := by
  show Tendsto _ _ _
  simp only [ContinuousMap.coe_add, Pi.add_apply]
  rw [integral_add (integrable_of_continuousMap f) (integrable_of_continuousMap g)]
  refine (hf.add hg).congr fun L => ?_
  simp only [weylAvg, Pi.add_apply, Finset.sum_add_distrib, mul_add]

lemma weylSet_smul (c : ℂ) {f : C(UnitAddCircle, ℂ)} (hf : f ∈ weylSet α β) :
    c • f ∈ weylSet α β := by
  show Tendsto _ _ _
  simp only [ContinuousMap.coe_smul, Pi.smul_apply]
  rw [integral_smul]
  refine (hf.const_smul c).congr fun L => ?_
  simp only [weylAvg, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- `weylSet` as a submodule. -/
def weylSubmodule (α β : ℝ) : Submodule ℂ C(UnitAddCircle, ℂ) where
  carrier := weylSet α β
  add_mem' := weylSet_add
  zero_mem' := by
    show Tendsto _ _ _
    simp only [ContinuousMap.coe_zero, Pi.zero_apply, integral_zero]
    exact tendsto_const_nhds.congr fun L => by simp only [weylAvg, Pi.zero_apply, sum_const_zero, mul_zero]
  smul_mem' := weylSet_smul

lemma integral_fourier_unit (n : ℤ) :
    ∫ x, (fourier n : C(UnitAddCircle, ℂ)) x = if n = 0 then 1 else 0 := by
  have h := congr_fun (fourierCoeff_fourier (T := 1) n) 0
  rw [fourierCoeff] at h
  simp only [neg_zero, fourier_zero, one_smul] at h
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul, h]
  by_cases hn : n = 0
  · subst hn; simp only [Pi.single_eq_same, ↓reduceIte]
  · simp only [ne_eq, Ne.symm hn, not_false_eq_true, Pi.single_eq_of_ne, hn, ↓reduceIte]

lemma fourier_mem_weylSet (hα : Irrational α) (n : ℤ) : fourier n ∈ weylSet α β := by
  show Tendsto _ _ _
  rw [integral_fourier_unit]
  by_cases hn : n = 0
  · subst hn
    simp only [ite_true]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with L hL
    simp only [weylAvg, fourier_zero, Finset.sum_const, card_window, nsmul_eq_mul, mul_one]
    have : (L : ℂ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
    field_simp
  · simp only [hn, ite_false]
    set z : ℂ := Complex.exp (2 * π * Complex.I * n * α) with hz
    set w : ℂ := Complex.exp (-(2 * π * Complex.I * n * β)) with hw
    have hz1 : z ≠ 1 := by
      intro h1
      rw [hz, Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      apply hα.ne_rat (k / n : ℚ)
      have hπ : (2 * π * Complex.I : ℂ) ≠ 0 := by
        simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero, pi_ne_zero, or_self, Complex.I_ne_zero, not_false_eq_true]
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have : (n : ℂ) * α = k := by
        have := hk
        apply mul_left_cancel₀ hπ
        linear_combination this
      have hr : (α : ℂ) = (k / n : ℚ) := by push_cast; field_simp; linear_combination this
      exact_mod_cast hr
    have hznorm : ‖z‖ = 1 := by
      rw [hz, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.I_re, Complex.mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, Complex.intCast_re, Complex.intCast_im, zero_add, exp_zero]
    have hwnorm : ‖w‖ = 1 := by
      rw [hw, Complex.norm_exp]
      simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.I_re, Complex.mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, Complex.intCast_re, Complex.intCast_im, zero_add, neg_zero, exp_zero]
    have hterm : ∀ N : ℕ, (fourier n : C(UnitAddCircle, ℂ)) ((N * α - β : ℝ) : UnitAddCircle) =
        w * z ^ N := by
      intro N
      rw [fourier_coe_apply, hz, hw, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hsum : ∀ L : ℕ, ‖∑ N ∈ window L, w * z ^ N‖ ≤ 2 / ‖z - 1‖ := by
      intro L
      have hwin : ∑ N ∈ window L, w * z ^ N = w * z ^ 2 * ∑ i ∈ range L, z ^ i := by
        have hw' : window L = Finset.Ico 2 (L + 2) := by
          ext m; simp only [window, Finset.mem_Icc, Finset.mem_Ico]; omega
        rw [hw', Finset.sum_Ico_eq_sum_range, Finset.mul_sum, show L + 2 - 2 = L by omega]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_add]
        ring
      rw [hwin, geom_sum_eq hz1, norm_mul, norm_mul, norm_pow, hwnorm, hznorm, norm_div]
      have hz1' : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
      rw [one_pow, one_mul, one_mul, div_le_div_iff_of_pos_right hz1']
      calc ‖z ^ L - 1‖ ≤ ‖z ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hznorm, one_pow, norm_one]; norm_num
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun L => ?_)
      (by simpa only [zero_mul] using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2 / ‖z - 1‖))
    simp only [weylAvg, hterm]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hsum L) (by positivity)

/-- **Weyl's equidistribution theorem** for the affine orbit `Nα - β`, every `β`, positive
times `N = 2, …, L+1`: proved from Mathlib's density of trigonometric polynomials. -/
theorem weyl_equidistribution : WeylSupplier := by
  intro α hα β f
  have hspan : Submodule.span ℂ (range (@fourier 1)) ≤ weylSubmodule α β := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    exact fourier_mem_weylSet hα n
  have hcl : (Submodule.span ℂ (range (@fourier 1))).topologicalClosure ≤ weylSubmodule α β :=
    Submodule.topologicalClosure_minimal _ hspan weylSet_isClosed
  rw [span_fourier_closure_eq_top] at hcl
  exact hcl (Submodule.mem_top (x := f))

/-- Real-valued form of Weyl's theorem. -/
theorem weyl_real {α : ℝ} (hα : Irrational α) (β : ℝ) (f : C(UnitAddCircle, ℝ)) :
    Tendsto (fun L : ℕ => (L : ℝ)⁻¹ * ∑ N ∈ window L, f ((N * α - β : ℝ) : UnitAddCircle))
      atTop (𝓝 (∫ x, f x)) := by
  let fC : C(UnitAddCircle, ℂ) := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have h := weyl_equidistribution α hα β fC
  have h2 := (Complex.continuous_re.tendsto _).comp h
  simp only [fC, ContinuousMap.coe_mk, integral_complex_ofReal, Complex.ofReal_re] at h2
  refine h2.congr fun L => ?_
  simp only [Function.comp_apply]
  rw [show ((L : ℂ))⁻¹ = ((L : ℝ)⁻¹ : ℝ) by push_cast; rfl, ← Complex.ofReal_sum,
    ← Complex.ofReal_mul, Complex.ofReal_re]

end Weyl

end ShiftedKMS
