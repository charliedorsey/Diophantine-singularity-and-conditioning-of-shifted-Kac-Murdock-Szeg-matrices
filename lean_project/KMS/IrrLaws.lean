import KMS.Suppliers
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Gate 5.2 — irrational phase points: bulk laws (`thm:irr-laws`)

* the empirical law of `d_N` (and of `c·d_N`) is uniform on `[0, 1/2]` (resp. `[0, c/2]`), from
  `weyl_real`;
* eq. `(uniformlaw)`: `N σ_min(B_N) ⇒ U[0, πγ/2]`;
* eq. `(paretolaw)`: over the nonsingular indices `𝓘_L^*`, `κ₂(B_N)/N ⇒ Law(C/U)`,
  `U ~ U[0,1/2]`, with `L - 1 ≤ L^* ≤ L`;
* eq. `(paretotail)`: `Pr(C/U > t) = min{1, 2C/t}` for `t > 0`;
* eq. `(cesaro)`: `L⁻¹ ∑_{N ∈ 𝓘_L^*} κ₂(B_N)/N → +∞`.
-/

open Real Set Filter Topology MeasureTheory Finset
open scoped ENNReal BoundedContinuousFunction

namespace ShiftedKMS

/-! ### Uniform laws and the circle integral -/

/-- The uniform probability law `U[u,v]`. -/
noncomputable def unif (u v : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (v - u))⁻¹ • volume.restrict (Icc u v)

lemma isProbabilityMeasure_unif {u v : ℝ} (huv : u < v) : IsProbabilityMeasure (unif u v) := by
  constructor
  rw [unif, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos])
    ENNReal.ofReal_ne_top

lemma integral_unif {u v : ℝ} (huv : u < v) (g : ℝ → ℝ) :
    ∫ x, g x ∂(unif u v) = (v - u)⁻¹ * ∫ x in u..v, g x := by
  rw [unif, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv.le, smul_eq_mul]

/-- `∫_{ℝ/ℤ} g(‖x‖) = 2 ∫_0^{1/2} g`. -/
lemma integral_circle_norm {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ x : UnitAddCircle, g ‖x‖ = 2 * ∫ t in (0 : ℝ)..1 / 2, g t := by
  rw [← UnitAddCircle.intervalIntegral_preimage (-(1 / 2)), show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
  have hcongr : ∫ a in -(1 / 2 : ℝ)..1 / 2, g ‖(a : UnitAddCircle)‖ =
      ∫ a in -(1 / 2 : ℝ)..1 / 2, g |a| := by
    apply intervalIntegral.integral_congr
    intro a ha
    rw [Set.uIcc_of_le (by norm_num)] at ha
    have : |a| ≤ |(1 : ℝ)| / 2 := by
      rw [abs_one]; exact abs_le.2 ⟨by linarith [ha.1], by linarith [ha.2]⟩
    simp only [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (x := a) one_ne_zero).2 this]
  rw [hcongr]
  have hi : ∀ u v : ℝ, IntervalIntegrable (fun a => g |a|) volume u v := fun u v =>
    (hg.comp continuous_abs).intervalIntegrable u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi _ 0) (hi 0 _)]
  have h1 : ∫ a in -(1 / 2 : ℝ)..0, g |a| = ∫ a in (0 : ℝ)..1 / 2, g a := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1 / 2) (fun a => g |a|)
    rw [neg_zero] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [abs_neg, abs_of_nonneg hx.1]
  have h2 : ∫ a in (0 : ℝ)..1 / 2, g |a| = ∫ a in (0 : ℝ)..1 / 2, g a := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [abs_of_nonneg hx.1]
  rw [h1, h2]; ring

section Irr

variable {a τ : ℝ}

lemma dN_nonneg (N : ℕ) : 0 ≤ dN N a τ := distZ_nonneg _
lemma dN_le_half (N : ℕ) : dN N a τ ≤ 1 / 2 := distZ_le_half _

/-- **Weyl ⇒ uniform law of the residual distances**: for irrational `α` and `c > 0`, the
empirical law of `c·d_N` converges weakly to `U[0, c/2]`. -/
theorem dN_law (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) {c : ℝ} (hc : 0 < c) :
    WeakLim (empMeasure (fun N => c * dN N a τ)) (unif 0 (c / 2)) := by
  intro g
  have _ := h
  simp only [integral_empMeasure]
  rw [integral_unif (by positivity)]
  let f : C(UnitAddCircle, ℝ) := ⟨fun x => g (c * ‖x‖), by fun_prop⟩
  have hw := weyl_real hα (betaOf a τ) f
  have hint : ∫ x, f x = (c / 2 - 0)⁻¹ * ∫ x in (0 : ℝ)..c / 2, g x := by
    show ∫ x : UnitAddCircle, (fun t => g (c * t)) ‖x‖ = _
    rw [integral_circle_norm (g := fun t => g (c * t))
      (g.continuous.comp (continuous_const.mul continuous_id)), intervalIntegral.integral_comp_mul_left
      (fun t => g t) hc.ne', mul_zero, smul_eq_mul, sub_zero]
    field_simp
  rw [hint] at hw
  refine hw.congr fun L => ?_
  congr 1
  refine Finset.sum_congr rfl fun N _ => ?_
  show g (c * ‖((N * alphaOf a τ - betaOf a τ : ℝ) : UnitAddCircle)‖) = g (c * dN N a τ)
  rw [norm_addCircle_one, dN]

/-- Transfer of a weak limit along an asymptotically equal bounded sequence. -/
lemma weakLim_of_close {x y : ℕ → ℝ} {ν : Measure ℝ} (hx : WeakLim (empMeasure x) ν) {B : ℝ}
    (hB : ∀ N, |x N| ≤ B) (hxy : Tendsto (fun N => y N - x N) atTop (𝓝 0)) :
    WeakLim (empMeasure y) ν := by
  intro g
  have hgx := hx g
  simp only [integral_empMeasure] at hgx ⊢
  have hD : Tendsto (fun N => g (y N) - g (x N)) atTop (𝓝 0) := by
    have huc := isCompact_Icc.uniformContinuousOn_of_continuous
      (s := Icc (-B - 1) (B + 1)) g.continuous.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := huc ε hε
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 hxy (min δ 1) (by positivity)
    refine ⟨N0, fun N hN => ?_⟩
    have h1 := hN0 N hN
    rw [Real.dist_eq, sub_zero] at h1 ⊢
    have hxB := abs_le.1 (hB N)
    have hd := abs_lt.1 (lt_of_lt_of_le h1 (min_le_right _ _))
    have hxm : x N ∈ Icc (-B - 1) (B + 1) := ⟨by linarith, by linarith⟩
    have hym : y N ∈ Icc (-B - 1) (B + 1) := ⟨by linarith, by linarith⟩
    have := hδε (y N) hym (x N) hxm (by rw [Real.dist_eq]; exact lt_of_lt_of_le h1 (min_le_left _ _))
    rwa [Real.dist_eq] at this
  have hc := cesaro_window hD.cesaro
  have := hgx.add hc
  rw [add_zero] at this
  refine this.congr fun L => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun N _ => by ring

/-- **eq. `(uniformlaw)`**: for irrational `α`, `L⁻¹ ∑_{N∈𝓘_L} δ_{N σ_min(B_N)} ⇒ U[0, πγ/2]`. -/
theorem thm_irr_laws_uniform (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    WeakLim (empMeasure (fun N => N * sigmaMin N a τ)) (unif 0 (π * gam a τ / 2)) := by
  have hγ := gam_pos h
  have hτ := h.tau_pos
  have hc : 0 < π * gam a τ := by positivity
  apply weakLim_of_close (dN_law h hα hc) (B := π * gam a τ / 2)
  · intro N
    rw [abs_of_nonneg (by have := dN_nonneg (a := a) (τ := τ) N; positivity)]
    have := dN_le_half (a := a) (τ := τ) N
    nlinarith
  · set K := Ksm a τ
    have hK := Ksm_nonneg h
    have hbound : ∀ N : ℕ, n1 a τ ≤ N → 1 ≤ N →
        |N * sigmaMin N a τ - π * gam a τ * dN N a τ| ≤ π * gam a τ / 2 * (K + τ) / N := by
      intro N hN hN1
      obtain ⟨lo, hi⟩ := thm_smin_relative h hN
      set P := π * gam a τ * dN N a τ with hP
      have hP0 : 0 ≤ P := by have := dN_nonneg (a := a) (τ := τ) N; positivity
      have hPh : P ≤ π * gam a τ / 2 := by
        have := dN_le_half (a := a) (τ := τ) N; rw [hP]; nlinarith
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
      set A := P / (N + τ) with hA
      have hA0 : 0 ≤ A := by positivity
      have hAN : A ≤ P / N := div_le_div_of_nonneg_left hP0 hNr (by linarith)
      have e1 : |sigmaMin N a τ - A| ≤ K / N * A := by
        rw [abs_le]; constructor <;> nlinarith
      have e2 : |N * A - P| ≤ P * τ / N := by
        have : N * A - P = -(P * τ / (N + τ)) := by rw [hA]; field_simp; ring
        rw [this, abs_neg, abs_of_nonneg (by positivity)]
        exact div_le_div_of_nonneg_left (by positivity) hNr (by linarith)
      calc |N * sigmaMin N a τ - P|
          = |N * (sigmaMin N a τ - A) + (N * A - P)| := by ring_nf
        _ ≤ |N * (sigmaMin N a τ - A)| + |N * A - P| := abs_add_le _ _
        _ ≤ N * (K / N * A) + P * τ / N := by
            rw [abs_mul, abs_of_pos hNr]
            exact add_le_add (mul_le_mul_of_nonneg_left e1 hNr.le) e2
        _ = K * A + P * τ / N := by field_simp
        _ ≤ K * (P / N) + P * τ / N := by gcongr
        _ = P * (K + τ) / N := by ring
        _ ≤ π * gam a τ / 2 * (K + τ) / N := by gcongr
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa only [mul_zero] using
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (π * gam a τ / 2 * (K + τ)))
    filter_upwards [eventually_ge_atTop (n1 a τ + 1)] with N hN
    rw [Real.norm_eq_abs]
    refine (hbound N (by omega) (by omega)).trans (le_of_eq ?_)
    ring

/-! ### The Pareto law -/

/-- `Law(C/U)`, `U ~ U[0,1/2]`. -/
noncomputable def paretoLaw (C : ℝ) : Measure ℝ := (unif 0 (1 / 2)).map (fun u => C / u)

lemma integral_paretoLaw (C : ℝ) (g : ℝ →ᵇ ℝ) :
    ∫ x, g x ∂(paretoLaw C) = 2 * ∫ u in (0 : ℝ)..1 / 2, g (C / u) := by
  have hm : Measurable (fun u : ℝ => C / u) := by fun_prop
  rw [paretoLaw, integral_map hm.aemeasurable
    g.continuous.aestronglyMeasurable, integral_unif (by norm_num)]
  norm_num

/-- **eq. `(paretotail)`**, for `t > 0`: `Pr(C/U > t) = min{1, 2C/t}`. -/
theorem paretoLaw_tail {C t : ℝ} (hC : 0 < C) (ht : 0 < t) :
    paretoLaw C (Ioi t) = ENNReal.ofReal (min 1 (2 * C / t)) := by
  have hm : Measurable (fun u : ℝ => C / u) := by fun_prop
  rw [paretoLaw, Measure.map_apply hm measurableSet_Ioi, unif,
    Measure.smul_apply, Measure.restrict_apply (measurableSet_Ioi.preimage hm), smul_eq_mul]
  have hset : (fun u : ℝ => C / u) ⁻¹' Ioi t ∩ Icc 0 (1 / 2) = Ioo 0 (C / t) ∩ Icc 0 (1 / 2) := by
    ext u
    simp only [mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases h2.lt_or_eq with hu | hu
      · exact ⟨⟨hu, by rwa [lt_div_iff₀ hu, mul_comm, ← lt_div_iff₀ ht] at h1⟩, h2, h3⟩
      · subst hu; simp only [div_zero] at h1; linarith
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨?_, h3, h4⟩
      rwa [lt_div_iff₀ h1, mul_comm, ← lt_div_iff₀ ht]
  rw [hset, show (1 / 2 : ℝ) - 0 = 1 / 2 by norm_num]
  rcases le_or_gt (C / t) (1 / 2) with hle | hgt
  · have : Ioo 0 (C / t) ∩ Icc 0 (1 / 2) = Ioo 0 (C / t) := by
      ext u; simp only [mem_inter_iff, Set.mem_Ioo, Set.mem_Icc]
      constructor
      · rintro ⟨h, -⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, h1.le, by linarith⟩
    rw [this, Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [min_eq_right]
    · field_simp
    · rw [div_le_one ht]; rw [div_le_iff₀ ht] at hle; linarith
  · have : Ioo 0 (C / t) ∩ Icc 0 (1 / 2) = Set.Ioc 0 (1 / 2) := by
      ext u; simp only [mem_inter_iff, Set.mem_Ioo, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, -⟩, -, h4⟩; exact ⟨h1, h4⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h1.le, h2⟩
    rw [this, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [min_eq_left]
    · norm_num
    · rw [le_div_iff₀ ht]; rw [lt_div_iff₀ ht] at hgt; linarith

end Irr

/-! ### Deleting the isolated singular index -/

section Pareto

variable {a τ : ℝ}

open Classical in
/-- `𝓘_L^* = {N ∈ 𝓘_L : B_N nonsingular}` (`= {N ∈ 𝓘_L : d_N > 0}`). -/
noncomputable def windowStar (a τ : ℝ) (L : ℕ) : Finset ℕ :=
  (window L).filter (fun N => Nonsingular N a τ)

/-- Empirical measure over `𝓘_L^*`, normalized by `L^* = |𝓘_L^*|`. -/
noncomputable def empMeasureStar (a τ : ℝ) (x : ℕ → ℝ) (L : ℕ) : Measure ℝ :=
  (((windowStar a τ L).card : ℝ≥0∞)⁻¹) • ∑ N ∈ windowStar a τ L, Measure.dirac (x N)

open Classical in
lemma card_sing_le (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) (L : ℕ) :
    ((window L).filter (fun N => ¬ Nonsingular N a τ)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro N₁ h₁ N₂ h₂
  simp only [Finset.mem_filter, window, Finset.mem_Icc, Nonsingular, not_not] at h₁ h₂
  exact singDims_subsingleton_of_irrational h hα ⟨h₁.1.1, h₁.2⟩ ⟨h₂.1.1, h₂.2⟩

open Classical in
/-- `L - 1 ≤ L^* ≤ L` (manuscript: `L^* = L`, or `L - 1` after one isolated singular dimension). -/
theorem card_windowStar (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) (L : ℕ) :
    L - 1 ≤ (windowStar a τ L).card ∧ (windowStar a τ L).card ≤ L := by
  have e := Finset.card_filter_add_card_filter_not (s := window L)
    (p := fun N => Nonsingular N a τ)
  rw [card_window] at e
  have := card_sing_le h hα L
  unfold windowStar
  omega

lemma Kkap_nonneg (h : InteriorParam a τ) : 0 ≤ Kkap a τ := by
  have := L2mu_nonneg h.1 h.2.1
  have := Mband_pos h
  have := Ksm_nonneg h
  unfold Kkap; positivity

lemma Cint_pos (h : InteriorParam a τ) : 0 < Cint a τ := by
  have := Mband_pos h
  have := gam_pos h
  unfold Cint; positivity

lemma kappa_nonneg {N : ℕ} (hN : 1 ≤ N) : 0 ≤ kappa N a τ :=
  div_nonneg (sigmaMax_nonneg' hN a τ) (sigmaMin_nonneg hN a τ)

/-- Quantitative closeness `κ₂/N ≈ C/d_N`, relative to `C/d_N`. -/
lemma kappa_div_close (h : InteriorParam a τ) {N : ℕ} (hN : n2 a τ ≤ N) (hN1 : 1 ≤ N)
    (hns : Nonsingular N a τ) :
    |kappa N a τ / N - Cint a τ / dN N a τ| ≤
      Cint a τ / dN N a τ * (Kkap a τ * (1 + τ) + τ) / N := by
  have hτ := h.tau_pos
  have hK := Kkap_nonneg h
  have hC := Cint_pos h
  have hN2 : 2 ≤ N := le_trans (by unfold n2 n1 n0; omega) hN
  have hd : 0 < dN N a τ := by
    rcases (dN_nonneg (a := a) (τ := τ) N).lt_or_eq with hl | he
    · exact hl
    · exact absurd ((thm_sing_dN h hN2).2 he.symm) hns
  set d := dN N a τ
  set C := Cint a τ
  set K := Kkap a τ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hk := thm_kappa_relative h hN hns
  set Q := C * (N + τ) / d with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have e1 : |kappa N a τ - Q| ≤ K / N * Q := by
    rw [abs_le]; constructor <;> nlinarith [hk.1, hk.2]
  have e2 : Q / N - C / d = C / d * τ / N := by rw [hQ]; field_simp; ring
  calc |kappa N a τ / N - C / d|
      = |(kappa N a τ - Q) / N + (Q / N - C / d)| := by ring_nf
    _ ≤ |(kappa N a τ - Q) / N| + |Q / N - C / d| := abs_add_le _ _
    _ ≤ K / N * Q / N + C / d * τ / N := by
        rw [abs_div, abs_of_pos hNr, e2,
          abs_of_nonneg (show (0 : ℝ) ≤ C / d * τ / N by positivity)]
        exact add_le_add (div_le_div_of_nonneg_right e1 hNr.le) le_rfl
    _ ≤ C / d * (K * (1 + τ) + τ) / N := by
        have hNτ : (N + τ) / N ≤ 1 + τ := by
          rw [div_le_iff₀ hNr]
          nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ N by exact_mod_cast hN1) hτ.le]
        have : K / N * Q / N = C / d * (K * ((N + τ) / N)) / N := by rw [hQ]; field_simp
        rw [this, ← add_div]
        apply div_le_div_of_nonneg_right _ hNr.le
        have hCd : 0 ≤ C / d := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hNτ (mul_nonneg hCd hK)]

/-- An ε/3-type approximation principle for real sequences. -/
lemma tendsto_of_approx {F : ℕ → ℝ} {I : ℝ}
    (h : ∀ η > 0, ∃ G : ℕ → ℝ, ∃ J : ℝ, Tendsto G atTop (𝓝 J) ∧ |J - I| ≤ η ∧
      ∀ᶠ L in atTop, |F L - G L| ≤ η) :
    Tendsto F atTop (𝓝 I) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨G, J, hG, hJ, hFG⟩ := h (ε / 4) (by positivity)
  obtain ⟨L1, hL1⟩ := Metric.tendsto_atTop.1 hG (ε / 4) (by positivity)
  obtain ⟨L2, hL2⟩ := eventually_atTop.1 hFG
  refine ⟨max L1 L2, fun L hL => ?_⟩
  have h1 := hL1 L (le_of_max_le_left hL)
  have h2 := hL2 L (le_of_max_le_right hL)
  rw [Real.dist_eq] at h1 ⊢
  calc |F L - I| = |(F L - G L) + (G L - J) + (J - I)| := by ring_nf
    _ ≤ |F L - G L| + |G L - J| + |J - I| := abs_add_three _ _ _
    _ < ε := by linarith

lemma intervalIntegrable_of_bdd {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (u v : ℝ) : IntervalIntegrable f volume u v := by
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (M := M) (by
    rw [Set.uIoc]; exact measure_Ioc_lt_top.ne) hf.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hM x)

/-- The continuous cutoff `φ_δ = 1` on `(-∞, δ]`, `0` on `[2δ, ∞)`. -/
noncomputable def cutoff (δ : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun u => max 0 (min 1 (2 - u / δ)), by fun_prop⟩ 1
    (fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]
      constructor <;>
      · have h1 := le_max_left 0 (min 1 (2 - x / δ))
        have h2 := le_max_left 0 (min 1 (2 - y / δ))
        have h3 : max 0 (min 1 (2 - x / δ)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
        have h4 : max 0 (min 1 (2 - y / δ)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
        linarith)

lemma cutoff_apply (δ u : ℝ) : cutoff δ u = max 0 (min 1 (2 - u / δ)) := rfl

lemma cutoff_nonneg (δ u : ℝ) : 0 ≤ cutoff δ u := le_max_left _ _

lemma cutoff_le_one (δ u : ℝ) : cutoff δ u ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma cutoff_eq_one {δ u : ℝ} (hδ : 0 < δ) (hu : u ≤ δ) : cutoff δ u = 1 := by
  rw [cutoff_apply, min_eq_left, max_eq_right zero_le_one]
  have : u / δ ≤ 1 := by rw [div_le_one hδ]; exact hu
  linarith

lemma cutoff_eq_zero {δ u : ℝ} (hδ : 0 < δ) (hu : 2 * δ ≤ u) : cutoff δ u = 0 := by
  rw [cutoff_apply]
  have : 2 ≤ u / δ := by rw [le_div_iff₀ hδ]; linarith
  exact max_eq_left (min_le_of_right_le (by linarith))

lemma integral_cutoff_le {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    ∫ u in (0 : ℝ)..1 / 2, cutoff δ u ≤ 2 * δ := by
  have hi : ∀ u v, IntervalIntegrable (fun x => cutoff δ x) volume u v := fun u v =>
    (cutoff δ).continuous.intervalIntegrable u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (2 * δ)) (hi _ _)]
  have h1 : ∫ u in (0 : ℝ)..2 * δ, cutoff δ u ≤ ∫ u in (0 : ℝ)..2 * δ, (1 : ℝ) :=
    intervalIntegral.integral_mono_on (by positivity) (hi _ _) intervalIntegrable_const
      fun u _ => cutoff_le_one δ u
  have h2 : ∫ u in 2 * δ..1 / 2, cutoff δ u = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
    intro u hu
    rw [Set.uIcc_of_le (by linarith)] at hu
    exact cutoff_eq_zero hδ hu.1
  rw [h2, add_zero]
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using h1

/-- **eq. `(paretolaw)`**: for irrational `α`, over the nonsingular indices `𝓘_L^*`,
`(L^*)⁻¹ ∑_{N∈𝓘_L^*} δ_{κ₂(B_N)/N} ⇒ Law(C/U)`, `U ~ U[0,1/2]`. -/
theorem thm_irr_laws_pareto (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    WeakLim (empMeasureStar a τ (fun N => kappa N a τ / N)) (paretoLaw (Cint a τ)) := by
  classical
  intro g
  have hτ := h.tau_pos
  set C := Cint a τ with hCdef
  have hC : 0 < C := Cint_pos h
  set M := ‖g‖ with hMdef
  have hM : 0 ≤ M := norm_nonneg _
  have hgM : ∀ x, |g x| ≤ M := fun x => by rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm x
  rw [integral_paretoLaw]
  set H : ℝ → ℝ := fun u => g (C / u) with hHdef
  have hHm : Measurable H := g.continuous.measurable.comp (by fun_prop)
  have hHi : ∀ u v, IntervalIntegrable H volume u v :=
    intervalIntegrable_of_bdd hHm (fun x => hgM _)
  set I := 2 * ∫ u in (0 : ℝ)..1 / 2, H u with hIdef
  let y : ℕ → ℝ := fun N => if Nonsingular N a τ then g (kappa N a τ / N) else 0
  have hyM : ∀ N, |y N| ≤ M := fun N => by
    simp only [y]; split_ifs
    · exact hgM _
    · rw [abs_zero]; exact hM
  -- Step A: the full-window average of `y` converges to `I`.
  have hA : Tendsto (fun L : ℕ => (L : ℝ)⁻¹ * ∑ N ∈ window L, y N) atTop (𝓝 I) := by
    apply tendsto_of_approx
    intro η hη
    set δ := min (1 / 4) (η / (40 * (M + 1))) with hδdef
    have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
    have hδ4 : δ ≤ 1 / 4 := min_le_left _ _
    have hMδ : 40 * M * δ ≤ η := by
      have : δ ≤ η / (40 * (M + 1)) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith
    set ε' := η / 8 with hε'
    have hε'0 : 0 < ε' := by positivity
    -- the truncated test function `G_δ(u) = g(C / max u δ)`
    let Gδ : ℝ →ᵇ ℝ := g.compContinuous ⟨fun u => C / max u δ, by
      have : ∀ u : ℝ, max u δ ≠ 0 := fun u => (lt_of_lt_of_le hδ (le_max_right u δ)).ne'
      fun_prop (disch := exact this _)⟩
    have hGδ : ∀ u, Gδ u = g (C / max u δ) := fun u => rfl
    have hGM : ∀ u, |Gδ u| ≤ M := fun u => hgM _
    refine ⟨fun L => (L : ℝ)⁻¹ * ∑ N ∈ window L, Gδ (1 * dN N a τ),
      2 * ∫ u in (0 : ℝ)..1 / 2, Gδ u, ?_, ?_, ?_⟩
    · -- Weyl for the truncated test function
      have := dN_law h hα one_pos Gδ
      simp only [integral_empMeasure] at this
      rw [integral_unif (by norm_num)] at this
      convert this using 2
      norm_num
    · -- truncation error in the limit
      have hsplit : ∀ F : ℝ → ℝ, (∀ u v, IntervalIntegrable F volume u v) →
          ∫ u in (0 : ℝ)..1 / 2, F u = (∫ u in (0 : ℝ)..δ, F u) + ∫ u in δ..1 / 2, F u :=
        fun F hF => (intervalIntegral.integral_add_adjacent_intervals (hF _ _) (hF _ _)).symm
      have hGi : ∀ u v, IntervalIntegrable (fun x => Gδ x) volume u v := fun u v =>
        Gδ.continuous.intervalIntegrable u v
      rw [hIdef, hsplit _ hGi, hsplit _ hHi]
      have heq : ∫ u in δ..1 / 2, Gδ u = ∫ u in δ..1 / 2, H u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le (by linarith)] at hu
        simp only [hGδ, H, max_eq_left hu.1]
      rw [heq]
      have hb : ‖∫ u in (0 : ℝ)..δ, (Gδ u - H u)‖ ≤ 2 * M * |δ - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => by
          rw [Real.norm_eq_abs]
          calc |Gδ u - H u| ≤ |Gδ u| + |H u| := abs_sub _ _
            _ ≤ 2 * M := by linarith [hGM u, hgM (C / u)]
      rw [intervalIntegral.integral_sub (hGi _ _) (hHi _ _), Real.norm_eq_abs, sub_zero,
        abs_of_pos hδ] at hb
      calc |2 * ((∫ u in (0 : ℝ)..δ, Gδ u) + ∫ u in δ..1 / 2, H u) -
            2 * ((∫ u in (0 : ℝ)..δ, H u) + ∫ u in δ..1 / 2, H u)|
          = 2 * |(∫ u in (0 : ℝ)..δ, Gδ u) - ∫ u in (0 : ℝ)..δ, H u| := by
            rw [← abs_two, ← abs_mul]; ring_nf
        _ ≤ 2 * (2 * M * δ) := by gcongr
        _ ≤ η := by nlinarith
    · -- termwise comparison, eventually in `L`
      set c0 := Kkap a τ * (1 + τ) + τ with hc0
      have hc00 : 0 ≤ c0 := by have := Kkap_nonneg h; positivity
      -- uniform continuity of `g` on a compact window
      have huc := isCompact_Icc.uniformContinuousOn_of_continuous
        (s := Icc (-1) (C / δ + 1)) g.continuous.continuousOn
      rw [Metric.uniformContinuousOn_iff] at huc
      obtain ⟨ρ, hρ, hρε⟩ := huc ε' hε'0
      obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, n2 a τ + 1 ≤ N0 ∧ C / δ * c0 / N0 < min ρ 1 := by
        obtain ⟨N0, hN0⟩ := exists_nat_gt (C / δ * c0 / min ρ 1)
        refine ⟨max N0 (n2 a τ + 1), le_max_right _ _, ?_⟩
        have hm : 0 < min ρ 1 := lt_min hρ one_pos
        have hpos : (0 : ℝ) < max N0 (n2 a τ + 1) := by
          exact_mod_cast lt_of_lt_of_le (Nat.succ_pos _) (le_max_right _ _)
        rw [div_lt_iff₀ hpos]
        rw [div_lt_iff₀ hm] at hN0
        have : (N0 : ℝ) ≤ max N0 (n2 a τ + 1) := by exact_mod_cast le_max_left _ _
        nlinarith
      -- pointwise bound
      have hpoint : ∀ N : ℕ, |y N - Gδ (1 * dN N a τ)| ≤ 2 * M * cutoff δ (1 * dN N a τ) + ε' +
          ((if N < N0 then 2 * M else 0) + (if Nonsingular N a τ then 0 else 2 * M)) := by
        intro N
        have hφ0 := cutoff_nonneg δ (1 * dN N a τ)
        have hbase : |y N - Gδ (1 * dN N a τ)| ≤ 2 * M := by
          calc |y N - Gδ (1 * dN N a τ)| ≤ |y N| + |Gδ (1 * dN N a τ)| := abs_sub _ _
            _ ≤ 2 * M := by linarith [hyM N, hGM (1 * dN N a τ)]
        by_cases hlt : N < N0
        · simp only [hlt, ite_true]
          have : 0 ≤ (if Nonsingular N a τ then (0 : ℝ) else 2 * M) := by split_ifs <;> positivity
          nlinarith
        by_cases hns : Nonsingular N a τ
        swap
        · simp only [hns, ite_false]
          have : 0 ≤ (if N < N0 then 2 * M else (0 : ℝ)) := by split_ifs; positivity
          nlinarith
        simp only [hlt, hns, ite_false, ite_true, add_zero]
        push Not at hlt
        rw [one_mul] at hbase ⊢
        rw [one_mul] at hφ0
        have hMφ : 0 ≤ 2 * M * cutoff δ (dN N a τ) := mul_nonneg (by positivity) hφ0
        set d := dN N a τ with hd
        by_cases hdδ : δ ≤ d
        · -- far from the singular scale: uniform continuity
          have hN1 : 1 ≤ N := by omega
          have hN2 : n2 a τ ≤ N := by omega
          have hd0 : 0 < d := lt_of_lt_of_le hδ hdδ
          have hclose := kappa_div_close h hN2 hN1 hns
          rw [← hd] at hclose
          have hNr : (N0 : ℝ) ≤ N := by exact_mod_cast hlt
          have hN0r : (0 : ℝ) < N0 := by exact_mod_cast (show 0 < N0 by omega)
          have hCd : C / d ≤ C / δ := div_le_div_of_nonneg_left hC.le hδ hdδ
          have hb : C / d * c0 / N ≤ C / δ * c0 / N0 := by
            apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hCd hc00) hN0r hNr
          have hlt' : |kappa N a τ / N - C / d| < min ρ 1 := lt_of_le_of_lt (hclose.trans hb) hN0.2
          have hd2 : C / d ∈ Icc (-1) (C / δ + 1) :=
            ⟨by have : 0 ≤ C / d := by positivity
                linarith, by linarith⟩
          have hk2 : kappa N a τ / N ∈ Icc (-1) (C / δ + 1) := by
            have := abs_lt.1 (lt_of_lt_of_le hlt' (min_le_right _ _))
            have : 0 ≤ C / d := by positivity
            exact ⟨by linarith, by linarith⟩
          have := hρε _ hk2 _ hd2 (by rw [Real.dist_eq]; exact lt_of_lt_of_le hlt' (min_le_left _ _))
          rw [Real.dist_eq] at this
          simp only [y, hns, ite_true, hGδ, max_eq_left hdδ]
          nlinarith
        · -- near the singular scale: the cutoff is `1`
          push Not at hdδ
          rw [cutoff_eq_one hδ hdδ.le]
          nlinarith
      -- summed bound
      have hφlim : Tendsto (fun L : ℕ => (L : ℝ)⁻¹ * ∑ N ∈ window L, cutoff δ (1 * dN N a τ))
          atTop (𝓝 (2 * ∫ u in (0 : ℝ)..1 / 2, cutoff δ u)) := by
        have := dN_law h hα one_pos (cutoff δ)
        simp only [integral_empMeasure] at this
        rw [integral_unif (by norm_num)] at this
        convert this using 2
        norm_num
      have hφle := integral_cutoff_le hδ hδ4
      have hev1 : ∀ᶠ L : ℕ in atTop,
          (L : ℝ)⁻¹ * ∑ N ∈ window L, cutoff δ (1 * dN N a τ) ≤ 5 * δ :=
        hφlim.eventually (ge_mem_nhds (by linarith))
      have hev2 : ∀ᶠ L : ℕ in atTop, 2 * M * (N0 + 1) / L ≤ ε' := by
        have : Tendsto (fun L : ℕ => 2 * M * (N0 + 1) * (L : ℝ)⁻¹) atTop (𝓝 0) := by
          simpa only [mul_zero] using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
            (2 * M * (N0 + 1))
        filter_upwards [this.eventually (ge_mem_nhds hε'0)] with L hL
        rwa [div_eq_mul_inv]
      filter_upwards [hev1, hev2, eventually_ge_atTop 1] with L h1 h2 hL1
      have hLr : (0 : ℝ) < L := by exact_mod_cast hL1
      have hcount1 : ∑ N ∈ window L, (if N < N0 then 2 * M else (0 : ℝ)) ≤ 2 * M * N0 := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        have : ((window L).filter (fun N => N < N0)).card ≤ N0 := by
          calc ((window L).filter (fun N => N < N0)).card ≤ (range N0).card :=
                Finset.card_le_card fun N hN => by
                  simp only [Finset.mem_filter] at hN; exact Finset.mem_range.2 hN.2
            _ = N0 := Finset.card_range N0
        have : (((window L).filter (fun N => N < N0)).card : ℝ) ≤ N0 := by exact_mod_cast this
        nlinarith
      have hcount2 : ∑ N ∈ window L, (if Nonsingular N a τ then (0 : ℝ) else 2 * M) ≤ 2 * M := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
        have : (((window L).filter (fun N => ¬ Nonsingular N a τ)).card : ℝ) ≤ 1 := by
          exact_mod_cast card_sing_le h hα L
        nlinarith
      have hsum : |∑ N ∈ window L, y N - ∑ N ∈ window L, Gδ (1 * dN N a τ)| ≤
          2 * M * ∑ N ∈ window L, cutoff δ (1 * dN N a τ) + L * ε' + 2 * M * (N0 + 1) := by
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun N _ => hpoint N).trans ?_
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_const, card_window, nsmul_eq_mul, ← Finset.mul_sum]
        linarith
      rw [← mul_sub, abs_mul, abs_inv, abs_of_pos hLr]
      calc (L : ℝ)⁻¹ * |∑ N ∈ window L, y N - ∑ N ∈ window L, Gδ (1 * dN N a τ)|
          ≤ (L : ℝ)⁻¹ * (2 * M * ∑ N ∈ window L, cutoff δ (1 * dN N a τ) + L * ε' +
              2 * M * (N0 + 1)) := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 2 * M * ((L : ℝ)⁻¹ * ∑ N ∈ window L, cutoff δ (1 * dN N a τ)) + ε' +
              2 * M * (N0 + 1) / L := by field_simp
        _ ≤ 2 * M * (5 * δ) + ε' + ε' := by gcongr
        _ ≤ η := by rw [hε']; nlinarith
  -- Step B: renormalize by `L^*` and drop the zero terms.
  have hratio : Tendsto (fun L : ℕ => (L : ℝ) / (windowStar a τ L).card) atTop (𝓝 1) := by
    have hlo : Tendsto (fun L : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hhi : Tendsto (fun L : ℕ => (L : ℝ) / (L - 1)) atTop (𝓝 1) := by
      have : Tendsto (fun L : ℕ => 1 + 1 / ((L : ℝ) - 1)) atTop (𝓝 (1 + 0)) := by
        refine tendsto_const_nhds.add (tendsto_const_nhds.div_atTop ?_)
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with L hL
      have : (L : ℝ) - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ L := by exact_mod_cast hL
        linarith
      field_simp
      ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with L hL
      obtain ⟨c1, c2⟩ := card_windowStar h hα L
      have hc : (0 : ℝ) < (windowStar a τ L).card := by exact_mod_cast (by omega : 0 < _)
      rw [le_div_iff₀ hc, one_mul]; exact_mod_cast c2
    · filter_upwards [eventually_ge_atTop 2] with L hL
      obtain ⟨c1, c2⟩ := card_windowStar h hα L
      have hc : (0 : ℝ) < (windowStar a τ L).card := by exact_mod_cast (by omega : 0 < _)
      have hL1 : (1 : ℝ) ≤ L - 1 := by
        have : (2 : ℝ) ≤ L := by exact_mod_cast hL
        linarith
      rw [div_le_div_iff₀ hc (by linarith)]
      have : ((L - 1 : ℕ) : ℝ) ≤ (windowStar a τ L).card := by exact_mod_cast c1
      rw [Nat.cast_sub (by omega), Nat.cast_one] at this
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      nlinarith
  have := hratio.mul hA
  rw [one_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with L hL
  obtain ⟨c1, -⟩ := card_windowStar h hα L
  have hc : ((windowStar a τ L).card : ℝ) ≠ 0 := by exact_mod_cast (by omega : (windowStar a τ L).card ≠ 0)
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  rw [empMeasureStar, integral_smul_sum_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hsf : ∑ N ∈ windowStar a τ L, g (kappa N a τ / N) = ∑ N ∈ window L, y N := by
    rw [windowStar, Finset.sum_filter]
  rw [hsf]
  field_simp

/-- **eq. `(cesaro)`**: for irrational `α`, after deleting the isolated singular index,
`L⁻¹ ∑_{N ∈ 𝓘_L^*} κ₂(B_N)/N → +∞`. -/
theorem thm_irr_laws_cesaro (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    Tendsto (fun L : ℕ => (L : ℝ)⁻¹ * ∑ N ∈ windowStar a τ L, kappa N a τ / N) atTop atTop := by
  classical
  have hτ := h.tau_pos
  set C := Cint a τ
  have hC : 0 < C := Cint_pos h
  set K := Kkap a τ
  have hK := Kkap_nonneg h
  rw [tendsto_atTop]
  intro b
  -- choose the truncation height `R`
  set R := 2 * C * Real.exp ((|b| + 1) / C) with hR
  have hR2 : 2 * C < R := by
    have : 1 < Real.exp ((|b| + 1) / C) := Real.one_lt_exp_iff.2 (by positivity)
    rw [hR]; nlinarith
  have hR0 : 0 < R := by linarith
  set s := C / R with hs
  have hs0 : 0 < s := by positivity
  have hs2 : s < 1 / 2 := by rw [hs, div_lt_iff₀ hR0]; linarith
  -- truncated test function `H_R(u) = C / max u s ∈ [0, R]`
  let HR : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨fun u => C / max u s, by
      have : ∀ u : ℝ, max u s ≠ 0 := fun u => (lt_of_lt_of_le hs0 (le_max_right u s)).ne'
      fun_prop (disch := exact this _)⟩ (2 * R) (fun x y => by
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        have hb : ∀ u, 0 ≤ C / max u s ∧ C / max u s ≤ R := fun u => by
          have hm : s ≤ max u s := le_max_right u s
          have hm0 : 0 < max u s := lt_of_lt_of_le hs0 hm
          refine ⟨by positivity, ?_⟩
          rw [div_le_iff₀ hm0]; rw [hs] at hm
          have := (div_le_iff₀ hR0).1 hm
          linarith
        rw [abs_le]; constructor <;> linarith [(hb x).1, (hb x).2, (hb y).1, (hb y).2])
  have hHR : ∀ u, HR u = C / max u s := fun u => rfl
  have hHRb : ∀ u, 0 ≤ HR u ∧ HR u ≤ R := fun u => by
    rw [hHR]
    have hm : s ≤ max u s := le_max_right u s
    have hm0 : 0 < max u s := lt_of_lt_of_le hs0 hm
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hm0]; rw [hs] at hm
    have := (div_le_iff₀ hR0).1 hm
    linarith
  -- its integral is `≥ C log(R/(2C)) = |b| + 1`
  have hint : |b| + 1 ≤ ∫ u in (0 : ℝ)..1 / 2, HR u := by
    have hi : ∀ u v, IntervalIntegrable (fun x => HR x) volume u v := fun u v =>
      HR.continuous.intervalIntegrable u v
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s _)]
    have h1 : 0 ≤ ∫ u in (0 : ℝ)..s, HR u :=
      intervalIntegral.integral_nonneg hs0.le fun u _ => (hHRb u).1
    have h2 : ∫ u in s..1 / 2, HR u = C * Real.log ((1 / 2) / s) := by
      rw [intervalIntegral.integral_congr (g := fun u => C * u⁻¹), intervalIntegral.integral_const_mul,
        integral_inv_of_pos hs0 (by norm_num)]
      intro u hu
      rw [Set.uIcc_of_le hs2.le] at hu
      simp only [hHR, max_eq_left hu.1, div_eq_mul_inv]
    have h3 : C * Real.log ((1 / 2) / s) = |b| + 1 := by
      have : (1 / 2) / s = Real.exp ((|b| + 1) / C) := by
        rw [hs, hR]; field_simp
      rw [this, Real.log_exp]; field_simp
    linarith
  -- the averages of `H_R(d_N)` converge to `2 ∫ H_R ≥ 2(|b|+1)`
  have hlim := dN_law h hα one_pos HR
  simp only [integral_empMeasure] at hlim
  rw [integral_unif (by norm_num), show (1 / 2 : ℝ) - 0 = 1 / 2 by norm_num, inv_div, div_one] at hlim
  have hlim1 : ∀ᶠ L : ℕ in atTop, |b| + 1 / 2 ≤
      (L : ℝ)⁻¹ * ∑ N ∈ window L, HR (1 * dN N a τ) / 2 := by
    have : Tendsto (fun L : ℕ => (L : ℝ)⁻¹ * ∑ N ∈ window L, HR (1 * dN N a τ) / 2) atTop
        (𝓝 ((2 * ∫ u in (0 : ℝ)..1 / 2, HR u) / 2)) := by
      refine (hlim.div_const 2).congr fun L => ?_
      rw [← Finset.sum_div]; ring
    rw [mul_div_cancel_left₀ _ two_ne_zero] at this
    exact this.eventually (le_mem_nhds (show |b| + 1 / 2 < ∫ u in (0 : ℝ)..1 / 2, HR u by linarith))
  -- exceptional indices
  set N1 := n2 a τ + ⌈2 * K⌉₊ + 2 with hN1
  have hev2 : ∀ᶠ L : ℕ in atTop, R * (N1 + 1) / L ≤ 1 / 2 := by
    have : Tendsto (fun L : ℕ => R * (N1 + 1) * (L : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (R * (N1 + 1))
    filter_upwards [this.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with L hL
    rwa [div_eq_mul_inv]
  filter_upwards [hlim1, hev2, eventually_ge_atTop 1] with L h1 h2 hL1
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL1
  -- termwise lower bound on the full window
  have hpt : ∀ N ∈ window L, HR (1 * dN N a τ) / 2 -
      ((if N < N1 then R else 0) + (if Nonsingular N a τ then 0 else R)) ≤
      (if Nonsingular N a τ then kappa N a τ / N else 0) := by
    intro N hNw
    have hN2 : 2 ≤ N := (Finset.mem_Icc.1 hNw).1
    have hb := hHRb (1 * dN N a τ)
    by_cases hlt : N < N1
    · have hr : 0 ≤ (if Nonsingular N a τ then (0 : ℝ) else R) := by split_ifs <;> linarith
      have hk : 0 ≤ (if Nonsingular N a τ then kappa N a τ / N else 0) := by
        split_ifs
        · exact div_nonneg (kappa_nonneg (by omega)) (Nat.cast_nonneg _)
        · exact le_rfl
      simp only [hlt, ite_true]; linarith
    by_cases hns : Nonsingular N a τ
    swap
    · simp only [hns, ite_false]; split_ifs; linarith
    simp only [hlt, hns, ite_false, ite_true, add_zero, sub_zero]
    push Not at hlt
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hn2 : n2 a τ ≤ N := by omega
    have hd : 0 < dN N a τ := by
      rcases (dN_nonneg (a := a) (τ := τ) N).lt_or_eq with hl | he
      · exact hl
      · exact absurd ((thm_sing_dN h hN2).2 he.symm) hns
    have hk := (thm_kappa_relative h hn2 hns).1
    have hKN : K / N ≤ 1 / 2 := by
      rw [div_le_iff₀ hNr]
      have : (⌈2 * K⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈2 * K⌉₊ ≤ N)
      have := Nat.le_ceil (2 * K)
      linarith
    -- `κ/N ≥ (1/2) C/d ≥ (1/2) H_R(d)`
    have h1 : C / dN N a τ / 2 ≤ kappa N a τ / N := by
      rw [le_div_iff₀ hNr]
      have hQ : C / dN N a τ * N ≤ C * (N + τ) / dN N a τ := by
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hd]; nlinarith
      have hQ0 : 0 ≤ C * (N + τ) / dN N a τ := by positivity
      calc C / dN N a τ / 2 * N = (1 / 2) * (C / dN N a τ * N) := by ring
        _ ≤ (1 / 2) * (C * (N + τ) / dN N a τ) := by gcongr
        _ ≤ (1 - K / N) * (C * (N + τ) / dN N a τ) := by gcongr; linarith
        _ ≤ kappa N a τ := hk
    have h2 : HR (1 * dN N a τ) ≤ C / dN N a τ := by
      rw [hHR, one_mul]
      exact div_le_div_of_nonneg_left hC.le hd (le_max_left _ _)
    linarith
  have hsum : ∑ N ∈ window L, HR (1 * dN N a τ) / 2 - R * (N1 + 1) ≤
      ∑ N ∈ windowStar a τ L, kappa N a τ / N := by
    rw [windowStar, Finset.sum_filter]
    have hc1 : ∑ N ∈ window L, (if N < N1 then R else (0 : ℝ)) ≤ R * N1 := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have : ((window L).filter (fun N => N < N1)).card ≤ N1 := by
        calc ((window L).filter (fun N => N < N1)).card ≤ (range N1).card :=
              Finset.card_le_card fun N hN => by
                simp only [Finset.mem_filter] at hN; exact Finset.mem_range.2 hN.2
          _ = N1 := Finset.card_range N1
      have : (((window L).filter (fun N => N < N1)).card : ℝ) ≤ N1 := by exact_mod_cast this
      nlinarith
    have hc2 : ∑ N ∈ window L, (if Nonsingular N a τ then (0 : ℝ) else R) ≤ R := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
      have : (((window L).filter (fun N => ¬ Nonsingular N a τ)).card : ℝ) ≤ 1 := by
        exact_mod_cast card_sing_le h hα L
      nlinarith
    have := Finset.sum_le_sum hpt
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at this
    linarith
  calc b ≤ |b| := le_abs_self b
    _ = (|b| + 1 / 2) - 1 / 2 := by ring
    _ ≤ (L : ℝ)⁻¹ * ∑ N ∈ window L, HR (1 * dN N a τ) / 2 - R * (N1 + 1) / L := by linarith
    _ = (L : ℝ)⁻¹ * (∑ N ∈ window L, HR (1 * dN N a τ) / 2 - R * (N1 + 1)) := by
        field_simp
    _ ≤ (L : ℝ)⁻¹ * ∑ N ∈ windowStar a τ L, kappa N a τ / N :=
        mul_le_mul_of_nonneg_left hsum (by positivity)

end Pareto

end ShiftedKMS
