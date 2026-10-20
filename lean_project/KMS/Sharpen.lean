import KMS.Spikes

/-!
# Analytic, probability, and arithmetic refinements

1. `card_windowStar_eventually`: for irrational `α`, `L^* = |𝓘_L^*|` is eventually exactly `L - ε`
   with `ε ∈ {0,1}` (not merely `L - 1 ≤ L^* ≤ L`).
2. `empProbStar`, `thm_irr_laws_pareto_prob`, `thm_irr_laws_uniform_prob`: the starred and
   unstarred empirical laws as genuine `ProbabilityMeasure`s, converging in Mathlib's weak topology.
3. `thm_generic_triangle`: `thm:generic` with `0 < α < 1` and `(α, β)` in the open triangle.
4. `paretoLaw_tail_nonpos`: for `t ≤ 0`, `Pr(C/U > t) = 1` (eq. `(paretotail)` is the `t > 0`
   case, `paretoLaw_tail`).
5. `thm_irr_laws_cesaro_le`: an alternative Cesàro formulation with the singular index
   *explicitly deleted* (`L⁻¹ ∑_{2 ≤ N ≤ L, B_N nonsingular} κ₂/N → ∞`); the corresponding paper statement is
   `thm_irr_laws_cesaro` (window `𝓘_L^*`, denominator `L`).
6. `gam_tendsto_zero_upper/lower`, `Cint_tendsto_atTop_upper/lower`: the band-edge
   non-uniformity remark of `thm:main-conditioning` (`γ(a,τ) → 0`, `C(a,τ) → ∞` as `τ → μ_±`).
-/

open Real Set Filter Topology MeasureTheory Finset
open scoped ENNReal BoundedContinuousFunction

namespace ShiftedKMS

variable {a τ : ℝ}

/-! ### 1. Eventual constancy of `L^*` -/

open Classical in
theorem card_windowStar_eventually (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    ∃ ε : ℕ, ε ≤ 1 ∧ ∃ L₀ : ℕ, ∀ L ≥ L₀, (windowStar a τ L).card = L - ε := by
  have hsplit : ∀ L, (windowStar a τ L).card +
      ((window L).filter (fun N => ¬ Nonsingular N a τ)).card = L := by
    intro L
    have e := Finset.card_filter_add_card_filter_not (s := window L)
      (p := fun N => Nonsingular N a τ)
    rw [card_window] at e
    unfold windowStar
    convert e using 3
  by_cases hs : ∃ N₀, 2 ≤ N₀ ∧ ¬ Nonsingular N₀ a τ
  · obtain ⟨N₀, hN₀, hsing⟩ := hs
    refine ⟨1, le_rfl, N₀, fun L hL => ?_⟩
    have h1 : ((window L).filter (fun N => ¬ Nonsingular N a τ)).card = 1 := by
      apply le_antisymm (card_sing_le h hα L)
      apply Finset.card_pos.2
      exact ⟨N₀, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hN₀, by omega⟩, hsing⟩⟩
    have := hsplit L
    omega
  · push Not at hs
    refine ⟨0, Nat.zero_le _, 0, fun L _ => ?_⟩
    have h0 : ((window L).filter (fun N => ¬ Nonsingular N a τ)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro N hN hns
      exact hns (hs N (Finset.mem_Icc.1 hN).1)
    have := hsplit L
    omega

/-! ### 2. Empirical laws as probability measures -/

lemma isProbabilityMeasure_empMeasureStar (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ))
    (x : ℕ → ℝ) {L : ℕ} (hL : 2 ≤ L) : IsProbabilityMeasure (empMeasureStar a τ x L) := by
  constructor
  have hc : 1 ≤ (windowStar a τ L).card := by
    have := (card_windowStar h hα L).1; omega
  rw [empMeasureStar, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (by omega : (windowStar a τ L).card ≠ 0))
    (ENNReal.natCast_ne_top _)

/-- The starred empirical laws `(L^*)⁻¹ ∑_{N ∈ 𝓘_{L+2}^*} δ_{x_N}` as probability measures. -/
noncomputable def empProbStar (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ))
    (x : ℕ → ℝ) (L : ℕ) : ProbabilityMeasure ℝ :=
  ⟨empMeasureStar a τ x (L + 2), isProbabilityMeasure_empMeasureStar h hα x (by omega)⟩

lemma isProbabilityMeasure_paretoLaw (C : ℝ) : IsProbabilityMeasure (paretoLaw C) := by
  have hu := isProbabilityMeasure_unif (u := 0) (v := 1 / 2) (by norm_num)
  have hm : Measurable (fun u : ℝ => C / u) := by fun_prop
  unfold paretoLaw
  exact (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 hu

/-- `Law(C/U)`, `U ~ U[0,1/2]`, as a probability measure. -/
noncomputable def paretoProb (C : ℝ) : ProbabilityMeasure ℝ :=
  ⟨paretoLaw C, isProbabilityMeasure_paretoLaw C⟩

/-- `U[u,v]` as a probability measure. -/
noncomputable def unifProb {u v : ℝ} (huv : u < v) : ProbabilityMeasure ℝ :=
  ⟨unif u v, isProbabilityMeasure_unif huv⟩

/-- **eq. `(paretolaw)` in Mathlib's weak topology on `ProbabilityMeasure ℝ`.** -/
theorem thm_irr_laws_pareto_prob (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    Tendsto (empProbStar h hα (fun N => kappa N a τ / N)) atTop (𝓝 (paretoProb (Cint a τ))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  exact (tendsto_add_atTop_iff_nat 2).2 (thm_irr_laws_pareto h hα g)

/-- **eq. `(uniformlaw)` in Mathlib's weak topology on `ProbabilityMeasure ℝ`.** -/
theorem thm_irr_laws_uniform_prob (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    Tendsto (empProb (fun N => N * sigmaMin N a τ)) atTop
      (𝓝 (unifProb (show (0 : ℝ) < π * gam a τ / 2 by have := gam_pos h; positivity))) :=
  (weakLim_iff_tendsto _ _).1 (thm_irr_laws_uniform h hα)

/-- The residual law `d_N ⇒ U[0,1/2]` in Mathlib's weak topology. -/
theorem dN_law_prob (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    Tendsto (empProb (fun N => 1 * dN N a τ)) atTop
      (𝓝 (unifProb (show (0 : ℝ) < 1 / 2 by norm_num))) :=
  (weakLim_iff_tendsto _ _).1 (dN_law h hα one_pos)

/-! ### 3. `thm:generic` with the triangle hypotheses explicit -/

theorem thm_generic_triangle {α : ℝ} (hα : Irrational α) (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ᵐ β : ℝ, (α, β) ∈ triangleSet →
      Mplus α β = 0 ∧ wplus α β = 1 ∧
      limsup (fun N : ℕ => ENNReal.ofReal
        (Real.log (kappa N (aOf α β) (tauOf α β)) / Real.log N)) atTop = 2 ∧
      limsup (fun N : ℕ => ENNReal.ofReal
        (kappa N (aOf α β) (tauOf α β) / (N : ℝ) ^ 2)) atTop = ⊤ := by
  have _ := hα1
  filter_upwards [thm_generic hα hα0] with β hβ hmem
  exact hβ ⟨hmem.2.1, by linarith [hmem.2.2]⟩

/-! ### 4. The Pareto tail for `t ≤ 0` -/

theorem paretoLaw_tail_nonpos {C t : ℝ} (hC : 0 < C) (ht : t ≤ 0) :
    paretoLaw C (Ioi t) = 1 := by
  have hm : Measurable (fun u : ℝ => C / u) := by fun_prop
  rw [paretoLaw, Measure.map_apply hm measurableSet_Ioi, unif, Measure.smul_apply,
    Measure.restrict_apply (measurableSet_Ioi.preimage hm), smul_eq_mul,
    show (1 / 2 : ℝ) - 0 = 1 / 2 by norm_num]
  have hsub1 : Ioc (0 : ℝ) (1 / 2) ⊆ (fun u : ℝ => C / u) ⁻¹' Ioi t ∩ Icc 0 (1 / 2) := by
    intro u hu
    refine ⟨?_, hu.1.le, hu.2⟩
    show t < C / u
    have : 0 < C / u := div_pos hC hu.1
    linarith
  have hsub2 : (fun u : ℝ => C / u) ⁻¹' Ioi t ∩ Icc 0 (1 / 2) ⊆ Icc (0 : ℝ) (1 / 2) :=
    Set.inter_subset_right
  have hle := measure_mono (μ := volume) hsub2
  have hge := measure_mono (μ := volume) hsub1
  rw [Real.volume_Icc] at hle
  rw [Real.volume_Ioc] at hge
  have heq : volume ((fun u : ℝ => C / u) ⁻¹' Ioi t ∩ Icc 0 (1 / 2)) =
      ENNReal.ofReal (1 / 2) := le_antisymm (by simpa using hle) (by simpa using hge)
  rw [heq]
  exact ENNReal.inv_mul_cancel (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; norm_num)
    ENNReal.ofReal_ne_top

/-! ### 5. Cesàro with the singular index deleted, `N ≤ L` indexing -/

open Classical in
theorem thm_irr_laws_cesaro_le (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    Tendsto (fun L : ℕ => (L : ℝ)⁻¹ *
      ∑ N ∈ (Finset.Icc 2 L).filter (fun N => Nonsingular N a τ), kappa N a τ / N)
      atTop atTop := by
  have hG := thm_irr_laws_cesaro h hα
  have hG' : Tendsto (fun L : ℕ => (1 / 2 : ℝ) * ((↑(L - 1) : ℝ)⁻¹ *
      ∑ N ∈ windowStar a τ (L - 1), kappa N a τ / N)) atTop atTop :=
    (hG.comp (tendsto_sub_atTop_nat 1)).const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hG'
  filter_upwards [eventually_ge_atTop 2] with L hL
  have hwin : (Finset.Icc 2 L).filter (fun N => Nonsingular N a τ) = windowStar a τ (L - 1) := by
    unfold windowStar window
    rw [show L - 1 + 1 = L by omega]
  rw [hwin]
  set S := ∑ N ∈ windowStar a τ (L - 1), kappa N a τ / N
  have hS : 0 ≤ S := Finset.sum_nonneg fun N hN => by
    have hN2 : 2 ≤ N := (Finset.mem_Icc.1 (Finset.mem_filter.1 hN).1).1
    exact div_nonneg (kappa_nonneg (by omega)) (Nat.cast_nonneg _)
  have hL1 : (1 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ L - 1)
  have hLr : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  rw [hLr] at hL1 ⊢
  rw [show (1 / 2 : ℝ) * (((L : ℝ) - 1)⁻¹ * S) = S / (2 * ((L : ℝ) - 1)) by field_simp,
    show (L : ℝ)⁻¹ * S = S / L by ring]
  exact div_le_div_of_nonneg_left hS (by positivity) (by linarith)

/-! ### 6. Band-edge non-uniformity: `γ → 0`, `C → ∞` -/

section Edges

variable (ha0 : 0 < a) (ha1 : a < 1)
include ha0 ha1

lemma continuous_dmu : Continuous (dmu a) := by
  have hR : ∀ θ, (1 - 2 * a * Real.cos θ + a ^ 2) ^ 2 ≠ 0 := fun θ =>
    pow_ne_zero 2 (Ra_pos ha0 ha1 θ).ne'
  unfold dmu Ra
  fun_prop (disch := exact hR _)

lemma crossCos_upperEdge : crossCos a (upperEdge a) = 1 := by
  have h1 : (1 - a) ≠ 0 := by intro h; linarith
  have h2 : (1 + a) ≠ 0 := by intro h; linarith
  unfold crossCos upperEdge
  field_simp
  ring

lemma crossCos_lowerEdge : crossCos a (lowerEdge a) = -1 := by
  have h1 : (1 - a) ≠ 0 := by intro h; linarith
  have h2 : (1 + a) ≠ 0 := by intro h; linarith
  unfold crossCos lowerEdge
  field_simp
  ring

lemma continuousAt_crossCos {τ₀ : ℝ} (hτ₀ : τ₀ ≠ 0) : ContinuousAt (crossCos a) τ₀ := by
  unfold crossCos
  exact ((continuousAt_const.sub (continuousAt_const.div continuousAt_id hτ₀)).div_const _)

theorem gam_tendsto_zero_upper : Tendsto (gam a) (𝓝 (upperEdge a)) (𝓝 0) := by
  have hu : upperEdge a ≠ 0 := by
    unfold upperEdge; exact div_ne_zero (by linarith) (by linarith)
  have hc : ContinuousAt (fun τ => |dmu a (Real.arccos (crossCos a τ))|) (upperEdge a) :=
    ((continuous_dmu ha0 ha1).continuousAt.comp
      (Real.continuous_arccos.continuousAt.comp (continuousAt_crossCos ha0 ha1 hu))).abs
  have := hc.tendsto
  rwa [crossCos_upperEdge ha0 ha1, Real.arccos_one, dmu_zero, abs_zero] at this

theorem gam_tendsto_zero_lower : Tendsto (gam a) (𝓝 (lowerEdge a)) (𝓝 0) := by
  have hl : lowerEdge a ≠ 0 := (lowerEdge_pos ha0 ha1).ne'
  have hc : ContinuousAt (fun τ => |dmu a (Real.arccos (crossCos a τ))|) (lowerEdge a) :=
    ((continuous_dmu ha0 ha1).continuousAt.comp
      (Real.continuous_arccos.continuousAt.comp (continuousAt_crossCos ha0 ha1 hl))).abs
  have := hc.tendsto
  rwa [crossCos_lowerEdge ha0 ha1, Real.arccos_neg_one, dmu_pi, abs_zero] at this

lemma edges_lt : lowerEdge a < upperEdge a := by
  have := symbol_strict_bounds ha0 ha1 (show (1 : ℝ) ∈ Ioo 0 π from
    ⟨one_pos, by linarith [Real.two_le_pi]⟩)
  linarith [this.1, this.2]

/-- **Band-edge non-uniformity**: `C(a,τ) → +∞` as `τ ↑ μ₊`. -/
theorem Cint_tendsto_atTop_upper : Tendsto (Cint a) (𝓝[<] upperEdge a) atTop := by
  have hW : 0 < upperEdge a - lowerEdge a := by linarith [edges_lt ha0 ha1]
  have hM : Tendsto (Mband a) (𝓝[<] upperEdge a)
      (𝓝 (max (upperEdge a - upperEdge a) (upperEdge a - lowerEdge a))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    unfold Mband
    exact ((tendsto_const_nhds.sub tendsto_id).max (tendsto_id.sub tendsto_const_nhds))
  rw [sub_self, max_eq_right hW.le] at hM
  have hev : ∀ᶠ τ in 𝓝[<] upperEdge a, InteriorParam a τ := by
    have h1 : ∀ᶠ τ in 𝓝[<] upperEdge a, lowerEdge a < τ :=
      nhdsWithin_le_nhds (lt_mem_nhds (edges_lt ha0 ha1))
    filter_upwards [h1, self_mem_nhdsWithin] with τ hτ1 hτ2
    exact ⟨ha0, ha1, hτ1, hτ2⟩
  have hden : Tendsto (fun τ => π * gam a τ) (𝓝[<] upperEdge a) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := ((gam_tendsto_zero_upper ha0 ha1).mono_left
        (nhdsWithin_le_nhds (s := Iio (upperEdge a)))).const_mul π
      rwa [mul_zero] at this
    · filter_upwards [hev] with τ hτ
      exact mul_pos Real.pi_pos (gam_pos hτ)
  have := hM.pos_mul_atTop hW ((tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp hden)
  refine this.congr fun τ => ?_
  simp only [Function.comp_apply, Cint, div_eq_mul_inv]

/-- **Band-edge non-uniformity**: `C(a,τ) → +∞` as `τ ↓ μ₋`. -/
theorem Cint_tendsto_atTop_lower : Tendsto (Cint a) (𝓝[>] lowerEdge a) atTop := by
  have hW : 0 < upperEdge a - lowerEdge a := by linarith [edges_lt ha0 ha1]
  have hM : Tendsto (Mband a) (𝓝[>] lowerEdge a)
      (𝓝 (max (upperEdge a - lowerEdge a) (lowerEdge a - lowerEdge a))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    unfold Mband
    exact ((tendsto_const_nhds.sub tendsto_id).max (tendsto_id.sub tendsto_const_nhds))
  rw [sub_self, max_eq_left hW.le] at hM
  have hev : ∀ᶠ τ in 𝓝[>] lowerEdge a, InteriorParam a τ := by
    have h1 : ∀ᶠ τ in 𝓝[>] lowerEdge a, τ < upperEdge a :=
      nhdsWithin_le_nhds (gt_mem_nhds (edges_lt ha0 ha1))
    filter_upwards [h1, self_mem_nhdsWithin] with τ hτ1 hτ2
    exact ⟨ha0, ha1, hτ2, hτ1⟩
  have hden : Tendsto (fun τ => π * gam a τ) (𝓝[>] lowerEdge a) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := ((gam_tendsto_zero_lower ha0 ha1).mono_left
        (nhdsWithin_le_nhds (s := Ioi (lowerEdge a)))).const_mul π
      rwa [mul_zero] at this
    · filter_upwards [hev] with τ hτ
      exact mul_pos Real.pi_pos (gam_pos hτ)
  have := hM.pos_mul_atTop hW ((tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).comp hden)
  refine this.congr fun τ => ?_
  simp only [Function.comp_apply, Cint, div_eq_mul_inv]

end Edges

end ShiftedKMS
