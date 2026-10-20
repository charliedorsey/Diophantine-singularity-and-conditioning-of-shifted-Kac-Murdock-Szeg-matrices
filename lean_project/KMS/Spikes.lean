import KMS.IrrLaws
import KMS.Cassels

/-!
# Gate 5.3 – 5.4 — exceptional spikes and generic shifted conditioning

All `limsup`/`liminf` statements live in `ℝ≥0∞`, so `C/0 = +∞` is literal and a single isolated
singular dimension (where Lean's `κ₂ = σ_max/0 = 0`) is invisible to `limsup`/`liminf`
(finitely many indices never matter) — this is exactly the manuscript's "after deleting any
isolated exact singular dimension".

* `Mplus α β = liminf_{N→∞} N‖Nα - β‖` (eq. `(Mplus)`; positive `N`, nearest-integer `‖·‖`).
* `wplus α β = sup {w ≥ 0 : ‖Nα - β‖ < N^{-w} for infinitely many N ∈ ℕ}` (`def:wplus`).
* `thm_quadratic_envelope` (eq. `(quadratic-envelope)`): `limsup κ₂/N² = C/𝓜₊`.
* `thm_exponent` (eq. `(condexp)`): `limsup log κ₂ / log N = 1 + w₊`.
* `thm_generic` (eqs. `(genericM)`, `(genericcond)`): for a.e. `0 < β < 1 - α`,
  `𝓜₊ = 0`, `w₊ = 1`, `limsup log κ₂/log N = 2`, `limsup κ₂/N² = +∞`.
* `prop_affinecollapse_Mplus` (eq. `(Mhom)`): on an affine-hit line `𝓜₊(α, rα - m) = 𝓜₊(α, 0)`.
-/

open Real Set Filter Topology MeasureTheory Finset
open scoped ENNReal NNReal

namespace ShiftedKMS

/-! ### Definitions -/

/-- `𝓜₊(α,β) = liminf_{N→∞} N ‖Nα - β‖ ∈ [0, ∞]` (eq. `(Mplus)`). -/
noncomputable def Mplus (α β : ℝ) : ℝ≥0∞ :=
  liminf (fun N : ℕ => ENNReal.ofReal (N * distZ (N * α - β))) atTop

/-- `w₊(α,β) = sup {w ≥ 0 : ‖Nα - β‖ < N^{-w} for infinitely many N ∈ ℕ} ∈ [0, ∞]`
(`def:wplus`). -/
noncomputable def wplus (α β : ℝ) : ℝ≥0∞ :=
  ⨆ (w : ℝ≥0) (_ : ∃ᶠ N : ℕ in atTop, distZ (N * α - β) < (N : ℝ) ^ (-(w : ℝ))), (w : ℝ≥0∞)

/-- `log(1/‖Nα - β‖) / log N`. -/
noncomputable def logRatio (α β : ℝ) (N : ℕ) : ℝ := -Real.log (distZ (N * α - β)) / Real.log N

/-! ### ENNReal squeezing tools -/

lemma ennreal_le_of_forall_mul {a b : ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ ENNReal.ofReal (1 + ε) * b) : a ≤ b := by
  rcases eq_or_ne b ⊤ with hb | hb
  · rw [hb]; exact le_top
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  set t := b.toReal with ht
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  set ε := (δ : ℝ) / (t + 1) with hε
  have hε0 : 0 < ε := by positivity
  refine (h ε hε0).trans ?_
  rw [ENNReal.ofReal_add zero_le_one hε0.le, ENNReal.ofReal_one, add_mul, one_mul]
  gcongr
  rw [← ENNReal.ofReal_toReal hb, ← ht, ← ENNReal.ofReal_mul hε0.le, ← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- Two sequences that agree up to factors `1 + ε` eventually have the same `limsup`. -/
lemma limsup_eq_of_ratio {u v : ℕ → ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      u N ≤ ENNReal.ofReal (1 + ε) * v N ∧ v N ≤ ENNReal.ofReal (1 + ε) * u N) :
    limsup u atTop = limsup v atTop := by
  apply le_antisymm
  · refine ennreal_le_of_forall_mul fun ε hε => ?_
    rw [← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
    exact limsup_le_limsup ((h ε hε).mono fun N hN => hN.1)
  · refine ennreal_le_of_forall_mul fun ε hε => ?_
    rw [← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
    exact limsup_le_limsup ((h ε hε).mono fun N hN => hN.2)

/-- Same for `liminf`. -/
lemma liminf_eq_of_ratio {u v : ℕ → ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      u N ≤ ENNReal.ofReal (1 + ε) * v N ∧ v N ≤ ENNReal.ofReal (1 + ε) * u N) :
    liminf u atTop = liminf v atTop := by
  apply le_antisymm
  · refine ennreal_le_of_forall_mul fun ε hε => ?_
    rw [← ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top]
    exact liminf_le_liminf ((h ε hε).mono fun N hN => hN.1)
  · refine ennreal_le_of_forall_mul fun ε hε => ?_
    rw [← ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top]
    exact liminf_le_liminf ((h ε hε).mono fun N hN => hN.2)

/-! ### Arithmetic facts about `d_N = ‖Nα - β‖` -/

/-- For irrational `α`, at most one `N` has `‖Nα - β‖ = 0`; hence eventually `d_N > 0`. -/
lemma eventually_distZ_pos {α : ℝ} (hα : Irrational α) (β : ℝ) :
    ∀ᶠ N : ℕ in atTop, 0 < distZ (N * α - β) := by
  by_cases hex : ∃ N₀ : ℕ, distZ (N₀ * α - β) = 0
  · obtain ⟨N₀, hN₀⟩ := hex
    filter_upwards [eventually_gt_atTop N₀] with N hN
    rcases (distZ_nonneg (N * α - β)).lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨z₁, hz₁⟩ := (distZ_eq_zero_iff _).1 h.symm
      obtain ⟨z₀, hz₀⟩ := (distZ_eq_zero_iff _).1 hN₀
      apply hα.ne_rat ((z₁ - z₀ : ℤ) / ((N - N₀ : ℕ) : ℤ) : ℚ)
      have hNN : ((N - N₀ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : N - N₀ ≠ 0)
      rw [Nat.cast_sub hN.le] at hNN
      push_cast
      rw [Nat.cast_sub hN.le]
      field_simp
      linarith
  · push Not at hex
    exact Eventually.of_forall fun N =>
      lt_of_le_of_ne (distZ_nonneg _) (hex N).symm

lemma logRatio_gt_iff {α β : ℝ} {N : ℕ} (hN : 2 ≤ N) (hd : 0 < distZ (N * α - β)) (w : ℝ) :
    w < logRatio α β N ↔ distZ (N * α - β) < (N : ℝ) ^ (-w) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos hNr
  rw [logRatio, lt_div_iff₀ hlog, ← Real.log_lt_log_iff hd (by positivity),
    Real.log_rpow (by linarith)]
  constructor <;> intro h <;> linarith

lemma logRatio_nonneg {α β : ℝ} (N : ℕ) : 0 ≤ logRatio α β N := by
  unfold logRatio
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N <;> simp only [Nat.cast_zero, Nat.cast_one, Real.log_zero, Real.log_one,
      div_zero, le_refl]
  · have hNr : (1 : ℝ) < N := by exact_mod_cast hN
    apply div_nonneg _ (Real.log_pos hNr).le
    rcases (distZ_nonneg (N * α - β)).lt_or_eq with hd | hd
    · have := Real.log_nonpos hd.le ((distZ_le_half _).trans (by norm_num))
      linarith
    · rw [← hd, Real.log_zero, neg_zero]

/-- `limsup log(1/d_N)/log N = w₊` (the definition of `w₊` read as a `limsup`). -/
theorem limsup_logRatio_eq_wplus {α : ℝ} (hα : Irrational α) (β : ℝ) :
    limsup (fun N => ENNReal.ofReal (logRatio α β N)) atTop = wplus α β := by
  have hev : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ 0 < distZ (N * α - β) :=
    (eventually_ge_atTop 2).and (eventually_distZ_pos hα β)
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc
    refine le_trans ?_ hr2.le
    apply limsup_le_of_le (by isBoundedDefault)
    by_contra hcon
    rw [not_eventually] at hcon
    have hfr : ∃ᶠ N : ℕ in atTop, distZ (N * α - β) < (N : ℝ) ^ (-(r : ℝ)) := by
      refine (hcon.and_eventually hev).mono fun N ⟨h1, h2, h3⟩ => ?_
      rw [← logRatio_gt_iff h2 h3]
      push Not at h1
      have : (r : ℝ≥0∞) = ENNReal.ofReal r := (ENNReal.ofReal_coe_nnreal).symm
      rw [this] at h1
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1 h1
    have : (r : ℝ≥0∞) ≤ wplus α β := le_iSup₂ (f := fun (w : ℝ≥0) (_ : ∃ᶠ N : ℕ in atTop,
      distZ (N * α - β) < (N : ℝ) ^ (-(w : ℝ))) => (w : ℝ≥0∞)) r hfr
    exact absurd hr1 (not_lt.2 this)
  · refine iSup₂_le fun w hw => ?_
    apply le_limsup_of_frequently_le _ (by isBoundedDefault)
    refine (hw.and_eventually hev).mono fun N ⟨h1, h2, h3⟩ => ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal ((logRatio_gt_iff h2 h3 w).2 h1).le

/-! ### G5.3 — quadratic envelope and conditioning exponent -/

section Spikes

variable {a τ : ℝ}

lemma dN_eq_distZ (N : ℕ) : dN N a τ = distZ (N * alphaOf a τ - betaOf a τ) := rfl

/-- For nonsingular `N ≥ n₂`, the two-sided relative bound for `κ₂`. -/
lemma kappa_bounds (h : InteriorParam a τ) {N : ℕ} (hN : n2 a τ ≤ N) (hns : Nonsingular N a τ) :
    (1 - Kkap a τ / N) * (Cint a τ * (N + τ) / dN N a τ) ≤ kappa N a τ ∧
      kappa N a τ ≤ (1 + Kkap a τ / N) * (Cint a τ * (N + τ) / dN N a τ) :=
  thm_kappa_relative h hN hns

lemma eventually_nonsingular (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    ∀ᶠ N : ℕ in atTop, Nonsingular N a τ ∧ 0 < dN N a τ := by
  filter_upwards [eventually_distZ_pos hα (betaOf a τ), eventually_ge_atTop 2] with N hd hN
  refine ⟨fun hdet => ?_, hd⟩
  rw [thm_sing_dN h hN] at hdet
  exact hd.ne' hdet

/-- **`thm:quadratic-envelope`**: for irrational `α`, `limsup κ₂(B_N)/N² = C/𝓜₊(α,β)`
(in `ℝ≥0∞`, so `C/0 = +∞`). -/
theorem thm_quadratic_envelope (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    limsup (fun N : ℕ => ENNReal.ofReal (kappa N a τ / (N : ℝ) ^ 2)) atTop =
      ENNReal.ofReal (Cint a τ) / Mplus (alphaOf a τ) (betaOf a τ) := by
  have hτ := h.tau_pos
  have hC := Cint_pos h
  have hK := Kkap_nonneg h
  set C := Cint a τ
  set K := Kkap a τ
  -- comparison sequence `C / (N d_N)`
  have hv : limsup (fun N : ℕ => ENNReal.ofReal C / ENNReal.ofReal (N * dN N a τ)) atTop =
      ENNReal.ofReal C / Mplus (alphaOf a τ) (betaOf a τ) := by
    simp only [div_eq_mul_inv]
    rw [ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top, ← ENNReal.inv_liminf]
    rfl
  rw [← hv]
  apply limsup_eq_of_ratio
  intro ε hε
  -- eventually `(1 - K/N)(1) ≥ 1/(1+ε)` and `(1 + K/N)(1 + τ/N) ≤ 1 + ε`
  have hsmall : Tendsto (fun N : ℕ => (K + τ + K * τ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsmall2 : Tendsto (fun N : ℕ => K / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hδ : 0 < ε / (2 * (1 + ε)) := by positivity
  filter_upwards [eventually_nonsingular h hα, eventually_ge_atTop (n2 a τ + 1),
    hsmall.eventually (ge_mem_nhds hε), hsmall2.eventually (ge_mem_nhds hδ)]
    with N ⟨hns, hd⟩ hN hs1 hs2
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨lo, hi⟩ := kappa_bounds h (by omega : n2 a τ ≤ N) hns
  set d := dN N a τ
  set Q := C * (N + τ) / d with hQ
  -- `κ/N² = λ · C/(N d)` with `λ ∈ [1 - K/N, (1 + K/N)(1 + τ/N)]`
  have hval : ENNReal.ofReal C / ENNReal.ofReal (N * d) = ENNReal.ofReal (C / (N * d)) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
  rw [hval]
  have hK1 : K / N ≤ ε / (2 * (1 + ε)) := hs2
  have hKlt : K / N < 1 := by
    have : ε / (2 * (1 + ε)) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  have hupper : kappa N a τ / (N : ℝ) ^ 2 ≤ (1 + ε) * (C / (N * d)) := by
    have e : (1 + K / N) * Q / (N : ℝ) ^ 2 = (1 + K / N) * (1 + τ / N) * (C / (N * d)) := by
      rw [hQ]; field_simp
    have h1 : (1 + K / N) * (1 + τ / N) ≤ 1 + ε := by
      have : (1 + K / N) * (1 + τ / N) = 1 + (K + τ + K * τ / N) / N := by field_simp; ring
      rw [this]
      have : K * τ / N ≤ K * τ := div_le_self (by positivity) hNr
      have : (K + τ + K * τ / N) / N ≤ (K + τ + K * τ) / N :=
        div_le_div_of_nonneg_right (by linarith) hN0.le
      linarith
    calc kappa N a τ / (N : ℝ) ^ 2 ≤ (1 + K / N) * Q / (N : ℝ) ^ 2 := by gcongr
      _ = (1 + K / N) * (1 + τ / N) * (C / (N * d)) := e
      _ ≤ (1 + ε) * (C / (N * d)) := by gcongr
  have hlower : C / (N * d) ≤ (1 + ε) * (kappa N a τ / (N : ℝ) ^ 2) := by
    have e : (1 - K / N) * Q / (N : ℝ) ^ 2 = (1 - K / N) * (1 + τ / N) * (C / (N * d)) := by
      rw [hQ]; field_simp
    have hb : (1 - K / N) * (C / (N * d)) ≤ kappa N a τ / (N : ℝ) ^ 2 := by
      calc (1 - K / N) * (C / (N * d)) ≤ (1 - K / N) * (1 + τ / N) * (C / (N * d)) := by
            have : 0 ≤ (1 - K / N) * (C / (N * d)) := mul_nonneg (by linarith) (by positivity)
            have : 0 ≤ τ / N := by positivity
            nlinarith
        _ = (1 - K / N) * Q / (N : ℝ) ^ 2 := e.symm
        _ ≤ kappa N a τ / (N : ℝ) ^ 2 := by gcongr
    have hc : 1 ≤ (1 + ε) * (1 - K / N) := by
      have : (1 + ε) * (K / N) ≤ ε / 2 := by
        calc (1 + ε) * (K / N) ≤ (1 + ε) * (ε / (2 * (1 + ε))) := by gcongr
          _ = ε / 2 := by field_simp
      nlinarith
    have hCd : 0 ≤ C / (N * d) := by positivity
    calc C / (N * d) ≤ (1 + ε) * (1 - K / N) * (C / (N * d)) := by nlinarith
      _ = (1 + ε) * ((1 - K / N) * (C / (N * d))) := by ring
      _ ≤ (1 + ε) * (kappa N a τ / (N : ℝ) ^ 2) := by gcongr
  constructor
  · rw [← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal hupper
  · rw [← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal hlower

/-- **`thm:exponent`**: for irrational `α`, `limsup log κ₂(B_N) / log N = 1 + w₊(α,β)`. -/
theorem thm_exponent (h : InteriorParam a τ) (hα : Irrational (alphaOf a τ)) :
    limsup (fun N : ℕ => ENNReal.ofReal (Real.log (kappa N a τ) / Real.log N)) atTop =
      1 + wplus (alphaOf a τ) (betaOf a τ) := by
  have hτ := h.tau_pos
  have hC := Cint_pos h
  have hK := Kkap_nonneg h
  set C := Cint a τ
  set K := Kkap a τ
  set α := alphaOf a τ
  set β := betaOf a τ
  rw [← limsup_logRatio_eq_wplus hα β]
  set B := Real.log 2 + |Real.log C| + Real.log (1 + τ) with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Real.log (1 + τ) := Real.log_nonneg (by linarith)
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have := abs_nonneg (Real.log C)
    linarith
  -- key estimate: `|log κ / log N - 1 - logRatio| ≤ B / log N` eventually
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hBl : Tendsto (fun N : ℕ => B / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogN
  have hKN : Tendsto (fun N : ℕ => K / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hest : ∀ᶠ N : ℕ in atTop,
      |Real.log (kappa N a τ) / Real.log N - 1 - logRatio α β N| ≤ B / Real.log N := by
    filter_upwards [eventually_nonsingular h hα, eventually_ge_atTop (n2 a τ + 2),
      hKN.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with N ⟨hns, hd⟩ hN hKN2
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
    have hN0 : (0 : ℝ) < N := by linarith
    have hlog : 0 < Real.log N := Real.log_pos (by linarith)
    obtain ⟨lo, hi⟩ := kappa_bounds h (by omega : n2 a τ ≤ N) hns
    set d := dN N a τ
    have hd' : d = distZ (N * α - β) := rfl
    set Q := C * (N + τ) / d with hQ
    have hQ0 : 0 < Q := by positivity
    have hlam1 : (1 / 2 : ℝ) ≤ 1 - K / N := by linarith
    have hlam2 : 1 + K / N ≤ 2 := by linarith
    have hκ0 : 0 < kappa N a τ := lt_of_lt_of_le (by positivity) lo
    -- `log κ` between `log(Q/2)` and `log(2Q)`
    have hl1 : Real.log Q - Real.log 2 ≤ Real.log (kappa N a τ) := by
      rw [← Real.log_div hQ0.ne' (by norm_num)]
      apply Real.log_le_log (by positivity)
      calc Q / 2 = (1 / 2) * Q := by ring
        _ ≤ (1 - K / N) * Q := by gcongr
        _ ≤ kappa N a τ := lo
    have hl2 : Real.log (kappa N a τ) ≤ Real.log Q + Real.log 2 := by
      rw [← Real.log_mul hQ0.ne' (by norm_num)]
      apply Real.log_le_log hκ0
      calc kappa N a τ ≤ (1 + K / N) * Q := hi
        _ ≤ 2 * Q := by gcongr
        _ = Q * 2 := by ring
    -- `log Q = log C + log (N + τ) - log d`, with `log N ≤ log (N+τ) ≤ log N + log (1+τ)`
    have hlQ : Real.log Q = Real.log C + Real.log (N + τ) - Real.log d := by
      rw [hQ, Real.log_div (by positivity) hd.ne', Real.log_mul hC.ne' (by positivity)]
    have hNτ1 : Real.log N ≤ Real.log (N + τ) := Real.log_le_log hN0 (by linarith)
    have hNτ2 : Real.log (N + τ) ≤ Real.log N + Real.log (1 + τ) := by
      rw [← Real.log_mul hN0.ne' (by positivity)]
      apply Real.log_le_log (by positivity)
      nlinarith
    have hCabs := abs_le.1 (le_refl |Real.log C|)
    have hr : logRatio α β N * Real.log N = -Real.log d := by
      rw [logRatio, ← hd']; field_simp
    have hX : (Real.log (kappa N a τ) / Real.log N - 1 - logRatio α β N) * Real.log N =
        Real.log (kappa N a τ) - Real.log N + Real.log d := by
      rw [sub_mul, sub_mul, div_mul_cancel₀ _ hlog.ne', hr]; ring
    have hXb : |Real.log (kappa N a τ) - Real.log N + Real.log d| ≤ B := by
      have h1τ : 0 ≤ Real.log (1 + τ) := Real.log_nonneg (by linarith)
      rw [abs_le]; constructor <;>
        linarith [le_abs_self (Real.log C), neg_abs_le (Real.log C)]
    rw [← hX, abs_mul, abs_of_pos hlog] at hXb
    rwa [le_div_iff₀ hlog]
  -- conclude in `ℝ≥0∞`
  apply le_antisymm
  · -- `limsup ≤ 1 + E`
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
    have hev : ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (Real.log (kappa N a τ) / Real.log N) ≤
        (1 + (ε : ℝ≥0∞)) + ENNReal.ofReal (logRatio α β N) := by
      filter_upwards [hest, hBl.eventually (ge_mem_nhds hεr)] with N h1 h2
      have := (abs_le.1 h1).2
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add zero_le_one hεr.le,
        ← ENNReal.ofReal_add (by linarith) (logRatio_nonneg N)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    calc limsup (fun N : ℕ => ENNReal.ofReal (Real.log (kappa N a τ) / Real.log N)) atTop
        ≤ limsup (fun N : ℕ => (1 + (ε : ℝ≥0∞)) + ENNReal.ofReal (logRatio α β N)) atTop :=
          limsup_le_limsup hev
      _ = (1 + (ε : ℝ≥0∞)) + limsup (fun N : ℕ => ENNReal.ofReal (logRatio α β N)) atTop :=
          limsup_const_add (F := atTop) _ _ (by isBoundedDefault) (by isBoundedDefault)
      _ = 1 + limsup (fun N : ℕ => ENNReal.ofReal (logRatio α β N)) atTop + ε := by ring
  · -- `1 + E ≤ limsup`
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
    set ε1 := min (ε : ℝ) 1 with hε1
    have hε10 : 0 < ε1 := lt_min hεr one_pos
    have hev : ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (1 - ε1) + ENNReal.ofReal (logRatio α β N) ≤
        ENNReal.ofReal (Real.log (kappa N a τ) / Real.log N) := by
      filter_upwards [hest, hBl.eventually (ge_mem_nhds hε10)] with N h1 h2
      have := (abs_le.1 h1).1
      rw [← ENNReal.ofReal_add (by linarith [min_le_right (ε : ℝ) 1]) (logRatio_nonneg N)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hlim : ENNReal.ofReal (1 - ε1) + limsup (fun N : ℕ => ENNReal.ofReal (logRatio α β N)) atTop
        ≤ limsup (fun N : ℕ => ENNReal.ofReal (Real.log (kappa N a τ) / Real.log N)) atTop := by
      rw [← limsup_const_add (F := atTop) _ _ (by isBoundedDefault) (by isBoundedDefault)]
      exact limsup_le_limsup hev
    calc 1 + limsup (fun N : ℕ => ENNReal.ofReal (logRatio α β N)) atTop
        ≤ (ENNReal.ofReal (1 - ε1) + ε) +
            limsup (fun N : ℕ => ENNReal.ofReal (logRatio α β N)) atTop := by
          gcongr
          rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (by linarith [min_le_right (ε : ℝ) 1])
            hεr.le, ← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          linarith [min_le_left (ε : ℝ) 1]
      _ = (ENNReal.ofReal (1 - ε1) +
            limsup (fun N : ℕ => ENNReal.ofReal (logRatio α β N)) atTop) + ε := by ring
      _ ≤ _ := by gcongr

end Spikes

/-! ### G5.4 — generic shifted conditioning -/

/-- For irrational `α` and a.e. `β ∈ ℝ`: `𝓜₊(α, β) = 0` (Cassels, all `c = 1/(j+1)`). -/
theorem ae_Mplus_eq_zero {α : ℝ} (hα : Irrational α) : ∀ᵐ β : ℝ, Mplus α β = 0 := by
  have h : ∀ j : ℕ, ∀ᵐ β : ℝ, ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * distZ (N * α - β) < 1 / (j + 1) := fun j =>
    casselsSupplier α hα _ (by positivity)
  rw [← ae_all_iff] at h
  filter_upwards [h] with β hβ
  refine le_antisymm ?_ (by positivity)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  rw [zero_add]
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε by exact_mod_cast hε)
  apply liminf_le_of_frequently_le' ((hβ j).mono fun N hN => ?_)
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- For irrational `α` and a.e. `β ∈ ℝ`: `w₊(α, β) = 1` (Borel–Cantelli for `≤`, Cassels with
`c = 1` for `≥`). -/
theorem ae_wplus_eq_one {α : ℝ} (hα : Irrational α) : ∀ᵐ β : ℝ, wplus α β = 1 := by
  have hBC : ∀ j : ℕ, ∀ᵐ β : ℝ, ∀ᶠ N : ℕ in atTop,
      ¬ distZ (N * α - β) < (N : ℝ) ^ (-(1 + 1 / ((j : ℝ) + 1))) := fun j =>
    ae_eventually_not_lt_rpow α (by positivity)
  rw [← ae_all_iff] at hBC
  filter_upwards [hBC, casselsSupplier α hα 1 one_pos] with β hβ hC
  apply le_antisymm
  · refine iSup₂_le fun w hw => ?_
    by_contra hlt
    push Not at hlt
    have hw1 : (1 : ℝ) < w := by exact_mod_cast hlt
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show (0 : ℝ) < w - 1 by linarith)
    apply (hw.and_eventually ((hβ j).and (eventually_ge_atTop 1))).exists.elim
    rintro N ⟨h1, h2, hN⟩
    apply h2
    refine lt_of_lt_of_le h1 ?_
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    apply Real.rpow_le_rpow_of_exponent_le hNr
    linarith
  · have hmem : ∃ᶠ N : ℕ in atTop, distZ (N * α - β) < (N : ℝ) ^ (-((1 : ℝ≥0) : ℝ)) := by
      refine (hC.and_eventually (eventually_ge_atTop 1)).mono fun N ⟨h1, hN⟩ => ?_
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      rw [NNReal.coe_one, Real.rpow_neg_one, ← one_div, lt_div_iff₀ hNr, mul_comm]
      exact h1
    have := le_iSup₂ (f := fun (w : ℝ≥0) (_ : ∃ᶠ N : ℕ in atTop,
      distZ (N * α - β) < (N : ℝ) ^ (-(w : ℝ))) => (w : ℝ≥0∞)) 1 hmem
    unfold wplus
    simpa only [ENNReal.coe_one] using this

/-- **`thm:generic`**: fix irrational `α > 0` (the target interval is empty unless `α < 1`). For Lebesgue-a.e. target `0 < β < 1 - α`, with
`(a, τ)` the interior pair of `(α, β)` (eq. `(inverse)`):
`𝓜₊(α,β) = 0`, `w₊(α,β) = 1`, `limsup log κ₂/log N = 2`, `limsup κ₂/N² = +∞`. -/
theorem thm_generic {α : ℝ} (hα : Irrational α) (hα0 : 0 < α) :
    ∀ᵐ β : ℝ, β ∈ Ioo 0 (1 - α) →
      Mplus α β = 0 ∧ wplus α β = 1 ∧
      limsup (fun N : ℕ => ENNReal.ofReal
        (Real.log (kappa N (aOf α β) (tauOf α β)) / Real.log N)) atTop = 2 ∧
      limsup (fun N : ℕ => ENNReal.ofReal
        (kappa N (aOf α β) (tauOf α β) / (N : ℝ) ^ 2)) atTop = ⊤ := by
  filter_upwards [ae_Mplus_eq_zero hα, ae_wplus_eq_one hα] with β hM hw hβ
  obtain ⟨hint, hαe, hβe⟩ := triangle_inverse (α := α) (β := β)
    ⟨hα0, hβ.1, by linarith [hβ.2]⟩
  have hαi : Irrational (alphaOf (aOf α β) (tauOf α β)) := by rwa [hαe]
  refine ⟨hM, hw, ?_, ?_⟩
  · rw [thm_exponent hint hαi, hαe, hβe, hw]; norm_num
  · rw [thm_quadratic_envelope hint hαi, hαe, hβe, hM]
    exact ENNReal.div_zero (ENNReal.ofReal_pos.2 (Cint_pos hint)).ne'

/-- **`prop:affinecollapse`, eq. `(Mhom)`** (the clause deferred from Gate 03): on an affine-hit
line `β = rα - m`, `𝓜₊(α, β) = liminf_{q→∞} q‖qα‖ = 𝓜₊(α, 0)`. -/
theorem prop_affinecollapse_Mplus (α : ℝ) (r : ℕ) (m : ℤ) :
    Mplus α (r * α - m) = Mplus α 0 := by
  unfold Mplus
  have hshift : ∀ N : ℕ, distZ ((N + r : ℕ) * α - (r * α - m)) = distZ (N * α - 0) := by
    intro N
    rw [show ((N + r : ℕ) : ℝ) * α - (r * α - m) = (N * α - 0) + m by push_cast; ring,
      distZ_add_int]
  rw [← liminf_nat_add _ r]
  simp only [hshift]
  apply liminf_eq_of_ratio
  intro ε hε
  have hr : Tendsto (fun N : ℕ => (r : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hr.eventually (ge_mem_nhds hε), eventually_ge_atTop 1] with N hN hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hd := distZ_nonneg (N * α - 0)
  constructor
  · rw [← ENNReal.ofReal_mul (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    have : ((N + r : ℕ) : ℝ) ≤ (1 + ε) * N := by
      push_cast
      rw [div_le_iff₀ hNr] at hN
      linarith
    nlinarith
  · rw [← ENNReal.ofReal_mul (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (N : ℝ) ≤ ((N + r : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right N r
    have h2 := mul_le_mul_of_nonneg_right h1 hd
    have h3 : 0 ≤ ε * (((N + r : ℕ) : ℝ) * distZ (N * α - 0)) := by positivity
    nlinarith

end ShiftedKMS
