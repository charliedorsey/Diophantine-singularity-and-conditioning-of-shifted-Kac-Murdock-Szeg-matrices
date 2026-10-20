import KMS.Cond

/-!
# Gate 4.3 – 4.5 — σ_max, interior κ, outside the band, and the band edges

* G4.3: `thm_smax_general`, `thm_smax` (eq. `(smax)`), `thm_kappa_relative` (eq. `(kappa)`).
* G4.4: `thm_outside_lower`, `thm_outside_upper` (eqs. `(outside-lower)`, `(outside-upper)`):
  strict uniform bound and the limit.
* G4.5: `thm_edge_upper_smin`, `thm_edge_upper_kappa`, `thm_edge_lower_smin`,
  `thm_edge_lower_kappa` (eqs. `(edge-up-smin)`, `(edge-up-kappa)`, `(edge-low-smin)`,
  `(edge-low-kappa)`) with exact constants and RELATIVE `O(N^{-2})` remainders.
-/

open Real Set Filter Topology

namespace ShiftedKMS

section General

variable {a : ℝ}

/-! ### Extreme eigenangles and the symbol near `0`, `π` -/

lemma angle_bounds_general (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) (x y : ℝ) :
    |Gph N a x - Gph N a y| / (N + upperEdge a) ≤ |x - y| ∧
      |x - y| ≤ |Gph N a x - Gph N a y| / (N + lowerEdge a) := by
  obtain ⟨ξ, -, hξ⟩ := mvt_between (hasDerivAt_Gph ha0 ha1 N) x y
  have hlo := lowerEdge_le_symbol ha0 ha1 ξ
  have hhi := symbol_le_upperEdge ha0 ha1 ξ
  have hl0 := lowerEdge_pos ha0 ha1
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [hξ, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < N + symbol a ξ)]
  have hu := abs_nonneg (x - y)
  constructor
  · rw [div_le_iff₀ (by linarith)]; nlinarith
  · rw [le_div_iff₀ (by linarith)]; nlinarith

lemma theta1_bounds (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 1 ≤ N) :
    π / (N + upperEdge a) ≤ eigAngle N a 1 ∧ eigAngle N a 1 ≤ π / (N + lowerEdge a) := by
  have hs := eigAngle_spec ha0 ha1 le_rfl hN
  have hb := angle_bounds_general ha0 ha1 N (eigAngle N a 1) 0
  rw [hs.2, Gph_zero, sub_zero, Nat.cast_one, one_mul, abs_of_pos Real.pi_pos, sub_zero,
    abs_of_pos hs.1.1] at hb
  exact hb

lemma thetaN_bounds (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 1 ≤ N) :
    π / (N + upperEdge a) ≤ π - eigAngle N a N ∧ π - eigAngle N a N ≤ π / (N + lowerEdge a) := by
  have hs := eigAngle_spec ha0 ha1 hN le_rfl
  have hb := angle_bounds_general ha0 ha1 N π (eigAngle N a N)
  rw [hs.2, Gph_pi, show ((N : ℝ) + 1) * π - N * π = π by ring, abs_of_pos Real.pi_pos,
    abs_of_pos (by linarith [hs.1.2])] at hb
  exact hb

lemma symbol_zero (ha1 : a < 1) : symbol a 0 = upperEdge a := by
  have h1 : (1 - a) ≠ 0 := by intro h; linarith
  unfold symbol upperEdge
  rw [Real.cos_zero, show (1 : ℝ) - 2 * a * 1 + a ^ 2 = (1 - a) ^ 2 by ring]
  field_simp
  ring

lemma symbol_pi (ha0 : 0 < a) : symbol a π = lowerEdge a := by
  have h1 : (1 + a) ≠ 0 := by positivity
  unfold symbol lowerEdge
  rw [Real.cos_pi, show (1 : ℝ) - 2 * a * -1 + a ^ 2 = (1 + a) ^ 2 by ring]
  field_simp
  ring

lemma dmu_zero (a : ℝ) : dmu a 0 = 0 := by simp only [dmu, sin_zero, mul_zero, neg_zero, zero_div]
lemma dmu_pi (a : ℝ) : dmu a π = 0 := by simp only [dmu, sin_pi, mul_zero, neg_zero, zero_div]

/-- `|μ_a(θ) - μ₊| ≤ L₂ θ²`. -/
lemma symbol_near_zero (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    |symbol a θ - upperEdge a| ≤ L2mu a * θ ^ 2 := by
  obtain ⟨c, hc, hmvt⟩ := mvt_between (hasDerivAt_symbol ha0 ha1) θ 0
  rw [← symbol_zero ha1, hmvt, abs_mul, sub_zero]
  have h1 : |dmu a c| ≤ L2mu a * |c| := by
    have := dmu_lipschitz ha0 ha1 c 0
    rwa [dmu_zero, sub_zero, sub_zero] at this
  rw [sub_zero, sub_zero] at hc
  have hL := L2mu_nonneg ha0 ha1
  calc |dmu a c| * |θ| ≤ L2mu a * |c| * |θ| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ L2mu a * |θ| * |θ| := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hL) (abs_nonneg _)
    _ = L2mu a * θ ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- `|μ_a(θ) - μ₋| ≤ L₂ (π - θ)²`. -/
lemma symbol_near_pi (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    |symbol a θ - lowerEdge a| ≤ L2mu a * (π - θ) ^ 2 := by
  obtain ⟨c, hc, hmvt⟩ := mvt_between (hasDerivAt_symbol ha0 ha1) θ π
  rw [← symbol_pi ha0, hmvt, abs_mul]
  have h1 : |dmu a c| ≤ L2mu a * |c - π| := by
    have := dmu_lipschitz ha0 ha1 c π
    rwa [dmu_pi, sub_zero] at this
  have hL := L2mu_nonneg ha0 ha1
  calc |dmu a c| * |θ - π| ≤ L2mu a * |c - π| * |θ - π| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ ≤ L2mu a * |θ - π| * |θ - π| := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hL) (abs_nonneg _)
    _ = L2mu a * (π - θ) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]; ring

/-! ### Ordering of the eigenvalues -/

lemma lam_anti (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (τ : ℝ) {k l : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l)
    (hl : l ≤ N) : lam N a τ l ≤ lam N a τ k := by
  unfold lam
  have hanti := symbol_strictAntiOn ha0 ha1
  have mk := (eigAngle_spec (N := N) ha0 ha1 hk (by omega)).1
  have ml := (eigAngle_spec (N := N) ha0 ha1 (by omega) hl).1
  rcases hkl.lt_or_eq with h | h
  · have := hanti ⟨mk.1.le, mk.2.le⟩ ⟨ml.1.le, ml.2.le⟩ (eigAngle_lt ha0 ha1 hk h hl)
    linarith
  · rw [h]

/-- `σ_max = max(|λ_1|, |λ_N|)`. -/
lemma sigmaMax_eq (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    sigmaMax N a τ = max |lam N a τ 1| |lam N a τ N| := by
  apply le_antisymm
  · apply sigmaMax_le hN
    intro k hk1 hkN
    rw [max_comm]
    exact abs_le_max_abs_abs (lam_anti ha0 ha1 τ hk1 hkN le_rfl)
      (lam_anti ha0 ha1 τ le_rfl hk1 hkN)
  · exact max_le (le_sigmaMax a τ le_rfl hN) (le_sigmaMax a τ hN le_rfl)

/-- `σ_min = |λ_N|` when all eigenvalues are `≥ 0`. -/
lemma sigmaMin_eq_last (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ}
    (hpos : 0 ≤ lam N a τ N) : sigmaMin N a τ = lam N a τ N := by
  apply le_antisymm
  · have := sigmaMin_le (N := N) a τ hN le_rfl; rwa [abs_of_nonneg hpos] at this
  · apply le_sigmaMin hN
    intro k hk1 hkN
    have := lam_anti ha0 ha1 τ hk1 hkN le_rfl
    rw [abs_of_nonneg (by linarith)]; exact this

/-- `σ_min = -λ_1` when all eigenvalues are `≤ 0`. -/
lemma sigmaMin_eq_first (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ}
    (hneg : lam N a τ 1 ≤ 0) : sigmaMin N a τ = -lam N a τ 1 := by
  apply le_antisymm
  · have := sigmaMin_le (N := N) a τ le_rfl hN; rwa [abs_of_nonpos hneg] at this
  · apply le_sigmaMin hN
    intro k hk1 hkN
    have := lam_anti ha0 ha1 τ le_rfl hk1 hkN
    rw [abs_of_nonpos (by linarith)]; linarith

/-! ### G4.3 — σ_max -/

/-- `|σ_max - max(|μ₊ - τ|, |μ₋ - τ|)| ≤ L₂ π²/N²` for every real `τ`. -/
theorem thm_smax_general (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    |sigmaMax N a τ - max (|upperEdge a - τ|) (|lowerEdge a - τ|)| ≤ L2mu a * π ^ 2 / N ^ 2 := by
  rw [sigmaMax_eq ha0 ha1 hN]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hl0 := lowerEdge_pos ha0 ha1
  have hL := L2mu_nonneg ha0 ha1
  have b1 : |lam N a τ 1 - (upperEdge a - τ)| ≤ L2mu a * π ^ 2 / N ^ 2 := by
    rw [show lam N a τ 1 - (upperEdge a - τ) = symbol a (eigAngle N a 1) - upperEdge a by
      unfold lam; ring]
    refine (symbol_near_zero ha0 ha1 _).trans ?_
    obtain ⟨-, hθ⟩ := theta1_bounds ha0 ha1 hN
    have hθ0 := (eigAngle_spec ha0 ha1 le_rfl hN).1.1
    have : eigAngle N a 1 ≤ π / N :=
      hθ.trans (div_le_div_of_nonneg_left Real.pi_pos.le hNr (by linarith))
    rw [mul_div_assoc, ← div_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hθ0.le this 2) hL
  have b2 : |lam N a τ N - (lowerEdge a - τ)| ≤ L2mu a * π ^ 2 / N ^ 2 := by
    rw [show lam N a τ N - (lowerEdge a - τ) = symbol a (eigAngle N a N) - lowerEdge a by
      unfold lam; ring]
    refine (symbol_near_pi ha0 ha1 _).trans ?_
    obtain ⟨-, hθ⟩ := thetaN_bounds ha0 ha1 hN
    have hθ0 := (eigAngle_spec ha0 ha1 hN le_rfl).1.2
    have : π - eigAngle N a N ≤ π / N :=
      hθ.trans (div_le_div_of_nonneg_left Real.pi_pos.le hNr (by linarith))
    rw [mul_div_assoc, ← div_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) this 2) hL
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · exact (abs_abs_sub_abs_le_abs_sub _ _).trans b1
  · exact (abs_abs_sub_abs_le_abs_sub _ _).trans b2

end General

section InteriorKappa

variable {a τ : ℝ}

/-- `M(a,τ) = max{μ₊ - τ, τ - μ₋}`, manuscript eq. `(M)`. -/
noncomputable def Mband (a τ : ℝ) : ℝ := max (upperEdge a - τ) (τ - lowerEdge a)

/-- `C(a,τ) = M/(πγ)`, manuscript eq. `(C)`. -/
noncomputable def Cint (a τ : ℝ) : ℝ := Mband a τ / (π * gam a τ)

lemma Mband_pos (h : InteriorParam a τ) : 0 < Mband a τ :=
  lt_of_lt_of_le (by linarith [h.2.2.2]) (le_max_left _ _)

/-- **eq. `(smax)`**: for interior `(a,τ)`, `|σ_max - M| ≤ L₂π²/N²` for all `N ≥ 1`. -/
theorem thm_smax (h : InteriorParam a τ) {N : ℕ} (hN : 1 ≤ N) :
    |sigmaMax N a τ - Mband a τ| ≤ L2mu a * π ^ 2 / N ^ 2 := by
  have e : Mband a τ = max |upperEdge a - τ| |lowerEdge a - τ| := by
    unfold Mband
    rw [abs_of_pos (by linarith [h.2.2.2]), abs_of_neg (by linarith [h.2.2.1])]
    congr 1; ring
  rw [e]; exact thm_smax_general h.1 h.2.1 hN τ

/-- Constant of the interior κ law. -/
noncomputable def Kkap (a τ : ℝ) : ℝ :=
  L2mu a * π ^ 2 / Mband a τ + 2 * Ksm a τ + (L2mu a * π ^ 2 / Mband a τ) * (2 * Ksm a τ)

/-- Threshold `n₂ = n₁ + ⌈2K⌉`. -/
noncomputable def n2 (a τ : ℝ) : ℕ := n1 a τ + ⌈2 * Ksm a τ⌉₊

/-- **`thm:kappa`, eq. `(kappa)`** (relative form, explicit constants): for every nonsingular
`N ≥ n₂(a,τ)`, `(1 - K₃/N) C (N+τ)/d_N ≤ κ₂(B_N) ≤ (1 + K₃/N) C (N+τ)/d_N`. -/
theorem thm_kappa_relative (h : InteriorParam a τ) {N : ℕ} (hN : n2 a τ ≤ N)
    (hns : Nonsingular N a τ) :
    (1 - Kkap a τ / N) * (Cint a τ * (N + τ) / dN N a τ) ≤ kappa N a τ ∧
      kappa N a τ ≤ (1 + Kkap a τ / N) * (Cint a τ * (N + τ) / dN N a τ) := by
  have ha0 := h.1
  have ha1 := h.2.1
  have hτ := h.tau_pos
  have hγ := gam_pos h
  have hpi := Real.pi_pos
  have hM := Mband_pos h
  have hK0 := Ksm_nonneg h
  have hL := L2mu_nonneg ha0 ha1
  have hN1 : n1 a τ ≤ N := le_trans (Nat.le_add_right _ _) hN
  have hN0 : n0 a τ ≤ N := le_trans (Nat.le_add_right _ _) hN1
  obtain ⟨hN2, -, -⟩ := n0_spec h hN0
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hKhalf : Ksm a τ / N ≤ 1 / 2 := by
    rw [div_le_iff₀ hNpos]
    have := Nat.le_ceil (2 * Ksm a τ)
    have : (⌈2 * Ksm a τ⌉₊ : ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_add_left _ _) hN
    linarith
  -- σ_min, A
  have hd : 0 < dN N a τ := by
    rcases (distZ_nonneg (resid N a τ)).lt_or_eq with hl | he
    · exact hl
    · exfalso; apply hns
      exact (thm_sing h hN2).2 ((distZ_eq_zero_iff _).1 he.symm)
  set A := π * gam a τ * dN N a τ / (N + τ) with hA
  have hA0 : 0 < A := by positivity
  obtain ⟨slo, shi⟩ := thm_smin_relative h hN1
  have hs0 : 0 < sigmaMin N a τ := (nonsingular_iff_sigmaMin_pos ha0 ha1 hN2 τ).1 hns
  have hsmax := thm_smax h (by omega : 1 ≤ N)
  -- relative factors
  set ρ₁ := sigmaMax N a τ / Mband a τ with hρ₁
  set ρ₂ := A / sigmaMin N a τ with hρ₂
  have e1 : |ρ₁ - 1| ≤ L2mu a * π ^ 2 / Mband a τ / N := by
    rw [hρ₁, show sigmaMax N a τ / Mband a τ - 1 = (sigmaMax N a τ - Mband a τ) / Mband a τ by
      field_simp, abs_div, abs_of_pos hM, div_le_iff₀ hM]
    refine hsmax.trans ?_
    rw [show L2mu a * π ^ 2 / Mband a τ / N * Mband a τ = L2mu a * π ^ 2 / N by field_simp]
    apply div_le_div_of_nonneg_left (by positivity) hNpos
    nlinarith
  have e2 : |ρ₂ - 1| ≤ 2 * Ksm a τ / N := by
    rw [hρ₂, show A / sigmaMin N a τ - 1 = (A - sigmaMin N a τ) / sigmaMin N a τ by field_simp,
      abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
    have habs : |A - sigmaMin N a τ| ≤ Ksm a τ / N * A := by
      rw [abs_le]; constructor <;> nlinarith
    have hlow : (1 / 2) * A ≤ sigmaMin N a τ := by nlinarith
    calc |A - sigmaMin N a τ| ≤ Ksm a τ / N * A := habs
      _ = 2 * Ksm a τ / N * ((1 / 2) * A) := by ring
      _ ≤ 2 * Ksm a τ / N * sigmaMin N a τ :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
  have hsmax0 : 0 ≤ sigmaMax N a τ :=
    le_trans (abs_nonneg _) (le_sigmaMax (N := N) a τ le_rfl (by omega))
  obtain ⟨plo, phi⟩ := prod_rel e1 e2 (div_nonneg hsmax0 hM.le) (div_nonneg hA0.le hs0.le)
  -- κ = (M/A) ρ₁ ρ₂ and M/A = C (N+τ)/d
  have hMA : Cint a τ * (N + τ) / dN N a τ = Mband a τ / A := by
    unfold Cint; rw [hA]; field_simp
  have hk : kappa N a τ = Mband a τ / A * (ρ₁ * ρ₂) := by
    unfold kappa; rw [hρ₁, hρ₂]; field_simp
  have hMA0 : 0 < Mband a τ / A := by positivity
  have hcol : L2mu a * π ^ 2 / Mband a τ / N + 2 * Ksm a τ / N +
      L2mu a * π ^ 2 / Mband a τ / N * (2 * Ksm a τ / N) ≤ Kkap a τ / N := by
    unfold Kkap
    have hc1 : 0 ≤ L2mu a * π ^ 2 / Mband a τ := by positivity
    have hc2 : 0 ≤ 2 * Ksm a τ := by positivity
    have : L2mu a * π ^ 2 / Mband a τ / N * (2 * Ksm a τ / N) ≤
        L2mu a * π ^ 2 / Mband a τ * (2 * Ksm a τ) / N := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hNpos]
      have := mul_nonneg hc1 hc2
      nlinarith [mul_le_mul_of_nonneg_left (show (N : ℝ) ≤ N * N by nlinarith) this]
    rw [add_div, add_div]
    linarith
  have hcol' : L2mu a * π ^ 2 / Mband a τ / N + 2 * Ksm a τ / N ≤ Kkap a τ / N := by
    have : 0 ≤ L2mu a * π ^ 2 / Mband a τ / N * (2 * Ksm a τ / N) := by positivity
    linarith
  rw [hk, hMA]
  constructor
  · calc (1 - Kkap a τ / N) * (Mband a τ / A) = Mband a τ / A * (1 - Kkap a τ / N) := mul_comm _ _
      _ ≤ Mband a τ / A * (ρ₁ * ρ₂) := mul_le_mul_of_nonneg_left (by linarith) hMA0.le
  · calc Mband a τ / A * (ρ₁ * ρ₂) ≤ Mband a τ / A * (1 + Kkap a τ / N) :=
          mul_le_mul_of_nonneg_left (by linarith) hMA0.le
      _ = (1 + Kkap a τ / N) * (Mband a τ / A) := mul_comm _ _

end InteriorKappa

/-! ### G4.4 — outside the symbol band -/

section Outside

variable {a τ : ℝ}

lemma tendsto_of_sq_bound {f : ℕ → ℝ} {L c : ℝ} (hb : ∀ N : ℕ, 1 ≤ N → |f N - L| ≤ c / N ^ 2) :
    Tendsto f atTop (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Tendsto (fun N : ℕ => c / (N : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) _ hc
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs]
  exact hb N hN

lemma theta1_le_pi_div (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 1 ≤ N) :
    eigAngle N a 1 ≤ π / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact (theta1_bounds ha0 ha1 hN).2.trans
    (div_le_div_of_nonneg_left Real.pi_pos.le hNr (by linarith [lowerEdge_pos ha0 ha1]))

lemma thetaN_le_pi_div (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 1 ≤ N) :
    π - eigAngle N a N ≤ π / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact (thetaN_bounds ha0 ha1 hN).2.trans
    (div_le_div_of_nonneg_left Real.pi_pos.le hNr (by linarith [lowerEdge_pos ha0 ha1]))

lemma first_conv (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun N : ℕ => symbol a (eigAngle N a 1)) atTop (𝓝 (upperEdge a)) := by
  apply tendsto_of_sq_bound (c := L2mu a * π ^ 2)
  intro N hN
  refine (symbol_near_zero ha0 ha1 _).trans ?_
  have h0 := (eigAngle_spec ha0 ha1 le_rfl hN).1.1
  rw [mul_div_assoc, ← div_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0.le (theta1_le_pi_div ha0 ha1 hN) 2)
    (L2mu_nonneg ha0 ha1)

lemma last_conv (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun N : ℕ => symbol a (eigAngle N a N)) atTop (𝓝 (lowerEdge a)) := by
  apply tendsto_of_sq_bound (c := L2mu a * π ^ 2)
  intro N hN
  refine (symbol_near_pi ha0 ha1 _).trans ?_
  have h0 := (eigAngle_spec ha0 ha1 hN le_rfl).1.2
  rw [mul_div_assoc, ← div_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith) (thetaN_le_pi_div ha0 ha1 hN) 2) (L2mu_nonneg ha0 ha1)

lemma eig_strict (ha0 : 0 < a) (ha1 : a < 1) {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    lowerEdge a < symbol a (eigAngle N a k) ∧ symbol a (eigAngle N a k) < upperEdge a :=
  symbol_strict_bounds ha0 ha1 (eigAngle_spec ha0 ha1 hk1 hkN).1

lemma kappa_below (ha0 : 0 < a) (ha1 : a < 1) (hτ : τ < lowerEdge a) {N : ℕ} (hN : 1 ≤ N) :
    kappa N a τ = (symbol a (eigAngle N a 1) - τ) / (symbol a (eigAngle N a N) - τ) := by
  have hN' := (eig_strict ha0 ha1 (N := N) hN le_rfl).1
  have h1' := (eig_strict ha0 ha1 (N := N) le_rfl hN).1
  have hpos : 0 ≤ lam N a τ N := by unfold lam; linarith
  have hlN := lam_anti ha0 ha1 τ (N := N) le_rfl hN le_rfl
  unfold kappa
  rw [sigmaMin_eq_last ha0 ha1 hN hpos, sigmaMax_eq ha0 ha1 hN, abs_of_nonneg hpos,
    abs_of_nonneg (by linarith), max_eq_left hlN]
  rfl

/-- **`thm:outside`, eq. `(outside-lower)`**: for `τ < μ₋`, every `B_N` (`N ≥ 2`) is nonsingular,
`κ₂(B_N) < (μ₊ - τ)/(μ₋ - τ)`, and `κ₂(B_N) → (μ₊ - τ)/(μ₋ - τ)`. -/
theorem thm_outside_lower (ha0 : 0 < a) (ha1 : a < 1) (hτ : τ < lowerEdge a) :
    (∀ N : ℕ, 2 ≤ N → Nonsingular N a τ ∧
        kappa N a τ < (upperEdge a - τ) / (lowerEdge a - τ)) ∧
      Tendsto (fun N : ℕ => kappa N a τ) atTop (𝓝 ((upperEdge a - τ) / (lowerEdge a - τ))) := by
  refine ⟨fun N hN => ⟨?_, ?_⟩, ?_⟩
  · rw [nonsingular_iff_sigmaMin_pos ha0 ha1 hN]
    have := (eig_strict ha0 ha1 (N := N) (by omega) le_rfl).1
    rw [sigmaMin_eq_last ha0 ha1 (by omega) (by unfold lam; linarith)]
    unfold lam; linarith
  · rw [kappa_below ha0 ha1 hτ (by omega)]
    have h1 := (eig_strict ha0 ha1 (N := N) le_rfl (by omega)).2
    have hN' := (eig_strict ha0 ha1 (N := N) (by omega) le_rfl).1
    have h1l := (eig_strict ha0 ha1 (N := N) le_rfl (by omega)).1
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    calc (symbol a (eigAngle N a 1) - τ) * (lowerEdge a - τ)
        < (upperEdge a - τ) * (lowerEdge a - τ) :=
          mul_lt_mul_of_pos_right (by linarith) (by linarith)
      _ ≤ (upperEdge a - τ) * (symbol a (eigAngle N a N) - τ) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  · have h := ((first_conv ha0 ha1).sub_const τ).div ((last_conv ha0 ha1).sub_const τ)
      (by linarith)
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [kappa_below ha0 ha1 hτ hN]; rfl

lemma kappa_above (ha0 : 0 < a) (ha1 : a < 1) (hτ : upperEdge a < τ) {N : ℕ} (hN : 1 ≤ N) :
    kappa N a τ = (τ - symbol a (eigAngle N a N)) / (τ - symbol a (eigAngle N a 1)) := by
  have h1' := (eig_strict ha0 ha1 (N := N) le_rfl hN).2
  have hneg : lam N a τ 1 ≤ 0 := by unfold lam; linarith
  have hlN := lam_anti ha0 ha1 τ (N := N) le_rfl hN le_rfl
  unfold kappa
  rw [sigmaMin_eq_first ha0 ha1 hN hneg, sigmaMax_eq ha0 ha1 hN, abs_of_nonpos hneg,
    abs_of_nonpos (by linarith), max_eq_right (by linarith)]
  unfold lam; congr 1 <;> ring

/-- **`thm:outside`, eq. `(outside-upper)`**: for `τ > μ₊`, every `B_N` (`N ≥ 2`) is nonsingular,
`κ₂(B_N) < (τ - μ₋)/(τ - μ₊)`, and `κ₂(B_N) → (τ - μ₋)/(τ - μ₊)`. -/
theorem thm_outside_upper (ha0 : 0 < a) (ha1 : a < 1) (hτ : upperEdge a < τ) :
    (∀ N : ℕ, 2 ≤ N → Nonsingular N a τ ∧
        kappa N a τ < (τ - lowerEdge a) / (τ - upperEdge a)) ∧
      Tendsto (fun N : ℕ => kappa N a τ) atTop (𝓝 ((τ - lowerEdge a) / (τ - upperEdge a))) := by
  refine ⟨fun N hN => ⟨?_, ?_⟩, ?_⟩
  · rw [nonsingular_iff_sigmaMin_pos ha0 ha1 hN]
    have := (eig_strict ha0 ha1 (N := N) le_rfl (by omega)).2
    rw [sigmaMin_eq_first ha0 ha1 (by omega) (by unfold lam; linarith)]
    unfold lam; linarith
  · rw [kappa_above ha0 ha1 hτ (by omega)]
    have h1 := (eig_strict ha0 ha1 (N := N) le_rfl (by omega)).2
    have hN' := (eig_strict ha0 ha1 (N := N) (by omega) le_rfl).1
    have hNu := (eig_strict ha0 ha1 (N := N) (by omega) le_rfl).2
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    calc (τ - symbol a (eigAngle N a N)) * (τ - upperEdge a)
        < (τ - lowerEdge a) * (τ - upperEdge a) :=
          mul_lt_mul_of_pos_right (by linarith) (by linarith)
      _ ≤ (τ - lowerEdge a) * (τ - symbol a (eigAngle N a 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  · have h := ((last_conv ha0 ha1).const_sub τ).div ((first_conv ha0 ha1).const_sub τ)
      (by linarith)
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [kappa_above ha0 ha1 hτ hN]; rfl

end Outside

/-! ### G4.5 — the band edges -/

section Edges

variable {a : ℝ}

lemma cos_half_sin (θ : ℝ) : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
  have h1 := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h1
  have h2 := Real.sin_sq_add_cos_sq (θ / 2)
  linarith

lemma cos_half_sin' (θ : ℝ) : Real.cos θ = 2 * Real.sin ((π - θ) / 2) ^ 2 - 1 := by
  have e : Real.sin ((π - θ) / 2) = Real.cos (θ / 2) := by
    rw [show (π - θ) / 2 = π / 2 - θ / 2 by ring, Real.sin_pi_div_two_sub]
  rw [e]
  have h1 := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h1
  linarith

/-- Exact upper-edge identity: `μ₊ - μ_a(θ) = 4a(1+a) sin²(θ/2) / ((1-a) R(θ))`. -/
lemma up_exact (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    upperEdge a - symbol a θ =
      4 * a * (1 + a) * Real.sin (θ / 2) ^ 2 / ((1 - a) * Ra a θ) := by
  have hR := Ra_pos ha0 ha1 θ
  have h1a : (1 - a) ≠ 0 := by intro h; linarith
  have hRe : Ra a θ = (1 - a) ^ 2 + 4 * a * Real.sin (θ / 2) ^ 2 := by
    unfold Ra; rw [cos_half_sin]; ring
  rw [symbol_eq_div_Ra, upperEdge, div_sub_div _ _ h1a hR.ne', div_eq_div_iff
    (mul_ne_zero h1a hR.ne') (mul_ne_zero h1a hR.ne')]
  rw [hRe]; ring

/-- Exact lower-edge identity: `μ_a(θ) - μ₋ = 4a(1-a) sin²((π-θ)/2) / ((1+a) R(θ))`. -/
lemma low_exact (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    symbol a θ - lowerEdge a =
      4 * a * (1 - a) * Real.sin ((π - θ) / 2) ^ 2 / ((1 + a) * Ra a θ) := by
  have hR := Ra_pos ha0 ha1 θ
  have h1a : (1 + a) ≠ 0 := by positivity
  have hRe : Ra a θ = (1 + a) ^ 2 - 4 * a * Real.sin ((π - θ) / 2) ^ 2 := by
    unfold Ra; rw [cos_half_sin']; ring
  rw [symbol_eq_div_Ra, lowerEdge, div_sub_div _ _ hR.ne' h1a, div_eq_div_iff
    (mul_ne_zero hR.ne' h1a) (mul_ne_zero h1a hR.ne')]
  rw [hRe]; ring

lemma sin_sq_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ 2 * (1 - x ^ 2 / 3) ≤ Real.sin x ^ 2 ∧ Real.sin x ^ 2 ≤ x ^ 2 := by
  have hs0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.two_le_pi])
  have hle := Real.sin_le hx0
  constructor
  · rcases hx0.lt_or_eq with hx | hx
    · have hgt := Real.sin_gt_sub_cube hx
      have hx2 : x ^ 2 ≤ 1 := by nlinarith
      have hx3 : x ^ 3 ≤ x := by nlinarith [mul_le_mul_of_nonneg_left hx2 hx0]
      have h1 : 0 ≤ x - x ^ 3 / 6 := by linarith
      have h2 : (x - x ^ 3 / 6) ^ 2 ≤ Real.sin x ^ 2 := pow_le_pow_left₀ h1 hgt.le 2
      nlinarith [sq_nonneg (x ^ 3)]
    · subst hx; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero, mul_one, sin_zero, Std.le_refl]
  · exact pow_le_pow_left₀ hs0 hle 2

/-- `κ_u = a(1+a)/(1-a)³` (so `σ_min ≈ π² κ_u/(N+μ₊)²`), and `c_u = 1/12 + a/(1-a)²`. -/
noncomputable def kapU (a : ℝ) : ℝ := a * (1 + a) / (1 - a) ^ 3
noncomputable def cU (a : ℝ) : ℝ := 1 / 12 + a / (1 - a) ^ 2
/-- `κ_l = a(1-a)/(1+a)³`, `c_l = 1/12 + 2a/(1+a)²`. -/
noncomputable def kapL (a : ℝ) : ℝ := a * (1 - a) / (1 + a) ^ 3
noncomputable def cL (a : ℝ) : ℝ := 1 / 12 + 2 * a / (1 + a) ^ 2

/-- Local quadratic law at the upper edge: for `0 ≤ θ ≤ 1`,
`|(μ₊ - μ_a(θ)) - κ_u θ²| ≤ c_u θ² · κ_u θ²`. -/
lemma up_local (ha0 : 0 < a) (ha1 : a < 1) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |(upperEdge a - symbol a θ) - kapU a * θ ^ 2| ≤ cU a * θ ^ 2 * (kapU a * θ ^ 2) := by
  rw [up_exact ha0 ha1]
  have h1a : 0 < 1 - a := by linarith
  obtain ⟨slo, shi⟩ := sin_sq_bounds (x := θ / 2) (by positivity) (by linarith)
  set S := Real.sin (θ / 2) ^ 2 with hS
  have hRe : Ra a θ = (1 - a) ^ 2 + 4 * a * S := by
    unfold Ra; rw [cos_half_sin]; ring
  have hS0 : 0 ≤ S := by positivity
  have hD : 0 < (1 - a) ^ 2 := by positivity
  rw [hRe]
  set D := (1 - a) ^ 2 with hDdef
  set X := (θ / 2) ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have hSX : S ≤ X := shi
  have hDS : 0 < D + 4 * a * S := by positivity
  set u := 4 * a * X / D with hu
  have hu0 : 0 ≤ u := by positivity
  have huD : u * D = 4 * a * X := by rw [hu]; field_simp
  have key1 : S / (D + 4 * a * S) ≤ X / D := by
    rw [div_le_div_iff₀ hDS hD]
    nlinarith [mul_le_mul_of_nonneg_right hSX hD.le, mul_nonneg (mul_nonneg ha0.le hS0) hX0]
  have key2 : X * (1 - (X / 3 + u)) / D ≤ S / (D + 4 * a * S) := by
    rw [div_le_div_iff₀ hD hDS]
    have f1 := mul_le_mul_of_nonneg_right slo hD.le
    have f2 : 0 ≤ 4 * a * S * X * (X / 3 + u) := by positivity
    have f3 : 4 * a * S * X ≤ 4 * a * X * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSX (by positivity)) hX0
    have f4 : X * (u * D) = X * (4 * a * X) := by rw [huD]
    nlinarith [f1, f2, f3, f4]
  have hc : 0 < 4 * a * (1 + a) / (1 - a) := by positivity
  have e1 : 4 * a * (1 + a) * S / ((1 - a) * (D + 4 * a * S)) =
      4 * a * (1 + a) / (1 - a) * (S / (D + 4 * a * S)) := by
    field_simp
  have e2 : kapU a * θ ^ 2 = 4 * a * (1 + a) / (1 - a) * (X / D) := by
    unfold kapU; rw [hDdef, hX]; field_simp; ring
  have ec : cU a * θ ^ 2 = X / 3 + u := by
    unfold cU; rw [hu, hDdef, hX]; field_simp; ring
  rw [e1, e2, ec, abs_le]
  have hcX : 0 ≤ 4 * a * (1 + a) / (1 - a) * (X / D) := by positivity
  constructor
  · have := mul_le_mul_of_nonneg_left key2 hc.le
    have e3 : 4 * a * (1 + a) / (1 - a) * (X * (1 - (X / 3 + u)) / D) =
        (1 - (X / 3 + u)) * (4 * a * (1 + a) / (1 - a) * (X / D)) := by ring
    rw [e3] at this
    nlinarith
  · have := mul_le_mul_of_nonneg_left key1 hc.le
    have : 0 ≤ (X / 3 + u) * (4 * a * (1 + a) / (1 - a) * (X / D)) := by positivity
    linarith

/-- Local quadratic law at the lower edge: for `0 ≤ π - θ ≤ 1`,
`|(μ_a(θ) - μ₋) - κ_l (π-θ)²| ≤ c_l (π-θ)² · κ_l (π-θ)²`. -/
lemma low_local (ha0 : 0 < a) (ha1 : a < 1) {θ : ℝ} (h0 : 0 ≤ π - θ) (h1 : π - θ ≤ 1) :
    |(symbol a θ - lowerEdge a) - kapL a * (π - θ) ^ 2| ≤
      cL a * (π - θ) ^ 2 * (kapL a * (π - θ) ^ 2) := by
  rw [low_exact ha0 ha1]
  have hR := Ra_pos ha0 ha1 θ
  obtain ⟨slo, shi⟩ := sin_sq_bounds (x := (π - θ) / 2) (by positivity) (by linarith)
  set S := Real.sin ((π - θ) / 2) ^ 2 with hS
  have hRe : Ra a θ = (1 + a) ^ 2 - 4 * a * S := by
    unfold Ra; rw [cos_half_sin']; ring
  have hS0 : 0 ≤ S := by positivity
  have hD : 0 < (1 + a) ^ 2 := by positivity
  rw [hRe] at hR ⊢
  set D := (1 + a) ^ 2 with hDdef
  set X := ((π - θ) / 2) ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have hX1 : X ≤ 1 / 4 := by rw [hX]; nlinarith
  have hSX : S ≤ X := shi
  have hu : 4 * a * X ≤ D / 2 := by rw [hDdef]; nlinarith
  have key1 : S / (D - 4 * a * S) ≤ X * (1 + 8 * a * X / D) / D := by
    rw [div_le_div_iff₀ hR hD]
    have hdiv : 8 * a * X / D * D = 8 * a * X := by field_simp
    have hDX : 0 < D - 4 * a * X := by linarith
    nlinarith [mul_nonneg hX0 hX0, mul_nonneg ha0.le hX0, mul_nonneg (mul_nonneg ha0.le hX0) hX0,
      mul_nonneg (mul_nonneg ha0.le hX0) hS0, mul_nonneg ha0.le hS0,
      mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * a * X / D) hS0]
  have key2 : X * (1 - X / 3) / D ≤ S / (D - 4 * a * S) := by
    rw [div_le_div_iff₀ hD hR]
    nlinarith [mul_nonneg ha0.le hS0, mul_nonneg (mul_nonneg ha0.le hS0) hX0]
  have hc : 0 < 4 * a * (1 - a) / (1 + a) := by
    have : 0 < 1 - a := by linarith
    positivity
  have e1 : 4 * a * (1 - a) * S / ((1 + a) * (D - 4 * a * S)) =
      4 * a * (1 - a) / (1 + a) * (S / (D - 4 * a * S)) := by
    field_simp
  have e2 : kapL a * (π - θ) ^ 2 = 4 * a * (1 - a) / (1 + a) * (X / D) := by
    unfold kapL; rw [hDdef, hX]; field_simp; ring
  have ec : cL a * (π - θ) ^ 2 = X / 3 + 8 * a * X / D := by
    unfold cL; rw [hDdef, hX]; field_simp; ring
  rw [e1, e2, ec, abs_le]
  have hcX : 0 ≤ 4 * a * (1 - a) / (1 + a) * (X / D) := by positivity
  constructor
  · have := mul_le_mul_of_nonneg_left key2 hc.le
    have e3 : 4 * a * (1 - a) / (1 + a) * (X * (1 - X / 3) / D) =
        (1 - X / 3) * (4 * a * (1 - a) / (1 + a) * (X / D)) := by ring
    rw [e3] at this
    have : 0 ≤ 8 * a * X / D * (4 * a * (1 - a) / (1 + a) * (X / D)) := by positivity
    nlinarith
  · have := mul_le_mul_of_nonneg_left key1 hc.le
    have e3 : 4 * a * (1 - a) / (1 + a) * (X * (1 + 8 * a * X / D) / D) =
        (1 + 8 * a * X / D) * (4 * a * (1 - a) / (1 + a) * (X / D)) := by ring
    rw [e3] at this
    have : 0 ≤ X / 3 * (4 * a * (1 - a) / (1 + a) * (X / D)) := by positivity
    nlinarith

/-! #### First/last root asymptotics -/

/-- `g(θ) = ψ_a(θ) - μ₊ θ`, with `|g(θ)| ≤ L₂ |θ|³`. -/
noncomputable def gU (a θ : ℝ) : ℝ := psi a θ - upperEdge a * θ

lemma gU_bound (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) : |gU a θ| ≤ L2mu a * |θ| ^ 3 := by
  have hd : ∀ x, HasDerivAt (gU a) (symbol a x - upperEdge a) x := fun x =>
    (hasDerivAt_psi ha0 ha1 x).sub ((hasDerivAt_id x).const_mul (upperEdge a)) |>.congr_deriv
      (by simp only [mul_one])
  obtain ⟨c, hc, hm⟩ := mvt_between hd θ 0
  have g0 : gU a 0 = 0 := by simp only [gU, psi_zero, mul_zero, sub_self]
  rw [g0, sub_zero, sub_zero] at hm
  rw [sub_zero, sub_zero] at hc
  rw [hm, abs_mul]
  have := symbol_near_zero ha0 ha1 c
  have hL := L2mu_nonneg ha0 ha1
  calc |symbol a c - upperEdge a| * |θ| ≤ L2mu a * c ^ 2 * |θ| :=
        mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ ≤ L2mu a * θ ^ 2 * |θ| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hL
        rw [← sq_abs c, ← sq_abs θ]; exact pow_le_pow_left₀ (abs_nonneg _) hc 2
    _ = L2mu a * |θ| ^ 3 := by rw [← sq_abs θ]; ring

/-- `h(θ) = ψ_a(θ) - π - μ₋ (θ - π)`, with `|h(θ)| ≤ L₂ |π - θ|³`. -/
noncomputable def hL (a θ : ℝ) : ℝ := psi a θ - π - lowerEdge a * (θ - π)

lemma hL_bound (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) : |hL a θ| ≤ L2mu a * |π - θ| ^ 3 := by
  have hd : ∀ x, HasDerivAt (hL a) (symbol a x - lowerEdge a) x := fun x => by
    have h1 := ((hasDerivAt_psi ha0 ha1 x).sub_const π).sub
      (((hasDerivAt_id' x).sub_const π).const_mul (lowerEdge a))
    exact h1.congr_deriv (by ring)
  obtain ⟨c, hc, hm⟩ := mvt_between hd θ π
  have g0 : hL a π = 0 := by simp only [hL, psi_pi, sub_self, mul_zero]
  rw [g0, sub_zero] at hm
  rw [hm, abs_mul]
  have := symbol_near_pi ha0 ha1 c
  have hLn := L2mu_nonneg ha0 ha1
  calc |symbol a c - lowerEdge a| * |θ - π| ≤ L2mu a * (π - c) ^ 2 * |θ - π| :=
        mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ ≤ L2mu a * (π - θ) ^ 2 * |θ - π| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hLn
        rw [← sq_abs (π - c), ← sq_abs (π - θ), abs_sub_comm π c, abs_sub_comm π θ]
        exact pow_le_pow_left₀ (abs_nonneg _) hc 2
    _ = L2mu a * |π - θ| ^ 3 := by rw [← sq_abs (π - θ), abs_sub_comm θ π]; ring

/-- Generic assembly: from `|σ - κ e²| ≤ x κ e²`, `e = T(1+v)`, `|v| ≤ δ ≤ 1`, get
`|σ - κ T²| ≤ (x + 3δ + 3xδ) κ T²`. -/
lemma edge_assemble {σ κ e T v x δ : ℝ} (hκ : 0 ≤ κ) (hx : 0 ≤ x) (he : e = T * (1 + v))
    (hv : |v| ≤ δ) (hδ : δ ≤ 1) (hσ : |σ - κ * e ^ 2| ≤ x * (κ * e ^ 2)) :
    |σ - κ * T ^ 2| ≤ (x + 3 * δ + 3 * x * δ) * (κ * T ^ 2) := by
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hv
  rw [abs_le] at hv
  have hp1 : |(1 + v) ^ 2 - 1| ≤ 3 * δ := by
    rw [abs_le]; constructor <;> nlinarith
  have hp2 : (1 + v) ^ 2 ≤ 1 + 3 * δ := by rw [abs_le] at hp1; linarith
  have he2 : κ * e ^ 2 = κ * T ^ 2 * (1 + v) ^ 2 := by rw [he]; ring
  have hκT : 0 ≤ κ * T ^ 2 := by positivity
  calc |σ - κ * T ^ 2| = |(σ - κ * e ^ 2) + κ * T ^ 2 * ((1 + v) ^ 2 - 1)| := by
        rw [he2]; ring_nf
    _ ≤ |σ - κ * e ^ 2| + |κ * T ^ 2 * ((1 + v) ^ 2 - 1)| := abs_add_le _ _
    _ ≤ x * (κ * T ^ 2 * (1 + v) ^ 2) + κ * T ^ 2 * (3 * δ) := by
        rw [abs_mul, abs_of_nonneg hκT, ← he2]
        exact add_le_add hσ (mul_le_mul_of_nonneg_left hp1 hκT)
    _ ≤ x * (κ * T ^ 2 * (1 + 3 * δ)) + κ * T ^ 2 * (3 * δ) := by
        have := mul_le_mul_of_nonneg_left hp2 hκT
        nlinarith
    _ = (x + 3 * δ + 3 * x * δ) * (κ * T ^ 2) := by ring

/-- Generic κ assembly. -/
lemma kappa_assemble {smax smin W S η y : ℝ} (hW : 0 < W) (hS : 0 < S) (hη : 0 ≤ η)
    (hsmax0 : 0 ≤ smax) (hy : 0 ≤ y) (hy2 : y ≤ 1 / 2) (hmax : |smax - W| ≤ η) (hmin : |smin - S| ≤ y * S) :
    |smax / smin - W / S| ≤ (η / W + 2 * y + η / W * (2 * y)) * (W / S) := by
  have hsmin : (1 / 2) * S ≤ smin := by rw [abs_le] at hmin; nlinarith
  have hs0 : 0 < smin := by linarith
  have e1 : |smax / W - 1| ≤ η / W := by
    rw [show smax / W - 1 = (smax - W) / W by field_simp, abs_div, abs_of_pos hW]
    exact div_le_div_of_nonneg_right hmax hW.le
  have e2 : |S / smin - 1| ≤ 2 * y := by
    rw [show S / smin - 1 = (S - smin) / smin by field_simp, abs_div, abs_of_pos hs0,
      div_le_iff₀ hs0, abs_sub_comm]
    calc |smin - S| ≤ y * S := hmin
      _ = 2 * y * ((1 / 2) * S) := by ring
      _ ≤ 2 * y * smin := mul_le_mul_of_nonneg_left hsmin (by positivity)
  obtain ⟨plo, phi⟩ := prod_rel e1 e2 (div_nonneg hsmax0 hW.le) (div_nonneg hS.le hs0.le)
  have hk : smax / smin = W / S * ((smax / W) * (S / smin)) := by field_simp
  rw [hk, show W / S * (smax / W * (S / smin)) - W / S = W / S * ((smax / W * (S / smin)) - 1) by
    ring, abs_mul, abs_of_pos (by positivity), mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [abs_le]; constructor <;> nlinarith [mul_nonneg (div_nonneg hη hW.le) hy]

/-! #### Upper edge `τ = μ₊` -/

/-- Constant of the upper-edge `σ_min` law. -/
noncomputable def KeU (a : ℝ) : ℝ :=
  cU a * π ^ 2 + 3 * (L2mu a * π ^ 2) + 3 * (cU a * π ^ 2) * (L2mu a * π ^ 2)

/-- Constant of the lower-edge `σ_min` law. -/
noncomputable def KeL (a : ℝ) : ℝ :=
  cL a * π ^ 2 + 3 * (L2mu a * π ^ 2) + 3 * (cL a * π ^ 2) * (L2mu a * π ^ 2)

/-- Threshold for the edge laws. -/
noncomputable def nE (a : ℝ) : ℕ := ⌈L2mu a * π ^ 2⌉₊ + ⌈2 * KeU a⌉₊ + ⌈2 * KeL a⌉₊ + 4

lemma nE_spec (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : nE a ≤ N) :
    4 ≤ N ∧ L2mu a * π ^ 2 / N ^ 2 ≤ 1 ∧ KeU a / N ^ 2 ≤ 1 / 2 ∧ KeL a / N ^ 2 ≤ 1 / 2 := by
  have h1 := Nat.le_ceil (L2mu a * π ^ 2)
  have h2 := Nat.le_ceil (2 * KeU a)
  have h3 := Nat.le_ceil (2 * KeL a)
  have hNr : (⌈L2mu a * π ^ 2⌉₊ : ℝ) + ⌈2 * KeU a⌉₊ + ⌈2 * KeL a⌉₊ + 4 ≤ N := by
    unfold nE at hN; exact_mod_cast hN
  have c1 : (0 : ℝ) ≤ ⌈L2mu a * π ^ 2⌉₊ := Nat.cast_nonneg _
  have c2 : (0 : ℝ) ≤ ⌈2 * KeU a⌉₊ := Nat.cast_nonneg _
  have c3 : (0 : ℝ) ≤ ⌈2 * KeL a⌉₊ := Nat.cast_nonneg _
  have hN4 : (4 : ℝ) ≤ N := by linarith
  have hNN : (N : ℝ) ≤ N ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < N ^ 2 := by positivity
  refine ⟨by unfold nE at hN; omega, ?_, ?_, ?_⟩
  · rw [div_le_one hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

/-- **`thm:edges`, eq. `(edge-up-smin)`**: at `τ = μ₊`, for `N ≥ n_E(a)`,
`|σ_min - π² κ_u/(N+μ₊)²| ≤ (K_u/N²) · π² κ_u/(N+μ₊)²`, `π² κ_u = π² a(1+a)/(1-a)³`. -/
theorem thm_edge_upper_smin (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : nE a ≤ N) :
    |sigmaMin N a (upperEdge a) - kapU a * (π / (N + upperEdge a)) ^ 2| ≤
      KeU a / N ^ 2 * (kapU a * (π / (N + upperEdge a)) ^ 2) := by
  obtain ⟨hN4, hδ1, -, -⟩ := nE_spec ha0 ha1 hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hpi := Real.pi_pos
  have hu0 : 0 < upperEdge a := lt_trans (lowerEdge_pos ha0 ha1)
    (lt_of_le_of_lt (lowerEdge_le_symbol ha0 ha1 1) (symbol_strict_bounds ha0 ha1
      (show (1 : ℝ) ∈ Ioo 0 π from ⟨one_pos, by linarith [Real.two_le_pi]⟩)).2)
  have hL := L2mu_nonneg ha0 ha1
  set θ1 := eigAngle N a 1 with hθ1
  have hs := eigAngle_spec ha0 ha1 le_rfl hN1
  have hθ0 : 0 < θ1 := hs.1.1
  have hθle : θ1 ≤ π / N := theta1_le_pi_div ha0 ha1 hN1
  have hθ1le : θ1 ≤ 1 := hθle.trans (by rw [div_le_one (by linarith)]; linarith [Real.pi_le_four])
  -- σ_min = μ₊ - μ(θ₁)
  have hlam : lam N a (upperEdge a) 1 ≤ 0 := by
    unfold lam; linarith [(eig_strict ha0 ha1 (N := N) le_rfl hN1).2]
  have hsm : sigmaMin N a (upperEdge a) = upperEdge a - symbol a θ1 := by
    rw [sigmaMin_eq_first ha0 ha1 hN1 hlam]; unfold lam; ring
  -- θ₁ = T (1 + v), v = -g(θ₁)/π
  set T := π / (N + upperEdge a) with hT
  have hNu : (0 : ℝ) < N + upperEdge a := by linarith
  have hG : (N + upperEdge a) * θ1 + gU a θ1 = π := by
    have := hs.2; unfold Gph at this; unfold gU; rw [Nat.cast_one, one_mul] at this; linarith
  set v := -(gU a θ1) / π with hv
  have hθT : θ1 = T * (1 + v) := by
    rw [hT, hv]; field_simp; linarith
  have hvb : |v| ≤ L2mu a * π ^ 2 / N ^ 2 := by
    rw [hv, abs_div, abs_neg, abs_of_pos hpi, div_le_iff₀ hpi]
    refine (gU_bound ha0 ha1 θ1).trans ?_
    rw [abs_of_pos hθ0]
    have h3 : θ1 ^ 3 ≤ (π / N) ^ 3 := pow_le_pow_left₀ hθ0.le hθle 3
    have h4 : (π / N) ^ 3 ≤ π ^ 3 / N ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (N : ℝ) ^ 2 ≤ N ^ 3 := by nlinarith
      nlinarith [pow_pos hpi 3]
    calc L2mu a * θ1 ^ 3 ≤ L2mu a * (π ^ 3 / N ^ 2) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) hL
      _ = L2mu a * π ^ 2 / N ^ 2 * π := by ring
  have hloc := up_local ha0 ha1 hθ0.le hθ1le
  have h1a : 0 < 1 - a := by linarith
  have hcU : 0 ≤ cU a := by unfold cU; positivity
  have hkU : 0 ≤ kapU a := by unfold kapU; positivity
  have hx : cU a * θ1 ^ 2 ≤ cU a * π ^ 2 / N ^ 2 := by
    have : θ1 ^ 2 ≤ (π / N) ^ 2 := pow_le_pow_left₀ hθ0.le hθle 2
    rw [div_pow] at this
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left this hcU
  have hloc' : |(upperEdge a - symbol a θ1) - kapU a * θ1 ^ 2| ≤
      cU a * π ^ 2 / N ^ 2 * (kapU a * θ1 ^ 2) :=
    hloc.trans (mul_le_mul_of_nonneg_right hx (by positivity))
  have hasm := edge_assemble hkU (by positivity) hθT hvb hδ1 hloc'
  rw [hsm]
  refine hasm.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  unfold KeU
  have hN2 : (1 : ℝ) ≤ N ^ 2 := by nlinarith
  have hc1 : 0 ≤ cU a * π ^ 2 := by positivity
  have hc2 : 0 ≤ L2mu a * π ^ 2 := by positivity
  have : cU a * π ^ 2 / N ^ 2 * (L2mu a * π ^ 2 / N ^ 2) ≤ cU a * π ^ 2 * (L2mu a * π ^ 2) / N ^ 2 := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_nonneg hc1 hc2
    nlinarith [mul_le_mul_of_nonneg_left hN2 this]
  rw [add_div, add_div, mul_div_assoc 3,
    show 3 * (cU a * π ^ 2) * (L2mu a * π ^ 2) / (N : ℝ) ^ 2 =
      3 * (cU a * π ^ 2 * (L2mu a * π ^ 2) / N ^ 2) by ring]
  linarith

/-- `W = μ₊ - μ₋` (band width) and the edge κ constants. -/
noncomputable def Wband (a : ℝ) : ℝ := upperEdge a - lowerEdge a

lemma Wband_pos (ha0 : 0 < a) (ha1 : a < 1) : 0 < Wband a := by
  have := symbol_strict_bounds ha0 ha1 (show (1 : ℝ) ∈ Ioo 0 π from
    ⟨one_pos, by linarith [Real.two_le_pi]⟩)
  unfold Wband; linarith [this.1, this.2]

/-- `W/κ_u = 4μ₋²`: the leading constant of eq. `(edge-up-kappa)`. -/
lemma Wband_div_kapU (ha0 : 0 < a) (ha1 : a < 1) : Wband a / kapU a = 4 * lowerEdge a ^ 2 := by
  have h1 : (1 - a) ≠ 0 := by intro h; linarith
  have h2 : (1 + a) ≠ 0 := by positivity
  unfold Wband kapU upperEdge lowerEdge
  field_simp
  ring

/-- `W/κ_l = 4μ₊²`: the leading constant of eq. `(edge-low-kappa)`. -/
lemma Wband_div_kapL (ha0 : 0 < a) (ha1 : a < 1) : Wband a / kapL a = 4 * upperEdge a ^ 2 := by
  have h1 : (1 - a) ≠ 0 := by intro h; linarith
  have h2 : (1 + a) ≠ 0 := by positivity
  unfold Wband kapL upperEdge lowerEdge
  field_simp
  ring

/-- Relative constants of the edge `κ` laws: `K = η₀/W + 2K_e + (η₀/W)(2K_e)`, `η₀ = L₂π²`. -/
noncomputable def KkU (a : ℝ) : ℝ :=
  L2mu a * π ^ 2 / Wband a + 2 * KeU a + L2mu a * π ^ 2 / Wband a * (2 * KeU a)
noncomputable def KkL (a : ℝ) : ℝ :=
  L2mu a * π ^ 2 / Wband a + 2 * KeL a + L2mu a * π ^ 2 / Wband a * (2 * KeL a)

lemma sigmaMax_nonneg' {N : ℕ} (hN : 1 ≤ N) (a τ : ℝ) : 0 ≤ sigmaMax N a τ :=
  (abs_nonneg _).trans (le_sigmaMax (N := N) a τ le_rfl hN)

/-- Shared final arithmetic of the two edge κ laws. -/
lemma edge_kappa_const {p K : ℝ} {N : ℕ} (hp : 0 ≤ p) (hK : 0 ≤ K) (hN : 1 ≤ N) (W : ℝ) (hW : 0 < W) :
    p / N ^ 2 / W + 2 * (K / N ^ 2) + p / N ^ 2 / W * (2 * (K / N ^ 2)) ≤
      (p / W + 2 * K + p / W * (2 * K)) / N ^ 2 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (1 : ℝ) ≤ N ^ 2 := by nlinarith
  have hz : p / W * (2 * K) / N ^ 2 / N ^ 2 ≤ p / W * (2 * K) / N ^ 2 :=
    div_le_self (by positivity) hN2
  have e1 : p / N ^ 2 / W + 2 * (K / N ^ 2) + p / N ^ 2 / W * (2 * (K / N ^ 2)) =
      p / W / N ^ 2 + 2 * K / N ^ 2 + p / W * (2 * K) / N ^ 2 / N ^ 2 := by ring
  have e2 : (p / W + 2 * K + p / W * (2 * K)) / N ^ 2 =
      p / W / N ^ 2 + 2 * K / N ^ 2 + p / W * (2 * K) / N ^ 2 := by ring
  rw [e1, e2]; linarith

/-- **`thm:edges`, eq. `(edge-up-kappa)`**: at `τ = μ₊`, for `N ≥ n_E(a)`, `B_N` is nonsingular and
`|κ₂ - 4μ₋²(N+μ₊)²/π²| ≤ (K/N²) · 4μ₋²(N+μ₊)²/π²`. -/
theorem thm_edge_upper_kappa (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : nE a ≤ N) :
    Nonsingular N a (upperEdge a) ∧
      |kappa N a (upperEdge a) - 4 * lowerEdge a ^ 2 * ((N + upperEdge a) / π) ^ 2| ≤
        KkU a / N ^ 2 * (4 * lowerEdge a ^ 2 * ((N + upperEdge a) / π) ^ 2) := by
  obtain ⟨hN4, -, hy2, -⟩ := nE_spec ha0 ha1 hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hpi := Real.pi_pos
  have hl0 := lowerEdge_pos ha0 ha1
  have hW := Wband_pos ha0 ha1
  have hu0 : 0 < upperEdge a := by unfold Wband at hW; linarith
  have h1a : 0 < 1 - a := by linarith
  have hkU : 0 < kapU a := by unfold kapU; positivity
  have hL := L2mu_nonneg ha0 ha1
  have hKe : 0 ≤ KeU a := by unfold KeU cU; positivity
  set T := π / (N + upperEdge a) with hT
  have hT0 : 0 < T := by positivity
  have hS : 0 < kapU a * T ^ 2 := by positivity
  have hmin := thm_edge_upper_smin ha0 ha1 hN
  have hy0 : 0 ≤ KeU a / N ^ 2 := by positivity
  have hsmin : 0 < sigmaMin N a (upperEdge a) := by
    rw [abs_le] at hmin
    nlinarith [mul_le_mul_of_nonneg_right hy2 hS.le]
  refine ⟨(nonsingular_iff_sigmaMin_pos ha0 ha1 (by omega) _).2 hsmin, ?_⟩
  have hmax : |sigmaMax N a (upperEdge a) - Wband a| ≤ L2mu a * π ^ 2 / N ^ 2 := by
    have h := thm_smax_general ha0 ha1 hN1 (upperEdge a)
    have e : max (|upperEdge a - upperEdge a|) (|lowerEdge a - upperEdge a|) = Wband a := by
      unfold Wband at hW ⊢
      rw [sub_self, abs_zero, abs_of_neg (by linarith), max_eq_right (by linarith)]; ring
    rwa [e] at h
  have hk := kappa_assemble hW hS (by positivity) (sigmaMax_nonneg' hN1 a _) hy0 hy2 hmax hmin
  have hWS : Wband a / (kapU a * T ^ 2) = 4 * lowerEdge a ^ 2 * ((N + upperEdge a) / π) ^ 2 := by
    rw [← div_div, Wband_div_kapU ha0 ha1, hT, div_pow, div_pow]
    field_simp
  unfold kappa
  rw [hWS] at hk
  refine hk.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact edge_kappa_const (by positivity) hKe hN1 _ hW

/-- **`thm:edges`, eq. `(edge-low-smin)`**: at `τ = μ₋`, for `N ≥ n_E(a)`,
`|σ_min - π² κ_l/(N+μ₋)²| ≤ (K_l/N²) · π² κ_l/(N+μ₋)²`, `π² κ_l = π² a(1-a)/(1+a)³`. -/
theorem thm_edge_lower_smin (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : nE a ≤ N) :
    |sigmaMin N a (lowerEdge a) - kapL a * (π / (N + lowerEdge a)) ^ 2| ≤
      KeL a / N ^ 2 * (kapL a * (π / (N + lowerEdge a)) ^ 2) := by
  obtain ⟨hN4, hδ1, -, -⟩ := nE_spec ha0 ha1 hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hpi := Real.pi_pos
  have hl0 := lowerEdge_pos ha0 ha1
  have hL2 := L2mu_nonneg ha0 ha1
  have h1a : 0 < 1 - a := by linarith
  have hcL : 0 ≤ cL a := by unfold cL; positivity
  have hkL : 0 ≤ kapL a := by unfold kapL; positivity
  set θN := eigAngle N a N with hθN
  have hs := eigAngle_spec ha0 ha1 hN1 le_rfl
  set ε := π - θN with hε
  have hε0 : 0 < ε := by rw [hε]; linarith [hs.1.2]
  have hεle : ε ≤ π / N := thetaN_le_pi_div ha0 ha1 hN1
  have hε1 : ε ≤ 1 := hεle.trans (by rw [div_le_one (by linarith)]; linarith [Real.pi_le_four])
  -- σ_min = μ(θ_N) - μ₋
  have hlam : 0 ≤ lam N a (lowerEdge a) N := by
    unfold lam; linarith [(eig_strict ha0 ha1 (N := N) hN1 le_rfl).1]
  have hsm : sigmaMin N a (lowerEdge a) = symbol a θN - lowerEdge a := by
    rw [sigmaMin_eq_last ha0 ha1 hN1 hlam]; unfold lam; ring
  -- ε = T (1 + v), v = h(θ_N)/π
  set T := π / (N + lowerEdge a) with hT
  have hNl : (0 : ℝ) < N + lowerEdge a := by linarith
  have hG : (N + lowerEdge a) * ε = π + hL a θN := by
    have := hs.2; unfold Gph at this; unfold hL; rw [hε]; linarith
  set v := hL a θN / π with hv
  have hεT : ε = T * (1 + v) := by
    rw [hT, hv]; field_simp; linarith
  have hvb : |v| ≤ L2mu a * π ^ 2 / N ^ 2 := by
    rw [hv, abs_div, abs_of_pos hpi, div_le_iff₀ hpi]
    have hb : |hL a θN| ≤ L2mu a * |ε| ^ 3 := hL_bound ha0 ha1 θN
    refine hb.trans ?_
    rw [abs_of_pos hε0]
    have h3 : ε ^ 3 ≤ (π / N) ^ 3 := pow_le_pow_left₀ hε0.le hεle 3
    have h4 : (π / N) ^ 3 ≤ π ^ 3 / N ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (N : ℝ) ^ 2 ≤ N ^ 3 := by nlinarith
      nlinarith [pow_pos hpi 3]
    calc L2mu a * ε ^ 3 ≤ L2mu a * (π ^ 3 / N ^ 2) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) hL2
      _ = L2mu a * π ^ 2 / N ^ 2 * π := by ring
  have hloc : |(symbol a θN - lowerEdge a) - kapL a * ε ^ 2| ≤ cL a * ε ^ 2 * (kapL a * ε ^ 2) :=
    low_local ha0 ha1 hε0.le hε1
  have hx : cL a * ε ^ 2 ≤ cL a * π ^ 2 / N ^ 2 := by
    have : ε ^ 2 ≤ (π / N) ^ 2 := pow_le_pow_left₀ hε0.le hεle 2
    rw [div_pow] at this
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left this hcL
  have hloc' : |(symbol a θN - lowerEdge a) - kapL a * ε ^ 2| ≤
      cL a * π ^ 2 / N ^ 2 * (kapL a * ε ^ 2) :=
    hloc.trans (mul_le_mul_of_nonneg_right hx (by positivity))
  have hasm := edge_assemble hkL (by positivity) hεT hvb hδ1 hloc'
  rw [hsm]
  refine hasm.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  unfold KeL
  have hN2 : (1 : ℝ) ≤ N ^ 2 := by nlinarith
  have hc1 : 0 ≤ cL a * π ^ 2 := by positivity
  have hc2 : 0 ≤ L2mu a * π ^ 2 := by positivity
  have : cL a * π ^ 2 / N ^ 2 * (L2mu a * π ^ 2 / N ^ 2) ≤ cL a * π ^ 2 * (L2mu a * π ^ 2) / N ^ 2 := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_nonneg hc1 hc2
    nlinarith [mul_le_mul_of_nonneg_left hN2 this]
  rw [add_div, add_div, mul_div_assoc 3,
    show 3 * (cL a * π ^ 2) * (L2mu a * π ^ 2) / (N : ℝ) ^ 2 =
      3 * (cL a * π ^ 2 * (L2mu a * π ^ 2) / N ^ 2) by ring]
  linarith

/-- **`thm:edges`, eq. `(edge-low-kappa)`**: at `τ = μ₋`, for `N ≥ n_E(a)`, `B_N` is nonsingular and
`|κ₂ - 4μ₊²(N+μ₋)²/π²| ≤ (K/N²) · 4μ₊²(N+μ₋)²/π²`. -/
theorem thm_edge_lower_kappa (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : nE a ≤ N) :
    Nonsingular N a (lowerEdge a) ∧
      |kappa N a (lowerEdge a) - 4 * upperEdge a ^ 2 * ((N + lowerEdge a) / π) ^ 2| ≤
        KkL a / N ^ 2 * (4 * upperEdge a ^ 2 * ((N + lowerEdge a) / π) ^ 2) := by
  obtain ⟨hN4, -, -, hy2⟩ := nE_spec ha0 ha1 hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hpi := Real.pi_pos
  have hl0 := lowerEdge_pos ha0 ha1
  have hW := Wband_pos ha0 ha1
  have hu0 : 0 < upperEdge a := by unfold Wband at hW; linarith
  have h1a : 0 < 1 - a := by linarith
  have hkL : 0 < kapL a := by unfold kapL; positivity
  have hL := L2mu_nonneg ha0 ha1
  have hKe : 0 ≤ KeL a := by unfold KeL cL; positivity
  set T := π / (N + lowerEdge a) with hT
  have hT0 : 0 < T := by positivity
  have hS : 0 < kapL a * T ^ 2 := by positivity
  have hmin := thm_edge_lower_smin ha0 ha1 hN
  have hy0 : 0 ≤ KeL a / N ^ 2 := by positivity
  have hsmin : 0 < sigmaMin N a (lowerEdge a) := by
    rw [abs_le] at hmin
    nlinarith [mul_le_mul_of_nonneg_right hy2 hS.le]
  refine ⟨(nonsingular_iff_sigmaMin_pos ha0 ha1 (by omega) _).2 hsmin, ?_⟩
  have hmax : |sigmaMax N a (lowerEdge a) - Wband a| ≤ L2mu a * π ^ 2 / N ^ 2 := by
    have h := thm_smax_general ha0 ha1 hN1 (lowerEdge a)
    have e : max (|upperEdge a - lowerEdge a|) (|lowerEdge a - lowerEdge a|) = Wband a := by
      unfold Wband at hW ⊢
      rw [sub_self, abs_zero, abs_of_pos hW, max_eq_left hW.le]
    rwa [e] at h
  have hk := kappa_assemble hW hS (by positivity) (sigmaMax_nonneg' hN1 a _) hy0 hy2 hmax hmin
  have hWS : Wband a / (kapL a * T ^ 2) = 4 * upperEdge a ^ 2 * ((N + lowerEdge a) / π) ^ 2 := by
    rw [← div_div, Wband_div_kapL ha0 ha1, hT, div_pow, div_pow]
    field_simp
  unfold kappa
  rw [hWS] at hk
  refine hk.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact edge_kappa_const (by positivity) hKe hN1 _ hW

end Edges


/-! ### Master theorem -/

/-- **`thm:main-conditioning`** (all five regimes, with explicit constants and thresholds).
For fixed `0 < a < 1`:
1. `τ < μ₋`: strict uniform bound and limit;
2. `τ = μ₋`: `κ₂ = 4μ₊²(N+μ₋)²/π² · (1 + O(N⁻²))` for `N ≥ n_E(a)`;
3. `μ₋ < τ < μ₊`: at every nonsingular `N ≥ n₂(a,τ)`, `σ_min = πγ d_N/(N+τ) · (1 + O(N⁻¹))` and
   `κ₂ = C (N+τ)/d_N · (1 + O(N⁻¹))`;
4. `τ = μ₊`: `κ₂ = 4μ₋²(N+μ₊)²/π² · (1 + O(N⁻²))` for `N ≥ n_E(a)`;
5. `τ > μ₊`: strict uniform bound and limit. -/
theorem thm_main_conditioning (ha0 : 0 < a) (ha1 : a < 1) :
    (∀ τ : ℝ, τ < lowerEdge a →
      (∀ N : ℕ, 2 ≤ N → Nonsingular N a τ ∧
          kappa N a τ < (upperEdge a - τ) / (lowerEdge a - τ)) ∧
        Tendsto (fun N : ℕ => kappa N a τ) atTop
          (𝓝 ((upperEdge a - τ) / (lowerEdge a - τ)))) ∧
    (∀ N : ℕ, nE a ≤ N → Nonsingular N a (lowerEdge a) ∧
      |kappa N a (lowerEdge a) - 4 * upperEdge a ^ 2 * ((N + lowerEdge a) / π) ^ 2| ≤
        KkL a / N ^ 2 * (4 * upperEdge a ^ 2 * ((N + lowerEdge a) / π) ^ 2)) ∧
    (∀ τ : ℝ, lowerEdge a < τ → τ < upperEdge a → ∀ N : ℕ, n2 a τ ≤ N → Nonsingular N a τ →
      |sigmaMin N a τ / (π * gam a τ * dN N a τ / (N + τ)) - 1| ≤ Ksm a τ / N ∧
      (1 - Kkap a τ / N) * (Cint a τ * (N + τ) / dN N a τ) ≤ kappa N a τ ∧
      kappa N a τ ≤ (1 + Kkap a τ / N) * (Cint a τ * (N + τ) / dN N a τ)) ∧
    (∀ N : ℕ, nE a ≤ N → Nonsingular N a (upperEdge a) ∧
      |kappa N a (upperEdge a) - 4 * lowerEdge a ^ 2 * ((N + upperEdge a) / π) ^ 2| ≤
        KkU a / N ^ 2 * (4 * lowerEdge a ^ 2 * ((N + upperEdge a) / π) ^ 2)) ∧
    (∀ τ : ℝ, upperEdge a < τ →
      (∀ N : ℕ, 2 ≤ N → Nonsingular N a τ ∧
          kappa N a τ < (τ - lowerEdge a) / (τ - upperEdge a)) ∧
        Tendsto (fun N : ℕ => kappa N a τ) atTop
          (𝓝 ((τ - lowerEdge a) / (τ - upperEdge a)))) := by
  refine ⟨fun τ hτ => thm_outside_lower ha0 ha1 hτ, fun N hN => thm_edge_lower_kappa ha0 ha1 hN,
    fun τ hl hu N hN hns => ?_, fun N hN => thm_edge_upper_kappa ha0 ha1 hN,
    fun τ hτ => thm_outside_upper ha0 ha1 hτ⟩
  have h : InteriorParam a τ := ⟨ha0, ha1, hl, hu⟩
  have hk := thm_kappa_relative h hN hns
  exact ⟨smin_ratio h (le_trans (Nat.le_add_right _ _) hN) hns, hk.1, hk.2⟩

end ShiftedKMS
