import KMS.Phase

/-!
# Gate 2.3 — the Diophantine-triangle coordinates (`thm:triangle`)

* `crossAngle a τ = arccos ((1 + a² - (1 - a²)/τ)/(2a))`: the unique `θ_τ ∈ (0, π)` with
  `μ_a(θ_τ) = τ` (manuscript eqs. `(crossing)`, `(costheta)`).
* `alphaOf a τ = θ_τ/π`, `betaOf a τ = 1 - ψ_a(θ_τ)/π` (eq. `(alphabeta)`).
* `triangle_forward`: interior `(a, τ)` lands in `𝒟 = {α > 0, β > 0, α + β < 1}` and the inverse
  formulas `(inverse)` hold.
* `triangle_inverse`: every `(α, β) ∈ 𝒟` comes from the interior pair given by `(inverse)`.
* `triangle_bijOn`: `(a, τ) ↦ (α, β)` is a bijection from the interior region onto `𝒟`.
-/

open Real Set

namespace ShiftedKMS

/-- Interior parameter region: `0 < a < 1`, `μ₋(a) < τ < μ₊(a)` (manuscript eq. `(interior)`). -/
def InteriorParam (a τ : ℝ) : Prop := 0 < a ∧ a < 1 ∧ lowerEdge a < τ ∧ τ < upperEdge a

/-- The open triangle `𝒟` (manuscript eq. `(triangle)`). -/
def triangleSet : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}

/-- The interior parameter region as a set of pairs `(a, τ)`. -/
def regionSet : Set (ℝ × ℝ) := {p | InteriorParam p.1 p.2}

/-- `cos θ_τ`, manuscript eq. `(costheta)`. -/
noncomputable def crossCos (a τ : ℝ) : ℝ := (1 + a ^ 2 - (1 - a ^ 2) / τ) / (2 * a)

/-- The crossing angle `θ_τ`. -/
noncomputable def crossAngle (a τ : ℝ) : ℝ := Real.arccos (crossCos a τ)

noncomputable def alphaOf (a τ : ℝ) : ℝ := crossAngle a τ / π
noncomputable def betaOf (a τ : ℝ) : ℝ := 1 - psi a (crossAngle a τ) / π

/-- The inverse map, manuscript eq. `(inverse)`. -/
noncomputable def aOf (α β : ℝ) : ℝ := Real.cos (π * (α + β) / 2) / Real.cos (π * (α - β) / 2)
noncomputable def tauOf (α β : ℝ) : ℝ := Real.sin (π * β) / Real.sin (π * α)

lemma lowerEdge_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < lowerEdge a := by
  unfold lowerEdge; apply div_pos <;> linarith

lemma InteriorParam.tau_pos {a τ : ℝ} (h : InteriorParam a τ) : 0 < τ :=
  (lowerEdge_pos h.1 h.2.1).trans h.2.2.1

lemma crossCos_mem {a τ : ℝ} (h : InteriorParam a τ) :
    -1 < crossCos a τ ∧ crossCos a τ < 1 := by
  obtain ⟨ha0, ha1, hlo, hhi⟩ := h
  have hτ : 0 < τ := (lowerEdge_pos ha0 ha1).trans hlo
  have h1a : 0 < 1 - a := by linarith
  have h1a' : 0 < 1 + a := by linarith
  unfold lowerEdge at hlo; unfold upperEdge at hhi
  rw [div_lt_iff₀ h1a'] at hlo
  rw [lt_div_iff₀ h1a] at hhi
  have k1 : (1 - a) ^ 2 * τ < 1 - a ^ 2 := by nlinarith
  have k2 : 1 - a ^ 2 < (1 + a) ^ 2 * τ := by nlinarith
  have q1 : (1 - a) ^ 2 < (1 - a ^ 2) / τ := by rw [lt_div_iff₀ hτ]; linarith
  have q2 : (1 - a ^ 2) / τ < (1 + a) ^ 2 := by rw [div_lt_iff₀ hτ]; linarith
  unfold crossCos
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_one (by positivity)]; nlinarith

lemma crossAngle_mem {a τ : ℝ} (h : InteriorParam a τ) : crossAngle a τ ∈ Ioo 0 π := by
  obtain ⟨h1, h2⟩ := crossCos_mem h
  exact ⟨Real.arccos_pos.2 h2, Real.arccos_lt_pi.2 h1⟩

lemma cos_crossAngle {a τ : ℝ} (h : InteriorParam a τ) :
    Real.cos (crossAngle a τ) = crossCos a τ := by
  obtain ⟨h1, h2⟩ := crossCos_mem h
  exact Real.cos_arccos h1.le h2.le

/-- `μ_a(θ_τ) = τ` (manuscript eq. `(crossing)`). -/
theorem symbol_crossAngle {a τ : ℝ} (h : InteriorParam a τ) : symbol a (crossAngle a τ) = τ := by
  have hτ := h.tau_pos
  have ha0 := h.1
  have ha1 := h.2.1
  unfold symbol
  rw [cos_crossAngle h, crossCos]
  have h1 : 1 - a ^ 2 ≠ 0 := by nlinarith
  field_simp
  have hx : (1 - a ^ 2)⁻¹ * (1 - a ^ 2) = 1 := inv_mul_cancel₀ h1
  linear_combination hx

/-- Uniqueness of the crossing angle on `[0, π]`. -/
theorem crossAngle_unique {a τ θ : ℝ} (h : InteriorParam a τ) (hθ : θ ∈ Icc 0 π)
    (hs : symbol a θ = τ) : θ = crossAngle a τ := by
  have hτ := h.tau_pos
  have ha0 := h.1
  have ha1 := h.2.1
  have hR := Ra_pos ha0 ha1 θ
  have hc : Real.cos θ = crossCos a τ := by
    rw [symbol_eq_div_Ra, div_eq_iff hR.ne'] at hs
    unfold Ra at hs
    unfold crossCos
    field_simp
    nlinarith
  rw [crossAngle, ← hc, Real.arccos_cos hθ.1 hθ.2]

/-! ### General interior-angle identities -/

/-- `μ_a(θ) = sin ψ_a(θ) / sin θ`. -/
lemma symbol_eq_sin_div {a θ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hθ : θ ∈ Ioo 0 π) :
    symbol a θ = Real.sin (psi a θ) / Real.sin θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hR := Ra_pos ha0 ha1 θ
  have h := sin_psi ha0 ha1 θ
  unfold Ea at h
  rw [symbol_eq_div_Ra, div_eq_div_iff hR.ne' hs.ne']
  linarith

/-- With `ψ = θ + 2φ`: `a · sin(θ + φ) = sin φ`, `sin(θ + φ) > 0`. -/
lemma a_sin_eq {a θ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hθ : θ ∈ Ioo 0 π) :
    let φ := Real.arctan (a * Real.sin θ / (1 - a * Real.cos θ))
    a * Real.sin (θ + φ) = Real.sin φ ∧ 0 < Real.sin (θ + φ) := by
  intro φ
  have hw := one_sub_a_cos_pos ha0 ha1 θ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hCp : 0 < Real.cos φ := Real.cos_arctan_pos _
  have h1 : Real.sin φ * (1 - a * Real.cos θ) = a * Real.sin θ * Real.cos φ := by
    have ht : Real.tan φ = a * Real.sin θ / (1 - a * Real.cos θ) := Real.tan_arctan _
    rw [Real.tan_eq_sin_div_cos, div_eq_iff hCp.ne'] at ht
    rw [ht]; field_simp
  rw [Real.sin_add]
  constructor
  · linear_combination (-1) * h1
  · -- `w · sin(θ+φ) = sin θ cos φ > 0`
    have : (1 - a * Real.cos θ) * (Real.sin θ * Real.cos φ + Real.cos θ * Real.sin φ) =
        Real.sin θ * Real.cos φ := by linear_combination Real.cos θ * h1
    have hp : 0 < Real.sin θ * Real.cos φ := mul_pos hs hCp
    by_contra hneg
    push_neg at hneg
    nlinarith

/-- **`thm:triangle`, forward half and eq. `(inverse)`.** -/
theorem triangle_forward {a τ : ℝ} (h : InteriorParam a τ) :
    (alphaOf a τ, betaOf a τ) ∈ triangleSet ∧
      τ = tauOf (alphaOf a τ) (betaOf a τ) ∧ a = aOf (alphaOf a τ) (betaOf a τ) := by
  have ha0 := h.1
  have ha1 := h.2.1
  set θ := crossAngle a τ with hθdef
  have hθ : θ ∈ Ioo 0 π := crossAngle_mem h
  have hpi := Real.pi_pos
  have hψ : psi a θ ∈ Ioo 0 π := psi_mem_Ioo ha0 ha1 hθ
  have hlt : θ < psi a θ := lt_psi ha0 ha1 hθ
  have eα : π * alphaOf a τ = θ := by rw [hθdef]; unfold alphaOf; field_simp
  have eβ : π * betaOf a τ = π - psi a θ := by rw [hθdef]; unfold betaOf; field_simp
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · unfold alphaOf; exact div_pos hθ.1 hpi
  · unfold betaOf; rw [sub_pos, div_lt_one hpi]; exact hψ.2
  · unfold alphaOf betaOf
    rw [← sub_pos]
    have : 1 - (θ / π + (1 - psi a θ / π)) = (psi a θ - θ) / π := by field_simp; ring
    rw [this]; exact div_pos (by linarith) hpi
  · unfold tauOf
    rw [eα, eβ, Real.sin_pi_sub, ← symbol_eq_sin_div ha0 ha1 hθ, symbol_crossAngle h]
  · unfold aOf
    obtain ⟨hk, hpos⟩ := a_sin_eq ha0 ha1 hθ
    set φ := Real.arctan (a * Real.sin θ / (1 - a * Real.cos θ)) with hφ
    have hψφ : psi a θ = θ + 2 * φ := rfl
    have e1 : π * (alphaOf a τ + betaOf a τ) / 2 = π / 2 - φ := by
      have : π * (alphaOf a τ + betaOf a τ) = θ + (π - psi a θ) := by rw [mul_add, eα, eβ]
      rw [this, hψφ]; ring
    have e2 : π * (alphaOf a τ - betaOf a τ) / 2 = (θ + φ) - π / 2 := by
      have : π * (alphaOf a τ - betaOf a τ) = θ - (π - psi a θ) := by rw [mul_sub, eα, eβ]
      rw [this, hψφ]; ring
    rw [e1, e2, Real.cos_pi_div_two_sub, Real.cos_sub_pi_div_two, eq_div_iff hpos.ne', hk]

lemma symbol_strict_bounds {a θ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hθ : θ ∈ Ioo 0 π) :
    lowerEdge a < symbol a θ ∧ symbol a θ < upperEdge a := by
  have hc1 : Real.cos θ < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2.le hθ.1
    simpa using this
  have hc2 : -1 < Real.cos θ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
    simpa using this
  have hR := Ra_pos ha0 ha1 θ
  have hRlo : (1 - a) ^ 2 < Ra a θ := by unfold Ra; nlinarith
  have hRhi : Ra a θ < (1 + a) ^ 2 := by unfold Ra; nlinarith
  have hn : 0 < 1 - a ^ 2 := by nlinarith
  constructor
  · rw [lowerEdge_eq ha0, symbol_eq_div_Ra]
    exact div_lt_div_of_pos_left hn hR hRhi
  · have h1 : (1 - a) ≠ 0 := by intro h; linarith
    have e : upperEdge a = (1 - a ^ 2) / (1 - a) ^ 2 := by
      unfold upperEdge
      rw [eq_div_iff (pow_ne_zero 2 h1)]
      field_simp
      ring
    rw [e, symbol_eq_div_Ra]
    exact div_lt_div_of_pos_left hn (by positivity) hRlo

/-- **`thm:triangle`, inverse half**: every `(α, β) ∈ 𝒟` arises from the interior pair
`(a, τ)` of eq. `(inverse)`, which maps back to `(α, β)`. -/
theorem triangle_inverse {α β : ℝ} (h : (α, β) ∈ triangleSet) :
    InteriorParam (aOf α β) (tauOf α β) ∧
      alphaOf (aOf α β) (tauOf α β) = α ∧ betaOf (aOf α β) (tauOf α β) = β := by
  obtain ⟨hα, hβ, hαβ⟩ := h
  have hpi := Real.pi_pos
  set θ := π * α with hθdef
  set φ0 := π * (1 - α - β) / 2 with hφ0
  have hθ : θ ∈ Ioo 0 π := ⟨by positivity, by nlinarith⟩
  have hφ0pos : 0 < φ0 := by rw [hφ0]; apply div_pos _ two_pos; nlinarith
  have hφ0lt : φ0 < π / 2 := by rw [hφ0]; nlinarith
  have hsφ0 : 0 < Real.sin φ0 := Real.sin_pos_of_pos_of_lt_pi hφ0pos (by linarith)
  have hcφ0 : 0 < Real.cos φ0 := Real.cos_pos_of_mem_Ioo ⟨by linarith, hφ0lt⟩
  -- the two cosines of eq. `(inverse)`
  have e1 : Real.cos (π * (α + β) / 2) = Real.sin φ0 := by
    rw [show π * (α + β) / 2 = π / 2 - φ0 by rw [hφ0]; ring, Real.cos_pi_div_two_sub]
  have e2 : Real.cos (π * (α - β) / 2) = Real.sin (θ + φ0) := by
    rw [show π * (α - β) / 2 = (θ + φ0) - π / 2 by rw [hφ0, hθdef]; ring, Real.cos_sub_pi_div_two]
  have hsum_lo : 0 < θ + φ0 := by linarith [hθ.1]
  have hsum_hi : θ + φ0 < π := by rw [hφ0, hθdef]; nlinarith
  have hsθφ : 0 < Real.sin (θ + φ0) := Real.sin_pos_of_pos_of_lt_pi hsum_lo hsum_hi
  have ha : aOf α β = Real.sin φ0 / Real.sin (θ + φ0) := by unfold aOf; rw [e1, e2]
  set a := aOf α β with hadef
  have ha0 : 0 < a := by rw [ha]; exact div_pos hsφ0 hsθφ
  have ha1 : a < 1 := by
    rw [ha, div_lt_one hsθφ, ← sub_pos, Real.sin_sub_sin]
    apply mul_pos (mul_pos two_pos _) _
    · apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hθ.1, hθ.2]
    · apply Real.cos_pos_of_mem_Ioo; constructor <;> nlinarith
  -- the phase at `θ` is `π(1 - β)`
  have hw := one_sub_a_cos_pos ha0 ha1 θ
  have hu : a * Real.sin θ / (1 - a * Real.cos θ) = Real.tan φ0 := by
    rw [Real.tan_eq_sin_div_cos, div_eq_div_iff hw.ne' hcφ0.ne']
    have hk : a * Real.sin (θ + φ0) = Real.sin φ0 := by rw [ha]; field_simp
    rw [Real.sin_add] at hk
    linear_combination hk
  have hpsi : psi a θ = π * (1 - β) := by
    unfold psi
    rw [hu, Real.arctan_tan (by linarith) hφ0lt, hφ0, hθdef]; ring
  -- `μ_a(θ) = τ`
  have hsym : symbol a θ = tauOf α β := by
    rw [symbol_eq_sin_div ha0 ha1 hθ, hpsi, tauOf, ← hθdef,
      show π * (1 - β) = π - π * β by ring, Real.sin_pi_sub]
  have hb := symbol_strict_bounds ha0 ha1 hθ
  have hint : InteriorParam a (tauOf α β) := ⟨ha0, ha1, hsym ▸ hb.1, hsym ▸ hb.2⟩
  have hcross : θ = crossAngle a (tauOf α β) :=
    crossAngle_unique hint ⟨hθ.1.le, hθ.2.le⟩ hsym
  refine ⟨hint, ?_, ?_⟩
  · unfold alphaOf; rw [← hcross, hθdef]; field_simp
  · unfold betaOf; rw [← hcross, hpsi]; field_simp; ring

/-- **`thm:triangle`**: `(a, τ) ↦ (α, β)` is a bijection from the interior parameter region onto
the open triangle `𝒟`, with inverse eq. `(inverse)`. -/
theorem triangle_bijOn :
    Set.BijOn (fun p : ℝ × ℝ => (alphaOf p.1 p.2, betaOf p.1 p.2)) regionSet triangleSet := by
  refine ⟨fun p hp => (triangle_forward hp).1, ?_, ?_⟩
  · intro p hp q hq hpq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨-, hτp, hap⟩ := triangle_forward hp
    obtain ⟨-, hτq, haq⟩ := triangle_forward hq
    rw [hpq.1, hpq.2] at hτp hap
    exact Prod.ext (hap.trans haq.symm) (hτp.trans hτq.symm)
  · rintro ⟨α, β⟩ hab
    obtain ⟨hint, h1, h2⟩ := triangle_inverse hab
    exact ⟨(aOf α β, tauOf α β), hint, by simp only [h1, h2]⟩

end ShiftedKMS
