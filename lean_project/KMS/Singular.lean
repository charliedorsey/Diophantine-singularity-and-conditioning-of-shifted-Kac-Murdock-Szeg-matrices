import KMS.Triangle
import Mathlib.Algebra.Order.Round
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Gate 3.0 / 3.1 (+ `prop:inertia`, `prop:kernel`) — exact determinant and exact singularity

Exact, algebraic half of Gate 3 (no topology / measure here).

* `distZ x = |x - round x|` — the manuscript's `‖x‖ = dist(x, ℤ)`; `dN N a τ = ‖Nα - β‖`.
* `thm_det` — manuscript eq. `(det)`; `thm_detdepth` — eq. `(detdepth)`.
* `thm_sing` — eq. `(sing)`: `det B_N = 0 ↔ Nα - β ∈ ℤ`.
* `shifted_ker_eq_span`, `shifted_nullity_one` — `prop:kernel` and "nullity exactly one".
* `thm_inertia` — `prop:inertia` (over the explicit simple spectrum of Gate 2).
-/

open Real Set Matrix

namespace ShiftedKMS

/-! ### Distance to the nearest integer -/

/-- `‖x‖ = dist(x, ℤ)`, realised as `|x - round x|`. -/
noncomputable def distZ (x : ℝ) : ℝ := |x - round x|

lemma distZ_add_int (x : ℝ) (m : ℤ) : distZ (x + m) = distZ x := by
  unfold distZ; rw [round_add_intCast]; push_cast; ring_nf

lemma distZ_eq_zero_iff (x : ℝ) : distZ x = 0 ↔ ∃ z : ℤ, x = z := by
  unfold distZ
  constructor
  · intro h; exact ⟨round x, by linarith [abs_eq_zero.1 h]⟩
  · rintro ⟨z, rfl⟩; simp only [round_intCast, sub_self, abs_zero]

lemma distZ_le_half (x : ℝ) : distZ x ≤ 1 / 2 := abs_sub_round x

lemma distZ_nonneg (x : ℝ) : 0 ≤ distZ x := abs_nonneg _

/-- `|sin (π x)| = sin (π ‖x‖)`. -/
lemma abs_sin_pi_mul (x : ℝ) : |Real.sin (π * x)| = Real.sin (π * distZ x) := by
  set y := x - round x with hy
  have hx : π * x = π * y + (round x : ℤ) * π := by rw [hy]; ring
  have h1 : |Real.sin (π * x)| = |Real.sin (π * y)| := by
    have hz : |((-1 : ℝ)) ^ (round x)| = 1 := by
      rcases Int.even_or_odd (round x) with he | ho
      · rw [he.neg_one_zpow, abs_one]
      · rw [ho.neg_one_zpow, abs_neg, abs_one]
    rw [hx, Real.sin_add_int_mul_pi, abs_mul, hz, one_mul]
  have hb : |y| ≤ 1 / 2 := abs_sub_round x
  have hpi := Real.pi_pos
  rw [h1, distZ, ← hy]
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg]
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    have := (abs_of_nonneg h) ▸ hb
    nlinarith
  · rw [abs_of_neg h, show π * y = -(π * -y) by ring, Real.sin_neg, abs_neg, abs_of_nonneg]
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith)
    have := (abs_of_neg h) ▸ hb
    nlinarith

/-- `d_N = ‖Nα - β‖` (manuscript eq. `(dN)`). -/
noncomputable def dN (N : ℕ) (a τ : ℝ) : ℝ := distZ (N * alphaOf a τ - betaOf a τ)

/-! ### The crossing in Chebyshev / phase coordinates -/

lemma chebX_crossAngle {a τ : ℝ} (h : InteriorParam a τ) :
    chebX a τ = -Real.cos (crossAngle a τ) := by
  rw [cos_crossAngle h, chebX, crossCos]
  have ha := h.1.ne'
  have hτ := h.tau_pos.ne'
  field_simp
  ring

lemma Ra_crossAngle {a τ : ℝ} (h : InteriorParam a τ) :
    Ra a (crossAngle a τ) = (1 - a ^ 2) / τ := by
  have hs := symbol_crossAngle h
  have hR := Ra_pos h.1 h.2.1 (crossAngle a τ)
  rw [symbol_eq_div_Ra, div_eq_iff hR.ne'] at hs
  rw [eq_div_iff h.tau_pos.ne']
  linarith

lemma crossAngle_eq_pi_alpha {a τ : ℝ} (_h : InteriorParam a τ) :
    crossAngle a τ = π * alphaOf a τ := by
  unfold alphaOf; field_simp

lemma psi_crossAngle {a τ : ℝ} (_h : InteriorParam a τ) :
    psi a (crossAngle a τ) = π * (1 - betaOf a τ) := by
  unfold betaOf; field_simp; ring

/-- `G_N(θ_τ) = π (Nα - β + 1)`. -/
lemma Gph_crossAngle {a τ : ℝ} (h : InteriorParam a τ) (N : ℕ) :
    Gph N a (crossAngle a τ) = π * (N * alphaOf a τ - betaOf a τ + 1) := by
  unfold Gph
  rw [psi_crossAngle h, crossAngle_eq_pi_alpha h]
  ring

lemma sin_pi_alpha_pos {a τ : ℝ} (h : InteriorParam a τ) : 0 < Real.sin (π * alphaOf a τ) := by
  rw [← crossAngle_eq_pi_alpha h]
  have hθ := crossAngle_mem h
  exact Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2

/-! ### G3.0 — the exact determinant -/

/-- **`thm:det`, eq. `(det)`**: for every interior pair and every `N ≥ 2`,
`det B_N(a,τ) = (-1)^{N+1} a^N τ^{N-1} sin π(Nα - β) / sin(πα)`. -/
theorem thm_det {a τ : ℝ} (h : InteriorParam a τ) {N : ℕ} (hN : 2 ≤ N) :
    (shifted N a τ).det =
      (-1) ^ (N + 1) * a ^ N * τ ^ (N - 1) *
        Real.sin (π * (N * alphaOf a τ - betaOf a τ)) / Real.sin (π * alphaOf a τ) := by
  have ha0 := h.1
  have ha1 := h.2.1
  have hτ := h.tau_pos
  have ha1' : a ^ 2 ≠ 1 := by nlinarith
  have hθ := crossAngle_mem h
  have hs : Real.sin (crossAngle a τ) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  rw [det_shifted_secular hN ha0.ne' ha1' hτ.ne' (chebX_crossAngle h) hs, lem_phase ha0 ha1,
    Ra_crossAngle h]
  have harg : (N : ℝ) * crossAngle a τ + psi a (crossAngle a τ) =
      π * (N * alphaOf a τ - betaOf a τ) + π := by
    rw [psi_crossAngle h, crossAngle_eq_pi_alpha h]; ring
  rw [harg, Real.sin_add_pi, crossAngle_eq_pi_alpha h]
  have hsa := sin_pi_alpha_pos h
  have h1a : (1 - a ^ 2) ≠ 0 := by nlinarith
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega]
  field_simp
  ring

/-- **`thm:det`, eq. `(detdepth)`**: `|det B_N| = a^N τ^{N-1} sin(π d_N) / sin(πα)`. -/
theorem thm_detdepth {a τ : ℝ} (h : InteriorParam a τ) {N : ℕ} (hN : 2 ≤ N) :
    |(shifted N a τ).det| =
      a ^ N * τ ^ (N - 1) * Real.sin (π * dN N a τ) / Real.sin (π * alphaOf a τ) := by
  rw [thm_det h hN, abs_div, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_pow, abs_pow, abs_of_pos h.1, abs_of_pos h.tau_pos,
    abs_of_pos (sin_pi_alpha_pos h), abs_sin_pi_mul, dN]

/-! ### G3.1 — exact singularity -/

/-- **`thm:sing`, eq. `(sing)`**: `B_N(a,τ)` is singular iff `Nα - β ∈ ℤ`. -/
theorem thm_sing {a τ : ℝ} (h : InteriorParam a τ) {N : ℕ} (hN : 2 ≤ N) :
    (shifted N a τ).det = 0 ↔ ∃ z : ℤ, (N : ℝ) * alphaOf a τ - betaOf a τ = z := by
  rw [thm_det h hN, div_eq_zero_iff, or_iff_left (sin_pi_alpha_pos h).ne']
  have hpow : (-1 : ℝ) ^ (N + 1) * a ^ N * τ ^ (N - 1) ≠ 0 := by
    have := h.1; have := h.tau_pos
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)) (by positivity)
  rw [mul_eq_zero, or_iff_right hpow, Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi := Real.pi_pos
    have h2 : π * ((N : ℝ) * alphaOf a τ - betaOf a τ - n) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hpi.ne'
    · linarith
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [hz]; ring⟩

/-- Equivalent form via `d_N`: singular iff `d_N = 0`. -/
theorem thm_sing_dN {a τ : ℝ} (h : InteriorParam a τ) {N : ℕ} (hN : 2 ≤ N) :
    (shifted N a τ).det = 0 ↔ dN N a τ = 0 := by
  rw [thm_sing h hN, dN, distZ_eq_zero_iff]

/-! ### Eigenvector expansion (from the simple spectrum of Gate 2) -/

lemma kms_expand {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) (x : Fin N → ℝ) :
    ∃ c : Fin N → ℝ, ∑ k, c k • eigVecK N a k = x := by
  have hli := eigVecK_linearIndependent ha0 ha1 hN
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card])
  have hxmem : x ∈ Submodule.span ℝ (Set.range (eigVecK N a)) := by
    rw [hspan]; exact Submodule.mem_top
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hxmem

lemma kms_coeff {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 2 ≤ N) {lam : ℝ}
    (c : Fin N → ℝ) (hx : kms N a *ᵥ (∑ k, c k • eigVecK N a k) =
      lam • ∑ k, c k • eigVecK N a k) (k : Fin N) :
    c k * (eigValK N a k - lam) = 0 := by
  have hli := eigVecK_linearIndependent ha0 ha1 hN
  have hT : Matrix.toLin' (kms N a) (∑ k, c k • eigVecK N a k) =
      ∑ k, (c k * eigValK N a k) • eigVecK N a k := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, Matrix.toLin'_apply]
    obtain ⟨h1, -⟩ := kms_eigenpair ha0 ha1 hN (by omega : 1 ≤ k.val + 1)
      (by omega : k.val + 1 ≤ N)
    rw [eigVecK, h1, smul_smul, eigValK]
  rw [Matrix.toLin'_apply, hx, Finset.smul_sum] at hT
  have hzero : ∑ k, (c k * eigValK N a k - lam * c k) • eigVecK N a k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, smul_smul] at hT ⊢
    rw [← hT, sub_self]
  have := (Fintype.linearIndependent_iff.1 hli) _ hzero k
  linear_combination this

/-! ### Nullity one and the kernel (`prop:kernel`) -/

/-- At a singular dimension the crossing angle is the eigenangle `θ_{z+1}`. -/
lemma crossAngle_eq_eigAngle {a τ : ℝ} (h : InteriorParam a τ) {N : ℕ} {z : ℤ}
    (hz : (N : ℝ) * alphaOf a τ - betaOf a τ = z) :
    1 ≤ z + 1 ∧ z + 1 ≤ N ∧ crossAngle a τ = eigAngle N a (z + 1).toNat := by
  have ha0 := h.1
  have ha1 := h.2.1
  have hθ := crossAngle_mem h
  have hG := Gph_crossAngle h N
  rw [hz] at hG
  have hm := strictMono_Gph ha0 ha1 N
  have hlo : 0 < Gph N a (crossAngle a τ) := by
    have := hm hθ.1; rwa [Gph_zero] at this
  have hhi : Gph N a (crossAngle a τ) < (N + 1) * π := by
    have := hm hθ.2; rwa [Gph_pi] at this
  have hpi := Real.pi_pos
  rw [hG] at hlo hhi
  have h1 : (0 : ℝ) < z + 1 := by nlinarith
  have h2 : (z : ℝ) + 1 < N + 1 := by nlinarith
  have h1' : 0 < z + 1 := by exact_mod_cast h1
  have h2' : z + 1 < N + 1 := by exact_mod_cast h2
  refine ⟨by omega, by omega, ?_⟩
  apply eq_eigAngle ha0 ha1 (by omega) (by omega) hθ
  rw [Gph_crossAngle h, hz]
  have : (((z + 1).toNat : ℕ) : ℝ) = (z : ℝ) + 1 := by
    have e : (((z + 1).toNat : ℕ) : ℤ) = z + 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast e
  rw [this]; ring

/-- **`prop:kernel` / nullity one**: at a singular dimension,
`B_N x = 0 ↔ x ∈ span {v(θ_τ)}` with `v_j = sin((j+1)θ_τ) - a sin(jθ_τ)`. -/
theorem shifted_mulVec_eq_zero_iff {a τ : ℝ} (h : InteriorParam a τ) {N : ℕ} (hN : 2 ≤ N)
    (hsing : (shifted N a τ).det = 0) (x : Fin N → ℝ) :
    shifted N a τ *ᵥ x = 0 ↔ ∃ c : ℝ, c • eigVec N a (crossAngle a τ) = x := by
  have ha0 := h.1
  have ha1 := h.2.1
  obtain ⟨z, hz⟩ := (thm_sing h hN).1 hsing
  obtain ⟨hk1, hkN, hθk⟩ := crossAngle_eq_eigAngle h hz
  set k := (z + 1).toNat with hkdef
  have hk1' : 1 ≤ k := by omega
  have hkN' : k ≤ N := by omega
  set j : Fin N := ⟨k - 1, by omega⟩ with hj
  have hjk : j.val + 1 = k := by simp only [hj]; omega
  have hvj : eigVecK N a j = eigVec N a (crossAngle a τ) := by rw [eigVecK, hjk, hθk]
  have hμj : eigValK N a j = τ := by rw [eigValK, hjk, ← hθk, symbol_crossAngle h]
  have hdiag : ∀ y : Fin N → ℝ, shifted N a τ *ᵥ y = kms N a *ᵥ y - τ • y := by
    intro y
    rw [shifted, Matrix.sub_mulVec]
    congr 1
    funext i
    simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro hx
    have hT : kms N a *ᵥ x = τ • x := by rw [hdiag, sub_eq_zero] at hx; exact hx
    obtain ⟨c, hc⟩ := kms_expand ha0 ha1 hN x
    rw [← hc] at hT
    have hcoef := kms_coeff ha0 ha1 hN c hT
    refine ⟨c j, ?_⟩
    rw [← hc, ← hvj, Finset.sum_eq_single j]
    · intro i _ hij
      have hne : eigValK N a i ≠ τ := by
        rw [← hμj]; exact fun e => hij (eigValK_injective ha0 ha1 N e)
      have := hcoef i
      rcases mul_eq_zero.1 this with h0 | h0
      · rw [h0, zero_smul]
      · exact absurd (sub_eq_zero.1 h0) hne
    · intro hj'; exact absurd (Finset.mem_univ j) hj'
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul, hθk, shifted_eigenpair ha0 ha1 hN hk1' hkN', ← hθk,
      symbol_crossAngle h, sub_self, zero_smul, smul_zero]

/-- **`prop:kernel`**, as an equality of subspaces. -/
theorem shifted_ker_eq_span {a τ : ℝ} (h : InteriorParam a τ) {N : ℕ} (hN : 2 ≤ N)
    (hsing : (shifted N a τ).det = 0) :
    LinearMap.ker (Matrix.toLin' (shifted N a τ)) =
      Submodule.span ℝ {eigVec N a (crossAngle a τ)} := by
  ext x
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, Submodule.mem_span_singleton]
  exact shifted_mulVec_eq_zero_iff h hN hsing x

/-- **`thm:sing` (nullity)**: at a singular dimension the nullity is exactly one. -/
theorem shifted_nullity_one {a τ : ℝ} (h : InteriorParam a τ) {N : ℕ} (hN : 2 ≤ N)
    (hsing : (shifted N a τ).det = 0) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (shifted N a τ))) = 1 := by
  rw [shifted_ker_eq_span h hN hsing]
  apply finrank_span_singleton
  have hθ := crossAngle_mem h
  exact eigVec_ne_zero (by omega) a (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'

/-! ### `prop:inertia` — the inertia staircase -/

/-- `μ_a` is strictly decreasing on `[0, π]`. -/
lemma symbol_strictAntiOn {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    StrictAntiOn (symbol a) (Icc 0 π) := by
  intro x hx y hy hxy
  have hc := Real.strictAntiOn_cos hx hy hxy
  rw [symbol_eq_div_Ra, symbol_eq_div_Ra]
  apply div_lt_div_of_pos_left (by nlinarith) (Ra_pos ha0 ha1 x)
  unfold Ra; nlinarith

/-- Number of positive eigenvalues of `B_N(a,τ)`, counted over the explicit (simple, complete)
spectrum `{μ_a(θ_k) - τ}` of Gate 2 (`kms_spectrum`, `eigValK_injective`). -/
noncomputable def posCount (N : ℕ) (a τ : ℝ) : ℕ :=
  ((Finset.Icc 1 N).filter fun k => τ < symbol a (eigAngle N a k)).card

/-- Number of zero eigenvalues of `B_N(a,τ)`. -/
noncomputable def zeroCount (N : ℕ) (a τ : ℝ) : ℕ :=
  ((Finset.Icc 1 N).filter fun k => symbol a (eigAngle N a k) = τ).card

/-- Number of negative eigenvalues of `B_N(a,τ)`. -/
noncomputable def negCount (N : ℕ) (a τ : ℝ) : ℕ :=
  ((Finset.Icc 1 N).filter fun k => symbol a (eigAngle N a k) < τ).card

lemma symbol_lt_iff {a τ : ℝ} (h : InteriorParam a τ) {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    τ < symbol a (eigAngle N a k) ↔ (k : ℝ) < N * alphaOf a τ - betaOf a τ + 1 := by
  have ha0 := h.1
  have ha1 := h.2.1
  have hk := (eigAngle_spec ha0 ha1 hk1 hkN)
  have hθ := crossAngle_mem h
  have hanti := symbol_strictAntiOn ha0 ha1
  have mk : eigAngle N a k ∈ Icc 0 π := ⟨hk.1.1.le, hk.1.2.le⟩
  have mt : crossAngle a τ ∈ Icc 0 π := ⟨hθ.1.le, hθ.2.le⟩
  have e : τ < symbol a (eigAngle N a k) ↔
      symbol a (crossAngle a τ) < symbol a (eigAngle N a k) := by rw [symbol_crossAngle h]
  have iff1 : symbol a (crossAngle a τ) < symbol a (eigAngle N a k) ↔
      eigAngle N a k < crossAngle a τ := by
    constructor
    · intro hl
      by_contra hc
      push_neg at hc
      rcases hc.lt_or_eq with hc | hc
      · exact absurd (hanti mt mk hc) (not_lt.2 hl.le)
      · rw [hc] at hl; exact lt_irrefl _ hl
    · intro hl; exact hanti mk mt hl
  rw [e, iff1, ← (strictMono_Gph ha0 ha1 N).lt_iff_lt,
    hk.2, Gph_crossAngle h]
  have hpi := Real.pi_pos
  constructor
  · intro h1; nlinarith
  · intro h1; nlinarith

/-- **`prop:inertia`, eq. `(inertia)`**: `n_+(B_N) = ⌈Nα - β⌉`. -/
theorem thm_inertia {a τ : ℝ} (h : InteriorParam a τ) {N : ℕ} (hN : 2 ≤ N) :
    (posCount N a τ : ℤ) = ⌈(N : ℝ) * alphaOf a τ - betaOf a τ⌉ := by
  set X := (N : ℝ) * alphaOf a τ - betaOf a τ with hX
  have ha0 := h.1
  have ha1 := h.2.1
  have hθ := crossAngle_mem h
  have hm := strictMono_Gph ha0 ha1 N
  have hpi := Real.pi_pos
  have hlo : 0 < Gph N a (crossAngle a τ) := by
    have := hm hθ.1; rwa [Gph_zero] at this
  have hhi : Gph N a (crossAngle a τ) < (N + 1) * π := by
    have := hm hθ.2; rwa [Gph_pi] at this
  rw [Gph_crossAngle h, ← hX] at hlo hhi
  have hX1 : -1 < X := by nlinarith
  have hX2 : X < N := by nlinarith
  have hc0 : 0 ≤ ⌈X⌉ := Int.ceil_nonneg_of_neg_one_lt hX1
  have hcN : ⌈X⌉ ≤ N := Int.ceil_le.2 (by exact_mod_cast hX2.le)
  have hfilter : (Finset.Icc 1 N).filter (fun k => τ < symbol a (eigAngle N a k)) =
      Finset.Icc 1 ⌈X⌉.toNat := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, hkN⟩, hlt⟩
      rw [symbol_lt_iff h hk1 hkN, ← hX] at hlt
      refine ⟨hk1, ?_⟩
      have : ((k : ℤ) - 1) < ⌈X⌉ := Int.lt_ceil.2 (by push_cast; linarith)
      omega
    · rintro ⟨hk1, hkc⟩
      have hkN : k ≤ N := by omega
      refine ⟨⟨hk1, hkN⟩, ?_⟩
      rw [symbol_lt_iff h hk1 hkN, ← hX]
      have : ((k : ℤ) - 1) < ⌈X⌉ := by omega
      have := Int.lt_ceil.1 this
      push_cast at this
      linarith
  unfold posCount
  rw [hfilter, Nat.card_Icc, Nat.add_sub_cancel, Int.toNat_of_nonneg hc0]

open Classical in
/-- `prop:inertia`: exactly one zero eigenvalue at a singular dimension, none otherwise. -/
theorem thm_zeroCount {a τ : ℝ} (h : InteriorParam a τ) {N : ℕ} (hN : 2 ≤ N) :
    zeroCount N a τ = if ∃ z : ℤ, (N : ℝ) * alphaOf a τ - betaOf a τ = z then 1 else 0 := by
  have ha0 := h.1
  have ha1 := h.2.1
  have hθ := crossAngle_mem h
  have key : ∀ k, 1 ≤ k → k ≤ N →
      (symbol a (eigAngle N a k) = τ ↔ crossAngle a τ = eigAngle N a k) := by
    intro k hk1 hkN
    have hk := eigAngle_spec ha0 ha1 hk1 hkN
    constructor
    · intro hs
      exact (crossAngle_unique h ⟨hk.1.1.le, hk.1.2.le⟩ hs).symm
    · intro he; rw [← he, symbol_crossAngle h]
  split_ifs with hz
  · obtain ⟨z, hz⟩ := hz
    obtain ⟨hk1, hkN, hθk⟩ := crossAngle_eq_eigAngle h hz
    unfold zeroCount
    rw [Finset.card_eq_one]
    refine ⟨(z + 1).toNat, ?_⟩
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hk1', hkN'⟩, hs⟩
      rw [key k hk1' hkN', hθk] at hs
      by_contra hne
      have h1 : 1 ≤ (z + 1).toNat := by omega
      have h2 : (z + 1).toNat ≤ N := by omega
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact (eigAngle_lt ha0 ha1 hk1' hlt h2).ne hs.symm
      · exact (eigAngle_lt ha0 ha1 h1 hlt hkN').ne hs
    · rintro rfl
      exact ⟨⟨by omega, by omega⟩, (key _ (by omega) (by omega)).2 hθk⟩
  · unfold zeroCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k hk hs
    rw [Finset.mem_Icc] at hk
    have hk' := eigAngle_spec ha0 ha1 hk.1 hk.2
    rw [key k hk.1 hk.2] at hs
    apply hz
    have hG := Gph_crossAngle h N
    rw [hs, hk'.2] at hG
    refine ⟨(k : ℤ) - 1, ?_⟩
    have hpi := Real.pi_pos
    push_cast
    nlinarith

/-- `prop:inertia`: the negative eigenvalues are the remainder. -/
theorem thm_inertia_sum {a τ : ℝ} (_h : InteriorParam a τ) (N : ℕ) :
    posCount N a τ + zeroCount N a τ + negCount N a τ = N := by
  unfold posCount zeroCount negCount
  rw [← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
  · rw [show (Finset.Icc 1 N).filter (fun k => τ < symbol a (eigAngle N a k)) ∪
        (Finset.Icc 1 N).filter (fun k => symbol a (eigAngle N a k) = τ) ∪
        (Finset.Icc 1 N).filter (fun k => symbol a (eigAngle N a k) < τ) = Finset.Icc 1 N by
      ext k
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩) <;> exact h
      · intro hk
        rcases lt_trichotomy τ (symbol a (eigAngle N a k)) with h | h | h
        · exact Or.inl (Or.inl ⟨hk, h⟩)
        · exact Or.inl (Or.inr ⟨hk, h.symm⟩)
        · exact Or.inr ⟨hk, h⟩]
    simp only [Nat.card_Icc, add_tsub_cancel_right]
  · rw [Finset.disjoint_union_left, Finset.disjoint_filter, Finset.disjoint_filter]
    exact ⟨fun k _ h1 h2 => by linarith, fun k _ h1 h2 => by linarith⟩
  · rw [Finset.disjoint_filter]; intro k _ h1 h2; linarith

end ShiftedKMS
