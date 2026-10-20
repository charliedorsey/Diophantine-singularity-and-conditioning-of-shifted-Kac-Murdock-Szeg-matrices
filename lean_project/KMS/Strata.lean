import KMS.Arith
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Gate 3.3 — `thm:dense-strata` (topology, measure, cardinality)

Kept separate from the exact arithmetic files (`Singular.lean`, `Arith.lean`).

* `strat j = 𝒮_j = {(α,β) ∈ 𝒟 : #{N ≥ 2 : B_N(a,τ) singular} = j}`, `(a,τ) = (aOf α β, tauOf α β)`.
* `web` — the affine singularity web `⋃_{N ≥ 2, m ∈ ℤ} {β = Nα - m}`; `web_null`.
* In `𝒟`: `strat0_eq` (`𝒮₀ = 𝒟 \ 𝒲`), `strat0_full`, `strat1_null`, `stratTop_null`,
  `stratTop_countable`, `strat1_not_countable`, and density of all three strata.
* In the physical region `𝒫`: `physStrat j = G '' strat j` with `G = (aOf, tauOf)` a
  differentiable bijection `𝒟 → 𝒫`; density, cardinality and null sets transfer
  (`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`).
-/

open Real Set MeasureTheory Filter Topology

namespace ShiftedKMS

/-! ### Hits, strata, the web -/

/-- Hits of the web at `(α, β)`: `{N ≥ 2 : Nα - β ∈ ℤ}`. -/
def hits (α β : ℝ) : Set ℕ := {N | 2 ≤ N ∧ ∃ z : ℤ, (N : ℝ) * α - β = z}

lemma singDims_eq_hits {α β : ℝ} (h : (α, β) ∈ triangleSet) :
    singDims (aOf α β) (tauOf α β) = hits α β := by
  obtain ⟨hint, h1, h2⟩ := triangle_inverse h
  ext N
  rw [mem_singDims hint, h1, h2]
  rfl

/-- The stratum `𝒮_j` in the triangle (`j ∈ {0, 1, ⊤}`). -/
def strat (j : ℕ∞) : Set (ℝ × ℝ) :=
  {p | p ∈ triangleSet ∧ (singDims (aOf p.1 p.2) (tauOf p.1 p.2)).encard = j}

/-- The stratum in the physical parameter region `𝒫`. -/
def physStrat (j : ℕ∞) : Set (ℝ × ℝ) :=
  {q | q ∈ regionSet ∧ (singDims q.1 q.2).encard = j}

/-- The affine singularity web `𝒲 = ⋃_{N ≥ 2} ⋃_{m ∈ ℤ} {β = Nα - m}`. -/
def web : Set (ℝ × ℝ) := ⋃ N : ℕ, ⋃ m : ℤ, {p | 2 ≤ N ∧ p.2 = N * p.1 - m}

lemma mem_web_iff (p : ℝ × ℝ) : p ∈ web ↔ (hits p.1 p.2).Nonempty := by
  simp only [web, mem_iUnion, mem_setOf_eq, hits]
  constructor
  · rintro ⟨N, m, hN, hm⟩; exact ⟨N, hN, m, by linarith⟩
  · rintro ⟨N, hN, z, hz⟩; exact ⟨N, z, hN, by linarith⟩

lemma line_null (c d : ℝ) : volume {p : ℝ × ℝ | p.2 = c * p.1 - d} = 0 := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.2 = c * p.1 - d} :=
    (isClosed_eq continuous_snd (by fun_prop)).measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  have : ∀ x : ℝ, (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.2 = c * p.1 - d}) = {c * x - d} := by
    intro x; ext y; simp only [preimage_ofPred_eq, ofPred_eq_eq_singleton, mem_singleton_iff]
  simp only [this, Real.volume_singleton, lintegral_zero]

/-- The web has two-dimensional measure zero. -/
theorem web_null : volume web = 0 := by
  apply measure_iUnion_null; intro N
  apply measure_iUnion_null; intro m
  exact measure_mono_null (fun p hp => hp.2) (line_null N m)

lemma isOpen_triangle : IsOpen triangleSet := by
  have h1 : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have h2 : IsOpen {p : ℝ × ℝ | 0 < p.2} := isOpen_lt continuous_const continuous_snd
  have h3 : IsOpen {p : ℝ × ℝ | p.1 + p.2 < 1} := isOpen_lt (by fun_prop) continuous_const
  exact h1.and (h2.and h3)

lemma encard_strat {p : ℝ × ℝ} (hp : p ∈ triangleSet) :
    (singDims (aOf p.1 p.2) (tauOf p.1 p.2)).encard = (hits p.1 p.2).encard := by
  rw [singDims_eq_hits hp]

lemma hits_subsingleton_of_irrational {α β : ℝ} (hirr : Irrational α) :
    (hits α β).Subsingleton := by
  intro N₁ h₁ N₂ h₂
  obtain ⟨-, z₁, hz₁⟩ := h₁
  obtain ⟨-, z₂, hz₂⟩ := h₂
  by_contra hne
  have hm : ((N₁ : ℤ) - N₂) ≠ 0 := by omega
  apply (hirr.mul_intCast hm).ne_int (z₁ - z₂)
  push_cast; linarith

/-! ### The three strata in the triangle -/

/-- `𝒮₀ = 𝒟 \ 𝒲`. -/
theorem strat0_eq : strat 0 = triangleSet \ web := by
  ext p
  simp only [strat, mem_setOf_eq, mem_diff, mem_web_iff]
  constructor
  · rintro ⟨hp, he⟩
    rw [encard_strat hp, Set.encard_eq_zero] at he
    exact ⟨hp, by rw [he]; exact Set.not_nonempty_empty⟩
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_⟩
    rw [encard_strat hp, Set.encard_eq_zero]
    exact Set.not_nonempty_iff_eq_empty.1 hn

lemma strat_sub_web {j : ℕ∞} (hj : j ≠ 0) : strat j ⊆ web := by
  rintro p ⟨hp, he⟩
  rw [mem_web_iff]
  rw [encard_strat hp] at he
  by_contra hn
  rw [Set.not_nonempty_iff_eq_empty] at hn
  rw [hn, Set.encard_empty] at he
  exact hj he.symm

/-- `𝒮₀` has full measure in `𝒟`. -/
theorem strat0_full : volume (triangleSet \ strat 0) = 0 := by
  rw [strat0_eq]
  exact measure_mono_null (fun p hp => by simp only [mem_diff] at hp; tauto) web_null

theorem strat1_null : volume (strat 1) = 0 :=
  measure_mono_null (strat_sub_web one_ne_zero) web_null

theorem stratTop_null : volume (strat ⊤) = 0 :=
  measure_mono_null (strat_sub_web ENat.top_ne_zero) web_null

/-- Every point of `𝒟` lies in exactly one of `𝒮₀`, `𝒮₁`, `𝒮_∞` (`thm:zeroinf`). -/
theorem strata_cover {p : ℝ × ℝ} (hp : p ∈ triangleSet) :
    p ∈ strat 0 ∨ p ∈ strat 1 ∨ p ∈ strat ⊤ := by
  obtain ⟨hint, -, -⟩ := triangle_inverse hp
  rcases thm_zeroinf hint with h | h | h
  · exact Or.inl ⟨hp, h⟩
  · exact Or.inr (Or.inl ⟨hp, h⟩)
  · exact Or.inr (Or.inr ⟨hp, h⟩)

/-- `𝒮₁ = (𝒲 ∩ 𝒟) \ 𝒮_∞` (as in the manuscript's proof). -/
theorem strat1_eq : strat 1 = (web ∩ triangleSet) \ strat ⊤ := by
  ext p
  constructor
  · intro hp
    refine ⟨⟨strat_sub_web one_ne_zero hp, hp.1⟩, fun ht => ?_⟩
    have := hp.2.symm.trans ht.2
    exact ENat.one_ne_top this
  · rintro ⟨⟨hw, hp⟩, hn⟩
    rcases strata_cover hp with h | h | h
    · rw [strat0_eq] at h; exact absurd hw h.2
    · exact h
    · exact absurd h hn

/-- `𝒮_∞` is countable (it lies in `ℚ²`, by `cor:param`). -/
theorem stratTop_countable : (strat ⊤).Countable := by
  apply (Set.countable_range (fun x : ℚ × ℚ => ((x.1 : ℝ), (x.2 : ℝ)))).mono
  rintro ⟨α, β⟩ ⟨hp, he⟩
  obtain ⟨hint, h1, h2⟩ := triangle_inverse hp
  have hinf : (singDims (aOf α β) (tauOf α β)).Infinite := Set.encard_eq_top_iff.1 he
  obtain ⟨p, q, r, -, -, -, -, hα, hβ, -⟩ := cor_param hint hinf
  rw [h1] at hα
  rw [h2] at hβ
  refine ⟨((p : ℚ) / q, (r : ℚ) / q), ?_⟩
  simp only [hα, hβ]
  push_cast
  rfl

/-! ### Density -/

lemma volume_prod_isOpenPos : (volume : Measure (ℝ × ℝ)).IsOpenPosMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

/-- `𝒮₀` is dense in `𝒟`. -/
theorem strat0_dense : triangleSet ⊆ closure (strat 0) := by
  haveI := volume_prod_isOpenPos
  intro x hx
  rw [_root_.mem_closure_iff]
  intro o ho hxo
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hU : IsOpen (o ∩ triangleSet) := ho.inter isOpen_triangle
  have hpos := hU.measure_ne_zero volume ⟨x, hxo, hx⟩
  apply hpos
  apply measure_mono_null _ web_null
  intro y ⟨hyo, hyD⟩
  by_contra hyw
  have : y ∈ o ∩ strat 0 := ⟨hyo, by rw [strat0_eq]; exact ⟨hyD, hyw⟩⟩
  rw [hempty] at this
  exact this

/-- Rational points with prime denominator approximate any point of `𝒟`. -/
lemma exists_recurrent_near {x : ℝ × ℝ} (hx : x ∈ triangleSet) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ strat ⊤, dist x y < ε := by
  obtain ⟨hα0, hβ0, hαβ⟩ := hx
  obtain ⟨q, hqn, hq⟩ := Nat.exists_infinite_primes (⌈1 / x.1 + 1 / x.2 + 1 / ε⌉₊ + 2)
  have hqR : (⌈1 / x.1 + 1 / x.2 + 1 / ε⌉₊ : ℝ) + 2 ≤ q := by exact_mod_cast hqn
  have hceil := Nat.le_ceil (1 / x.1 + 1 / x.2 + 1 / ε)
  have hq0 : (0 : ℝ) < q := by
    have : (0 : ℝ) ≤ ⌈1 / x.1 + 1 / x.2 + 1 / ε⌉₊ := Nat.cast_nonneg _
    linarith
  have hb1 : 1 / x.1 < q := by
    have : 0 < 1 / x.2 := by positivity
    have : 0 < 1 / ε := by positivity
    linarith
  have hb2 : 1 / x.2 < q := by
    have : 0 < 1 / x.1 := by positivity
    have : 0 < 1 / ε := by positivity
    linarith
  have hb3 : 1 / ε < q := by
    have : 0 < 1 / x.1 := by positivity
    have : 0 < 1 / x.2 := by positivity
    linarith
  have hαq : 1 < x.1 * q := by rw [div_lt_iff₀ hα0] at hb1; linarith
  have hβq : 1 < x.2 * q := by rw [div_lt_iff₀ hβ0] at hb2; linarith
  have hεq : 1 < ε * q := by rw [div_lt_iff₀ hε] at hb3; linarith
  set p := ⌊x.1 * q⌋₊ with hpdef
  set r := ⌊x.2 * q⌋₊ with hrdef
  have hp1 : 1 ≤ p := Nat.one_le_floor_iff _ |>.2 hαq.le
  have hr1 : 1 ≤ r := Nat.one_le_floor_iff _ |>.2 hβq.le
  have hpl : (p : ℝ) ≤ x.1 * q := Nat.floor_le (by positivity)
  have hrl : (r : ℝ) ≤ x.2 * q := Nat.floor_le (by positivity)
  have hpu : x.1 * q < p + 1 := Nat.lt_floor_add_one _
  have hru : x.2 * q < r + 1 := Nat.lt_floor_add_one _
  have hprq : p + r < q := by
    have : (p : ℝ) + r < q := by nlinarith
    exact_mod_cast this
  have hcop : Nat.Coprime p q :=
    ((Nat.Prime.coprime_iff_not_dvd hq).2 (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
  have hy : ((p : ℝ) / q, (r : ℝ) / q) ∈ triangleSet := by
    refine ⟨by positivity, by positivity, ?_⟩
    rw [← add_div, div_lt_one hq0]; exact_mod_cast hprq
  obtain ⟨hint, h1, h2⟩ := triangle_inverse hy
  have hr : (q : ℝ) * betaOf (aOf (p / q) (r / q)) (tauOf (p / q) (r / q)) = (r : ℤ) := by
    rw [h2]; field_simp; push_cast; ring
  refine ⟨((p : ℝ) / q, (r : ℝ) / q), ⟨hy, ?_⟩, ?_⟩
  · exact Set.encard_eq_top_iff.2 (singDims_infinite hint hcop h1 hr)
  · have hqε : 1 / (q : ℝ) < ε := by rw [div_lt_iff₀ hq0]; linarith
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    constructor
    · rw [abs_lt]; constructor
      · have : x.1 - p / q ≥ 0 := by rw [ge_iff_le, sub_nonneg, div_le_iff₀ hq0]; linarith
        linarith
      · have : x.1 - p / q < 1 / q := by
          rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hq0]; linarith
        linarith
    · rw [abs_lt]; constructor
      · have : x.2 - r / q ≥ 0 := by rw [ge_iff_le, sub_nonneg, div_le_iff₀ hq0]; linarith
        linarith
      · have : x.2 - r / q < 1 / q := by
          rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hq0]; linarith
        linarith

/-- `𝒮_∞` is dense in `𝒟`. -/
theorem stratTop_dense : triangleSet ⊆ closure (strat ⊤) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  exact exists_recurrent_near hx hε

/-- `𝒮₁` is dense in `𝒟` (web segments through recurrent points carry irrational-`α` points). -/
theorem strat1_dense : triangleSet ⊆ closure (strat 1) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y, ⟨hyD, hyinf⟩, hxy⟩ := exists_recurrent_near hx (half_pos hε)
  rw [encard_strat hyD, Set.encard_eq_top_iff] at hyinf
  obtain ⟨N, hN2, m, hm⟩ := hyinf.nonempty
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_triangle y hyD
  set δ := min ρ (ε / 2) / (N + 1) with hδ
  have hN0 : (0 : ℝ) < N + 1 := by positivity
  have hδ0 : 0 < δ := div_pos (lt_min hρ (half_pos hε)) hN0
  obtain ⟨α', hirr, hα1, hα2⟩ := exists_irrational_btwn (lt_add_of_pos_right y.1 hδ0)
  set z : ℝ × ℝ := (α', y.2 + N * (α' - y.1)) with hz
  have hd : 0 < α' - y.1 := by linarith
  have hdz : dist z y < min ρ (ε / 2) := by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    have hNd : (N : ℝ) * (α' - y.1) < min ρ (ε / 2) := by
      have : α' - y.1 < δ := by linarith
      calc (N : ℝ) * (α' - y.1) ≤ (N + 1) * (α' - y.1) := by nlinarith
        _ < (N + 1) * δ := by apply mul_lt_mul_of_pos_left this hN0
        _ = min ρ (ε / 2) := by rw [hδ]; field_simp
    have hδle : δ ≤ min ρ (ε / 2) :=
      div_le_self (lt_min hρ (half_pos hε)).le (by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith)
    constructor
    · rw [abs_of_pos hd]
      linarith
    · rw [show y.2 + N * (α' - y.1) - y.2 = N * (α' - y.1) by ring,
        abs_of_nonneg (by positivity)]
      exact hNd
  have hzD : z ∈ triangleSet := hball (lt_of_lt_of_le hdz (min_le_left _ _))
  refine ⟨z, ⟨hzD, ?_⟩, ?_⟩
  · rw [encard_strat hzD, Set.encard_eq_one]
    refine ⟨N, (hits_subsingleton_of_irrational hirr).eq_singleton_of_mem ⟨hN2, m, ?_⟩⟩
    simp only [hz]
    linarith
  · calc dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          rw [dist_comm y z]
          exact add_lt_add hxy (lt_of_lt_of_le hdz (min_le_right _ _))
      _ = ε := by ring

/-- `𝒮₁` is uncountable: it contains `{(α, 2α) : α ∈ (0, 1/3) irrational}`. -/
theorem strat1_not_countable : ¬ (strat 1).Countable := by
  intro hc
  set T := {α : ℝ | Irrational α ∧ α ∈ Ioo 0 (1 / 3)} with hT
  have hmaps : MapsTo (fun α : ℝ => (α, 2 * α)) T (strat 1) := by
    rintro α ⟨hirr, h0, h1⟩
    have hD : (α, 2 * α) ∈ triangleSet := ⟨h0, by linarith, by simp only; linarith⟩
    refine ⟨hD, ?_⟩
    rw [encard_strat hD, Set.encard_eq_one]
    exact ⟨2, (hits_subsingleton_of_irrational hirr).eq_singleton_of_mem
      ⟨le_rfl, 0, by simp only; push_cast; ring⟩⟩
  have hinj : InjOn (fun α : ℝ => (α, 2 * α)) T := fun a _ b _ h => (Prod.mk.inj h).1
  have hTc : T.Countable := hmaps.countable_of_injOn hinj hc
  have hQ : (Set.range ((↑) : ℚ → ℝ)).Countable := Set.countable_range _
  have hcov : Ioo (0 : ℝ) (1 / 3) ⊆ T ∪ Set.range ((↑) : ℚ → ℝ) := by
    intro α hα
    by_cases hirr : Irrational α
    · exact Or.inl ⟨hirr, hα⟩
    · right; unfold Irrational at hirr; push_neg at hirr; exact hirr
  have hnull := measure_mono_null hcov ((hTc.union hQ).measure_zero volume)
  rw [Real.volume_Ioo] at hnull
  norm_num at hnull

/-! ### Transfer to the physical region `𝒫` -/

/-- The inverse coordinate map `G(α, β) = (a, τ)`, eq. `(inverse)`. -/
noncomputable def Gmap (p : ℝ × ℝ) : ℝ × ℝ := (aOf p.1 p.2, tauOf p.1 p.2)

/-- `𝒫`-strata are the `G`-images of the triangle strata. -/
theorem physStrat_eq_image (j : ℕ∞) : physStrat j = Gmap '' strat j := by
  ext q
  constructor
  · rintro ⟨hq, he⟩
    obtain ⟨hD, hτ, ha⟩ := triangle_forward hq
    have hG : Gmap (alphaOf q.1 q.2, betaOf q.1 q.2) = q := by
      simp only [Gmap]; exact Prod.ext ha.symm hτ.symm
    refine ⟨(alphaOf q.1 q.2, betaOf q.1 q.2), ⟨hD, ?_⟩, hG⟩
    have : (aOf (alphaOf q.1 q.2) (betaOf q.1 q.2), tauOf (alphaOf q.1 q.2) (betaOf q.1 q.2)) =
        q := hG
    simp only
    rw [show aOf (alphaOf q.1 q.2) (betaOf q.1 q.2) = q.1 from congrArg Prod.fst this,
      show tauOf (alphaOf q.1 q.2) (betaOf q.1 q.2) = q.2 from congrArg Prod.snd this]
    exact he
  · rintro ⟨p, ⟨hp, he⟩, rfl⟩
    exact ⟨(triangle_inverse hp).1, he⟩

lemma Gmap_injOn : InjOn Gmap triangleSet := by
  intro p hp p' hp' h
  obtain ⟨-, h1, h2⟩ := triangle_inverse hp
  obtain ⟨-, h1', h2'⟩ := triangle_inverse hp'
  have e1 : aOf p.1 p.2 = aOf p'.1 p'.2 := congrArg Prod.fst h
  have e2 : tauOf p.1 p.2 = tauOf p'.1 p'.2 := congrArg Prod.snd h
  rw [e1, e2] at h1 h2
  exact Prod.ext (h1.symm.trans h1') (h2.symm.trans h2')

lemma Gmap_differentiableAt {p : ℝ × ℝ} (hp : p ∈ triangleSet) :
    DifferentiableAt ℝ Gmap p := by
  obtain ⟨hα, hβ, hαβ⟩ := hp
  have hpi := Real.pi_pos
  have hc : Real.cos (π * (p.1 - p.2) / 2) ≠ 0 := by
    apply (Real.cos_pos_of_mem_Ioo ⟨_, _⟩).ne' <;> nlinarith
  have hs : Real.sin (π * p.1) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)).ne'
  have h1 : DifferentiableAt ℝ (fun p : ℝ × ℝ => aOf p.1 p.2) p := by
    unfold aOf
    fun_prop (disch := assumption)
  have h2 : DifferentiableAt ℝ (fun p : ℝ × ℝ => tauOf p.1 p.2) p := by
    unfold tauOf
    fun_prop (disch := assumption)
  exact h1.prodMk h2

lemma Gmap_differentiableOn : DifferentiableOn ℝ Gmap triangleSet :=
  fun _ hp => (Gmap_differentiableAt hp).differentiableWithinAt

lemma volume_prod_isAddHaar : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

/-- `G` maps null subsets of `𝒟` to null sets. -/
lemma Gmap_null {S : Set (ℝ × ℝ)} (hS : S ⊆ triangleSet) (h0 : volume S = 0) :
    volume (Gmap '' S) = 0 := by
  haveI := volume_prod_isAddHaar
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (Gmap_differentiableOn.mono hS) h0

lemma strat_sub_triangle (j : ℕ∞) : strat j ⊆ triangleSet := fun _ hp => hp.1

/-- Density transfers to `𝒫`. -/
theorem physStrat_dense_of {j : ℕ∞} (hd : triangleSet ⊆ closure (strat j)) :
    regionSet ⊆ closure (physStrat j) := by
  intro q hq
  obtain ⟨hD, hτ, ha⟩ := triangle_forward hq
  have hG : Gmap (alphaOf q.1 q.2, betaOf q.1 q.2) = q := by
    simp only [Gmap]; exact Prod.ext ha.symm hτ.symm
  rw [physStrat_eq_image, ← hG]
  exact ((Gmap_differentiableAt hD).continuousAt.continuousWithinAt).mem_closure_image (hd hD)

/-- **`thm:dense-strata`, triangle form.** -/
theorem thm_dense_strata_triangle :
    (triangleSet ⊆ closure (strat 0) ∧ triangleSet ⊆ closure (strat 1) ∧
      triangleSet ⊆ closure (strat ⊤)) ∧
    volume (triangleSet \ strat 0) = 0 ∧
    (¬ (strat 1).Countable ∧ volume (strat 1) = 0) ∧
    ((strat ⊤).Countable ∧ volume (strat ⊤) = 0) :=
  ⟨⟨strat0_dense, strat1_dense, stratTop_dense⟩, strat0_full,
    ⟨strat1_not_countable, strat1_null⟩, ⟨stratTop_countable, stratTop_null⟩⟩

/-- **`thm:dense-strata`, physical form** (in `𝒫 = {0 < a < 1, μ₋(a) < τ < μ₊(a)}`). -/
theorem thm_dense_strata_physical :
    (regionSet ⊆ closure (physStrat 0) ∧ regionSet ⊆ closure (physStrat 1) ∧
      regionSet ⊆ closure (physStrat ⊤)) ∧
    volume (regionSet \ physStrat 0) = 0 ∧
    (¬ (physStrat 1).Countable ∧ volume (physStrat 1) = 0) ∧
    ((physStrat ⊤).Countable ∧ volume (physStrat ⊤) = 0) := by
  refine ⟨⟨physStrat_dense_of strat0_dense, physStrat_dense_of strat1_dense,
    physStrat_dense_of stratTop_dense⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- `𝒫 \ 𝒫₀ ⊆ G '' (𝒟 \ 𝒮₀)`
    apply measure_mono_null _ (Gmap_null diff_subset strat0_full)
    rintro q ⟨hq, hn⟩
    obtain ⟨hD, hτ, ha⟩ := triangle_forward hq
    have hG : Gmap (alphaOf q.1 q.2, betaOf q.1 q.2) = q := by
      simp only [Gmap]; exact Prod.ext ha.symm hτ.symm
    refine ⟨(alphaOf q.1 q.2, betaOf q.1 q.2), ⟨hD, fun hs => hn ?_⟩, hG⟩
    rw [physStrat_eq_image, ← hG]
    exact mem_image_of_mem _ hs
  · rw [physStrat_eq_image]
    intro hc
    exact strat1_not_countable
      ((mapsTo_image Gmap (strat 1)).countable_of_injOn
        (Gmap_injOn.mono (strat_sub_triangle 1)) hc)
  · rw [physStrat_eq_image]; exact Gmap_null (strat_sub_triangle 1) strat1_null
  · rw [physStrat_eq_image]; exact stratTop_countable.image _
  · rw [physStrat_eq_image]; exact Gmap_null (strat_sub_triangle ⊤) stratTop_null

end ShiftedKMS
