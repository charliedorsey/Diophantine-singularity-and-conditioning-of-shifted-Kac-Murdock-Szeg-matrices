import KMS.Suppliers
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.PSeries

/-!
# Gate 5.4 — Cassels' metric inhomogeneous theorem (proved), and Borel–Cantelli

`casselsSupplier : CasselsSupplier`. For a fixed irrational `α` and every `c > 0`, for Lebesgue-a.e.
`β ∈ ℝ`, `N ‖Nα - β‖ < c` for infinitely many **positive** `N` (nearest-integer distance).

Proof (self-contained, from Mathlib's ergodicity of irrational rotations):
1. `exists_good_rat`: reduced fractions `p/q`, `q ≥ D` arbitrary, with `|α - p/q| < 1/q²`.
2. `distZ_sep`: for `0 < |j|`, `4|j| < q`, `‖jα‖ ≥ 3/(4q)`.
3. `measure_block_ge`: the `⌊q/4⌋` closed balls of radius `c'/q` around `Nα`,
   `q ≤ N < q + ⌊q/4⌋`, are pairwise disjoint; their union has measure `≥ c'/4`
   (`c' = min(c,1)/8`) and lies in `{y : N‖Nα - y‖ < c}`.
4. Hence `F_c = {y : N‖Nα - y‖ < c i.o.}` has measure `≥ c'/4 > 0`.
5. `F_c` is sub-invariant under `y ↦ α + y`, hence a.e.-invariant, hence (ergodicity, Mathlib
   `AddCircle.ergodic_add_left`) of full measure.
6. Lift from `ℝ/ℤ` to `ℝ` through the measure-preserving quotient map on each `(k, k+1]`.

Also `ae_not_frequently_lt_rpow`: first Borel–Cantelli for the targets `‖Nα - β‖ < N^{-(1+ε)}`.
-/

open Real Set Filter Topology MeasureTheory Finset
open scoped ENNReal

namespace ShiftedKMS

section Cassels

variable {α : ℝ}

lemma distZ_le_abs_sub_int (x : ℝ) (m : ℤ) : distZ x ≤ |x - m| := round_le x m

lemma distZ_pos_of_irrational (hα : Irrational α) {k : ℕ} (hk : 1 ≤ k) : 0 < distZ (k * α) := by
  rcases (distZ_nonneg (k * α)).lt_or_eq with h | h
  · exact h
  · obtain ⟨z, hz⟩ := (distZ_eq_zero_iff _).1 h.symm
    exfalso
    apply hα.ne_rat (z / k : ℚ)
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    push_cast
    field_simp
    linarith

/-- Reduced fractions with arbitrarily large denominators and `|α - p/q| < 1/q²`. -/
lemma exists_good_rat (hα : Irrational α) (D : ℕ) :
    ∃ r : ℚ, D ≤ r.den ∧ |α - r| < 1 / (r.den : ℝ) ^ 2 := by
  set D' := max D 1 with hD'
  have hD'1 : 1 ≤ D' := le_max_right _ _
  have hne : (Finset.Icc 1 D').Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hD'1⟩⟩
  set δ := (Finset.Icc 1 D').inf' hne (fun k => distZ (k * α)) with hδ
  have hδ0 : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    intro k hk
    exact distZ_pos_of_irrational hα (Finset.mem_Icc.1 hk).1
  have hD'r : (0 : ℝ) < D' := by exact_mod_cast (by omega : 0 < D')
  obtain ⟨q0, hq0a, hq0b⟩ := exists_rat_btwn (show α - δ / D' < α by
    have : 0 < δ / D' := by positivity
    linarith)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_abs_sub_lt_and_lt_of_irrational hα q0
  refine ⟨r, ?_, hr1⟩
  by_contra hlt
  push Not at hlt
  have hden1 : 1 ≤ r.den := r.den_pos
  have hmem : r.den ∈ Finset.Icc 1 D' := Finset.mem_Icc.2 ⟨hden1, by omega⟩
  have hle : δ ≤ distZ (r.den * α) := Finset.inf'_le _ hmem
  have hr2' : |α - r| < δ / D' := by
    calc |α - r| < |α - q0| := hr2
      _ = α - q0 := abs_of_pos (by linarith)
      _ < δ / D' := by linarith
  have hdr : (0 : ℝ) < r.den := by exact_mod_cast hden1
  have hkey : distZ (r.den * α) ≤ r.den * |α - r| := by
    have := distZ_le_abs_sub_int (r.den * α) r.num
    have e : (r.den : ℝ) * α - r.num = r.den * (α - r) := by
      rw [Rat.cast_def]
      field_simp
    rwa [e, abs_mul, abs_of_pos hdr] at this
  have : (r.den : ℝ) * |α - r| < δ := by
    calc (r.den : ℝ) * |α - r| ≤ D' * |α - r| := by
          gcongr
          exact_mod_cast (show r.den ≤ D' by omega)
      _ < D' * (δ / D') := by gcongr
      _ = δ := by field_simp
  linarith

/-- Separation: if `|α - p/q| < 1/q²` (reduced) and `0 < |j|`, `4|j| < q`, then
`‖jα‖ ≥ 3/(4q)`. -/
lemma distZ_sep {r : ℚ} (hr : |α - r| < 1 / (r.den : ℝ) ^ 2) {j : ℤ} (hj0 : j ≠ 0)
    (hj : 4 * |j| < r.den) : 3 / (4 * r.den) ≤ distZ (j * α) := by
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  -- `‖j p/q‖ ≥ 1/q`
  have h1 : 1 / (r.den : ℝ) ≤ distZ (j * r) := by
    unfold distZ
    set m := round ((j : ℝ) * r)
    have hne : j * r.num - m * r.den ≠ 0 := by
      intro h0
      have hdvd : (r.den : ℤ) ∣ j * r.num := ⟨m, by linarith⟩
      have hcop : IsCoprime (r.den : ℤ) r.num := by
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
        exact_mod_cast r.reduced
      have := hcop.dvd_of_dvd_mul_right hdvd
      have hle := Int.le_of_dvd (abs_pos.2 hj0) ((dvd_abs _ _).2 this)
      have : (r.den : ℤ) ≤ |j| := hle
      omega
    have e : (j : ℝ) * r - m = (j * r.num - m * r.den : ℤ) / r.den := by
      rw [Rat.cast_def]
      push_cast
      field_simp
    rw [e, abs_div, abs_of_pos hq, div_le_div_iff_of_pos_right hq]
    have : (1 : ℤ) ≤ |j * r.num - m * r.den| := Int.one_le_abs hne
    exact_mod_cast this
  -- Lipschitz bound of `distZ`
  have h2 : distZ (j * r) ≤ distZ (j * α) + |(j : ℝ)| * |α - r| := by
    have := distZ_le_abs_sub_int (j * r) (round ((j : ℝ) * α))
    calc distZ (j * r) ≤ |(j : ℝ) * r - round ((j : ℝ) * α)| := this
      _ = |((j : ℝ) * α - round ((j : ℝ) * α)) - j * (α - r)| := by ring_nf
      _ ≤ |(j : ℝ) * α - round ((j : ℝ) * α)| + |(j : ℝ) * (α - r)| := abs_sub _ _
      _ = distZ (j * α) + |(j : ℝ)| * |α - r| := by rw [abs_mul]; rfl
  have h3 : |(j : ℝ)| * |α - r| ≤ 1 / (4 * r.den) := by
    have hj' : (4 : ℝ) * |(j : ℝ)| ≤ r.den := by
      have h0 : 4 * |j| ≤ (r.den : ℤ) := hj.le
      have := (Int.cast_le (R := ℝ)).2 h0
      push_cast at this
      exact this
    calc |(j : ℝ)| * |α - r| ≤ (r.den / 4) * (1 / (r.den : ℝ) ^ 2) := by
          apply mul_le_mul (by linarith) hr.le (abs_nonneg _) (by positivity)
      _ = 1 / (4 * r.den) := by field_simp
  have : 1 / (r.den : ℝ) - 1 / (4 * r.den) = 3 / (4 * r.den) := by field_simp; ring
  linarith

local notation "𝕋" => UnitAddCircle

lemma norm_sub_coe (x y : ℝ) : ‖((x : ℝ) : 𝕋) - ((y : ℝ) : 𝕋)‖ = distZ (x - y) := by
  rw [← AddCircle.coe_sub, norm_addCircle_one]

/-- The block estimate: the union of the target balls has measure `≥ c'/4`. -/
lemma measure_block_ge (hα : Irrational α) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ENNReal.ofReal (min c 1 / 32) ≤
      volume (⋃ (N : ℕ) (_ : n ≤ N), {y : 𝕋 | (N : ℝ) * ‖((N * α : ℝ) : 𝕋) - y‖ < c}) := by
  set c' := min c 1 / 8 with hc'
  have hc'0 : 0 < c' := by positivity
  have hc'1 : c' ≤ 1 / 8 := by rw [hc']; have := min_le_right c 1; linarith
  have hc'c : 8 * c' ≤ c := by rw [hc']; have := min_le_left c 1; linarith
  obtain ⟨r, hrD, hr⟩ := exists_good_rat hα (max n 8)
  set q := r.den with hqdef
  have hq8 : 8 ≤ q := le_trans (le_max_right _ _) hrD
  have hqn : n ≤ q := le_trans (le_max_left _ _) hrD
  have hq : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set B := Finset.Ico q (q + q / 4) with hB
  set ρ := c' / q with hρ
  have hρ0 : 0 < ρ := by positivity
  -- the balls are disjoint
  have hdisj : (B : Set ℕ).PairwiseDisjoint
      (fun N : ℕ => Metric.closedBall (((N * α : ℝ) : 𝕋)) ρ) := by
    intro N hN N' hN' hne
    rw [Function.onFun, Set.disjoint_left]
    intro y hy hy'
    rw [Metric.mem_closedBall, dist_eq_norm] at hy hy'
    have hN1 := Finset.mem_Ico.1 (Finset.mem_coe.1 hN)
    have hN2 := Finset.mem_Ico.1 (Finset.mem_coe.1 hN')
    set j : ℤ := (N : ℤ) - N'
    have hj0 : j ≠ 0 := by intro h; apply hne; omega
    have hj : 4 * |j| < q := by
      have : |j| < q / 4 := by
        rw [abs_lt]; constructor <;> omega
      have : 4 * (q / 4 : ℤ) ≤ q := Int.mul_ediv_self_le (by norm_num)
      omega
    have hsep := distZ_sep hr hj0 hj
    have heq : distZ (j * α) = ‖((N * α : ℝ) : 𝕋) - ((N' * α : ℝ) : 𝕋)‖ := by
      rw [norm_sub_coe]; congr 1; simp only [j]; push_cast; ring
    have htri : ‖((N * α : ℝ) : 𝕋) - ((N' * α : ℝ) : 𝕋)‖ ≤ 2 * ρ := by
      calc ‖((N * α : ℝ) : 𝕋) - ((N' * α : ℝ) : 𝕋)‖
          = ‖(((N * α : ℝ) : 𝕋) - y) + (y - ((N' * α : ℝ) : 𝕋))‖ := by abel_nf
        _ ≤ ‖((N * α : ℝ) : 𝕋) - y‖ + ‖y - ((N' * α : ℝ) : 𝕋)‖ := norm_add_le _ _
        _ ≤ ρ + ρ := by
            rw [norm_sub_rev]
            exact add_le_add hy hy'
        _ = 2 * ρ := by ring
    have : 2 * ρ < 3 / (4 * q) := by
      rw [hρ, show 2 * (c' / q) = 2 * c' / q by ring, div_lt_div_iff₀ hq (by positivity)]
      nlinarith
    linarith
  -- each ball lies in the target set
  have hsub : (⋃ N ∈ B, Metric.closedBall (((N * α : ℝ) : 𝕋)) ρ) ⊆
      ⋃ (N : ℕ) (_ : n ≤ N), {y : 𝕋 | (N : ℝ) * ‖((N * α : ℝ) : 𝕋) - y‖ < c} := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨N, hN, hyN⟩ := hy
    have hN1 := Finset.mem_Ico.1 hN
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨N, by omega, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at hyN
    have hNq : (N : ℝ) < 2 * q := by
      have : N < 2 * q := by omega
      exact_mod_cast this
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc (N : ℝ) * ‖((N * α : ℝ) : 𝕋) - y‖ ≤ N * ρ := mul_le_mul_of_nonneg_left hyN hN0
      _ ≤ 2 * q * ρ := by gcongr
      _ = 2 * c' := by rw [hρ]; field_simp
      _ < c := by linarith
  -- measure of the union
  have hmeas : volume (⋃ N ∈ B, Metric.closedBall (((N * α : ℝ) : 𝕋)) ρ) =
      ∑ N ∈ B, volume (Metric.closedBall (((N * α : ℝ) : 𝕋)) ρ) :=
    measure_biUnion_finset hdisj (fun N _ => Metric.isClosed_closedBall.measurableSet)
  have hball : ∀ N : ℕ, volume (Metric.closedBall (((N * α : ℝ) : 𝕋)) ρ) = ENNReal.ofReal (2 * ρ) := by
    intro N
    have h2ρ : 2 * ρ ≤ 1 := by
      rw [hρ, show 2 * (c' / q) = 2 * c' / q by ring, div_le_one hq]
      have : (8 : ℝ) ≤ q := by exact_mod_cast hq8
      linarith
    rw [AddCircle.volume_closedBall, min_eq_right h2ρ]
  refine le_trans ?_ (le_trans (le_of_eq hmeas.symm) (measure_mono hsub))
  rw [Finset.sum_congr rfl (fun N _ => hball N), Finset.sum_const, hB, Nat.card_Ico, nsmul_eq_mul,
    show q + q / 4 - q = q / 4 by omega]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hq4 : (q : ℝ) / 8 ≤ ((q / 4 : ℕ) : ℝ) := by
    have h1 : q ≤ 4 * (q / 4) + 3 := by omega
    have h2 : (q : ℝ) ≤ 4 * ((q / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast h1
    have h3 : (8 : ℝ) ≤ q := by exact_mod_cast hq8
    linarith
  calc min c 1 / 32 = q / 8 * (2 * ρ) := by rw [hρ, hc']; field_simp; ring
    _ ≤ ((q / 4 : ℕ) : ℝ) * (2 * ρ) := by gcongr

/-- The set `F_c = {y ∈ ℝ/ℤ : N ‖Nα - y‖ < c for infinitely many N}`. -/
def Fset (α c : ℝ) : Set 𝕋 :=
  ⋂ n : ℕ, ⋃ (N : ℕ) (_ : n ≤ N), {y : 𝕋 | (N : ℝ) * ‖((N * α : ℝ) : 𝕋) - y‖ < c}

lemma measurableSet_Fset (α c : ℝ) : MeasurableSet (Fset α c) := by
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun _ => ?_
  exact (isOpen_lt (by fun_prop) continuous_const).measurableSet

lemma volume_Fset_pos (hα : Irrational α) {c : ℝ} (hc : 0 < c) : 0 < volume (Fset α c) := by
  have hmono : Antitone (fun n : ℕ =>
      ⋃ (N : ℕ) (_ : n ≤ N), {y : 𝕋 | (N : ℝ) * ‖((N * α : ℝ) : 𝕋) - y‖ < c}) := by
    intro n m hnm y hy
    simp only [Set.mem_iUnion] at hy ⊢
    obtain ⟨N, hN, h⟩ := hy
    exact ⟨N, le_trans hnm hN, h⟩
  have hmeas : ∀ n : ℕ, MeasurableSet
      (⋃ (N : ℕ) (_ : n ≤ N), {y : 𝕋 | (N : ℝ) * ‖((N * α : ℝ) : 𝕋) - y‖ < c}) := fun n =>
    MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun _ =>
      (isOpen_lt (by fun_prop) continuous_const).measurableSet
  rw [Fset, hmono.measure_iInter (fun n => (hmeas n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
  refine lt_of_lt_of_le ?_ (le_iInf fun n => measure_block_ge hα hc n)
  rw [ENNReal.ofReal_pos]
  positivity

lemma preimage_Fset_subset (α c : ℝ) :
    (fun y : 𝕋 => (α : 𝕋) + y) ⁻¹' Fset α c ⊆ Fset α c := by
  intro y hy
  simp only [Fset, Set.mem_preimage, Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq] at hy ⊢
  intro n
  obtain ⟨N, hN, h⟩ := hy (n + 1)
  refine ⟨N - 1, by omega, ?_⟩
  have e : ((N * α : ℝ) : 𝕋) - ((α : 𝕋) + y) = ((((N - 1 : ℕ) : ℝ) * α : ℝ) : 𝕋) - y := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one, sub_mul, one_mul, AddCircle.coe_sub]
    abel
  rw [e] at h
  have h1 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  have h2 : 0 ≤ ‖((((N - 1 : ℕ) : ℝ) * α : ℝ) : 𝕋) - y‖ := norm_nonneg _
  nlinarith

/-- `F_c` has full measure (ergodicity of the irrational rotation). -/
lemma ae_mem_Fset (hα : Irrational α) {c : ℝ} (hc : 0 < c) : ∀ᵐ y : 𝕋, y ∈ Fset α c := by
  have hE := ergodic_irrational_rotation hα
  have hmp := hE.toMeasurePreserving
  have hF := measurableSet_Fset α c
  have hae : (fun y : 𝕋 => (α : 𝕋) + y) ⁻¹' Fset α c =ᵐ[volume] Fset α c := by
    refine ae_eq_of_subset_of_measure_ge (preimage_Fset_subset α c) ?_
      (hF.preimage hmp.measurable).nullMeasurableSet (measure_ne_top _ _)
    rw [hmp.measure_preimage hF.nullMeasurableSet]
  rcases hE.quasiErgodic.ae_empty_or_univ₀ hF.nullMeasurableSet hae with h | h
  · exfalso
    have := measure_congr h
    rw [measure_empty] at this
    exact (volume_Fset_pos hα hc).ne' this
  · exact (ae_eq_univ.1 h)

/-- Lifting an a.e. statement from `ℝ/ℤ` to `ℝ`. -/
lemma ae_real_of_ae_circle {P : 𝕋 → Prop} (hP : ∀ᵐ y : 𝕋, P y) :
    ∀ᵐ β : ℝ, P (β : 𝕋) := by
  obtain ⟨Z, hZsub, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hP)
  rw [ae_iff]
  have hmk : Measurable ((↑) : ℝ → 𝕋) := (AddCircle.continuous_mk' (1 : ℝ)).measurable
  refine measure_mono_null (t := ⋃ k : ℤ, (((↑) : ℝ → 𝕋) ⁻¹' Z ∩ Ioc (k : ℝ) (k + 1))) ?_ ?_
  · intro β hβ
    simp only [Set.mem_ofPred_eq] at hβ
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc]
    refine ⟨⌈β⌉ - 1, hZsub hβ, ?_, ?_⟩
    · push_cast; linarith [Int.ceil_lt_add_one β]
    · push_cast; linarith [Int.le_ceil β]
  · refine measure_iUnion_null fun k => ?_
    have := (UnitAddCircle.measurePreserving_mk (k : ℝ)).measure_preimage hZm.nullMeasurableSet
    rw [Measure.restrict_apply (hZm.preimage hmk), hZ0] at this
    exact this

/-- **Cassels' theorem** (positive times, nearest-integer distance, fixed irrational `α`, a.e.
target `β`), eq. `(cassels)`: proved. -/
theorem casselsSupplier : CasselsSupplier := by
  intro α hα c hc
  have h := ae_real_of_ae_circle (ae_mem_Fset hα hc)
  filter_upwards [h] with β hβ
  rw [Filter.frequently_atTop]
  intro n
  simp only [Fset, Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq] at hβ
  obtain ⟨N, hN, hlt⟩ := hβ n
  refine ⟨N, hN, ?_⟩
  rwa [norm_sub_coe] at hlt

/-- **First Borel–Cantelli lemma** for shrinking targets: for every `ε > 0` and a.e. `β`,
`‖Nα - β‖ < N^{-(1+ε)}` holds only for finitely many `N` (any real `α`). -/
theorem ae_eventually_not_lt_rpow (α : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ β : ℝ, ∀ᶠ N : ℕ in atTop, ¬ distZ (N * α - β) < (N : ℝ) ^ (-(1 + ε)) := by
  set V : ℕ → Set 𝕋 := fun N => Metric.ball (((N * α : ℝ) : 𝕋)) ((N : ℝ) ^ (-(1 + ε)))
  have hV : ∀ N, volume (V N) ≤ ENNReal.ofReal (2 * ((N : ℝ) ^ (1 + ε))⁻¹) := by
    intro N
    refine (measure_mono Metric.ball_subset_closedBall).trans ?_
    rw [AddCircle.volume_closedBall]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg (Nat.cast_nonneg N)]
    exact min_le_right _ _
  have hsum : (∑' N, volume (V N)) ≠ ∞ := by
    have hs : Summable (fun N : ℕ => 2 * ((N : ℝ) ^ (1 + ε))⁻¹) :=
      (Real.summable_nat_rpow_inv.2 (by linarith)).mul_left 2
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hV)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity) hs]
    exact ENNReal.ofReal_ne_top
  have hBC := ae_eventually_notMem hsum
  have h := ae_real_of_ae_circle hBC
  filter_upwards [h] with β hβ
  filter_upwards [hβ] with N hN
  intro hlt
  apply hN
  simp only [V, Metric.mem_ball, dist_eq_norm]
  rwa [norm_sub_rev, norm_sub_coe]

end Cassels

end ShiftedKMS
