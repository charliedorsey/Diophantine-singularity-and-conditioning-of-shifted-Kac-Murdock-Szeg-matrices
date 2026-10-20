import KMS.Regimes
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Gate 5.0 – 5.1 — empirical measures and the rational normalized laws

* G5.0: the window `𝓘_L = {2, …, L+1}`, empirical measures `L⁻¹ ∑_{N ∈ 𝓘_L} δ_{x_N}`, weak
  convergence (`WeakLim`, equivalent to Mathlib's topology on `ProbabilityMeasure`), and the
  `EReal`-valued normalized condition number `κ₂/N` with value `+∞` at a singular dimension (so the
  `+∞` atom of a compatible rational class is preserved, not collapsed by Lean's `x / 0 = 0`).
* G5.1: `thm:rational-laws` (eqs. `(rat-incompat)`, `(rat-measure)`): per-residue limits
  `κ₂/N → C/d_r`, the singular residue class, and the weak limit `q⁻¹ ∑_r δ_{C/d_r}` with
  `C/0 = +∞`.
-/

open Real Set Filter Topology MeasureTheory Finset
open scoped ENNReal BoundedContinuousFunction

namespace ShiftedKMS

/-! ### G5.0 — windows, empirical measures, weak limits -/

/-- The window `𝓘_L = {2, …, L+1}` (manuscript `thm:irr-laws`). -/
def window (L : ℕ) : Finset ℕ := Finset.Icc 2 (L + 1)

lemma card_window (L : ℕ) : (window L).card = L := by
  simp only [window, Nat.card_Icc]; omega

/-- Empirical measure `L⁻¹ ∑_{N ∈ 𝓘_L} δ_{x_N}`. -/
noncomputable def empMeasure {X : Type*} [MeasurableSpace X] (x : ℕ → X) (L : ℕ) : Measure X :=
  ((L : ℝ≥0∞)⁻¹) • ∑ N ∈ window L, Measure.dirac (x N)

lemma isProbabilityMeasure_empMeasure {X : Type*} [MeasurableSpace X] (x : ℕ → X) {L : ℕ}
    (hL : 1 ≤ L) : IsProbabilityMeasure (empMeasure x L) := by
  constructor
  rw [empMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, card_window, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (by omega : L ≠ 0)) (ENNReal.natCast_ne_top L)

/-- Weak convergence of a sequence of measures, tested against bounded continuous functions. -/
def WeakLim {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (μs : ℕ → Measure X)
    (ν : Measure X) : Prop :=
  ∀ g : X →ᵇ ℝ, Tendsto (fun L => ∫ y, g y ∂(μs L)) atTop (𝓝 (∫ y, g y ∂ν))

/-- The empirical measures as probability measures (`L ↦ 𝓘_{L+1}`). -/
noncomputable def empProb {X : Type*} [MeasurableSpace X] (x : ℕ → X) (L : ℕ) :
    ProbabilityMeasure X :=
  ⟨empMeasure x (L + 1), isProbabilityMeasure_empMeasure x (by omega)⟩

/-- `WeakLim` is exactly convergence in Mathlib's weak topology on `ProbabilityMeasure`. -/
theorem weakLim_iff_tendsto {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (x : ℕ → X) (ν : ProbabilityMeasure X) :
    WeakLim (empMeasure x) ν ↔ Tendsto (empProb x) atTop (𝓝 ν) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  refine forall_congr' fun g => ?_
  rw [← tendsto_add_atTop_iff_nat 1]
  rfl

lemma integral_smul_sum_dirac {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (s : Finset ι) (x : ι → X) (c : ℝ≥0∞) (g : X →ᵇ ℝ) :
    ∫ y, g y ∂(c • ∑ i ∈ s, Measure.dirac (x i)) = c.toReal * ∑ i ∈ s, g (x i) := by
  rw [integral_smul_measure, integral_finsetSum_measure (fun i _ => g.integrable _), smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_dirac' _ _ g.continuous.stronglyMeasurable

lemma integral_empMeasure {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (x : ℕ → X) (L : ℕ) (g : X →ᵇ ℝ) :
    ∫ y, g y ∂(empMeasure x L) = (L : ℝ)⁻¹ * ∑ N ∈ window L, g (x N) := by
  rw [empMeasure, integral_smul_sum_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-! ### Cesàro averages over the window -/

lemma window_sum (y : ℕ → ℝ) (L : ℕ) :
    ∑ N ∈ window L, y N = ∑ N ∈ range (L + 2), y N - (y 0 + y 1) := by
  have h : window L = Finset.Ico 2 (L + 2) := by
    ext n; simp only [window, Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [h, Finset.sum_Ico_eq_sub _ (by omega : 2 ≤ L + 2)]
  simp only [sum_range_succ, Finset.range_one, sum_singleton]

/-- Cesàro over `range n` transfers to the window `{2, …, L+1}`. -/
lemma cesaro_window {y : ℕ → ℝ} {l : ℝ}
    (h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, y i) atTop (𝓝 l)) :
    Tendsto (fun L : ℕ => (L : ℝ)⁻¹ * ∑ N ∈ window L, y N) atTop (𝓝 l) := by
  have h2 := (tendsto_add_atTop_iff_nat 2).2 h
  have hr : Tendsto (fun L : ℕ => ((L : ℝ) + 2) / L) atTop (𝓝 1) := by
    have : Tendsto (fun L : ℕ => 1 + 2 * (L : ℝ)⁻¹) atTop (𝓝 (1 + 2 * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
    rw [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with L hL
    have : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
    field_simp
  have hc : Tendsto (fun L : ℕ => (L : ℝ)⁻¹ * (y 0 + y 1)) atTop (𝓝 (0 * (y 0 + y 1))) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul tendsto_const_nhds
  rw [zero_mul] at hc
  have := (hr.mul h2).sub hc
  rw [one_mul, sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with L hL
  have : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  have : (L : ℝ) + 2 ≠ 0 := by positivity
  rw [window_sum]
  push_cast
  field_simp

/-- A sequence tending to `0` along every residue class mod `q` tends to `0`. -/
lemma tendsto_zero_of_residues {z : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (h : ∀ r < q, Tendsto (fun k => z (r + q * k)) atTop (𝓝 0)) : Tendsto z atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hK : ∀ r < q, ∃ K : ℕ, ∀ k ≥ K, dist (z (r + q * k)) 0 < ε := fun r hr =>
    Metric.tendsto_atTop.1 (h r hr) ε hε
  choose! K hK using hK
  refine ⟨q * ∑ r ∈ range q, K r, fun n hn => ?_⟩
  have hr : n % q < q := Nat.mod_lt _ hq
  have hKle : K (n % q) ≤ n / q := by
    have h1 : K (n % q) ≤ ∑ r ∈ range q, K r :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hr)
    have h2 : ∑ r ∈ range q, K r ≤ n / q := (Nat.le_div_iff_mul_le hq).2 (by linarith)
    omega
  have := hK (n % q) hr (n / q) hKle
  rwa [Nat.mod_add_div] at this

lemma sum_range_periodic (ℓ : ℕ → ℝ) {q : ℕ} (m s : ℕ) (hs : s ≤ q) :
    ∑ i ∈ range (q * m + s), ℓ (i % q) = m * ∑ r ∈ range q, ℓ r + ∑ i ∈ range s, ℓ i := by
  induction m with
  | zero =>
    simp only [mul_zero, zero_add, CharP.cast_eq_zero, zero_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.1 hi) hs)]
  | succ m ih =>
    have e : q * (m + 1) + s = (q * m + s) + q := by ring
    rw [e, Finset.sum_range_add, ih]
    have : ∑ x ∈ range q, ℓ ((q * m + s + x) % q) = ∑ x ∈ range (s + q), ℓ (x % q) -
        ∑ x ∈ range s, ℓ (x % q) := by
      rw [Finset.sum_range_add, add_sub_cancel_left]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [show q * m + s + i = (s + i) + q * m by ring, Nat.add_mul_mod_self_left]
    rw [this]
    have h1 : ∑ x ∈ range (s + q), ℓ (x % q) = ∑ r ∈ range q, ℓ r + ∑ x ∈ range s, ℓ (x % q) := by
      rw [add_comm s q, Finset.sum_range_add]
      congr 1
      · exact Finset.sum_congr rfl fun i hi => by rw [Nat.mod_eq_of_lt (Finset.mem_range.1 hi)]
      · exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_mod_left]
    rw [h1]
    push_cast
    ring

/-- Cesàro average of a `q`-periodic sequence. -/
lemma cesaro_periodic (ℓ : ℕ → ℝ) {q : ℕ} (hq : 0 < q) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, ℓ (i % q)) atTop
      (𝓝 ((q : ℝ)⁻¹ * ∑ r ∈ range q, ℓ r)) := by
  set S := ∑ r ∈ range q, ℓ r
  set B := ∑ r ∈ range q, |ℓ r|
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hsplit : ∀ n, ∑ i ∈ range n, ℓ (i % q) =
      ((n / q : ℕ) : ℝ) * S + ∑ i ∈ range (n % q), ℓ i := by
    intro n
    have := sum_range_periodic ℓ (q := q) (n / q) (n % q) (Nat.mod_lt _ hq).le
    rwa [Nat.div_add_mod] at this
  have hR : ∀ n, |∑ i ∈ range (n % q), ℓ i| ≤ B := by
    intro n
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (Nat.mod_lt _ hq).le) (fun _ _ _ => abs_nonneg _)
  -- `⌊n/q⌋/n → 1/q`
  have hfl : Tendsto (fun n : ℕ => ((n / q : ℕ) : ℝ) / n) atTop (𝓝 (q : ℝ)⁻¹) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) / q - 1) / n) atTop (𝓝 (q : ℝ)⁻¹) := by
      have : Tendsto (fun n : ℕ => (q : ℝ)⁻¹ - (n : ℝ)⁻¹) atTop (𝓝 ((q : ℝ)⁻¹ - 0)) :=
        tendsto_const_nhds.sub (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      field_simp
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) / q) / n) atTop (𝓝 (q : ℝ)⁻¹) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      field_simp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      apply div_le_div_of_nonneg_right _ hn0.le
      have := Nat.lt_div_mul_add (a := n) hq
      have h' : (n : ℝ) < (n / q : ℕ) * q + q := by exact_mod_cast this
      rw [div_sub_one hqr.ne', div_le_iff₀ hqr]; linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      apply div_le_div_of_nonneg_right _ hn0.le
      rw [le_div_iff₀ hqr]
      exact_mod_cast Nat.div_mul_le_self n q
  have hrem : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range (n % q), ℓ i) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (by simpa only [zero_mul] using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const B)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (hR n) (by positivity)
  rw [show (q : ℝ)⁻¹ * S = (q : ℝ)⁻¹ * S + 0 by ring]
  refine ((hfl.mul_const S).add hrem).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [hsplit]
  ring

/-- **Residue-class Cesàro lemma.** If `y` converges to `ℓ_r` along each residue class `r mod q`,
then its window averages converge to `q⁻¹ ∑_r ℓ_r`. -/
theorem cesaro_window_residues {y ℓ : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (h : ∀ r < q, Tendsto (fun k => y (r + q * k)) atTop (𝓝 (ℓ r))) :
    Tendsto (fun L : ℕ => (L : ℝ)⁻¹ * ∑ N ∈ window L, y N) atTop
      (𝓝 ((q : ℝ)⁻¹ * ∑ r ∈ range q, ℓ r)) := by
  apply cesaro_window
  have hz : Tendsto (fun N => y N - ℓ (N % q)) atTop (𝓝 0) := by
    apply tendsto_zero_of_residues hq
    intro r hr
    have : ∀ k, (r + q * k) % q = r := fun k => by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    simp only [this]
    simpa only [sub_self] using (h r hr).sub_const (ℓ r)
  have := hz.cesaro.add (cesaro_periodic ℓ hq)
  rw [zero_add] at this
  refine this.congr' (Eventually.of_forall fun n => ?_)
  simp only [Finset.sum_sub_distrib]
  ring

/-! ### The normalized condition number, with `+∞` at a singular dimension -/

open Classical in
/-- `κ₂(B_N)/N ∈ EReal`, equal to `+∞` when `B_N` is singular. -/
noncomputable def kapNormE (a τ : ℝ) (N : ℕ) : EReal :=
  if Nonsingular N a τ then ((kappa N a τ / N : ℝ) : EReal) else ⊤

/-- An atom `C/d` with `C/0 = +∞`. -/
noncomputable def atomVal (C d : ℝ) : EReal := if d = 0 then ⊤ else ((C / d : ℝ) : EReal)

/-! ### G5.1 — rational phase points -/

section Rational

variable {a τ : ℝ} {p q : ℕ}

/-- The `q` periodic distances `d_r = ‖r p/q - β‖`, eq. `(dr)`. -/
noncomputable def dRes (a τ : ℝ) (p q r : ℕ) : ℝ := distZ (r * p / q - betaOf a τ)

/-- The limiting rational law `q⁻¹ ∑_{r<q} δ_{C/d_r}` (eq. `(rat-measure)`), on `EReal`. -/
noncomputable def ratLaw (a τ : ℝ) (p q : ℕ) : Measure EReal :=
  ((q : ℝ≥0∞)⁻¹) • ∑ r ∈ range q, Measure.dirac (atomVal (Cint a τ) (dRes a τ p q r))

/-- The same law on `ℝ` (meaningful when every `d_r > 0`). -/
noncomputable def ratLawR (a τ : ℝ) (p q : ℕ) : Measure ℝ :=
  ((q : ℝ≥0∞)⁻¹) • ∑ r ∈ range q, Measure.dirac (Cint a τ / dRes a τ p q r)

lemma isProbabilityMeasure_ratLaw (hq : 0 < q) : IsProbabilityMeasure (ratLaw a τ p q) := by
  constructor
  rw [ratLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hq.ne') (ENNReal.natCast_ne_top q)

/-- `d_N` is `q`-periodic: `d_N = d_{N mod q}`. -/
lemma dN_eq_dRes (hα : alphaOf a τ = p / q) (hq : 0 < q) (N : ℕ) :
    dN N a τ = dRes a τ p q (N % q) := by
  unfold dN dRes
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hN : (N : ℝ) = ((N % q : ℕ) : ℝ) + q * ((N / q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div N q).symm
  have e : (N : ℝ) * alphaOf a τ - betaOf a τ =
      (((N % q : ℕ) : ℝ) * p / q - betaOf a τ) + (((N / q * p : ℕ) : ℤ) : ℝ) := by
    rw [Int.cast_natCast, Nat.cast_mul, hα, hN]; field_simp; ring
  rw [e, distZ_add_int]

lemma dRes_nonneg (r : ℕ) : 0 ≤ dRes a τ p q r := distZ_nonneg _

/-- Singularity of `N ≥ 2` is decided by the residue class: singular iff `d_{N mod q} = 0`. -/
lemma nonsingular_iff_dRes (h : InteriorParam a τ) (hα : alphaOf a τ = p / q) (hq : 0 < q)
    {N : ℕ} (hN : 2 ≤ N) : Nonsingular N a τ ↔ dRes a τ p q (N % q) ≠ 0 := by
  unfold Nonsingular
  rw [ne_eq, thm_sing_dN h hN, dN_eq_dRes hα hq]

/-- Along a nonsingular residue class, `κ₂(B_N)/N → C/d_r` (eq. `(rat-incompat)`). -/
theorem kappa_div_tendsto_class (h : InteriorParam a τ) (hα : alphaOf a τ = p / q) (hq : 0 < q)
    {r : ℕ} (hr : r < q) (hd : 0 < dRes a τ p q r) :
    Tendsto (fun k : ℕ => kappa (r + q * k) a τ / ((r + q * k : ℕ) : ℝ)) atTop
      (𝓝 (Cint a τ / dRes a τ p q r)) := by
  set d := dRes a τ p q r with hdd
  set C := Cint a τ
  set K := Kkap a τ
  have hτ := h.tau_pos
  have hmod : ∀ k, (r + q * k) % q = r := fun k => by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have hNtop : Tendsto (fun k : ℕ => ((r + q * k : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    exact Filter.tendsto_atTop_atTop.2 fun b => ⟨b, fun k hk => by nlinarith⟩
  have hNinv := tendsto_inv_atTop_zero.comp hNtop
  have hlim : ∀ s : ℝ, Tendsto (fun k : ℕ => (1 + s * ((r + q * k : ℕ) : ℝ)⁻¹) *
      (C / d * (1 + τ * ((r + q * k : ℕ) : ℝ)⁻¹))) atTop (𝓝 (C / d)) := by
    intro s
    have := (tendsto_const_nhds (x := (1 : ℝ)).add (hNinv.const_mul s)).mul
      (tendsto_const_nhds (x := C / d) |>.mul (tendsto_const_nhds (x := (1 : ℝ)).add
        (hNinv.const_mul τ)))
    simpa only [Function.comp_def, mul_zero, add_zero, one_mul, mul_one] using this
  have hev : ∀ᶠ k : ℕ in atTop, 2 ≤ r + q * k ∧ n2 a τ ≤ r + q * k := by
    filter_upwards [eventually_ge_atTop (n2 a τ + 2)] with k hk
    constructor <;> nlinarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (-K)) (hlim K) ?_ ?_
  · filter_upwards [hev] with k ⟨h2, hn2⟩
    set N := r + q * k
    have hns : Nonsingular N a τ := by
      rw [nonsingular_iff_dRes h hα hq h2, hmod]; exact hd.ne'
    have hdN : dN N a τ = d := by rw [dN_eq_dRes hα hq, hmod]
    have hk := (thm_kappa_relative h hn2 hns).1
    rw [hdN] at hk
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    rw [le_div_iff₀ hN0]
    convert hk using 1
    field_simp
    ring
  · filter_upwards [hev] with k ⟨h2, hn2⟩
    set N := r + q * k
    have hns : Nonsingular N a τ := by
      rw [nonsingular_iff_dRes h hα hq h2, hmod]; exact hd.ne'
    have hdN : dN N a τ = d := by rw [dN_eq_dRes hα hq, hmod]
    have hk := (thm_kappa_relative h hn2 hns).2
    rw [hdN] at hk
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    rw [div_le_iff₀ hN0]
    convert hk using 1
    field_simp
    ring

/-- **`thm:rational-laws`** (both branches at once). For rational `α = p/q`:
1. a residue class with `d_r = 0` is singular at every `N ≥ 2` in it;
2. along a class with `d_r > 0`, `κ₂(B_N)/N → C/d_r`;
3. the empirical law of `κ₂/N ∈ EReal` (value `+∞` at singular `N`) converges weakly to
   `q⁻¹ ∑_{r<q} δ_{C/d_r}` with `C/0 = +∞`. -/
theorem thm_rational_laws (h : InteriorParam a τ) (hα : alphaOf a τ = p / q) :
    (∀ r < q, dRes a τ p q r = 0 → ∀ N : ℕ, 2 ≤ N → N % q = r → ¬ Nonsingular N a τ) ∧
    (∀ r < q, 0 < dRes a τ p q r →
      Tendsto (fun k : ℕ => kappa (r + q * k) a τ / ((r + q * k : ℕ) : ℝ)) atTop
        (𝓝 (Cint a τ / dRes a τ p q r))) ∧
    WeakLim (empMeasure (kapNormE a τ)) (ratLaw a τ p q) := by
  obtain ⟨hq, -, -⟩ := rational_pq h hα
  have hmod : ∀ r < q, ∀ k, (r + q * k) % q = r := fun r hr k => by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  refine ⟨fun r _ hd N hN hNr => ?_, fun r hr hd => kappa_div_tendsto_class h hα hq hr hd, ?_⟩
  · rw [nonsingular_iff_dRes h hα hq hN, hNr]; exact not_not.2 hd
  · intro g
    simp only [integral_empMeasure, ratLaw, integral_smul_sum_dirac, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    apply cesaro_window_residues hq
    intro r hr
    rcases (dRes_nonneg (a := a) (τ := τ) (p := p) (q := q) r).lt_or_eq with hd | hd
    · -- nonsingular class
      have hconv := kappa_div_tendsto_class h hα hq hr hd
      have hval : atomVal (Cint a τ) (dRes a τ p q r) = ((Cint a τ / dRes a τ p q r : ℝ) : EReal) :=
        by rw [atomVal, ite_eq_right hd.ne']
      rw [hval]
      have := (g.continuous.comp continuous_coe_real_ereal).tendsto _ |>.comp hconv
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with k hk
      have h2 : 2 ≤ r + q * k := by nlinarith
      have hns : Nonsingular (r + q * k) a τ := by
        rw [nonsingular_iff_dRes h hα hq h2, hmod r hr]; exact hd.ne'
      simp only [Function.comp_apply, kapNormE, ite_eq_left hns]
    · -- singular class: constantly `+∞`
      have hval : atomVal (Cint a τ) (dRes a τ p q r) = ⊤ := by rw [atomVal, ite_eq_left hd.symm]
      rw [hval]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with k hk
      have h2 : 2 ≤ r + q * k := by nlinarith
      have hns : ¬ Nonsingular (r + q * k) a τ := by
        rw [nonsingular_iff_dRes h hα hq h2, hmod r hr]; exact not_not.2 hd.symm
      simp only [kapNormE, ite_eq_right hns]

/-- `thm:rational-laws`, incompatible branch: if `qβ ∉ ℤ`, every `d_r > 0`, so the limit law has
no `+∞` atom, and the real-valued empirical law of `κ₂/N` converges to `q⁻¹ ∑_r δ_{C/d_r}`. -/
theorem thm_rational_laws_incompat (h : InteriorParam a τ) (hα : alphaOf a τ = p / q)
    (hβ : ∀ z : ℤ, (q : ℝ) * betaOf a τ ≠ z) :
    (∀ r, 0 < dRes a τ p q r) ∧
      (∀ N : ℕ, 2 ≤ N → Nonsingular N a τ) ∧
      WeakLim (empMeasure (fun N => kappa N a τ / N)) (ratLawR a τ p q) := by
  obtain ⟨hq, -, -⟩ := rational_pq h hα
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpos : ∀ r, 0 < dRes a τ p q r := by
    intro r
    rcases (dRes_nonneg (a := a) (τ := τ) (p := p) (q := q) r).lt_or_eq with hd | hd
    · exact hd
    · exfalso
      obtain ⟨z, hz⟩ := (distZ_eq_zero_iff _).1 hd.symm
      apply hβ (r * p - q * z)
      push_cast
      field_simp at hz
      linarith
  refine ⟨hpos, fun N hN => ?_, ?_⟩
  · rw [nonsingular_iff_dRes h hα hq hN]; exact (hpos _).ne'
  · intro g
    simp only [integral_empMeasure, ratLawR, integral_smul_sum_dirac, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    apply cesaro_window_residues hq
    intro r hr
    exact (g.continuous.tendsto _).comp (kappa_div_tendsto_class h hα hq hr (hpos r))

/-- `thm:rational-laws`, compatible branch: if `qβ ∈ ℤ` and `gcd(p,q) = 1`, exactly one residue
class `r < q` has `d_r = 0` (the singular class, the `+∞` atom of mass `1/q`). -/
theorem thm_rational_laws_compat (h : InteriorParam a τ) (hcop : Nat.Coprime p q)
    (hα : alphaOf a τ = p / q) {z : ℤ} (hz : (q : ℝ) * betaOf a τ = z) :
    ∃! r, r < q ∧ dRes a τ p q r = 0 := by
  obtain ⟨hq, hp, hpq⟩ := rational_pq h hα
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  obtain ⟨c, hc0, hcq, hc⟩ := thm_rational_one_class hcop (by omega) z
  have key : ∀ r : ℕ, dRes a τ p q r = 0 ↔ (r : ℤ) * p ≡ z [ZMOD q] := by
    intro r
    have hβ : betaOf a τ = z / q := by rw [eq_div_iff hqr, mul_comm, hz]
    rw [dRes, distZ_eq_zero_iff, Int.modEq_iff_dvd, hβ]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨-w, ?_⟩
      field_simp at hw
      have : (z : ℝ) - r * p = q * -w := by linarith
      exact_mod_cast this
    · rintro ⟨w, hw⟩
      refine ⟨-w, ?_⟩
      have hw' : (z : ℝ) - r * p = q * w := by exact_mod_cast hw
      field_simp
      push_cast
      linarith
  refine ⟨c.toNat, ⟨by omega, ?_⟩, ?_⟩
  · rw [key, hc, Int.toNat_of_nonneg hc0]
  · rintro r ⟨hr, hr0⟩
    rw [key, hc] at hr0
    have h1 : (r : ℤ) % q = c % q := hr0
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt hc0 hcq] at h1
    omega

end Rational

end ShiftedKMS
