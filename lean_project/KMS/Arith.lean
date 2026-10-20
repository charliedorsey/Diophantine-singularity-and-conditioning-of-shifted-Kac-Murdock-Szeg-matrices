import KMS.Singular
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Int.GCD
import Mathlib.Data.Set.Card

/-!
# Gate 3.2 (+ `thm:resonance`, `cor:hollowdich`, `prop:affinecollapse`) — exact arithmetic

Exact arithmetic half of Gate 3 (no topology / measure here).

* `singDims a τ = {N ≥ 2 | B_N(a,τ) singular}`.
* `thm_rational_*` — `thm:rational`: compatibility `qβ ∈ ℤ`, `0 < r < q - p`, the congruence
  `Np ≡ r (mod q)`, and that it is exactly one residue class; incompatibility ⇒ no hits.
* `singDims_subsingleton_of_irrational`, `thm_zeroinf` — `thm:zeroinf` (the `0/1/∞` law).
* `cor_param`, `cor_param_converse` — `cor:param`.
* `thm_resonance`, `cor_hollowdich_*`, `prop_affinecollapse` — §6 exact statements.
-/

open Real Set

namespace ShiftedKMS

/-- Singular dimensions `{N ≥ 2 : det B_N(a,τ) = 0}`. -/
def singDims (a τ : ℝ) : Set ℕ := {N | 2 ≤ N ∧ (shifted N a τ).det = 0}

lemma mem_singDims {a τ : ℝ} (h : InteriorParam a τ) (N : ℕ) :
    N ∈ singDims a τ ↔ 2 ≤ N ∧ ∃ z : ℤ, (N : ℝ) * alphaOf a τ - betaOf a τ = z := by
  unfold singDims
  constructor
  · rintro ⟨hN, hd⟩; exact ⟨hN, (thm_sing h hN).1 hd⟩
  · rintro ⟨hN, hz⟩; exact ⟨hN, (thm_sing h hN).2 hz⟩

lemma alpha_beta_bounds {a τ : ℝ} (h : InteriorParam a τ) :
    0 < alphaOf a τ ∧ 0 < betaOf a τ ∧ alphaOf a τ + betaOf a τ < 1 :=
  (triangle_forward h).1

/-! ### `thm:zeroinf`, irrational half -/

/-- **`thm:zeroinf`**: for irrational `α`, at most one singular dimension. -/
theorem singDims_subsingleton_of_irrational {a τ : ℝ} (h : InteriorParam a τ)
    (hirr : Irrational (alphaOf a τ)) : (singDims a τ).Subsingleton := by
  intro N₁ h₁ N₂ h₂
  obtain ⟨-, z₁, hz₁⟩ := (mem_singDims h N₁).1 h₁
  obtain ⟨-, z₂, hz₂⟩ := (mem_singDims h N₂).1 h₂
  by_contra hne
  have hm : ((N₁ : ℤ) - N₂) ≠ 0 := by omega
  have := (hirr.mul_intCast hm).ne_int (z₁ - z₂)
  apply this
  push_cast
  linarith

/-! ### `thm:rational` -/

section Rational

variable {a τ : ℝ} {p q : ℕ}

lemma rational_pq (h : InteriorParam a τ) (hα : alphaOf a τ = p / q) :
    0 < q ∧ 0 < p ∧ p < q := by
  obtain ⟨hα0, -, hαβ⟩ := alpha_beta_bounds h
  have hβ0 := (alpha_beta_bounds h).2.1
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0] at hα; simp only [CharP.cast_eq_zero, div_zero] at hα; linarith
    · exact h0
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  rw [hα] at hα0 hαβ
  have hp : (0 : ℝ) < p := by
    by_contra hc; push_neg at hc
    have : (p : ℝ) / q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hqr.le
    linarith
  have hpq : (p : ℝ) < q := by
    have : (p : ℝ) / q < 1 := by linarith
    rwa [div_lt_one hqr] at this
  exact ⟨hq, by exact_mod_cast hp, by exact_mod_cast hpq⟩

/-- **`thm:rational`, necessity of eq. `(compat)`**: a singular dimension forces `qβ ∈ ℤ`. -/
theorem thm_rational_compat (h : InteriorParam a τ) (hα : alphaOf a τ = p / q)
    (hne : (singDims a τ).Nonempty) : ∃ r : ℤ, (q : ℝ) * betaOf a τ = r := by
  obtain ⟨hq, -, -⟩ := rational_pq h hα
  obtain ⟨N, hN⟩ := hne
  obtain ⟨-, z, hz⟩ := (mem_singDims h N).1 hN
  refine ⟨N * p - q * z, ?_⟩
  rw [hα] at hz
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp at hz
  linarith

/-- **`thm:rational`, eq. `(congruence)`**: if `r = qβ ∈ ℤ`, then `0 < r < q - p` and the
singular dimensions are exactly `N ≥ 2` with `N p ≡ r (mod q)`. -/
theorem thm_rational_congr (h : InteriorParam a τ) (hα : alphaOf a τ = p / q) {r : ℤ}
    (hr : (q : ℝ) * betaOf a τ = r) :
    0 < r ∧ r < (q : ℤ) - p ∧
      ∀ N : ℕ, 2 ≤ N → (N ∈ singDims a τ ↔ (N : ℤ) * p ≡ r [ZMOD q]) := by
  obtain ⟨hq, hp, hpq⟩ := rational_pq h hα
  obtain ⟨-, hβ0, hαβ⟩ := alpha_beta_bounds h
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hβ : betaOf a τ = r / q := by rw [eq_div_iff hqr.ne', mul_comm, hr]
  refine ⟨?_, ?_, ?_⟩
  · have : (0 : ℝ) < r := by rw [← hr]; positivity
    exact_mod_cast this
  · rw [hα, hβ, ← add_div, div_lt_one hqr] at hαβ
    have : (r : ℝ) < q - p := by linarith
    exact_mod_cast this
  · intro N hN
    rw [mem_singDims h, Int.modEq_iff_dvd, hα, hβ]
    constructor
    · rintro ⟨-, z, hz⟩
      refine ⟨-z, ?_⟩
      field_simp at hz
      have : (r : ℝ) - N * p = q * -z := by linarith
      exact_mod_cast this
    · rintro ⟨z, hz⟩
      refine ⟨hN, -z, ?_⟩
      have hz' : (r : ℝ) - N * p = q * z := by exact_mod_cast hz
      field_simp
      push_cast
      linarith

/-- **`thm:rational`, "exactly one congruence class"**: with `gcd(p,q) = 1`, the congruence
`N p ≡ r (mod q)` is equivalent to `N ≡ c (mod q)` for a single residue `0 ≤ c < q`. -/
theorem thm_rational_one_class (hcop : Nat.Coprime p q) (hq : 1 < q) (r : ℤ) :
    ∃ c : ℤ, 0 ≤ c ∧ c < q ∧ ∀ N : ℤ, (N * p ≡ r [ZMOD q] ↔ N ≡ c [ZMOD q]) := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq
  have hpm : ((p : ℤ) * m) ≡ 1 [ZMOD q] := by
    unfold Int.ModEq
    have : ((p * m % q : ℕ) : ℤ) = 1 := by exact_mod_cast hm
    push_cast at this
    rw [this]
    exact (Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hq)).symm
  have hq0 : (0 : ℤ) < q := by exact_mod_cast (by omega : 0 < q)
  refine ⟨(r * m) % q, Int.emod_nonneg _ hq0.ne', Int.emod_lt_of_pos _ hq0, ?_⟩
  intro N
  have hc : r * m ≡ (r * m) % q [ZMOD q] := (Int.mod_modEq _ _).symm
  constructor
  · intro hN
    have h1 : N * p * m ≡ r * m [ZMOD q] := hN.mul_right _
    have h2 : N * (p * m) ≡ N * 1 [ZMOD q] := hpm.mul_left _
    rw [mul_one, ← mul_assoc] at h2
    exact (h2.symm.trans h1).trans hc
  · intro hN
    have h1 : N * p ≡ (r * m) * p [ZMOD q] := (hN.trans hc.symm).mul_right _
    have h2 : r * (p * m) ≡ r * 1 [ZMOD q] := hpm.mul_left _
    rw [mul_one] at h2
    exact h1.trans (by rw [mul_assoc, mul_comm (m : ℤ) (p : ℤ)]; exact h2)

/-- Compatible rational parameters are recurrent: infinitely many singular dimensions. -/
theorem singDims_infinite (h : InteriorParam a τ) (hcop : Nat.Coprime p q)
    (hα : alphaOf a τ = p / q) {r : ℤ} (hr : (q : ℝ) * betaOf a τ = r) :
    (singDims a τ).Infinite := by
  obtain ⟨hq0, hp, hpq⟩ := rational_pq h hα
  have hq : 1 < q := by omega
  obtain ⟨-, -, hcong⟩ := thm_rational_congr h hα hr
  obtain ⟨c, hc0, hcq, hcls⟩ := thm_rational_one_class hcop hq r
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  set N : ℕ := c.toNat + q * (B + 2) with hNdef
  have hN2 : 2 ≤ N := by
    have : 2 ≤ q * (B + 2) := by nlinarith
    omega
  have hmem : N ∈ singDims a τ := by
    rw [hcong N hN2, hcls]
    unfold Int.ModEq
    rw [hNdef]
    push_cast
    rw [Int.toNat_of_nonneg hc0, Int.add_mul_emod_self_left]
  have := hB hmem
  have : B < N := by
    have : B + 2 ≤ q * (B + 2) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  omega

/-- **`thm:rational`**: incompatible rational parameters are never singular. -/
theorem singDims_empty (h : InteriorParam a τ) (hα : alphaOf a τ = p / q)
    (hno : ¬ ∃ r : ℤ, (q : ℝ) * betaOf a τ = r) : singDims a τ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro N hN
  exact hno (thm_rational_compat h hα ⟨N, hN⟩)

/-- **`thm:rational`, existence**: singularity occurs for some dimension iff `qβ ∈ ℤ`. -/
theorem thm_rational_exists (h : InteriorParam a τ) (hcop : Nat.Coprime p q)
    (hα : alphaOf a τ = p / q) :
    (singDims a τ).Nonempty ↔ ∃ r : ℤ, (q : ℝ) * betaOf a τ = r := by
  constructor
  · exact thm_rational_compat h hα
  · rintro ⟨r, hr⟩
    exact (singDims_infinite h hcop hα hr).nonempty

end Rational

/-! ### `thm:zeroinf` — the `0/1/∞` law -/

lemma rat_repr {x : ℝ} (hx0 : 0 < x) (hx : ¬ Irrational x) :
    ∃ p q : ℕ, Nat.Coprime p q ∧ x = p / q := by
  unfold Irrational at hx
  push_neg at hx
  obtain ⟨y, rfl⟩ := hx
  have hy : 0 < y := by exact_mod_cast hx0
  have hnum : 0 < y.num := Rat.num_pos.2 hy
  refine ⟨y.num.toNat, y.den, ?_, ?_⟩
  · have := y.reduced
    rwa [show y.num.natAbs = y.num.toNat by omega] at this
  · rw [Rat.cast_def]
    congr 1
    have : ((y.num.toNat : ℕ) : ℤ) = y.num := Int.toNat_of_nonneg hnum.le
    exact_mod_cast this.symm

/-- **`thm:zeroinf`, eq. `(card)`**: `#{N ≥ 2 : B_N singular} ∈ {0, 1, ∞}`. -/
theorem thm_zeroinf {a τ : ℝ} (h : InteriorParam a τ) :
    (singDims a τ).encard = 0 ∨ (singDims a τ).encard = 1 ∨ (singDims a τ).encard = ⊤ := by
  by_cases hirr : Irrational (alphaOf a τ)
  · have hs := singDims_subsingleton_of_irrational h hirr
    rcases Set.encard_le_one_iff_eq.1 (Set.encard_le_one_iff_subsingleton.2 hs) with he | ⟨x, hx⟩
    · left; rw [he, Set.encard_empty]
    · right; left; rw [hx, Set.encard_singleton]
  · obtain ⟨p, q, hcop, hα⟩ := rat_repr (alpha_beta_bounds h).1 hirr
    by_cases hc : ∃ r : ℤ, (q : ℝ) * betaOf a τ = r
    · obtain ⟨r, hr⟩ := hc
      right; right
      exact Set.encard_eq_top_iff.2 (singDims_infinite h hcop hα hr)
    · left; rw [singDims_empty h hα hc, Set.encard_empty]

/-! ### `cor:param` — complete recurrent parametrization -/

/-- **`cor:param`**: every interior pair with infinitely many singular dimensions is given by
eq. `(param)` from integers `0 < p`, `0 < r`, `p + r < q`, `gcd(p,q) = 1`, and its singular
dimensions are `N p ≡ r (mod q)`. -/
theorem cor_param {a τ : ℝ} (h : InteriorParam a τ) (hinf : (singDims a τ).Infinite) :
    ∃ p q r : ℕ, 0 < p ∧ 0 < r ∧ p + r < q ∧ Nat.Coprime p q ∧
      alphaOf a τ = p / q ∧ betaOf a τ = r / q ∧
      τ = Real.sin (r * π / q) / Real.sin (p * π / q) ∧
      a = Real.cos ((p + r) * π / (2 * q)) / Real.cos (((p : ℝ) - r) * π / (2 * q)) ∧
      ∀ N : ℕ, 2 ≤ N → (N ∈ singDims a τ ↔ (N : ℤ) * p ≡ r [ZMOD q]) := by
  have hirr : ¬ Irrational (alphaOf a τ) := fun hi =>
    hinf ((singDims_subsingleton_of_irrational h hi).finite)
  obtain ⟨p, q, hcop, hα⟩ := rat_repr (alpha_beta_bounds h).1 hirr
  obtain ⟨hq, hp, hpq⟩ := rational_pq h hα
  obtain ⟨r, hr⟩ := thm_rational_compat h hα hinf.nonempty
  obtain ⟨hr0, hrq, hcong⟩ := thm_rational_congr h hα hr
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hβ : betaOf a τ = r / q := by rw [eq_div_iff hqr.ne', mul_comm, hr]
  obtain ⟨-, hτ, ha⟩ := triangle_forward h
  refine ⟨p, q, r.toNat, hp, by omega, by omega, hcop, hα, ?_, ?_, ?_, ?_⟩
  · rw [hβ]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hr0.le).symm
  · rw [hτ, tauOf, hα, hβ]
    have : ((r.toNat : ℕ) : ℝ) = r := by exact_mod_cast Int.toNat_of_nonneg hr0.le
    rw [this]; congr 1 <;> ring_nf
  · rw [ha, aOf, hα, hβ]
    have : ((r.toNat : ℕ) : ℝ) = r := by exact_mod_cast Int.toNat_of_nonneg hr0.le
    rw [this]; congr 1 <;> ring_nf
  · intro N hN
    rw [hcong N hN, Int.toNat_of_nonneg hr0.le]

/-- **`cor:param`, converse**: every such integer triple produces an interior pair, through
eq. `(param)`, with infinitely many singular dimensions, namely `N p ≡ r (mod q)`. -/
theorem cor_param_converse {p q r : ℕ} (hp : 0 < p) (hr : 0 < r) (hpr : p + r < q)
    (hcop : Nat.Coprime p q) :
    let a := Real.cos ((p + r) * π / (2 * q)) / Real.cos (((p : ℝ) - r) * π / (2 * q))
    let τ := Real.sin (r * π / q) / Real.sin (p * π / q)
    InteriorParam a τ ∧ alphaOf a τ = p / q ∧ betaOf a τ = r / q ∧ (singDims a τ).Infinite ∧
      ∀ N : ℕ, 2 ≤ N → (N ∈ singDims a τ ↔ (N : ℤ) * p ≡ r [ZMOD q]) := by
  intro a τ
  have hq : 0 < q := by omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have htri : ((p : ℝ) / q, (r : ℝ) / q) ∈ triangleSet := by
    refine ⟨by positivity, by positivity, ?_⟩
    rw [← add_div, div_lt_one hqr]; exact_mod_cast hpr
  obtain ⟨hint, hα, hβ⟩ := triangle_inverse htri
  have ea : aOf (p / q) (r / q) = a := by
    simp only [aOf, a]; congr 1 <;> ring_nf
  have eτ : tauOf (p / q) (r / q) = τ := by
    simp only [tauOf, τ]; congr 1 <;> ring_nf
  rw [ea, eτ] at hint hα hβ
  have hrq : (q : ℝ) * betaOf a τ = (r : ℤ) := by rw [hβ]; field_simp; push_cast; ring
  refine ⟨hint, hα, hβ, singDims_infinite hint hcop hα hrq, ?_⟩
  intro N hN
  exact (thm_rational_congr hint hα hrq).2.2 N hN

/-! ### §6 — resonance, hollow dichotomy, affine-hit collapse (exact parts) -/

/-- **`thm:resonance`, eqs. `(resonance)`, `(tau-regions)`**. -/
theorem thm_resonance {a τ : ℝ} (h : InteriorParam a τ) :
    (τ = 1 ↔ betaOf a τ = alphaOf a τ) ∧ (alphaOf a τ < betaOf a τ ↔ 1 < τ) ∧
      (betaOf a τ < alphaOf a τ ↔ τ < 1) := by
  obtain ⟨⟨hα, hβ, hαβ⟩, hτ, -⟩ := triangle_forward h
  set α := alphaOf a τ
  set β := betaOf a τ
  have hpi := Real.pi_pos
  have hsα : 0 < Real.sin (π * α) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hcos : 0 < Real.cos ((π * β + π * α) / 2) := by
    apply Real.cos_pos_of_mem_Ioo; constructor <;> nlinarith
  have hdiff : Real.sin (π * β) - Real.sin (π * α) =
      2 * Real.sin ((π * β - π * α) / 2) * Real.cos ((π * β + π * α) / 2) :=
    Real.sin_sub_sin _ _
  have hτ' : τ - 1 = (Real.sin (π * β) - Real.sin (π * α)) / Real.sin (π * α) := by
    rw [hτ, tauOf, sub_div, div_self hsα.ne']
  -- sign of `sin((πβ - πα)/2)` is the sign of `β - α`
  have pos : α < β → 0 < Real.sin ((π * β - π * α) / 2) := fun hl =>
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  have neg : β < α → Real.sin ((π * β - π * α) / 2) < 0 := fun hl => by
    rw [show (π * β - π * α) / 2 = -((π * α - π * β) / 2) by ring, Real.sin_neg, neg_lt_zero]
    exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  have gt : α < β ↔ 1 < τ := by
    constructor
    · intro hl
      have : 0 < τ - 1 := by rw [hτ', hdiff]; have := pos hl; positivity
      linarith
    · intro hl
      by_contra hc; push_neg at hc
      rcases hc.lt_or_eq with hc | hc
      · have : τ - 1 < 0 := by
          rw [hτ', hdiff]
          apply div_neg_of_neg_of_pos _ hsα
          have := neg hc
          nlinarith
        linarith
      · have : τ - 1 = 0 := by rw [hτ', hdiff, hc]; simp only [sub_self, zero_div, sin_zero, mul_zero, add_self_div_two, zero_mul]
        linarith
  have lt : β < α ↔ τ < 1 := by
    constructor
    · intro hl
      have : τ - 1 < 0 := by
        rw [hτ', hdiff]
        apply div_neg_of_neg_of_pos _ hsα
        have := neg hl
        nlinarith
      linarith
    · intro hl
      by_contra hc; push_neg at hc
      rcases hc.lt_or_eq with hc | hc
      · linarith [gt.1 hc]
      · have : τ - 1 = 0 := by rw [hτ', hdiff, hc]; simp only [sub_self, zero_div, sin_zero, mul_zero, add_self_div_two, zero_mul]
        linarith
  refine ⟨?_, gt, lt⟩
  constructor
  · intro h1
    rcases lt_trichotomy α β with hc | hc | hc
    · linarith [gt.1 hc]
    · exact hc.symm
    · linarith [lt.1 hc]
  · intro h1
    have : τ - 1 = 0 := by rw [hτ', hdiff, h1]; simp only [sub_self, zero_div, sin_zero, mul_zero, add_self_div_two, zero_mul]
    linarith

/-- **`cor:hollowdich`, eq. `(hollowd)`**: at `τ = 1`, `d_N = ‖(N - 1)α‖`. -/
theorem cor_hollowdich_dN {a τ : ℝ} (h : InteriorParam a τ) (hτ : τ = 1) (N : ℕ) :
    dN N a τ = distZ (((N : ℝ) - 1) * alphaOf a τ) := by
  have hβ := (thm_resonance h).1.1 hτ
  rw [dN, hβ]; ring_nf

/-- **`cor:hollowdich`, eq. `(hollowcong)`**: at `τ = 1` with `α = p/q` in lowest terms,
`T_N(a) - I_N` is singular exactly when `N ≡ 1 (mod q)`. -/
theorem cor_hollowdich_rational {a τ : ℝ} (h : InteriorParam a τ) (hτ : τ = 1) {p q : ℕ}
    (hcop : Nat.Coprime p q) (hα : alphaOf a τ = p / q) (N : ℕ) (hN : 2 ≤ N) :
    N ∈ singDims a τ ↔ (N : ℤ) ≡ 1 [ZMOD q] := by
  have hβ := (thm_resonance h).1.1 hτ
  obtain ⟨hq, hp, -⟩ := rational_pq h hα
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : (q : ℝ) * betaOf a τ = (p : ℤ) := by
    rw [hβ, hα]; field_simp; push_cast; ring
  rw [(thm_rational_congr h hα hr).2.2 N hN, Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  have e : (p : ℤ) - N * p = p * (1 - N) := by ring
  rw [e]
  constructor
  · intro hd
    exact Int.dvd_of_dvd_mul_right_of_gcd_one hd (by
      rw [Int.gcd_natCast_natCast]; exact hcop.symm)
  · intro hd; exact Dvd.dvd.mul_left hd _

/-- **`cor:hollowdich`, irrational half**: at `τ = 1` with irrational `α`, no singular
physical dimension. -/
theorem cor_hollowdich_irrational {a τ : ℝ} (h : InteriorParam a τ) (hτ : τ = 1)
    (hirr : Irrational (alphaOf a τ)) : singDims a τ = ∅ := by
  have hβ := (thm_resonance h).1.1 hτ
  rw [Set.eq_empty_iff_forall_notMem]
  intro N hN
  obtain ⟨hN2, z, hz⟩ := (mem_singDims h N).1 hN
  rw [hβ] at hz
  have hm : ((N : ℤ) - 1) ≠ 0 := by omega
  apply (hirr.mul_intCast hm).ne_int z
  push_cast; linarith

/-- **`prop:affinecollapse`, eq. `(affinehom)`**: if `β = rα - m` (`r ≥ 1`, `m ∈ ℤ`, i.e.
`β ≡ rα (mod 1)`), then `d_N = ‖(N - r)α‖` for every `N`. -/
theorem prop_affinecollapse {a τ : ℝ} {r : ℕ} {m : ℤ}
    (hβ : betaOf a τ = r * alphaOf a τ - m) (N : ℕ) :
    dN N a τ = distZ (((N : ℝ) - r) * alphaOf a τ) := by
  rw [dN, hβ, show (N : ℝ) * alphaOf a τ - (r * alphaOf a τ - m) =
    ((N : ℝ) - r) * alphaOf a τ + m by ring, distZ_add_int]

end ShiftedKMS
