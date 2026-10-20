import KMS.PaperStatements
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# The homogeneous approximation constant, Hurwitz's theorem, and noble extremality

The accompanying manuscript notes after `prop:affinecollapse`: *"Thus the classical
homogeneous Markov–Lagrange theory reappears on every affine-hit line. In particular, on `τ = 1` it
gives the Hurwitz bound and the familiar noble/golden extremality of the normalized arithmetic
constant."*

The normalized arithmetic constant on an affine-hit line is (eq. `(Mhom)`)
`h(α) = liminf_{q→∞} q‖qα‖ = 𝓜₊(α, 0)`. This file proves, from first principles (no continued-fraction
library):

* **H3, Hurwitz.** For every irrational `α` there are infinitely many `q` with
  `|qα - p| < 1/(√5 q)` for some integer `p`; hence `h(α) ≤ 1/√5`. The proof is the classical
  Farey/mediant argument along a Stern–Brocot descent.
* **Quadratic lower bound.** If `Aβ² + Bβ + C = 0` with integers, `A ≠ 0` and discriminant
  `B² - 4AC = 5`, then `h(β) ≥ 1/√5`; with Hurwitz, `h(β) = 1/√5`.
* **H4a, noble extremality.** Every unimodular image `(aφ+b)/(cφ+d)`, `ad - bc = ±1`, of the golden
  ratio has discriminant 5, hence `h = 1/√5`; in particular `h(φ) = 1/√5` and the constant in
  Hurwitz's theorem cannot be lowered.
* **H5, transport.** `h(1-α) = h(α)`, `h(α+n) = h(α)`; `𝓜₊(α,α) = h(α)`; the golden hollow parameter
  `α_h = (3-√5)/2`; and the consequences for the actual hollow matrices `T_N(a) - I_N`.
-/

open Real Set Filter Topology Finset
open scoped ENNReal

namespace ShiftedKMS

namespace Hurwitz

/-- The homogeneous approximation constant `h(α) = liminf_{q→∞} q‖qα‖ ∈ [0,∞]`. -/
noncomputable def hconst (α : ℝ) : ℝ≥0∞ :=
  liminf (fun q : ℕ => ENNReal.ofReal (q * distZ (q * α))) atTop

lemma hconst_eq_Mplus (α : ℝ) : hconst α = Mplus α 0 := by
  simp only [hconst, Mplus, sub_zero]

/-! ## Arithmetic of `√5` -/

lemma irrational_sqrt_five : Irrational √5 := by
  have := Nat.Prime.irrational_sqrt (p := 5) Nat.prime_five
  simpa using this

lemma sqrt_five_sq : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)

lemma sqrt_five_pos : (0 : ℝ) < √5 := Real.sqrt_pos.2 (by norm_num)

/-- `x² = 5y²` has no integer solution with `y ≠ 0`. -/
lemma int_sq_ne_five_mul_sq {x y : ℤ} (hy : y ≠ 0) : x ^ 2 ≠ 5 * y ^ 2 := by
  intro h
  apply irrational_sqrt_five
  refine ⟨(|x| : ℚ) / |y|, ?_⟩
  have hy' : (0 : ℝ) < |(y : ℝ)| := abs_pos.2 (by exact_mod_cast hy)
  have hsq : ((|(x : ℝ)|) / |(y : ℝ)|) ^ 2 = 5 := by
    rw [div_pow, sq_abs, sq_abs, div_eq_iff (by positivity)]
    exact_mod_cast h
  push_cast
  rw [← hsq, Real.sqrt_sq (by positivity)]

/-! ## Elementary facts about `distZ` -/

lemma distZ_neg (x : ℝ) : distZ (-x) = distZ x := by
  apply le_antisymm
  · refine (round_le (-x) (-round x)).trans (le_of_eq ?_)
    rw [distZ]; push_cast
    rw [show -x - -(round x : ℝ) = -(x - round x) by ring, abs_neg]
  · refine (round_le x (-round (-x))).trans (le_of_eq ?_)
    rw [distZ]; push_cast
    rw [show x - -(round (-x) : ℝ) = -(-x - round (-x)) by ring, abs_neg]

lemma distZ_int_sub (x : ℝ) (m : ℤ) : distZ (m - x) = distZ x := by
  rw [show (m : ℝ) - x = -x + m by ring, distZ_add_int, distZ_neg]

lemma distZ_le_abs_sub_int (x : ℝ) (m : ℤ) : distZ x ≤ |x - m| := round_le x m

lemma distZ_pos_of_irrational {α : ℝ} (hα : Irrational α) {q : ℕ} (hq : 1 ≤ q) :
    0 < distZ (q * α) := by
  rcases (distZ_nonneg (q * α)).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨z, hz⟩ := (distZ_eq_zero_iff _).1 h.symm
    apply hα
    refine ⟨(z : ℚ) / q, ?_⟩
    have : (q : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ q := by exact_mod_cast hq
                             linarith
    push_cast
    field_simp
    linarith

/-! ## H5a: invariances of `h` -/

theorem hconst_add_int (α : ℝ) (n : ℤ) : hconst (α + n) = hconst α := by
  unfold hconst
  congr 1
  funext q
  rw [show (q : ℝ) * (α + n) = q * α + ((q : ℤ) * n : ℤ) by push_cast; ring, distZ_add_int]

theorem hconst_one_sub (α : ℝ) : hconst (1 - α) = hconst α := by
  unfold hconst
  congr 1
  funext q
  rw [show (q : ℝ) * (1 - α) = ((q : ℤ) : ℝ) - q * α by push_cast; ring, distZ_int_sub]

theorem hconst_neg (α : ℝ) : hconst (-α) = hconst α := by
  have := hconst_one_sub (-α)
  rw [show 1 - -α = α + ((1 : ℤ) : ℝ) by push_cast; ring, hconst_add_int] at this
  exact this.symm

/-! ## H3: the Stern–Brocot descent and Hurwitz's theorem -/

/-- Farey neighbours around an irrational `α` with `b + d` as large as we like:
`a/b < α < c/d`, `bc - ad = 1`. -/
lemma farey_descent {α : ℝ} (hα : Irrational α) (k : ℕ) :
    ∃ a c : ℤ, ∃ b d : ℕ, 1 ≤ b ∧ 1 ≤ d ∧ (b : ℤ) * c - a * d = 1 ∧
      (a : ℝ) < α * b ∧ α * d < c ∧ k + 2 ≤ b + d := by
  induction k with
  | zero =>
    refine ⟨⌊α⌋, ⌊α⌋ + 1, 1, 1, le_rfl, le_rfl, by ring, ?_, ?_, le_rfl⟩
    · have h1 := Int.floor_le α
      have h2 : (⌊α⌋ : ℝ) ≠ α := fun h => hα ⟨⌊α⌋, by simpa using h⟩
      push_cast; rw [mul_one]; exact lt_of_le_of_ne h1 h2
    · push_cast; rw [mul_one]; exact Int.lt_floor_add_one α
  | succ k ih =>
    obtain ⟨a, c, b, d, hb, hd, hdet, hab, hcd, hk⟩ := ih
    have hne : α * (b + d : ℕ) ≠ ((a + c : ℤ) : ℝ) := by
      intro h
      apply hα
      refine ⟨((a + c : ℤ) : ℚ) / (b + d : ℕ), ?_⟩
      have : ((b + d : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast at h ⊢
      field_simp
      linarith
    rcases lt_or_gt_of_ne hne with h | h
    · refine ⟨a, a + c, b, b + d, hb, by omega, by push_cast; linear_combination hdet, hab, ?_, by omega⟩
      push_cast at h ⊢; linarith
    · refine ⟨a + c, c, b + d, d, by omega, hd, by push_cast; linear_combination hdet, ?_, hcd, by omega⟩
      push_cast at h ⊢; linarith

/-- The algebraic core of Hurwitz's argument: for positive `x, y`,
`x² - √5 xy + y² ≤ 0` and `2x ≤ (√5 - 1) y` force `√5 = (2x + y)/y`. -/
lemma hurwitz_core {x y : ℝ} (hy : 0 < y) (h1 : x ^ 2 - √5 * x * y + y ^ 2 ≤ 0)
    (h2 : 2 * x ≤ (√5 - 1) * y) : √5 = (2 * x + y) / y := by
  have hs := sqrt_five_sq
  set u := 2 * x - (√5 - 1) * y with hu
  have key : u * (u - 2 * y) ≤ 0 := by
    have : u * (u - 2 * y) = 4 * (x ^ 2 - √5 * x * y + y ^ 2) := by
      rw [hu]; linear_combination (y ^ 2) * hs
    rw [this]; linarith
  have hu0 : u ≤ 0 := by linarith
  have : u = 0 := by nlinarith
  rw [eq_div_iff hy.ne']
  linarith

lemma hurwitz_core_nat {x y : ℕ} (hy : 1 ≤ y)
    (h1 : (x : ℝ) ^ 2 - √5 * x * y + (y : ℝ) ^ 2 ≤ 0) (h2 : 2 * (x : ℝ) ≤ (√5 - 1) * y) : False := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have := hurwitz_core hy' h1 h2
  exact irrational_sqrt_five ⟨((2 * x + y : ℕ) : ℚ) / y, by rw [this]; push_cast; ring⟩

/-- The larger root bound: `y² - √5 yu + u² ≤ 0`, `y > 0` give `2u ≤ (√5 + 1) y`. -/
lemma upper_root {u y : ℝ} (hy : 0 < y) (h : y ^ 2 - √5 * y * u + u ^ 2 ≤ 0) :
    2 * u ≤ (√5 + 1) * y := by
  by_contra hc
  push Not at hc
  have h1 : 0 < 2 * u - √5 * y - y := by linarith
  have h2 : 0 < 2 * u - √5 * y + y := by linarith
  have e : (2 * u - √5 * y - y) * (2 * u - √5 * y + y) = 4 * (y ^ 2 - √5 * y * u + u ^ 2) := by
    linear_combination (y ^ 2) * sqrt_five_sq
  have := mul_pos h1 h2
  linarith

/-- **Hurwitz's three-fraction lemma.** Among `a/b`, `c/d` and the mediant `(a+c)/(b+d)` of Farey
neighbours around an irrational `α`, one fraction `p/q` satisfies `|qα - p| < 1/(√5 q)`; it also
lies within the Farey interval, `|qα - p| < q/(bd)`. -/
lemma hurwitz_three {α : ℝ} (hα : Irrational α) {a c : ℤ} {b d : ℕ} (hb : 1 ≤ b) (hd : 1 ≤ d)
    (hdet : (b : ℤ) * c - a * d = 1) (hab : (a : ℝ) < α * b) (hcd : α * d < c) :
    ∃ p : ℤ, ∃ q : ℕ, 1 ≤ q ∧ |q * α - p| < 1 / (√5 * q) ∧ |q * α - p| < q / (b * d) := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hb0 : (0 : ℝ) < b := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hdetR : (b : ℝ) * c - a * d = 1 := by exact_mod_cast hdet
  have h5 := sqrt_five_pos
  set xa : ℝ := b * α - a with hxa
  set xc : ℝ := c - d * α with hxc
  have hxa0 : 0 < xa := by rw [hxa]; linarith
  have hxc0 : 0 < xc := by rw [hxc]; linarith
  -- `xa·d + xc·b = 1`
  have e : xa * d + xc * b = 1 := by rw [hxa, hxc]; linear_combination hdetR
  have hxad : xa * d < 1 := by nlinarith
  have hxcb : xc * b < 1 := by nlinarith
  have hbd0 : (0 : ℝ) < b * d := by positivity
  clear_value xa xc
  have hIa : |b * α - a| < b / (b * d) := by
    rw [← hxa, abs_of_pos hxa0, lt_div_iff₀ hbd0]; nlinarith
  have hIc : |d * α - c| < d / (b * d) := by
    rw [show (d : ℝ) * α - c = -xc by rw [hxc]; ring, abs_neg, abs_of_pos hxc0,
      lt_div_iff₀ hbd0]
    nlinarith
  by_cases hA : |b * α - a| < 1 / (√5 * b)
  · exact ⟨a, b, hb, hA, hIa⟩
  by_cases hC : |d * α - c| < 1 / (√5 * d)
  · exact ⟨c, d, hd, hC, hIc⟩
  push Not at hA hC
  rw [← hxa, abs_of_pos hxa0, div_le_iff₀ (by positivity)] at hA
  rw [show (d : ℝ) * α - c = -xc by rw [hxc]; ring, abs_neg, abs_of_pos hxc0,
    div_le_iff₀ (by positivity)] at hC
  -- `b² - √5 bd + d² ≤ 0`
  have hstar : (b : ℝ) ^ 2 - √5 * b * d + (d : ℝ) ^ 2 ≤ 0 := by
    have h1 : (b : ℝ) * d * √5 * (xa * d + xc * b) = b * d * √5 := by rw [e, mul_one]
    have h2 := mul_le_mul_of_nonneg_left hA (sq_nonneg (d : ℝ))
    have h3 := mul_le_mul_of_nonneg_left hC (sq_nonneg (b : ℝ))
    linear_combination h2 + h3 + h1
  set B : ℕ := b + d with hBdef
  have hBR : (B : ℝ) = b + d := by rw [hBdef]; push_cast; ring
  have hB0 : (0 : ℝ) < B := by rw [hBR]; positivity
  set xm : ℝ := B * α - ((a + c : ℤ) : ℝ) with hxm
  have hxm_eq : xm = xa - xc := by rw [hxm, hBR, hxa, hxc]; push_cast; ring
  have hne : xm ≠ 0 := by
    intro h
    apply hα
    refine ⟨((a + c : ℤ) : ℚ) / B, ?_⟩
    rw [hxm, sub_eq_zero] at h
    push_cast at h ⊢
    field_simp
    linarith
  have hB1 : 1 ≤ B := by omega
  have hIm : |xm| < B / (b * d) := by
    rw [lt_div_iff₀ hbd0, hxm_eq, hBR]
    have k1 : xa * (b * d) < b := by
      have := mul_lt_mul_of_pos_left hxad hb0; linarith [show xa * (b * d) = b * (xa * d) by ring]
    have k2 : xc * (b * d) < d := by
      have := mul_lt_mul_of_pos_left hxcb hd0; linarith [show xc * (b * d) = d * (xc * b) by ring]
    have k3 : 0 < xa * (b * d) := by positivity
    have k4 : 0 < xc * (b * d) := by positivity
    rcases abs_cases (xa - xc) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
  by_cases hM : |xm| < 1 / (√5 * B)
  · exact ⟨a + c, B, hB1, hM, hIm⟩
  exfalso
  push Not at hM
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- the mediant lies above `α`: `(a+c) - Bα = xc - xa > 0`, paired with `a/b`
    rw [abs_of_neg hlt, div_le_iff₀ (by positivity), hxm_eq, hBR] at hM
    -- `xa·(b+d) + (xc - xa)·b = 1`
    have e2 : xa * (b + d) + (xc - xa) * b = 1 := by linear_combination e
    have h3 : (b : ℝ) ^ 2 - √5 * b * (b + d) + ((b : ℝ) + d) ^ 2 ≤ 0 := by
      have h1 : (b : ℝ) * (b + d) * √5 * (xa * (b + d) + (xc - xa) * b) = b * (b + d) * √5 := by
        rw [e2, mul_one]
      have h2 := mul_le_mul_of_nonneg_left hA (sq_nonneg ((b : ℝ) + d))
      have h4 := mul_le_mul_of_nonneg_left hM (sq_nonneg (b : ℝ))
      linear_combination h2 + h4 + h1
    have hr := upper_root hb0 h3
    exact hurwitz_core_nat (x := d) (y := b) hb (by linear_combination hstar) (by linarith)
  · -- the mediant lies below `α`: `Bα - (a+c) = xa - xc > 0`, paired with `c/d`
    rw [abs_of_pos hgt, div_le_iff₀ (by positivity), hxm_eq, hBR] at hM
    have e2 : (xa - xc) * d + xc * (b + d) = 1 := by linear_combination e
    have h3 : (d : ℝ) ^ 2 - √5 * d * (b + d) + ((b : ℝ) + d) ^ 2 ≤ 0 := by
      have h1 : (d : ℝ) * (b + d) * √5 * ((xa - xc) * d + xc * (b + d)) = d * (b + d) * √5 := by
        rw [e2, mul_one]
      have h2 := mul_le_mul_of_nonneg_left hC (sq_nonneg ((b : ℝ) + d))
      have h4 := mul_le_mul_of_nonneg_left hM (sq_nonneg (d : ℝ))
      linear_combination h2 + h4 + h1
    have hr := upper_root hd0 h3
    exact hurwitz_core_nat (x := b) (y := d) hd hstar (by linarith)

/-- **Hurwitz's theorem (H3), quantitative form.** For every irrational `α` and every `Q`, there is
`q ≥ Q` and an integer `p` with `|qα - p| < 1/(√5 q)`. -/
theorem hurwitz_exists_large {α : ℝ} (hα : Irrational α) (Q : ℕ) :
    ∃ q : ℕ, Q ≤ q ∧ 1 ≤ q ∧ ∃ p : ℤ, |q * α - p| < 1 / (√5 * q) := by
  -- `δ = min_{1 ≤ q ≤ Q} ‖qα‖ > 0`
  obtain ⟨q₀, hq₀, hmin⟩ := (Finset.Icc 1 (Q + 1)).exists_min_image (fun q : ℕ => distZ (q * α))
    ⟨1, by simp⟩
  set δ := distZ (q₀ * α)
  have hδ : 0 < δ := distZ_pos_of_irrational hα (Finset.mem_Icc.1 hq₀).1
  obtain ⟨k, hk⟩ := exists_nat_gt ((Q + 1) / δ)
  obtain ⟨a, c, b, d, hb, hd, hdet, hab, hcd, hbd⟩ := farey_descent hα k
  obtain ⟨p, q, hq, hgood, hin⟩ := hurwitz_three hα hb hd hdet hab hcd
  refine ⟨q, ?_, hq, p, hgood⟩
  by_contra hlt
  push Not at hlt
  have hqmem : q ∈ Finset.Icc 1 (Q + 1) := Finset.mem_Icc.2 ⟨hq, by omega⟩
  have h1 : δ ≤ |q * α - p| := (hmin q hqmem).trans (distZ_le_abs_sub_int _ p)
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbd' : (k : ℝ) + 2 ≤ b + d := by exact_mod_cast hbd
  have hprod : (k : ℝ) + 1 ≤ b * d := by nlinarith
  have hq' : (q : ℝ) ≤ Q + 1 := by exact_mod_cast (by omega : q ≤ Q + 1)
  have : δ < (Q + 1) / (k + 1) := by
    calc δ ≤ |q * α - p| := h1
      _ < q / (b * d) := hin
      _ ≤ (Q + 1) / (k + 1) := by
          apply div_le_div₀ (by positivity) hq' (by positivity) hprod
  rw [div_lt_iff₀ (by positivity)] at hk
  rw [lt_div_iff₀ (by positivity)] at this
  nlinarith

/-- **Hurwitz's theorem (H3)**: infinitely many denominators `q` admit `p` with
`|α - p/q| < 1/(√5 q²)`. -/
theorem hurwitz_infinite {α : ℝ} (hα : Irrational α) :
    {q : ℕ | 1 ≤ q ∧ ∃ p : ℤ, |α - p / q| < 1 / (√5 * q ^ 2)}.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨Q, hQ⟩ => ?_
  obtain ⟨q, hQq, hq, p, hp⟩ := hurwitz_exists_large hα (Q + 1)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have : q ∈ {q : ℕ | 1 ≤ q ∧ ∃ p : ℤ, |α - p / q| < 1 / (√5 * q ^ 2)} := by
    refine ⟨hq, p, ?_⟩
    rw [show α - p / q = (q * α - p) / q by field_simp, abs_div, abs_of_pos hq',
      div_lt_iff₀ hq']
    calc |q * α - p| < 1 / (√5 * q) := hp
      _ = 1 / (√5 * q ^ 2) * q := by field_simp
  have := hQ this
  omega

/-- **Hurwitz's bound (H3)**: `h(α) = liminf q‖qα‖ ≤ 1/√5` for every irrational `α`. -/
theorem hconst_le {α : ℝ} (hα : Irrational α) : hconst α ≤ ENNReal.ofReal (1 / √5) := by
  unfold hconst
  refine Filter.liminf_le_of_frequently_le' ?_
  rw [Filter.frequently_atTop]
  intro Q
  obtain ⟨q, hQq, hq, p, hp⟩ := hurwitz_exists_large hα Q
  refine ⟨q, hQq, ENNReal.ofReal_le_ofReal ?_⟩
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  calc (q : ℝ) * distZ (q * α) ≤ q * |q * α - p| :=
        mul_le_mul_of_nonneg_left (distZ_le_abs_sub_int _ p) hq'.le
    _ ≤ q * (1 / (√5 * q)) := mul_le_mul_of_nonneg_left hp.le hq'.le
    _ = 1 / √5 := by field_simp

/-! ## Quadratic irrationals of discriminant 5: the lower bound -/

section Quadratic

variable {A B C : ℤ} {β : ℝ}

lemma irrational_of_disc_five (hA : A ≠ 0) (hβ : A * β ^ 2 + B * β + C = 0)
    (hD : B ^ 2 - 4 * A * C = 5) : Irrational β := by
  rintro ⟨r, rfl⟩
  have hq : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_nz
  -- `(2A·num + B·den)² = 5 den²`
  apply int_sq_ne_five_mul_sq (x := 2 * A * r.num + B * r.den) hq
  have hr : (r : ℝ) = r.num / r.den := by exact_mod_cast (Rat.num_div_den r).symm
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  rw [hr] at hβ
  have hDR : (B : ℝ) ^ 2 - 4 * A * C = 5 := by exact_mod_cast hD
  have : ((2 * A * r.num + B * r.den : ℤ) : ℝ) ^ 2 = 5 * ((r.den : ℤ) : ℝ) ^ 2 := by
    push_cast
    field_simp at hβ
    linear_combination 4 * A * hβ + (r.den : ℝ) ^ 2 * hDR
  exact_mod_cast this

/-- For `q ≥ 1`: `q‖qβ‖ ≥ 1/(√5 + |A|/(2q))`. -/
lemma quad_lower_pointwise (hA : A ≠ 0) (hβ : A * β ^ 2 + B * β + C = 0)
    (hD : B ^ 2 - 4 * A * C = 5) {q : ℕ} (hq : 1 ≤ q) :
    1 / (√5 + |(A : ℝ)| / (2 * q)) ≤ q * distZ (q * β) := by
  set p : ℤ := round ((q : ℝ) * β)
  set ε := distZ (q * β) with hεdef
  have hε : ε = |(q : ℝ) * β - p| := rfl
  have hε0 : 0 ≤ ε := distZ_nonneg _
  have hεh : ε ≤ 1 / 2 := distZ_le_half _
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hA' : (0 : ℝ) < |(A : ℝ)| := abs_pos.2 (by exact_mod_cast hA)
  have hDR : (B : ℝ) ^ 2 - 4 * A * C = 5 := by exact_mod_cast hD
  set s : ℝ := 2 * A * β + B with hs
  have hs2 : s ^ 2 = 5 := by rw [hs]; linear_combination 4 * (A : ℝ) * hβ + hDR
  have hsabs : |s| = √5 := by rw [← Real.sqrt_sq_eq_abs, hs2]
  -- the integer norm `n = Ap² + Bpq + Cq²`
  obtain ⟨n, hn_def⟩ : ∃ n : ℤ, n = A * p ^ 2 + B * p * q + C * q ^ 2 := ⟨_, rfl⟩
  have hn : (n : ℝ) = (A * (p - q * β) + q * s) * (p - q * β) := by
    rw [hn_def]; push_cast; rw [hs]; linear_combination ((q : ℝ) ^ 2) * hβ
  have hn0 : n ≠ 0 := by
    intro h0
    apply int_sq_ne_five_mul_sq (x := 2 * A * p + B * q) (y := (q : ℤ)) (by exact_mod_cast (by omega : q ≠ 0))
    have : (2 * A * p + B * q) ^ 2 = 4 * A * n + (B ^ 2 - 4 * A * C) * q ^ 2 := by
      rw [hn_def]; ring
    rw [this, h0, hD]; ring
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast this
  -- `1 ≤ ε (|A| ε + q√5)`
  have key : 1 ≤ ε * (|(A : ℝ)| * ε + q * √5) := by
    calc (1 : ℝ) ≤ |(n : ℝ)| := hn1
      _ = |A * (p - q * β) + q * s| * |(p - q * β)| := by rw [hn, abs_mul]
      _ ≤ (|(A : ℝ)| * ε + q * √5) * ε := by
          have h1 : |(p : ℝ) - q * β| = ε := by rw [hε, abs_sub_comm]
          rw [h1]
          apply mul_le_mul_of_nonneg_right _ hε0
          calc |A * ((p : ℝ) - q * β) + q * s| ≤ |A * ((p : ℝ) - q * β)| + |q * s| := abs_add_le _ _
            _ = |(A : ℝ)| * ε + q * √5 := by
                rw [abs_mul, abs_mul, h1, abs_of_pos hq', hsabs]
      _ = ε * (|(A : ℝ)| * ε + q * √5) := by ring
  have h5 := sqrt_five_pos
  rw [div_le_iff₀ (by positivity)]
  have : |(A : ℝ)| * ε ≤ |(A : ℝ)| / 2 := by nlinarith
  calc (1 : ℝ) ≤ ε * (|(A : ℝ)| * ε + q * √5) := key
    _ ≤ ε * (|(A : ℝ)| / 2 + q * √5) := by nlinarith
    _ = q * ε * (√5 + |(A : ℝ)| / (2 * q)) := by field_simp; ring

/-- Eventually `q‖qβ‖` exceeds any `c < 1/√5`. -/
lemma quad_eventually_gt (hA : A ≠ 0) (hβ : A * β ^ 2 + B * β + C = 0)
    (hD : B ^ 2 - 4 * A * C = 5) {c : ℝ} (hc : c < 1 / √5) :
    ∀ᶠ q : ℕ in atTop, c < q * distZ (q * β) := by
  have h5 := sqrt_five_pos
  have hlim : Tendsto (fun q : ℕ => 1 / (√5 + |(A : ℝ)| / (2 * q))) atTop (𝓝 (1 / (√5 + 0))) := by
    refine tendsto_const_nhds.div (tendsto_const_nhds.add ?_) (by positivity)
    have : Tendsto (fun q : ℕ => (2 * (q : ℝ))) atTop atTop :=
      (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
    exact tendsto_const_nhds.div_atTop this
  rw [add_zero] at hlim
  filter_upwards [hlim.eventually (lt_mem_nhds hc), eventually_ge_atTop 1] with q h1 h2
  exact h1.trans_le (quad_lower_pointwise hA hβ hD h2)

theorem hconst_ge_of_disc_five (hA : A ≠ 0) (hβ : A * β ^ 2 + B * β + C = 0)
    (hD : B ^ 2 - 4 * A * C = 5) : ENNReal.ofReal (1 / √5) ≤ hconst β := by
  unfold hconst
  refine le_of_forall_lt_imp_le_of_dense fun x hx => ?_
  have hxt : x ≠ ⊤ := ne_top_of_lt hx
  have hxr : x.toReal < 1 / √5 := by
    rw [← ENNReal.ofReal_toReal hxt] at hx
    exact (ENNReal.ofReal_lt_ofReal_iff (by have := sqrt_five_pos; positivity)).1 hx
  have hev := quad_eventually_gt hA hβ hD hxr
  refine le_trans ?_ (Filter.le_liminf_of_le (by isBoundedDefault)
    (hev.mono fun q hq => ENNReal.ofReal_le_ofReal hq.le))
  rw [ENNReal.ofReal_toReal hxt]

/-- **Discriminant-5 quadratic irrationals attain the Hurwitz constant**: `h(β) = 1/√5`. -/
theorem hconst_eq_of_disc_five (hA : A ≠ 0) (hβ : A * β ^ 2 + B * β + C = 0)
    (hD : B ^ 2 - 4 * A * C = 5) : hconst β = ENNReal.ofReal (1 / √5) :=
  le_antisymm (hconst_le (irrational_of_disc_five hA hβ hD)) (hconst_ge_of_disc_five hA hβ hD)

/-- For `c > √5`, only finitely many `q` admit `p` with `|β - p/q| < 1/(c q²)`. -/
theorem finite_of_disc_five (hA : A ≠ 0) (hβ : A * β ^ 2 + B * β + C = 0)
    (hD : B ^ 2 - 4 * A * C = 5) {c : ℝ} (hc : √5 < c) :
    {q : ℕ | 1 ≤ q ∧ ∃ p : ℤ, |β - p / q| < 1 / (c * q ^ 2)}.Finite := by
  have h5 := sqrt_five_pos
  have hc0 : 0 < c := h5.trans hc
  have hc' : 1 / c < 1 / √5 := one_div_lt_one_div_of_lt h5 hc
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 (quad_eventually_gt hA hβ hD hc')
  refine (Set.finite_lt_nat Q).subset fun q ⟨hq, p, hp⟩ => ?_
  by_contra hlt
  have hQq := hQ q (not_lt.1 hlt)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [show β - p / q = (q * β - p) / q by field_simp, abs_div, abs_of_pos hq',
    div_lt_iff₀ hq'] at hp
  have : (q : ℝ) * distZ (q * β) < 1 / c := by
    calc (q : ℝ) * distZ (q * β) ≤ q * |q * β - p| :=
          mul_le_mul_of_nonneg_left (distZ_le_abs_sub_int _ p) hq'.le
      _ < q * (1 / (c * q ^ 2) * q) := mul_lt_mul_of_pos_left hp hq'
      _ = 1 / c := by field_simp
  linarith

end Quadratic

/-! ## The golden ratio and its unimodular (noble) images -/

theorem golden_quadratic : (1 : ℤ) * Real.goldenRatio ^ 2 + (-1 : ℤ) * Real.goldenRatio + (-1 : ℤ) = 0 := by
  push_cast; linear_combination Real.goldenRatio_sq

/-- `h(φ) = 1/√5`. -/
theorem hconst_goldenRatio : hconst Real.goldenRatio = ENNReal.ofReal (1 / √5) :=
  hconst_eq_of_disc_five (A := 1) (B := -1) (C := -1) one_ne_zero golden_quadratic (by norm_num)

/-- **Noble numbers satisfy a discriminant-5 equation.** If `β (cφ + d) = aφ + b` with
`ad - bc = ±1`, then `Aβ² + Bβ + C = 0` with `A = d² + cd - c²`, `B = 2ac - ad - bc - 2bd`,
`C = b² + ab - a²`, `A ≠ 0`, and `B² - 4AC = 5`. -/
theorem noble_quadratic {a b c d : ℤ} (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1) {β : ℝ}
    (hβ : β * (c * Real.goldenRatio + d) = a * Real.goldenRatio + b) :
    (d ^ 2 + c * d - c ^ 2 : ℤ) ≠ 0 ∧
    ((d ^ 2 + c * d - c ^ 2 : ℤ) : ℝ) * β ^ 2 + ((2 * a * c - a * d - b * c - 2 * b * d : ℤ) : ℝ) * β +
      ((b ^ 2 + a * b - a ^ 2 : ℤ) : ℝ) = 0 ∧
    (2 * a * c - a * d - b * c - 2 * b * d) ^ 2 - 4 * (d ^ 2 + c * d - c ^ 2) *
      (b ^ 2 + a * b - a ^ 2) = 5 := by
  have hdet2 : (a * d - b * c) ^ 2 = 1 := by rcases hdet with h | h <;> rw [h] <;> norm_num
  have hden : (c : ℝ) * Real.goldenRatio + d ≠ 0 := by
    intro h0
    by_cases hc : c = 0
    · subst hc
      have hd : d = 0 := by exact_mod_cast (by simpa using h0 : (d : ℝ) = 0)
      subst hd; simp at hdet2
    · apply Real.goldenRatio_irrational
      refine ⟨(-d : ℚ) / c, ?_⟩
      have : (c : ℝ) ≠ 0 := by exact_mod_cast hc
      push_cast
      rw [div_eq_iff this]
      linarith
  refine ⟨?_, ?_, ?_⟩
  · intro hA
    have h4 : (2 * d + c) ^ 2 = 5 * c ^ 2 := by linear_combination 4 * hA
    by_cases hc : c = 0
    · subst hc
      have : d ^ 2 = 0 := by simpa using hA
      have hd : d = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      subst hd; simp at hdet2
    · exact int_sq_ne_five_mul_sq hc h4
  · have hβ' : β = (a * Real.goldenRatio + b) / (c * Real.goldenRatio + d) := by
      rw [eq_div_iff hden]; exact hβ
    have hdet2R : ((a : ℝ) * d - b * c) ^ 2 = 1 := by exact_mod_cast hdet2
    have hg2 := Real.goldenRatio_sq
    generalize Real.goldenRatio = g at hβ' hden hg2
    rw [hβ']
    push_cast
    field_simp
    linear_combination ((a : ℝ) * d - b * c) ^ 2 * hg2
  · linear_combination 5 * hdet2

/-- **Noble extremality (H4a)**: every unimodular image of the golden ratio has `h = 1/√5`. -/
theorem hconst_noble {a b c d : ℤ} (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1) {β : ℝ}
    (hβ : β * (c * Real.goldenRatio + d) = a * Real.goldenRatio + b) :
    hconst β = ENNReal.ofReal (1 / √5) := by
  obtain ⟨hA, hq, hD⟩ := noble_quadratic hdet hβ
  exact hconst_eq_of_disc_five hA hq hD

/-- **Noble extremality (H4a), quotient form**: `h((aφ+b)/(cφ+d)) = 1/√5` whenever
`ad - bc = ±1` (the denominator `cφ + d` is then automatically nonzero). -/
theorem hconst_noble' {a b c d : ℤ} (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1) :
    (c : ℝ) * Real.goldenRatio + d ≠ 0 ∧
    hconst ((a * Real.goldenRatio + b) / (c * Real.goldenRatio + d)) = ENNReal.ofReal (1 / √5) := by
  have hdet2 : (a * d - b * c) ^ 2 = 1 := by rcases hdet with h | h <;> rw [h] <;> norm_num
  have hden : (c : ℝ) * Real.goldenRatio + d ≠ 0 := by
    intro h0
    by_cases hc : c = 0
    · subst hc
      have hd : d = 0 := by exact_mod_cast (by simpa using h0 : (d : ℝ) = 0)
      subst hd; simp at hdet2
    · apply Real.goldenRatio_irrational
      refine ⟨(-d : ℚ) / c, ?_⟩
      have : (c : ℝ) ≠ 0 := by exact_mod_cast hc
      push_cast
      rw [div_eq_iff this]
      linarith
  exact ⟨hden, hconst_noble hdet (div_mul_cancel₀ _ hden)⟩

/-- **Sharpness of Hurwitz's constant**: no constant below `1/√5` works for every irrational; the
golden ratio is a witness. -/
theorem hurwitz_sharp {c : ℝ} (hc : c < 1 / √5) :
    Irrational Real.goldenRatio ∧ ENNReal.ofReal c < hconst Real.goldenRatio := by
  refine ⟨Real.goldenRatio_irrational, ?_⟩
  rw [hconst_goldenRatio]
  exact (ENNReal.ofReal_lt_ofReal_iff (by have := sqrt_five_pos; positivity)).2 hc

/-! ## H5: transport to the golden hollow parameter and to the matrices -/

/-- The golden hollow parameter `α_h = (3 - √5)/2 = 2 - φ`. -/
noncomputable def alphaGold : ℝ := (3 - √5) / 2

lemma alphaGold_quadratic : (1 : ℤ) * alphaGold ^ 2 + (-3 : ℤ) * alphaGold + (1 : ℤ) = 0 := by
  unfold alphaGold; push_cast; linear_combination (1 / 4 : ℝ) * sqrt_five_sq

lemma alphaGold_eq : alphaGold = 2 - Real.goldenRatio := by
  unfold alphaGold Real.goldenRatio; ring

theorem hconst_alphaGold : hconst alphaGold = ENNReal.ofReal (1 / √5) :=
  hconst_eq_of_disc_five (A := 1) (B := -3) (C := 1) one_ne_zero alphaGold_quadratic (by norm_num)

lemma alphaGold_bounds : 0 < alphaGold ∧ 2 * alphaGold < 1 := by
  have h5 := sqrt_five_sq
  have h2 : (2 : ℝ) < √5 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h3 : √5 < 3 := by
    rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  unfold alphaGold; constructor <;> linarith

/-- On an affine-hit line with `r = 1` (in particular on `τ = 1`): `𝓜₊(α, α) = h(α)`. -/
theorem Mplus_self (α : ℝ) : Mplus α α = hconst α := by
  have := prop_affinecollapse_Mplus α 1 0
  simp only [Nat.cast_one, one_mul, Int.cast_zero, sub_zero] at this
  rw [this, hconst_eq_Mplus]

/-- **Hurwitz on every affine-hit line**: if `β ≡ rα (mod 1)` with `r ≥ 1` and `α` irrational,
then `𝓜₊(α, β) = h(α) ≤ 1/√5`. -/
theorem affine_hit_hurwitz {α β : ℝ} (hα : Irrational α) (r : ℕ) (m : ℤ)
    (hβ : β = r * α - m) : Mplus α β = hconst α ∧ Mplus α β ≤ ENNReal.ofReal (1 / √5) := by
  have e : Mplus α β = hconst α := by rw [hβ, prop_affinecollapse_Mplus, hconst_eq_Mplus]
  exact ⟨e, e ▸ hconst_le hα⟩

variable {a : ℝ}

lemma hollow_beta (ha0 : 0 < a) (ha1 : a < 1) : betaOf a 1 = alphaOf a 1 :=
  (ShiftedKMS.thm_resonance (hollow_interior ha0 ha1)).1.1 rfl

/-- **H5d, Hurwitz on the hollow line.** For `0 < a < 1` with irrational `α = α(a,1)`:
`𝓜₊(α, β) = h(α) ≤ 1/√5`, and therefore the quadratic envelope of the actual hollow matrices obeys
`limsup κ₂(T_N(a) - I_N)/N² ≥ √5 · C(a,1)` (singular dimension deleted). -/
theorem hollow_hurwitz (ha0 : 0 < a) (ha1 : a < 1) (hirr : Irrational (alphaOf a 1)) :
    Mplus (alphaOf a 1) (betaOf a 1) = hconst (alphaOf a 1) ∧
    Mplus (alphaOf a 1) (betaOf a 1) ≤ ENNReal.ofReal (1 / √5) ∧
    ENNReal.ofReal (√5 * Cint a 1) ≤
      limsup (fun N : ℕ => ENNReal.ofReal (kappaMat N a 1 / (N : ℝ) ^ 2))
        (atTop ⊓ 𝓟 {N : ℕ | IsUnit (shifted N a 1)}) := by
  have h := hollow_interior ha0 ha1
  have hM : Mplus (alphaOf a 1) (betaOf a 1) = hconst (alphaOf a 1) := by
    rw [hollow_beta ha0 ha1, Mplus_self]
  refine ⟨hM, hM ▸ hconst_le hirr, ?_⟩
  rw [(PaperStatement.thm_quadratic_envelope h hirr).2.2.1, hM]
  have h5 := sqrt_five_pos
  have e : ENNReal.ofReal (√5 * Cint a 1) = ENNReal.ofReal (Cint a 1) / ENNReal.ofReal (1 / √5) := by
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]; congr 1; field_simp
  rw [e]
  exact ENNReal.div_le_div_left (hconst_le hirr) _

/-- **H5d, noble extremality on the hollow line.** If `α(a,1)` is a discriminant-5 quadratic
irrational (e.g. any unimodular image of `φ`), the hollow envelope is exactly
`limsup κ₂(T_N(a) - I_N)/N² = √5 · C(a,1) = (√5/π) √((1+a)/(1-a))`. -/
theorem hollow_noble (ha0 : 0 < a) (ha1 : a < 1) {A B C : ℤ} (hA : A ≠ 0)
    (hq : (A : ℝ) * alphaOf a 1 ^ 2 + B * alphaOf a 1 + C = 0) (hD : B ^ 2 - 4 * A * C = 5) :
    limsup (fun N : ℕ => ENNReal.ofReal (kappaMat N a 1 / (N : ℝ) ^ 2))
        (atTop ⊓ 𝓟 {N : ℕ | IsUnit (shifted N a 1)}) =
      ENNReal.ofReal (√5 / π * √((1 + a) / (1 - a))) := by
  have h := hollow_interior ha0 ha1
  have hirr := irrational_of_disc_five hA hq hD
  rw [(PaperStatement.thm_quadratic_envelope h hirr).2.2.1, hollow_beta ha0 ha1, Mplus_self,
    hconst_eq_of_disc_five hA hq hD, (hollow_constants ha0 ha1).2.2.2]
  have h5 := sqrt_five_pos
  have hpi := Real.pi_pos
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp

/-- **The golden hollow matrix.** With `α_h = (3-√5)/2` and `a_h = cos(π α_h)`: `0 < a_h < 1`,
`α(a_h, 1) = α_h`, `𝓜₊ = h(α_h) = 1/√5`, and the envelope of `T_N(a_h) - I_N` is
`(√5/π)√((1+a_h)/(1-a_h))`, the smallest value permitted by Hurwitz's bound on the hollow line. -/
theorem golden_hollow :
    0 < Real.cos (π * alphaGold) ∧ Real.cos (π * alphaGold) < 1 ∧
    alphaOf (Real.cos (π * alphaGold)) 1 = alphaGold ∧
    Mplus alphaGold alphaGold = ENNReal.ofReal (1 / √5) ∧
    limsup (fun N : ℕ => ENNReal.ofReal (kappaMat N (Real.cos (π * alphaGold)) 1 / (N : ℝ) ^ 2))
        (atTop ⊓ 𝓟 {N : ℕ | IsUnit (shifted N (Real.cos (π * alphaGold)) 1)}) =
      ENNReal.ofReal (√5 / π * √((1 + Real.cos (π * alphaGold)) / (1 - Real.cos (π * alphaGold)))) := by
  obtain ⟨h0, h1⟩ := alphaGold_bounds
  have htri : (alphaGold, alphaGold) ∈ triangleSet := ⟨h0, h0, by linarith⟩
  obtain ⟨hI, hA, -⟩ := triangle_inverse htri
  have ea : aOf alphaGold alphaGold = Real.cos (π * alphaGold) := by
    unfold aOf; rw [sub_self, mul_zero, zero_div, Real.cos_zero, div_one]; ring_nf
  have et : tauOf alphaGold alphaGold = 1 := by
    unfold tauOf
    exact div_self (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])).ne'
  rw [ea, et] at hI hA
  refine ⟨hI.1, hI.2.1, hA, by rw [Mplus_self, hconst_alphaGold], ?_⟩
  have hq : ((1 : ℤ) : ℝ) * alphaOf (Real.cos (π * alphaGold)) 1 ^ 2 +
      ((-3 : ℤ) : ℝ) * alphaOf (Real.cos (π * alphaGold)) 1 + ((1 : ℤ) : ℝ) = 0 := by
    rw [hA]; exact alphaGold_quadratic
  exact hollow_noble hI.1 hI.2.1 one_ne_zero hq (by norm_num)

/-- **H5c**: the homogeneous `𝓜₊` at the golden ratio and at the golden hollow parameter. -/
theorem Mplus_golden :
    Mplus Real.goldenRatio 0 = ENNReal.ofReal (1 / √5) ∧
    Mplus alphaGold 0 = ENNReal.ofReal (1 / √5) ∧
    Mplus alphaGold alphaGold = ENNReal.ofReal (1 / √5) ∧
    Mplus (1 - alphaGold) 0 = ENNReal.ofReal (1 / √5) := by
  refine ⟨by rw [← hconst_eq_Mplus, hconst_goldenRatio], by rw [← hconst_eq_Mplus, hconst_alphaGold],
    by rw [Mplus_self, hconst_alphaGold], by rw [← hconst_eq_Mplus, hconst_one_sub, hconst_alphaGold]⟩

end Hurwitz

end ShiftedKMS
