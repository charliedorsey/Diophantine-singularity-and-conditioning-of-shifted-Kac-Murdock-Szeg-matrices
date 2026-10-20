import KMS.Tridiag
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Topology.Instances.Matrix

/-!
# Gate 1.1 / 1.3 — KMS inverse product, KMS determinant, shifted Chebyshev determinant

* `kmsInvTri n a`: the endpoint-modified tridiagonal matrix
  `tridiag(-a; 1, 1+a², …, 1+a², 1)`, i.e. `(1 - a²) · T_N(a)⁻¹` (manuscript, proof of
  `lem:chebshift`).
* `kms_mul_kmsInvTri`  (`n ≥ 2`, every real `a`): `T_n(a) · kmsInvTri n a = (1 - a²) • 1`.
* `det_kms`            (`n ≥ 1`, every real `a`): `det T_n(a) = (1 - a²)^(n-1)`.
* `shifted_mul_kmsInvTri`: `(T_n(a) - τ I) · kmsInvTri n a = H_n` with
  `H_n = tridiag(τa; d, c, …, c, d)`, `c = 1 - a² - τ(1+a²)`, `d = 1 - a² - τ`.
* `cont_cheb`: `P_k = b^k (U_k(x) + a U_{k-1}(x))` when `c = 2bx`, `d = b(2x+a)`.
* `lem_chebshift` (manuscript `lem:chebshift`, `N ≥ 2`, `0 < a < 1`, `τ ≠ 0`).
-/

open Matrix Polynomial

namespace ShiftedKMS

/-! ### A product formula against a tridiagonal matrix -/

lemma mul_triDiag_apply {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (b : R) (D : Fin n → R) (i j : Fin n) :
    (A * triDiag b D) i j =
      A i j * D j + b * (∑ k : Fin n, if k.val + 1 = j.val then A i k else 0) +
        b * (∑ k : Fin n, if j.val + 1 = k.val then A i k else 0) := by
  rw [mul_apply]
  have hpt : ∀ k : Fin n, A i k * triDiag b D k j =
      (if k = j then A i j * D j else 0) + b * (if k.val + 1 = j.val then A i k else 0) +
        b * (if j.val + 1 = k.val then A i k else 0) := by
    intro k
    rw [triDiag_apply]
    by_cases h : k = j
    · subst h
      simp only [↓reduceIte, Nat.add_eq_left, one_ne_zero, mul_zero, add_zero]
    · have hv : k.val ≠ j.val := fun e => h (Fin.ext e)
      rw [if_neg h, if_neg h]
      split_ifs <;> first | ring1 | (exfalso; omega)
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma sum_fin_pred {R : Type*} [CommRing R] {n J : ℕ} (hJ : J ≤ n) (g : ℕ → R) :
    (∑ k : Fin n, if k.val + 1 = J then g k.val else 0) = if 1 ≤ J then g (J - 1) else 0 := by
  have h := Fin.sum_univ_eq_sum_range (fun k => if k + 1 = J then g k else 0) n
  rw [h]
  rcases J with _ | m
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Finset.sum_const_zero, nonpos_iff_eq_zero]
  · simp only [add_left_inj, Finset.sum_ite_eq', Finset.mem_range]
    rw [if_pos (by omega), if_pos (by omega)]
    simp only [add_tsub_cancel_right]

lemma sum_fin_succ' {R : Type*} [CommRing R] {n : ℕ} (J : ℕ) (g : ℕ → R) :
    (∑ k : Fin n, if J + 1 = k.val then g k.val else 0) = if J + 1 < n then g (J + 1) else 0 := by
  have h := Fin.sum_univ_eq_sum_range (fun k => if J + 1 = k then g k else 0) n
  rw [h, Finset.sum_ite_eq]
  simp only [Finset.mem_range]

/-! ### The KMS inverse product -/

/-- The manuscript's endpoint-modified tridiagonal matrix (`(1 - a²) T_N(a)⁻¹`). -/
def kmsInvTri (n : ℕ) (a : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  triDiag (-a) (endMat n 1 (1 + a ^ 2) 1)

lemma dist_add_r (I k : ℕ) : Nat.dist I (I + k) = k := by
  rw [Nat.dist_eq_sub_of_le (Nat.le_add_right I k)]; omega

lemma dist_add_l (I k : ℕ) : Nat.dist (I + k) I = k := by
  rw [Nat.dist_comm, dist_add_r]

/-- The scalar identity behind `kms_mul_kmsInvTri`, in natural-number coordinates. -/
lemma kms_entry (a : ℝ) {n I J : ℕ} (hn : 2 ≤ n) (hI : I < n) (hJ : J < n) :
    a ^ Nat.dist I J * (if J = 0 then 1 else if J + 1 = n then 1 else 1 + a ^ 2) +
      -a * (if 1 ≤ J then a ^ Nat.dist I (J - 1) else 0) +
      -a * (if J + 1 < n then a ^ Nat.dist I (J + 1) else 0) =
      if I = J then 1 - a ^ 2 else 0 := by
  rcases lt_trichotomy I J with h | h | h
  · obtain ⟨e, rfl⟩ : ∃ e, J = I + e + 1 := ⟨J - I - 1, by omega⟩
    have d0 : Nat.dist I (I + e + 1) = e + 1 := by rw [add_assoc, dist_add_r]
    have d1 : Nat.dist I (I + e + 1 - 1) = e := by
      rw [show I + e + 1 - 1 = I + e by omega, dist_add_r]
    have d2 : Nat.dist I (I + e + 1 + 1) = e + 2 := by
      rw [show I + e + 1 + 1 = I + (e + 2) by omega, dist_add_r]
    rw [d0, d1, d2]
    split_ifs <;> first | ring1 | omega | contradiction
  · subst h
    have d0 : Nat.dist I I = 0 := Nat.dist_self I
    have d2 : Nat.dist I (I + 1) = 1 := dist_add_r I 1
    rw [d0, d2]
    rcases I with _ | m
    · split_ifs <;> first | ring1 | omega | contradiction
    · have d1 : Nat.dist (m + 1) (m + 1 - 1) = 1 := by
        rw [show m + 1 - 1 = m by omega, dist_add_l]
      rw [d1]
      split_ifs <;> first | ring1 | omega | contradiction
  · obtain ⟨e, rfl⟩ : ∃ e, I = J + e + 1 := ⟨I - J - 1, by omega⟩
    have d0 : Nat.dist (J + e + 1) J = e + 1 := by rw [add_assoc, dist_add_l]
    have d2 : Nat.dist (J + e + 1) (J + 1) = e := by
      rw [show J + e + 1 = J + 1 + e by omega, dist_add_l]
    rw [d0, d2]
    rcases J with _ | m
    · split_ifs <;> first | ring1 | omega | contradiction
    · have d1 : Nat.dist (m + 1 + e + 1) (m + 1 - 1) = e + 2 := by
        rw [show m + 1 - 1 = m by omega, show m + 1 + e + 1 = m + (e + 2) by omega, dist_add_l]
      rw [d1]
      split_ifs <;> first | ring1 | omega | contradiction

/-- **G1.1 (inverse product).** For `n ≥ 2` and every real `a`,
`T_n(a) · tridiag(-a; 1, 1+a², …, 1+a², 1) = (1 - a²) I`. -/
theorem kms_mul_kmsInvTri {n : ℕ} (hn : 2 ≤ n) (a : ℝ) :
    kms n a * kmsInvTri n a = (1 - a ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  rw [kmsInvTri, mul_triDiag_apply]
  simp only [kms_apply]
  rw [sum_fin_pred (n := n) j.isLt.le (fun k => a ^ Nat.dist i.val k),
    sum_fin_succ' (n := n) j.val (fun k => a ^ Nat.dist i.val k)]
  have h := kms_entry a hn i.isLt j.isLt
  simp only [Matrix.smul_apply, one_apply, smul_eq_mul, endMat]
  by_cases hij : i = j
  · rw [if_pos (congrArg Fin.val hij)] at h
    rw [if_pos hij, mul_one]
    exact h
  · have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
    rw [if_neg hv] at h
    rw [if_neg hij, mul_zero]
    exact h

/-- `cont b c 1 ≡ 1` when `c - b² = 1`. -/
lemma cont_one_of {R : Type*} [CommRing R] {b c : R} (h : c - b ^ 2 = 1) :
    ∀ k, cont b c 1 k = 1
  | 0 => rfl
  | 1 => rfl
  | (k + 2) => by rw [cont_succ_succ, cont_one_of h (k + 1), cont_one_of h k]; linear_combination h

theorem det_kmsInvTri {n : ℕ} (hn : 2 ≤ n) (a : ℝ) : (kmsInvTri n a).det = 1 - a ^ 2 := by
  rw [kmsInvTri, det_endMat hn, cont_one_of (b := -a) (c := 1 + a ^ 2) (by ring),
    cont_one_of (b := -a) (c := 1 + a ^ 2) (by ring)]
  ring

lemma det_kms_of_ne {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : a ^ 2 ≠ 1) :
    (kms n a).det = (1 - a ^ 2) ^ (n - 1) := by
  have h := congrArg Matrix.det (kms_mul_kmsInvTri hn a)
  rw [det_mul, det_kmsInvTri hn, det_smul, det_one, mul_one, Fintype.card_fin] at h
  have hne : (1 - a ^ 2) ≠ 0 := fun h0 => ha (by linarith)
  have e : (1 - a ^ 2) ^ n = (1 - a ^ 2) ^ (n - 1) * (1 - a ^ 2) := by
    rw [← pow_succ]; congr 1; omega
  rw [e] at h
  exact mul_right_cancel₀ hne h

/-- **G1.1 (KMS determinant).** For `n ≥ 1` and every real `a`, `det T_n(a) = (1 - a²)^(n-1)`. -/
theorem det_kms {n : ℕ} (hn : 1 ≤ n) (a : ℝ) : (kms n a).det = (1 - a ^ 2) ^ (n - 1) := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    rw [det_fin_one]; simp only [Fin.isValue, kms_diag, tsub_self, pow_zero]
  · have hc : Continuous fun a : ℝ => (kms n a).det := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro i j
      exact continuous_pow (Nat.dist i.val j.val)
    have hg : Continuous fun a : ℝ => (1 - a ^ 2) ^ (n - 1) := by fun_prop
    have hd : Dense (({1}ᶜ : Set ℝ) ∩ {-1}ᶜ) :=
      (dense_compl_singleton (1 : ℝ)).inter_of_isOpen_right (dense_compl_singleton (-1 : ℝ))
        isOpen_compl_singleton
    have := Continuous.ext_on hd hc hg (fun x hx => by
      have hx1 : x ≠ 1 := hx.1
      have hx2 : x ≠ -1 := hx.2
      apply det_kms_of_ne h2
      intro hsq
      have : (x - 1) * (x + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp this with h | h
      · exact hx1 (by linarith)
      · exact hx2 (by linarith))
    exact congrFun this a

/-! ### The shifted matrix against `kmsInvTri` -/

/-- `H_N`: off-diagonal `b = τa`, interior diagonal `c = 1 - a² - τ(1+a²)`,
corner diagonal `d = 1 - a² - τ`. -/
def Hmat (n : ℕ) (a τ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  triDiag (τ * a) (endMat n (1 - a ^ 2 - τ) (1 - a ^ 2 - τ * (1 + a ^ 2)) (1 - a ^ 2 - τ))

theorem shifted_mul_kmsInvTri {n : ℕ} (hn : 2 ≤ n) (a τ : ℝ) :
    shifted n a τ * kmsInvTri n a = Hmat n a τ := by
  rw [shifted, sub_mul, kms_mul_kmsInvTri hn]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_mul,
    kmsInvTri, Hmat, triDiag_apply,
    endMat, smul_eq_mul]
  split_ifs <;> ring

/-- `det (T_n(a) - τ I) = det H_n / (1 - a²)` (`n ≥ 2`, `a² ≠ 1`). -/
theorem det_shifted_eq_div {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : a ^ 2 ≠ 1) (τ : ℝ) :
    (shifted n a τ).det = (Hmat n a τ).det / (1 - a ^ 2) := by
  have hne : (1 - a ^ 2) ≠ 0 := fun h0 => ha (by linarith)
  rw [← shifted_mul_kmsInvTri hn, det_mul, det_kmsInvTri hn, mul_div_assoc, div_self hne,
    mul_one]

/-! ### Chebyshev form of the continuant -/

/-- `P_k = b^k (U_k(x) + a U_{k-1}(x))` for `c = 2bx`, `d = b(2x + a)` (with `U_{-1} = 0`). -/
theorem cont_cheb (a b x : ℝ) :
    ∀ k : ℕ, cont b (2 * b * x) (b * (2 * x + a)) k =
      b ^ k * ((Chebyshev.U ℝ (k : ℤ)).eval x + a * (Chebyshev.U ℝ ((k : ℤ) - 1)).eval x)
  | 0 => by simp only [cont_zero, pow_zero, CharP.cast_eq_zero, Chebyshev.U_zero, eval_one, zero_sub, Int.reduceNeg, Chebyshev.U_neg_one, eval_zero, mul_zero, add_zero, mul_one]
  | 1 => by simp only [cont_one, pow_one, Nat.cast_one, Chebyshev.U_one, eval_mul, eval_ofNat, eval_X, sub_self, Chebyshev.U_zero, eval_one, mul_one]
  | (k + 2) => by
      rw [cont_succ_succ, cont_cheb a b x (k + 1), cont_cheb a b x k]
      have r2 := congrArg (eval x) (Chebyshev.U_add_two ℝ (k : ℤ))
      have r1 := congrArg (eval x) (Chebyshev.U_add_one ℝ (k : ℤ))
      simp only [eval_sub, eval_mul, eval_X, eval_ofNat] at r1 r2
      have i1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      have i2 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by push_cast; ring
      have i3 : (k : ℤ) + 1 - 1 = k := by ring
      have i4 : (k : ℤ) + 2 - 1 = k + 1 := by ring
      rw [i1, i2, i3, i4]
      linear_combination (-b ^ (k + 2)) * r2 + (-a * b ^ (k + 2)) * r1

/-- The scalar `x = (1 - a² - τ(1 + a²)) / (2 τ a)` of manuscript eq. `(xdef)`. -/
noncomputable def chebX (a τ : ℝ) : ℝ := (1 - a ^ 2 - τ * (1 + a ^ 2)) / (2 * τ * a)

theorem det_Hmat {N : ℕ} (hN : 2 ≤ N) {a τ : ℝ} (ha : a ≠ 0) (hτ : τ ≠ 0) :
    (Hmat N a τ).det = (τ * a) ^ N *
      ((Chebyshev.U ℝ (N : ℤ)).eval (chebX a τ) +
        2 * a * (Chebyshev.U ℝ ((N : ℤ) - 1)).eval (chebX a τ) +
        a ^ 2 * (Chebyshev.U ℝ ((N : ℤ) - 2)).eval (chebX a τ)) := by
  set x := chebX a τ with hx
  set b := τ * a with hb
  have hc : 1 - a ^ 2 - τ * (1 + a ^ 2) = 2 * b * x := by
    have h2 : (2 * τ * a) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hτ) ha
    rw [hx, hb, chebX, mul_comm (2 * (τ * a)), div_mul_eq_mul_div, eq_div_iff h2]
    ring
  have hd : 1 - a ^ 2 - τ = b * (2 * x + a) := by
    rw [mul_add, ← mul_assoc, mul_comm b 2, ← hc, hb]; ring
  rw [Hmat, ← hb, hc, hd, det_endMat hN, cont_cheb, cont_cheb]
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have r2 := congrArg (eval x) (Chebyshev.U_add_two ℝ (m : ℤ))
  have r1 := congrArg (eval x) (Chebyshev.U_add_one ℝ (m : ℤ))
  simp only [eval_sub, eval_mul, eval_X, eval_ofNat] at r1 r2
  have e1 : ((m + 2 - 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by rw [show m + 2 - 1 = m + 1 by omega]; push_cast; ring
  have e2 : ((m + 2 - 2 : ℕ) : ℤ) = (m : ℤ) := by rw [show m + 2 - 2 = m by omega]
  have e3 : ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 := by push_cast; ring
  have e4 : (m : ℤ) + 1 - 1 = m := by ring
  have e5 : (m : ℤ) + 2 - 1 = m + 1 := by ring
  have e6 : (m : ℤ) + 2 - 2 = m := by ring
  rw [e1, e2, e3, e4, e5, e6, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  linear_combination (-(τ * a) ^ (m + 2)) * r2 + (-a * (τ * a) ^ (m + 2)) * r1

/-- **Manuscript `lem:chebshift` (shifted Chebyshev determinant), general form.**
For `N ≥ 2`, `a ≠ 0`, `a² ≠ 1`, `τ ≠ 0`. -/
theorem det_shifted_cheb {N : ℕ} (hN : 2 ≤ N) {a τ : ℝ} (ha : a ≠ 0) (ha1 : a ^ 2 ≠ 1)
    (hτ : τ ≠ 0) :
    (shifted N a τ).det = (τ * a) ^ N / (1 - a ^ 2) *
      ((Chebyshev.U ℝ (N : ℤ)).eval (chebX a τ) +
        2 * a * (Chebyshev.U ℝ ((N : ℤ) - 1)).eval (chebX a τ) +
        a ^ 2 * (Chebyshev.U ℝ ((N : ℤ) - 2)).eval (chebX a τ)) := by
  rw [det_shifted_eq_div hN ha1, det_Hmat hN ha hτ]
  ring

/-- **Manuscript `lem:chebshift`**, exactly as stated: `N ≥ 2`, `0 < a < 1`, `τ ≠ 0`,
`x = (1 - a² - τ(1 + a²)) / (2 τ a)`. -/
theorem lem_chebshift {N : ℕ} (hN : 2 ≤ N) {a τ : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hτ : τ ≠ 0) :
    (shifted N a τ).det = (τ * a) ^ N / (1 - a ^ 2) *
      ((Chebyshev.U ℝ (N : ℤ)).eval ((1 - a ^ 2 - τ * (1 + a ^ 2)) / (2 * τ * a)) +
        2 * a * (Chebyshev.U ℝ ((N : ℤ) - 1)).eval ((1 - a ^ 2 - τ * (1 + a ^ 2)) / (2 * τ * a)) +
        a ^ 2 * (Chebyshev.U ℝ ((N : ℤ) - 2)).eval
          ((1 - a ^ 2 - τ * (1 + a ^ 2)) / (2 * τ * a))) :=
  det_shifted_cheb hN ha0.ne' (by nlinarith) hτ

end ShiftedKMS
