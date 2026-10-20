import KMS.Basic

/-!
# Gate 1.2 — symmetric tridiagonal matrices and the continuant

* `triDiag b D`: diagonal `D : Fin n → R`, constant off-diagonal `b` (both sides).
* `det_triDiag_succ_succ`: expansion from the top corner.
* `det_triDiag_rev`: reversal invariance.
* `cont b c d`: `P₀ = 1`, `P₁ = d`, `P_k = c P_{k-1} - b² P_{k-2}`.
* `det_leadBlock`: the leading `k × k` block (first corner `d`, then `c`) has determinant `P_k`
  — this is the manuscript's `P_k` in the proof of `lem:chebshift`.
* `det_endMat`: distinct endpoint diagonals `d₀` (first), `d₁` (last), interior `c`:
  for `N ≥ 2`, `det = d₁ P_{N-1} - b² P_{N-2}` with `P` built from `d₀`.
-/

open Matrix

namespace ShiftedKMS

variable {R : Type*} [CommRing R]

/-- Symmetric tridiagonal matrix with diagonal `D` and constant off-diagonal `b`. -/
def triDiag {n : ℕ} (b : R) (D : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if i = j then D i else if i.val + 1 = j.val ∨ j.val + 1 = i.val then b else 0

lemma triDiag_apply {n : ℕ} (b : R) (D : Fin n → R) (i j : Fin n) :
    triDiag b D i j =
      if i = j then D i else if i.val + 1 = j.val ∨ j.val + 1 = i.val then b else 0 := rfl

lemma triDiag_submatrix_succ {n : ℕ} (b : R) (D : Fin (n + 1) → R) :
    (triDiag b D).submatrix Fin.succ Fin.succ = triDiag b (D ∘ Fin.succ) := by
  ext i j
  simp only [submatrix_apply, triDiag_apply, Function.comp, Fin.succ_inj, Fin.val_succ]
  split_ifs <;> first | rfl | omega

/-- Expansion of a tridiagonal determinant from the top-left corner. -/
theorem det_triDiag_succ_succ {n : ℕ} (b : R) (D : Fin (n + 2) → R) :
    (triDiag b D).det =
      D 0 * (triDiag b (D ∘ Fin.succ)).det -
        b ^ 2 * (triDiag b (D ∘ Fin.succ ∘ Fin.succ)).det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  -- rows ≥ 2 vanish in column 0
  have hrest : ∑ i : Fin n, (-1 : R) ^ (i.succ.succ : ℕ) * triDiag b D i.succ.succ 0 *
      ((triDiag b D).submatrix (Fin.succAbove i.succ.succ) Fin.succ).det = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have : triDiag b D i.succ.succ 0 = 0 := by
      simp only [triDiag_apply, Fin.val_succ, Fin.val_zero]
      split_ifs with h1 h2
      · exact absurd h1 (Fin.succ_ne_zero _)
      · exfalso; rcases h2 with h | h <;> simp only [zero_add, Nat.right_eq_add, Nat.add_eq_zero_iff, one_ne_zero, and_false] at h
      · rfl
    rw [this]; ring
  rw [hrest, add_zero]
  -- row 0
  have h0 : (triDiag b D).submatrix (Fin.succAbove 0) Fin.succ = triDiag b (D ∘ Fin.succ) := by
    rw [Fin.succAbove_zero]; exact triDiag_submatrix_succ b D
  -- row 1: the minor has first row (b, 0, …, 0)
  set B := (triDiag b D).submatrix (Fin.succAbove (1 : Fin (n + 2))) Fin.succ with hB
  have hB0 : ∀ j : Fin (n + 1), B 0 j = if j = 0 then b else 0 := by
    intro j
    simp only [hB, submatrix_apply, triDiag_apply]
    have v0 : (Fin.succAbove (1 : Fin (n + 2)) 0).val = 0 := rfl
    have vs := Fin.val_succ j
    have z1 : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
    split_ifs <;> first | rfl | omega | (simp only [Fin.ext_iff] at *; omega)
  have hBs : B.submatrix Fin.succ Fin.succ = triDiag b (D ∘ Fin.succ ∘ Fin.succ) := by
    ext i j
    simp only [hB, submatrix_apply, triDiag_apply, Function.comp]
    have e : ∀ k : Fin n, Fin.succAbove (1 : Fin (n + 2)) k.succ = k.succ.succ := by
      intro k
      apply Fin.succAbove_of_le_castSucc
      simp only [Fin.castSucc_succ, Fin.le_def, Fin.coe_ofNat_eq_mod, Nat.one_mod, Fin.val_succ, Fin.val_castSucc, le_add_iff_nonneg_left, zero_le]
    rw [e i]
    simp only [Fin.succ_inj, Fin.val_succ]
    split_ifs <;> first | rfl | omega
  have hBdet : B.det = b * (triDiag b (D ∘ Fin.succ ∘ Fin.succ)).det := by
    rw [det_succ_row_zero, Fin.sum_univ_succ]
    have hz : ∑ j : Fin n, (-1 : R) ^ (j.succ : ℕ) * B 0 j.succ *
        (B.submatrix Fin.succ (Fin.succAbove j.succ)).det = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hB0, if_neg (Fin.succ_ne_zero _)]; ring
    rw [hz, add_zero, hB0, if_pos rfl, Fin.succAbove_zero, hBs]
    simp only [Nat.succ_eq_add_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, one_mul]
  have h10 : triDiag b D 1 0 = b := by
    simp only [triDiag_apply, one_ne_zero, ↓reduceIte, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.reduceAdd, Nat.zero_mod, OfNat.ofNat_ne_zero, zero_add, or_true]
  have hD : triDiag b D 0 0 = D 0 := by simp only [triDiag_apply, ↓reduceIte]
  simp only [Fin.succ_zero_eq_one]
  rw [h0, h10, ← hB, hBdet, hD]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul]
  ring

/-- Reversal invariance of tridiagonal determinants. -/
theorem det_triDiag_rev {n : ℕ} (b : R) (D : Fin n → R) :
    (triDiag b (D ∘ Fin.rev)).det = (triDiag b D).det := by
  have h : (triDiag b D).submatrix Fin.revPerm Fin.revPerm = triDiag b (D ∘ Fin.rev) := by
    ext i j
    simp only [submatrix_apply, triDiag_apply, Function.comp, Fin.revPerm_apply,
      Fin.rev_inj, Fin.val_rev]
    have hi := i.isLt
    have hj := j.isLt
    split_ifs <;> first | rfl | omega
  rw [← h, det_submatrix_equiv_self]

/-- The continuant `P₀ = 1, P₁ = d, P_k = c P_{k-1} - b² P_{k-2}`. -/
def cont (b c d : R) : ℕ → R
  | 0 => 1
  | 1 => d
  | (k + 2) => c * cont b c d (k + 1) - b ^ 2 * cont b c d k

@[simp] lemma cont_zero (b c d : R) : cont b c d 0 = 1 := rfl
@[simp] lemma cont_one (b c d : R) : cont b c d 1 = d := rfl
lemma cont_succ_succ (b c d : R) (k : ℕ) :
    cont b c d (k + 2) = c * cont b c d (k + 1) - b ^ 2 * cont b c d k := rfl

/-- Diagonal `(c, …, c, d)` of length `k` (last corner `d`). -/
def lastCorner (k : ℕ) (c d : R) : Fin k → R := fun i => if i.val + 1 = k then d else c

/-- Diagonal `(d, c, …, c)` of length `k` (first corner `d`): the manuscript's leading block. -/
def firstCorner (k : ℕ) (d c : R) : Fin k → R := fun i => if i.val = 0 then d else c

theorem det_lastCorner (b c d : R) : ∀ k : ℕ, (triDiag b (lastCorner k c d)).det = cont b c d k
  | 0 => by simp only [det_isEmpty, cont_zero]
  | 1 => by simp only [det_unique, Fin.default_eq_zero, Fin.isValue, triDiag_apply, ↓reduceIte, lastCorner, Fin.val_eq_zero, zero_add, cont_one]
  | (k + 2) => by
      rw [det_triDiag_succ_succ]
      have e1 : lastCorner (k + 2) c d ∘ Fin.succ = lastCorner (k + 1) c d := by
        funext i; simp only [lastCorner, Function.comp, Fin.val_succ]
        congr 1; apply propext; omega
      have e2 : lastCorner (k + 2) c d ∘ Fin.succ ∘ Fin.succ = lastCorner k c d := by
        funext i; simp only [lastCorner, Function.comp, Fin.val_succ]
        congr 1; apply propext; omega
      have e0 : lastCorner (k + 2) c d 0 = c := by simp only [lastCorner, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, Nat.right_eq_add, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      rw [e1, e2, e0, det_lastCorner b c d (k + 1), det_lastCorner b c d k, cont_succ_succ]

/-- **Manuscript `P_k`**: determinant of the leading `k × k` block (first corner `d`). -/
theorem det_leadBlock (b c d : R) (k : ℕ) :
    (triDiag b (firstCorner k d c)).det = cont b c d k := by
  have e : firstCorner k d c = lastCorner k c d ∘ Fin.rev := by
    funext i
    simp only [firstCorner, lastCorner, Function.comp, Fin.val_rev]
    have := i.isLt
    congr 1; apply propext; omega
  rw [e, det_triDiag_rev, det_lastCorner]

/-- Diagonal with distinct endpoint values: `d₀` first, `d₁` last, `c` interior. -/
def endMat (N : ℕ) (d₀ c d₁ : R) : Fin N → R :=
  fun i => if i.val = 0 then d₀ else if i.val + 1 = N then d₁ else c

/-- **Endpoint-modified tridiagonal determinant** (manuscript form: apply the final corner
`d₁` to the leading blocks `P_k` built from the first corner `d₀`). -/
theorem det_endMat {N : ℕ} (hN : 2 ≤ N) (b d₀ c d₁ : R) :
    (triDiag b (endMat N d₀ c d₁)).det =
      d₁ * cont b c d₀ (N - 1) - b ^ 2 * cont b c d₀ (N - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have e : endMat (m + 2) d₀ c d₁ = endMat (m + 2) d₁ c d₀ ∘ Fin.rev := by
    funext i
    simp only [endMat, Function.comp, Fin.val_rev]
    have := i.isLt
    split_ifs <;> first | rfl | omega
  rw [e, det_triDiag_rev, det_triDiag_succ_succ]
  have e1 : endMat (m + 2) d₁ c d₀ ∘ Fin.succ = lastCorner (m + 1) c d₀ := by
    funext i; simp only [endMat, lastCorner, Function.comp]
    have := Fin.val_succ i
    split_ifs <;> first | rfl | omega
  have e2 : endMat (m + 2) d₁ c d₀ ∘ Fin.succ ∘ Fin.succ = lastCorner m c d₀ := by
    funext i; simp only [endMat, lastCorner, Function.comp]
    have := Fin.val_succ i
    have := Fin.val_succ i.succ
    split_ifs <;> first | rfl | omega
  have e0 : endMat (m + 2) d₁ c d₀ 0 = d₁ := by simp only [endMat, Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceIte]
  rw [e1, e2, e0, det_lastCorner, det_lastCorner]
  simp only [Nat.add_one_sub_one, add_tsub_cancel_right]

/-! ### Small-size checks (`n = 2, 3` independently via `det_fin_two/three`; `n = 4`). -/

example (b d₀ c d₁ : R) :
    (triDiag b (endMat 2 d₀ c d₁)).det = d₀ * d₁ - b ^ 2 := by
  rw [det_fin_two]; simp only [Fin.isValue, triDiag_apply, ↓reduceIte, endMat, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.mod_succ, one_ne_zero, Nat.reduceAdd, zero_ne_one, zero_add, OfNat.ofNat_ne_zero, or_false, or_true, sub_right_inj]; ring

example (b d₀ c d₁ : R) :
    (triDiag b (endMat 3 d₀ c d₁)).det = d₀ * c * d₁ - b ^ 2 * (d₀ + d₁) := by
  rw [det_fin_three]; simp only [Fin.isValue, triDiag_apply, ↓reduceIte, endMat, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.one_mod, one_ne_zero, Nat.reduceAdd, Nat.reduceEqDiff, Nat.mod_succ, OfNat.ofNat_ne_zero, Fin.reduceEq, OfNat.ofNat_ne_one, or_false, or_true, zero_ne_one, zero_add, OfNat.one_ne_ofNat, or_self, mul_zero, add_zero, zero_mul, sub_zero]; ring

example (b d₀ c d₁ : R) :
    (triDiag b (endMat 3 d₀ c d₁)).det = d₁ * cont b c d₀ 2 - b ^ 2 * cont b c d₀ 1 :=
  det_endMat (by norm_num) b d₀ c d₁

example (b d₀ c d₁ : R) :
    (triDiag b (endMat 4 d₀ c d₁)).det =
      d₀ * c * c * d₁ - b ^ 2 * (d₀ * c + c * d₁ + d₀ * d₁) + b ^ 4 := by
  rw [det_endMat (by norm_num)]; simp only [Nat.add_one_sub_one, cont_succ_succ, Nat.reduceAdd, zero_add, cont_one, cont_zero, mul_one, Nat.reduceSub]; ring

end ShiftedKMS
