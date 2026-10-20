import Mathlib

/-! Shifted KMS source-faithful bootstrap. No theorem of the paper assumed. -/
namespace ShiftedKMS
def kms (n : ℕ) (a : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => a ^ Nat.dist i.val j.val
def shifted (n : ℕ) (a τ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  kms n a - Matrix.diagonal (fun _ : Fin n => τ)
noncomputable def symbol (a θ : ℝ) : ℝ :=
  (1 - a ^ 2) / (1 - 2 * a * Real.cos θ + a ^ 2)
noncomputable def lowerEdge (a : ℝ) : ℝ := (1 - a) / (1 + a)
noncomputable def upperEdge (a : ℝ) : ℝ := (1 + a) / (1 - a)
theorem kms_apply (n : ℕ) (a : ℝ) (i j : Fin n) :
    kms n a i j = a ^ Nat.dist i.val j.val := rfl
theorem kms_diag (n : ℕ) (a : ℝ) (i : Fin n) :
    kms n a i i = 1 := by simp [kms]
theorem kms_transpose (n : ℕ) (a : ℝ) :
    (kms n a).transpose = kms n a := by
  ext i j
  simp [kms, Matrix.transpose_apply, Nat.dist_comm]
theorem shifted_apply (n : ℕ) (a τ : ℝ) (i j : Fin n) :
    shifted n a τ i j = a ^ Nat.dist i.val j.val - (if i = j then τ else 0) := by
  simp [shifted, kms, Matrix.sub_apply, Matrix.diagonal_apply]
end ShiftedKMS
