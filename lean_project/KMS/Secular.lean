import KMS.ChebShift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Gate 1.4 (stretch, partial) — the Chebyshev bracket at a symbolic crossing `x = -cos θ`

* `secular N a θ` — manuscript eq. `(secular)`:
  `S_N(θ) = sin((N+1)θ) - 2a sin(Nθ) + a² sin((N-1)θ)`.
* `secular_eq_DE` — the first half of `lem:phase`: `S_N = D sin(Nθ) + E cos(Nθ)` with
  `D = (1+a²) cos θ - 2a`, `E = (1-a²) sin θ`.  (The `R sin(Nθ + ψ)` / `arg` half is not done.)
* `bracket_neg_cos` — `U_N(-cos θ) + 2a U_{N-1}(-cos θ) + a² U_{N-2}(-cos θ)
  = (-1)^N S_N(θ) / sin θ` (`sin θ ≠ 0`).
* `det_shifted_secular` — `lem:chebshift` at any symbolic crossing `chebX a τ = -cos θ`.
-/

open Polynomial Real

namespace ShiftedKMS

/-- Manuscript eq. `(secular)`. -/
noncomputable def secular (N : ℕ) (a θ : ℝ) : ℝ :=
  Real.sin ((N + 1) * θ) - 2 * a * Real.sin (N * θ) + a ^ 2 * Real.sin ((N - 1) * θ)

/-- First half of manuscript `lem:phase`: `S_N(θ) = D(θ) sin(Nθ) + E(θ) cos(Nθ)`. -/
theorem secular_eq_DE (N : ℕ) (a θ : ℝ) :
    secular N a θ =
      ((1 + a ^ 2) * Real.cos θ - 2 * a) * Real.sin (N * θ) +
        ((1 - a ^ 2) * Real.sin θ) * Real.cos (N * θ) := by
  unfold secular
  have h1 : ((N : ℝ) + 1) * θ = N * θ + θ := by ring
  have h2 : ((N : ℝ) - 1) * θ = N * θ - θ := by ring
  rw [h1, h2, Real.sin_add, Real.sin_sub]
  ring

lemma U_neg_cos_mul_sin (k : ℕ) (θ : ℝ) :
    (Chebyshev.U ℝ (k : ℤ)).eval (-Real.cos θ) * Real.sin θ =
      (-1) ^ k * Real.sin ((k + 1) * θ) := by
  rw [Chebyshev.U_eval_neg, Int.cast_negOnePow_natCast, mul_assoc, Chebyshev.U_real_cos]
  push_cast; ring

/-- The Chebyshev bracket of `lem:chebshift` at `x = -cos θ`. -/
theorem bracket_neg_cos {N : ℕ} (hN : 2 ≤ N) (a θ : ℝ) (hs : Real.sin θ ≠ 0) :
    (Chebyshev.U ℝ (N : ℤ)).eval (-Real.cos θ) +
        2 * a * (Chebyshev.U ℝ ((N : ℤ) - 1)).eval (-Real.cos θ) +
        a ^ 2 * (Chebyshev.U ℝ ((N : ℤ) - 2)).eval (-Real.cos θ) =
      (-1) ^ N * secular N a θ / Real.sin θ := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have e1 : ((m + 2 : ℕ) : ℤ) - 1 = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
  have e2 : ((m + 2 : ℕ) : ℤ) - 2 = ((m : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2, eq_div_iff hs]
  have u0 := U_neg_cos_mul_sin (m + 2) θ
  have u1 := U_neg_cos_mul_sin (m + 1) θ
  have u2 := U_neg_cos_mul_sin m θ
  unfold secular
  have c1 : ((m + 1 : ℕ) : ℝ) + 1 = ((m + 2 : ℕ) : ℝ) := by push_cast; ring
  have c2 : ((m : ℕ) : ℝ) + 1 = ((m + 2 : ℕ) : ℝ) - 1 := by push_cast; ring
  rw [c1] at u1
  rw [c2] at u2
  have p1 : ((-1 : ℝ)) ^ (m + 1) = -(-1) ^ (m + 2) := by ring
  have p2 : ((-1 : ℝ)) ^ m = (-1) ^ (m + 2) := by ring
  rw [p1] at u1
  rw [p2] at u2
  linear_combination u0 + 2 * a * u1 + a ^ 2 * u2

/-- `lem:chebshift` evaluated at a symbolic interior crossing `x = -cos θ`. -/
theorem det_shifted_secular {N : ℕ} (hN : 2 ≤ N) {a τ θ : ℝ} (ha : a ≠ 0) (ha1 : a ^ 2 ≠ 1)
    (hτ : τ ≠ 0) (hx : chebX a τ = -Real.cos θ) (hs : Real.sin θ ≠ 0) :
    (shifted N a τ).det = (τ * a) ^ N / (1 - a ^ 2) * ((-1) ^ N * secular N a θ / Real.sin θ) := by
  rw [det_shifted_cheb hN ha ha1 hτ, hx, bracket_neg_cos hN a θ hs]

end ShiftedKMS
