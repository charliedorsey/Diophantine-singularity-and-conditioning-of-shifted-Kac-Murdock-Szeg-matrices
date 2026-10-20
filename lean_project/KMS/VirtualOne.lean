import KMS.Arith

/-!
# The virtual one-dimensional KMS singularity line

Unlike the main theorems, these statements deliberately use dimension one.
They formally identify the omitted \(N=1\) matrix with the resonance diagonal.
-/

namespace ShiftedKMS

/-- \(T_1(a)\) is the one-by-one matrix with entry \(1\), for every \(a\). -/
theorem kms_one_entry (a : ℝ) (i j : Fin 1) :
    kms 1 a i j = 1 := by
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp [kms]

/-- \(B_1(a,1)\) is the zero one-by-one matrix. -/
theorem shifted_one_at_one (a : ℝ) :
    shifted 1 a 1 = (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp [shifted_apply]

/-- The virtual \(N=1\) matrix has determinant zero at the hollow shift. -/
theorem shifted_one_det_zero (a : ℝ) :
    (shifted 1 a 1).det = 0 := by
  rw [shifted_one_at_one]
  simp

/-- The virtual \(N=1\) affine residual vanishes along the resonance line. -/
theorem virtual_one_residual_zero {a τ : ℝ}
    (h : InteriorParam a τ) (hτ : τ = 1) :
    dN 1 a τ = 0 := by
  have hb : betaOf a τ = alphaOf a τ := (thm_resonance h).1.1 hτ
  simp [dN, hb, distZ, round_zero]

/-- In the parameter triangle, the virtual affine hit is precisely the hollow line. -/
theorem virtual_one_hit_iff_hollow {a τ : ℝ} (h : InteriorParam a τ) :
    (∃ z : ℤ, alphaOf a τ - betaOf a τ = z) ↔ τ = 1 := by
  constructor
  · intro hh
    obtain ⟨z, hz⟩ := hh
    obtain ⟨ha, hb, hab⟩ := (triangle_forward h).1
    have hz0 : z = 0 := by
      have hzl : (-1 : ℝ) < z := by rw [← hz]; linarith
      have hzu : (z : ℝ) < 1 := by rw [← hz]; linarith
      have hzl' : (-1 : ℤ) < z := by exact_mod_cast hzl
      have hzu' : z < (1 : ℤ) := by exact_mod_cast hzu
      omega
    apply (thm_resonance h).1.2
    have : alphaOf a τ - betaOf a τ = 0 := by simpa [hz0] using hz
    linarith
  · intro hτ
    exact ⟨0, by rw [(thm_resonance h).1.1 hτ]; simp⟩

end ShiftedKMS
