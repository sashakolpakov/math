import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.SpectralFunctions
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Basis Spectral Operator -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.BasisSpectralOperator.Construction

noncomputable section

/-! Operators with prescribed values on an eigenbasis, including
self-adjointness for real weights on an orthonormal basis. -/

open scoped Classical

def basisSpectralEnd
    {k L ι : Type*} [Field k] [AddCommGroup L] [Module k L]
    (b : Module.Basis ι k L) (w : ι → k) : L →ₗ[k] L := b.constr k (fun i => w i • b i)

theorem basisSpectralEnd_apply_basis
    {k L ι : Type*} [Field k] [AddCommGroup L] [Module k L]
    (b : Module.Basis ι k L) (w : ι → k) (i : ι) :
    basisSpectralEnd b w (b i) = w i • b i := b.constr_basis k _ i

theorem basisSpectralEnd_mul
    {k L ι : Type*} [Field k] [AddCommGroup L] [Module k L]
    (b : Module.Basis ι k L) (w v : ι → k) :
    basisSpectralEnd b w * basisSpectralEnd b v = basisSpectralEnd b (fun i => w i * v i) := by
  apply b.ext
  intro i
  simp only [Module.End.mul_apply, basisSpectralEnd_apply_basis, map_smul, smul_smul, mul_comm]

theorem basisSpectralEnd_eq_of_eigenbasis
    {k L ι : Type*} [Field k] [AddCommGroup L] [Module k L]
    (b : Module.Basis ι k L) (w : ι → k) (A : L →ₗ[k] L)
    (hA : ∀ i, A (b i) = w i • b i) : basisSpectralEnd b w = A := by
  apply b.ext
  intro i
  rw [basisSpectralEnd_apply_basis, hA]

theorem basisSpectralEnd_isSymmetric
    {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    [FiniteDimensional ℝ L] [Fintype ι]
    (b : OrthonormalBasis ι ℝ L) (w : ι → ℝ) : (basisSpectralEnd b.toBasis w).IsSymmetric := by
  have he : basisSpectralEnd b.toBasis w = (basisSpectralEnd b.toBasis w).adjoint := by
    apply (LinearMap.eq_adjoint_iff_basis b.toBasis b.toBasis _ _).mpr
    intro i j
    rw [basisSpectralEnd_apply_basis, basisSpectralEnd_apply_basis]
    simp only [OrthonormalBasis.coe_toBasis, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, b.inner_eq_ite]
    split_ifs with hij
    · subst j
      rfl
    · simp
  exact (LinearMap.eq_adjoint_iff _ _).mp he

theorem basisSpectralEnd_inner_self
    {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [Fintype ι]
    (b : OrthonormalBasis ι ℝ L) (w : ι → ℝ) (x : L) :
    inner ℝ (basisSpectralEnd b.toBasis w x) x = ∑ i, w i * (b.repr x i) ^ 2 := by
  calc
    inner ℝ (basisSpectralEnd b.toBasis w x) x =
        inner ℝ (basisSpectralEnd b.toBasis w (∑ i, b.repr x i • b i)) x := by rw [b.sum_repr]
    _ = _ := by
      rw [map_sum, sum_inner]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, show basisSpectralEnd b.toBasis w (b i) = w i • b i from
        basisSpectralEnd_apply_basis b.toBasis w i, real_inner_smul_left, real_inner_smul_left,
        ← b.repr_apply_apply]
      ring

theorem basisSpectralEnd_positive
    {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [Fintype ι]
    (b : OrthonormalBasis ι ℝ L) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (x : L) (hx : x ≠ 0) :
    0 < inner ℝ (basisSpectralEnd b.toBasis w x) x := by
  have hn : ∃ i, b.repr x i ≠ 0 := by
    by_contra! h
    apply hx
    apply b.repr.injective
    rw [map_zero]
    ext i
    exact h i
  rw [basisSpectralEnd_inner_self]
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (le_of_lt (hw i)) (sq_nonneg _)
  · obtain ⟨i, hi⟩ := hn
    exact ⟨i, Finset.mem_univ i, mul_pos (hw i) (sq_pos_of_ne_zero hi)⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.BasisSpectralOperator.Construction
