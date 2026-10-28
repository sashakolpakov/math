import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.EuclideanCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketRepresentation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Trace

/-! # Hilbert Schmidt -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.HilbertSchmidt.Construction

noncomputable section

/-! The Euclidean norm on bilinear-operation coordinates is the
Hilbert--Schmidt norm. Infinitesimal changes of basis respect adjoints
for its associated inner product. -/

open scoped Classical
open _root_.ContinuousLinearMap

variable {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [FiniteDimensional ℝ L] [Fintype ι]

theorem continuousBilinearEuclideanCoordinates_inner
    (b : OrthonormalBasis ι ℝ L) (B C : L →L[ℝ] L →L[ℝ] L) :
    inner ℝ (EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis B)
      (EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis C) =
        ∑ i, ∑ j, inner ℝ (B (b i) (b j)) (C (b i) (b j)) := by
  change (∑ p : ι × ι × ι,
    EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis C p *
      EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates b.toBasis B p) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [EuclideanCoordinates.Construction.continuousBilinearEuclideanCoordinates_apply, Module.Basis.equivFun_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis]
  exact b.repr.inner_map_map (B (b i) (b j)) (C (b i) (b j))

omit [FiniteDimensional ℝ L] in
theorem orthonormal_sum_inner_precomp_adjoint [CompleteSpace L]
    (b : OrthonormalBasis ι ℝ L) (A F G : L →L[ℝ] L) :
    ∑ i, inner ℝ (F (A (b i))) (G (b i)) =
      ∑ i, inner ℝ (F (b i)) (G (adjoint A (b i))) := by
  let T : L →L[ℝ] L := (adjoint F).comp G
  have hleft : (∑ i, inner ℝ (F (A (b i))) (G (b i))) =
      LinearMap.trace ℝ L ((adjoint A).toLinearMap * T.toLinearMap) := by
    rw [LinearMap.trace_eq_sum_inner _ b]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℝ (F (A (b i))) (G (b i)) = inner ℝ (b i) (adjoint A (adjoint F (G (b i))))
    rw [adjoint_inner_right, adjoint_inner_right]
  have hright : LinearMap.trace ℝ L (T.toLinearMap * (adjoint A).toLinearMap) =
      ∑ i, inner ℝ (F (b i)) (G (adjoint A (b i))) := by
    rw [LinearMap.trace_eq_sum_inner _ b]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℝ (b i) (adjoint F (G (adjoint A (b i)))) = _
    rw [adjoint_inner_right]
  exact hleft.trans ((LinearMap.trace_mul_comm _ _ _).trans hright)

theorem bilinear_derivationDefect_sum_inner [CompleteSpace L]
    (b : OrthonormalBasis ι ℝ L) (A : L →L[ℝ] L) (B C : L →L[ℝ] L →L[ℝ] L) :
    (∑ i, ∑ j, inner ℝ (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A (b i) (b j)) (C (b i) (b j))) =
      ∑ i, ∑ j, inner ℝ (B (b i) (b j))
        (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect C (adjoint A) (b i) (b j)) := by
  have h₀ : (∑ i, ∑ j, inner ℝ (A (B (b i) (b j))) (C (b i) (b j))) =
      ∑ i, ∑ j, inner ℝ (B (b i) (b j)) (adjoint A (C (b i) (b j))) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (adjoint_inner_right A _ _).symm
  have h₁ : (∑ i, ∑ j, inner ℝ (B (A (b i)) (b j)) (C (b i) (b j))) =
      ∑ i, ∑ j, inner ℝ (B (b i) (b j)) (C (adjoint A (b i)) (b j)) := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact orthonormal_sum_inner_precomp_adjoint b A (B.flip (b j)) (C.flip (b j))
  have h₂ : (∑ i, ∑ j, inner ℝ (B (b i) (A (b j))) (C (b i) (b j))) =
      ∑ i, ∑ j, inner ℝ (B (b i) (b j)) (C (b i) (adjoint A (b j))) := by
    apply Finset.sum_congr rfl
    intro i _
    exact orthonormal_sum_inner_precomp_adjoint b A (B (b i)) (C (b i))
  simp only [Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect_apply, inner_sub_left, inner_sub_right,
    Finset.sum_sub_distrib, h₀, h₁, h₂]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.HilbertSchmidt.Construction
