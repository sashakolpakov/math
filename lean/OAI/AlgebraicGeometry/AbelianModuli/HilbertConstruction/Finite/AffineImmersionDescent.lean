import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.AffineOpenImmersionDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ImmersionExtension

/-! # Affine Immersion Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AffineImmersionDescent

noncomputable section

/-! Finitely many affine open immersions between flat models descend over a common coefficient algebra. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem exists_common_flat_affine_openImmersion_descent
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {ι : Type v} [Finite ι] (A B : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra C (A i)] [∀ i, Algebra C (B i)]
    [∀ i, Algebra.FiniteType C (A i)] [∀ i, Algebra.FiniteType C (B i)]
    [∀ i, Module.Flat C (A i)] [∀ i, Module.Flat C (B i)]
    (φ : ∀ i, A i →ₐ[C] B i)
    [∀ i, IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R R) (φ i)).toRingHom))]
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∀ i, IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id D D) (φ i)).toRingHom)) := by
  choose F _ hF hImm using fun i => HilbertConstruction.Flat.AffineOpenImmersionDescent.exists_flat_affine_openImmersion_descent (φ i) E hE
  obtain ⟨G, hG, hbound⟩ := CoefficientUpperBounds.exists_finiteType_coefficient_upperBound F hF
  refine ⟨E ⊔ G, le_sup_left, hE.sup hG, ?_⟩
  intro i
  have := hImm i
  exact Coefficient.ImmersionExtension.natural_tensorMap_isOpenImmersion_mono ((hbound i).trans le_sup_right) (φ i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AffineImmersionDescent
