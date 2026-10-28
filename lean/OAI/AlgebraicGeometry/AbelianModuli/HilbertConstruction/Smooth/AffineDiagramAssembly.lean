import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineDiagramModel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NestedNoetherianCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.RecoveryCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.SmoothModel

/-! # Affine Diagram Assembly -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineDiagramAssembly

noncomputable section

/-! Compatible descended arrows and smooth charts assemble into a recovered affine diagram model. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

theorem exists_smoothAffineDiagramModel_from_coefficients
    {R : Type u} [CommRing R] {I : Type v} (A : I → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {J : Type w} (s t : J → I) (φ : ∀ j, A (s j) →ₐ[R] A (t j))
    (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C]
    (B : I → CommAlgCat.{u} C) [∀ i, Algebra.Smooth C (B i)]
    (e : ∀ i, A i ≃ₐ[R] R ⊗[C] B i)
    (D : Subalgebra C R) (F : Subalgebra D R) (hD : D.FG) (hF : F.FG)
    (ψ : ∀ j, D ⊗[C] B (s j) →ₐ[D] D ⊗[C] B (t j))
    (hψ : ∀ j x, Coefficient.TensorMaps.coefficientTensorMap D (ψ j x) =
      Affine.ModelConjugation.modelConjugateMap (e (s j)) (e (t j)) (φ j) (Coefficient.TensorMaps.coefficientTensorMap D x))
    (hImm : ∀ j, IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (Iterated.AffineModelRecovery.iteratedCoefficientArrow D F (ψ j)).toRingHom))) :
    ∃ M : AffineDiagramModel.SmoothAffineDiagramModel R A s t φ, C ≤ M.coefficients := by
  obtain ⟨hCF, hFT, _⟩ := NestedNoetherianCoefficients.nested_noetherian_coefficients C D F hD hF
  let M : AffineDiagramModel.SmoothAffineDiagramModel R A s t φ := {
    coefficients := F.restrictScalars ℤ
    finiteType := hFT
    algebra := fun i => Iterated.AffineModelRecovery.iteratedCoefficientAlgebra (A₀ := B i) D F
    smooth := fun i => Iterated.SmoothModel.iteratedCoefficientAlgebra_smooth (A₀ := B i) D F
    arrow := fun j => Iterated.AffineModelRecovery.iteratedCoefficientArrow D F (ψ j)
    recovery := fun i => Iterated.AffineModelRecovery.iteratedCoefficientRecovery D F (e i)
    recovery_naturality := fun j a =>
      Iterated.RecoveryCompatibility.iteratedCoefficientRecovery_map D F (e (s j)) (e (t j)) (φ j) (ψ j) (hψ j) a
    arrow_open := hImm }
  exact ⟨M, hCF⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineDiagramAssembly
