import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineModels

/-! # Affine Diagram Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineDiagramModel

noncomputable section

/-! Smooth affine diagram models record the actual arrows and their recovery, over one coefficient ring. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

structure SmoothAffineDiagramModel
    (R : Type u) [CommRing R] {I : Type v} (A : I → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {J : Type w} (s t : J → I) (φ : ∀ j, A (s j) →ₐ[R] A (t j)) where
  coefficients : Subalgebra ℤ R
  finiteType : Algebra.FiniteType ℤ coefficients
  algebra : I → CommAlgCat.{u} coefficients
  smooth : ∀ i, Algebra.Smooth coefficients (algebra i)
  arrow : ∀ j, algebra (s j) →ₐ[coefficients] algebra (t j)
  recovery : ∀ i, A i ≃ₐ[R] R ⊗[coefficients] algebra i
  recovery_naturality : ∀ j a, recovery (t j) (φ j a) =
    Algebra.TensorProduct.map (AlgHom.id R R) (arrow j) (recovery (s j) a)
  arrow_open : ∀ j, IsOpenImmersion (Spec.map (CommRingCat.ofHom (arrow j).toRingHom))

attribute [instance] SmoothAffineDiagramModel.finiteType SmoothAffineDiagramModel.smooth
attribute [instance] SmoothAffineDiagramModel.arrow_open

namespace SmoothAffineDiagramModel

variable {R : Type u} [CommRing R] {I : Type v} {A : I → Type u}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable {J : Type w} {s t : J → I} {φ : ∀ j, A (s j) →ₐ[R] A (t j)}

instance coefficients_noetherian (M : SmoothAffineDiagramModel R A s t φ) :
    IsNoetherianRing M.coefficients := Algebra.FiniteType.isNoetherianRing ℤ M.coefficients

instance algebra_noetherian (M : SmoothAffineDiagramModel R A s t φ) (i : I) :
    IsNoetherianRing (M.algebra i) := Algebra.FiniteType.isNoetherianRing M.coefficients (M.algebra i)

end SmoothAffineDiagramModel

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineDiagramModel
