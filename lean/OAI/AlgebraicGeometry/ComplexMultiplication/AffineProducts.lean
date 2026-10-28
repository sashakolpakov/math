import OAI.AlgebraicGeometry.ComplexMultiplication.IntegralTensorProduct
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties

/-! # Affine Products -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.AffineProducts

noncomputable section

/-! # Actual integral affine products -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The actual affine fibred product is integral, with no extra geometric hypothesis. -/
theorem specIntegralProduct (A B : CommRingCat.{u}) [IsDomain A] [IsDomain B]
    (f : Spec A ⟶ Spec (.of K)) (g : Spec B ⟶ Spec (.of K))
    [LocallyOfFiniteType f] : IsIntegral (pullback f g) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom, ψ.hom]
  have hf : (algebraMap K A).FiniteType := HasRingHomProperty.Spec_iff.mp ‹_›
  let : Algebra.FiniteType K A := hf
  let : IsDomain (A ⊗[K] B) := IntegralTensorProduct.integralTensorProduct_isDomain
  exact IsIntegral.of_isIso (pullbackSpecIso K A B).inv

/-- The same result for actual affine schemes rather than chosen presentations. -/
theorem affineIntegralProduct {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] : IsIntegral (pullback f g) := by
  let i := pullback.map (X.isoSpec.inv ≫ f) (Y.isoSpec.inv ≫ g) f g
    X.isoSpec.inv Y.isoSpec.inv (𝟙 _) (by simp) (by simp)
  have : IsIntegral (pullback (X.isoSpec.inv ≫ f) (Y.isoSpec.inv ≫ g)) :=
    specIntegralProduct Γ(X, ⊤) Γ(Y, ⊤) _ _
  exact IsIntegral.of_isIso i

end

end OAI.AlgebraicGeometry.ComplexMultiplication.AffineProducts
