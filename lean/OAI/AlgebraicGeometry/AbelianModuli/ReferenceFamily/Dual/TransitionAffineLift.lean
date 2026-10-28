import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionDerivationLaws
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualLiftConormal

/-! # Transition Affine Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionAffineLift

noncomputable section

/-! A normalized original product transition gives an actual affine
dual-number lift, whose derivation is its original transition derivation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k B : Type) [CommRing k] [CommRing B] [Algebra k B]
    (e : (DualNumber k ⊗[k] B) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] B))
    (he : ∀ u, TensorReduction.dualTensorReduction k B (e u) = TensorReduction.dualTensorReduction k B u)

def dualTransitionAffineLift :
    {f : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber B) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k B //
      CoefficientSchemeTests.dualCoefficientOrigin k B ≫ f = Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B B (IsScalarTower.toAlgHom k B B)} := by
  let g : B →ₐ[k] DualNumber B :=
    (CoefficientLiftTensorMap.dualTensorTransitionCoordinates e).toAlgHom.comp (TrivSqZeroExt.inlAlgHom k B B)
  refine ⟨Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B (DualNumber B) g, ?_⟩
  apply (Affine.DualLiftReduction.affineDualLift_reduction_iff k B B (IsScalarTower.toAlgHom k B B) _).mpr
  rw [Affine.OverMorphismAlgebra.affineOverMorphismAlgebra_ofAlgHom]
  apply AlgHom.ext
  intro b
  exact CoefficientLiftTensorMap.dualTensorTransitionCoordinates_reduction e he (TrivSqZeroExt.inl b)

theorem dualTransitionAffineLift_derivation :
    Affine.DualLiftConormal.affineDualLiftDerivationEquiv k B B (dualTransitionAffineLift k B e he) =
      TransitionDerivationLaws.dualTensorTransitionDerivation e he := by
  apply Derivation.ext
  intro b
  rw [Affine.DualLiftConormal.affineDualLiftDerivationEquiv_apply]
  change (Affine.OverMorphismAlgebra.affineOverMorphismAlgebra k (DualNumber B) B
    (Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k B (DualNumber B)
      ((CoefficientLiftTensorMap.dualTensorTransitionCoordinates e).toAlgHom.comp (TrivSqZeroExt.inlAlgHom k B B))) b).snd = _
  rw [Affine.OverMorphismAlgebra.affineOverMorphismAlgebra_ofAlgHom]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TransitionAffineLift
