import OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricCoefficientShrink
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models

/-! # Geometric Affine Coefficients -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.GeometricAffineCoefficients.Abelian

noncomputable section

/-! Good affine fibers yield a concrete geometrically connected coefficient
model with its generic-fiber isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricCoefficientShrink.Construction OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients

theorem coefficient_model_of_eventually_integral_affine
    (R K : Type) [CommRing R] [Field K] [Algebra R K] (s : Finset K)
    (C : Type) [CommRing C] [Algebra (Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) C]
    [Algebra.FinitePresentation (Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) C]
    (r : Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) (hr : r ≠ 0)
    (hgood : ∀ (L : Type) [Field L] [Algebra (Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) L],
      algebraMap (Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s) L r ≠ 0 →
        IsDomain (L ⊗[Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s] C)) :
    ∃ M : AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients.CoefficientModel R K (Models.SpreadingOut.Affine.Construction.affineOver K (K ⊗[Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s] C)),
      GeometricallyConnected M.model.hom ∧ GeometricallyIrreducible M.model.hom := by
  obtain ⟨t, h, hT⟩ := Models.SpreadingOut.GeometricCoefficientShrink.Construction.coefficient_model_integral_fibers_after_enlargement R K s C r hr hgood
  let S := Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s
  let T := Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K t
  let ψ : S →+* T := Models.SpreadingOut.CoefficientFractionRing.Construction.coefficientRingInclusion R K h
  let : Algebra S T := ψ.toAlgebra
  have hSTK : IsScalarTower S T K := IsScalarTower.of_algebraMap_eq (fun a ↦ by
    exact (Models.SpreadingOut.CoefficientFractionRing.Construction.coefficientRingInclusion_coe R K h a).symm)
  let B := T ⊗[S] C
  let N := Models.SpreadingOut.Affine.Construction.affineOver T B
  have : IsAffineHom N.hom := inferInstanceAs (IsAffineHom
    (Spec.map (CommRingCat.ofHom (algebraMap T B))))
  have hfp : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism N.hom := ⟨inferInstance, inferInstance, inferInstance⟩
  let e : (Over.pullback (Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R K t)).obj N ≅ Models.SpreadingOut.Affine.Construction.affineOver K (K ⊗[S] C) :=
    Models.SpreadingOut.Affine.Construction.baseChangeAffineIso T K B ≪≫ Models.SpreadingOut.Affine.Construction.affineOverIso (Algebra.TensorProduct.cancelBaseChange S T K K C)
  refine ⟨⟨t, N, hfp, e⟩, ?_, ?_⟩
  · exact Models.SpreadingOut.AffineGeometricCriterion.Construction.affine_geometricallyConnected_of_tensor_domains T B hT
  · exact Models.SpreadingOut.AffineGeometricCriterion.Construction.affine_geometricallyIrreducible_of_tensor_domains T B hT

end

end OAI.ArithmeticGeometry.Descent.CMVariety.GeometricAffineCoefficients.Abelian
