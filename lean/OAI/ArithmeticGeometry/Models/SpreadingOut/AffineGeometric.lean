import OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricCoefficientShrink
import OAI.ArithmeticGeometry.Models.Foundations

/-! # Affine Geometric -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.AffineGeometric.Construction

noncomputable section

/-! Good affine fibers yield a concrete geometrically connected coefficient
model with its generic-fiber isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct _root_.NumberField

universe u

open OAI.ArithmeticGeometry.Models.Foundations.Constructions

theorem coefficient_model_of_eventually_integral_affine
    (K : Type u) [Field K] [NumberField K] (s : Finset K)
    (C : Type u) [CommRing C] [Algebra (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) C]
    [Algebra.FinitePresentation (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) C]
    (r : CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) (hr : r ≠ 0)
    (hgood : ∀ (L : Type u) [Field L] [Algebra (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) L],
      algebraMap (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) L r ≠ 0 →
        IsDomain (L ⊗[CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s] C)) :
    ∃ M : Foundations.Constructions.CoefficientModel K (Affine.Construction.affineOver K (K ⊗[CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s] C)),
      GeometricallyConnected M.model.hom ∧ GeometricallyIrreducible M.model.hom := by
  obtain ⟨t, h, hT⟩ := GeometricCoefficientShrink.Construction.coefficient_model_integral_fibers_after_enlargement (𝓞 K) K s C r hr hgood
  let S := CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s
  let T := CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K t
  let ψ : S →+* T := CoefficientFractionRing.Construction.coefficientRingInclusion (𝓞 K) K h
  let : Algebra S T := ψ.toAlgebra
  have hSTK : IsScalarTower S T K := IsScalarTower.of_algebraMap_eq (fun a ↦ by
    exact (CoefficientFractionRing.Construction.coefficientRingInclusion_coe (𝓞 K) K h a).symm)
  let B := T ⊗[S] C
  let N := Affine.Construction.affineOver T B
  have : IsAffineHom N.hom := inferInstanceAs (IsAffineHom
    (Spec.map (CommRingCat.ofHom (algebraMap T B))))
  have hfp : Scheme.Constructions.Foundations.FinitePresentationMorphism N.hom := ⟨inferInstance, inferInstance, inferInstance⟩
  let e : (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)).obj N ≅ Affine.Construction.affineOver K (K ⊗[S] C) :=
    Affine.Construction.baseChangeAffineIso T K B ≪≫ Affine.Construction.affineOverIso (Algebra.TensorProduct.cancelBaseChange S T K K C)
  refine ⟨⟨t, N, hfp, e⟩, ?_, ?_⟩
  · exact AffineGeometricCriterion.Construction.affine_geometricallyConnected_of_tensor_domains T B hT
  · exact AffineGeometricCriterion.Construction.affine_geometricallyIrreducible_of_tensor_domains T B hT

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.AffineGeometric.Construction
