import OAI.ArithmeticGeometry.Models.SpreadingOut.CoefficientFractionRing
import OAI.ArithmeticGeometry.Models.SpreadingOut.AffineGeometricCriterion

/-! # Geometric Coefficient Shrink -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricCoefficientShrink.Construction

noncomputable section

/-! Enlarge the finite coefficient ring to remove all bad fibers of an
affine model whose good fibers are controlled by one base element. -/

open scoped TensorProduct

universe u

theorem coefficient_model_integral_fibers_after_enlargement
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (s : Finset K) (C : Type u) [CommRing C] [Algebra (CoefficientSystem.Constructions.Foundations.coefficientRing R K s) C]
    (r : CoefficientSystem.Constructions.Foundations.coefficientRing R K s) (hr : r ≠ 0)
    (hgood : ∀ (L : Type u) [Field L] [Algebra (CoefficientSystem.Constructions.Foundations.coefficientRing R K s) L],
      algebraMap (CoefficientSystem.Constructions.Foundations.coefficientRing R K s) L r ≠ 0 →
        IsDomain (L ⊗[CoefficientSystem.Constructions.Foundations.coefficientRing R K s] C)) :
    ∃ (t : Finset K) (h : s ⊆ t),
      letI : Algebra (CoefficientSystem.Constructions.Foundations.coefficientRing R K s) (CoefficientSystem.Constructions.Foundations.coefficientRing R K t) :=
        (CoefficientFractionRing.Construction.coefficientRingInclusion R K h).toAlgebra
      ∀ (L : Type u) [Field L] [Algebra (CoefficientSystem.Constructions.Foundations.coefficientRing R K t) L],
        IsDomain (L ⊗[CoefficientSystem.Constructions.Foundations.coefficientRing R K t]
          (CoefficientSystem.Constructions.Foundations.coefficientRing R K t ⊗[CoefficientSystem.Constructions.Foundations.coefficientRing R K s] C)) := by
  obtain ⟨t, h, hu⟩ := CoefficientFractionRing.Construction.coefficient_element_becomes_unit R K s r hr
  let S := CoefficientSystem.Constructions.Foundations.coefficientRing R K s
  let T := CoefficientSystem.Constructions.Foundations.coefficientRing R K t
  let ψ : S →+* T := CoefficientFractionRing.Construction.coefficientRingInclusion R K h
  let : Algebra S T := ψ.toAlgebra
  refine ⟨t, h, ?_⟩
  intro L _ _
  let : Algebra S L := ((algebraMap T L).comp ψ).toAlgebra
  have : IsScalarTower S T L := IsScalarTower.of_algebraMap_eq' rfl
  have hunit : IsUnit (algebraMap S L r) := hu.map (algebraMap T L)
  have : IsDomain (L ⊗[S] C) := hgood L hunit.ne_zero
  let e := Algebra.TensorProduct.cancelBaseChange S T L L C
  exact Function.Injective.isDomain e.toRingHom e.injective

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricCoefficientShrink.Construction
