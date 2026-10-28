import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SmoothFiberCriterion

/-! # Map Smooth Fiber Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.MapSmoothFiberCriterion

noncomputable section

/-! The affine pointwise smooth-fiber criterion for an explicit map of coefficient rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem specMap_stalk_formallySmooth_of_smooth_fiber
    {C A : CommRingCat.{u}} (φ : C ⟶ A)
    [Flat (Spec.map φ)] [LocallyOfFinitePresentation (Spec.map φ)] (q : PrimeSpectrum A)
    [Smooth ((Spec.map φ).fiberToSpecResidueField (Spec.map φ q))] :
    ((Spec.map φ).stalkMap q).hom.FormallySmooth := by
  let : Algebra C A := φ.hom.toAlgebra
  have : Module.Flat C A := RingHom.flat_algebraMap_iff.mp
    ((HasRingHomProperty.Spec_iff (P := @Flat)).mp (inferInstanceAs (Flat (Spec.map φ))))
  have : Algebra.FinitePresentation C A := RingHom.finitePresentation_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp
      (inferInstanceAs (LocallyOfFinitePresentation (Spec.map φ))))
  have : Smooth ((Spec.map (CommRingCat.ofHom (algebraMap C A))).fiberToSpecResidueField
      (q.comap (algebraMap C A))) := inferInstanceAs (Smooth ((Spec.map φ).fiberToSpecResidueField (Spec.map φ q)))
  exact Affine.SmoothFiberCriterion.spec_stalk_formallySmooth_of_smooth_fiber q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.MapSmoothFiberCriterion
