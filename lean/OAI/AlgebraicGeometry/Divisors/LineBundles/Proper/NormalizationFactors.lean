import OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalFactorTo

/-! # Normalization Factors -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.NormalizationFactors.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual normalization lift and relative-normalization factor preserve properness -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
    (gX : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gX] [IsProper f]

include gX in
theorem NormalizationFunctor.normalizationLift_isProper : IsProper (NormalizationFunctorTo.BundleCycles.NormalizationFunctor.normalizationLift f hη) := by
  let : IsFinite (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap_isFinite X gX
  let : IsProper (NormalizationFunctorTo.BundleCycles.NormalizationFunctor.normalizationLift f hη ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y) := by
    rw [NormalizationFunctorTo.BundleCycles.NormalizationFunctor.normalizationLift_comp]
    infer_instance
  exact IsProper.of_comp (NormalizationFunctorTo.BundleCycles.NormalizationFunctor.normalizationLift f hη) (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y)

include gX in
theorem BirationalFactor.birationalFactor_isProper : IsProper (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor f hη) := by
  let : IsFinite (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X) := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap_isFinite X gX
  let : IsProper (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor f hη ≫ BirationalFactorTo.BundleCycles.BirationalFactor.intermediateMap f hη) := by
    rw [BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor_comp]
    infer_instance
  exact IsProper.of_comp (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor f hη) (BirationalFactorTo.BundleCycles.BirationalFactor.intermediateMap f hη)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.NormalizationFactors.BundleCycles
