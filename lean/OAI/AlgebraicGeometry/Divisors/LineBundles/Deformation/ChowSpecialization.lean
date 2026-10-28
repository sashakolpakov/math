import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberChowSpecialization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FiberSpecialization

/-! # Chow Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ChowSpecialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: Chow specialization on the constructed punctured global deformation

This is the actual source quotient of the already constructed cycle
specialization; all principal relations are killed by the proved fiber
intersection theorem, including singular supports and common components.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

def deformationChowSpecialization (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ
      (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) (d + 1) →ₗ[ℚ]
      DimensionChow.BundleCycles.DimensionChowQ (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) d :=
  Principal.FiberChowSpecialization.BundleCycles.principalFiberChowSpecialization (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)
    (ChowLocalization.BundleCycles.globalDeformationPunctured_closed_complement I) (Global.Specialization.BundleCycles.globalDeformationParameterSection I)
    (Global.Specialization.BundleCycles.globalSpecialFiberMap_range I) (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) d

@[simp]
theorem deformationChowSpecialization_cycle (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint
      (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) (d + 1) →₀ ℚ) :
    deformationChowSpecialization I f d
      (DimensionChow.BundleCycles.dimensionCycleToChowQ
        (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) (d + 1) z) =
      FiberSpecialization.BundleCycles.deformationFiberClassSpecialization I f d z := rfl

theorem deformationChowSpecialization_of_lift (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint
      (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) (d + 1) →₀ ℚ)
    (w : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) (d + 1) →₀ ℚ)
    (hw : Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I)
      (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) (d + 1) w = z) :
    deformationChowSpecialization I f d
      (DimensionChow.BundleCycles.dimensionCycleToChowQ
        (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) (d + 1) z) =
      Principal.CartierFiber.BundleCycles.principalCartierFiberClassMap (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I) (Global.Specialization.BundleCycles.globalDeformationParameterSection I)
        (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) d w :=
  Principal.FiberChowSpecialization.BundleCycles.principalFiberChowSpecialization_of_lift (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)
    (ChowLocalization.BundleCycles.globalDeformationPunctured_closed_complement I) (Global.Specialization.BundleCycles.globalDeformationParameterSection I)
    (Global.Specialization.BundleCycles.globalSpecialFiberMap_range I) (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) d z w hw

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ChowSpecialization.BundleCycles
