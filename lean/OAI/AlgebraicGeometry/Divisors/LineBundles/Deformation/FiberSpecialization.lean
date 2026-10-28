import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberSpecialization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ChowLocalization

/-! # Fiber Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FiberSpecialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: specialization from cycles on the actual punctured deformation

The constructed global parameter, its actual nonvanishing open, and its
proved closed normal-cone fiber instantiate the lift-independent cycle
specialization. The target Chow class is also constructed. Passage from
source Chow classes requires the remaining principal-relation proof.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme} [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- Specialization of finite cycles on the actual punctured deformation. -/
def deformationFiberCycleSpecialization (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint
      (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) (d + 1) →₀ ℚ) →ₗ[ℚ]
      (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) d →₀ ℚ) :=
  Principal.FiberSpecialization.BundleCycles.principalFiberCycleSpecialization (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)
    (Global.Specialization.BundleCycles.globalDeformationParameterSection I) (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) d

/-- Every actual ambient cycle lift gives the same specialization. -/
theorem deformationFiberCycleSpecialization_of_lift (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint
      (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) (d + 1) →₀ ℚ)
    (w : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) (d + 1) →₀ ℚ)
    (hw : Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I)
      (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) (d + 1) w = z) :
    deformationFiberCycleSpecialization I f d z =
      Principal.CartierFiber.BundleCycles.principalCartierFiberCycleMap (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I) (Global.Specialization.BundleCycles.globalDeformationParameterSection I)
        (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) d w :=
  Principal.FiberSpecialization.BundleCycles.principalFiberCycleSpecialization_of_lift (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)
    (ChowLocalization.BundleCycles.globalDeformationPunctured_closed_complement I) (Global.Specialization.BundleCycles.globalDeformationParameterSection I)
    (Global.Specialization.BundleCycles.globalSpecialFiberMap_range I) (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f) d z w hw

/-- The fiber Chow class of the actual specialization cycle, before source-relation descent. -/
def deformationFiberClassSpecialization (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint
      (ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) (d + 1) →₀ ℚ) →ₗ[ℚ]
      DimensionChow.BundleCycles.DimensionChowQ (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) d :=
  (DimensionChow.BundleCycles.dimensionCycleToChowQ (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I ≫ (Global.Deformation.BundleCycles.globalDeformationProjection I ≫ f)) d).comp
    (deformationFiberCycleSpecialization I f d)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FiberSpecialization.BundleCycles
