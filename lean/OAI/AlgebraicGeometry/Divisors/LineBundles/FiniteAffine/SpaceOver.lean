import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceProperties
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.SupportDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.SeparatedSchemeTopology

/-! # Space Over -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceOver.BundleCycles

noncomputable section

/-! Every finite relative affine space is an actual product over the
complex base, with native projection maps and limiting product cone. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable (ι : Type) [Finite ι]

def complexFiniteAffineSpaceOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (AffineSpace ι Foundations.Scheme.ProjectiveSpace.complexBase ↘ Foundations.Scheme.ProjectiveSpace.complexBase)

def finiteAffineSpaceOver (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (AffineSpace.map ι X.hom ≫ (AffineSpace ι Foundations.Scheme.ProjectiveSpace.complexBase ↘ Foundations.Scheme.ProjectiveSpace.complexBase))

omit [Finite ι] in
theorem finiteAffineSpaceOver_structure (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    (finiteAffineSpaceOver ι X).hom = (AffineSpace ι X.left ↘ X.left) ≫ X.hom :=
  AffineSpace.map_over X.hom

def finiteAffineSpaceFiberOver (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : finiteAffineSpaceOver ι X ⟶ complexFiniteAffineSpaceOver ι :=
  Over.homMk (AffineSpace.map ι X.hom) rfl

def finiteAffineSpaceProjectionOver (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : finiteAffineSpaceOver ι X ⟶ X :=
  Over.homMk (AffineSpace ι X.left ↘ X.left) (finiteAffineSpaceOver_structure ι X).symm

def finiteAffineSpaceProductIsLimit (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : IsLimit
    (BinaryFan.mk (finiteAffineSpaceFiberOver ι X) (finiteAffineSpaceProjectionOver ι X)) :=
  (AffineSpace.isPullback_map (n := ι) X.hom).isLimit.pullbackConeEquivBinaryFanFunctor

instance complexFiniteAffineSpaceOver_integral : IsIntegral (complexFiniteAffineSpaceOver ι).left :=
  inferInstanceAs (IsIntegral (AffineSpace ι Foundations.Scheme.ProjectiveSpace.complexBase))

instance complexFiniteAffineSpaceOver_smooth : Smooth (complexFiniteAffineSpaceOver ι).hom :=
  SpaceProperties.BundleCycles.finiteAffineSpaceProjection_smooth ι Foundations.Scheme.ProjectiveSpace.complexBase

instance complexFiniteAffineSpaceOver_noetherian : AlgebraicGeometry.IsNoetherian (complexFiniteAffineSpaceOver ι).left :=
  inferInstanceAs (AlgebraicGeometry.IsNoetherian (AffineSpace ι Foundations.Scheme.ProjectiveSpace.complexBase))

instance complexFiniteAffineSpaceOver_metrizable : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (complexFiniteAffineSpaceOver ι)) := by
  let : IsSeparated (complexFiniteAffineSpaceOver ι).hom := inferInstanceAs (IsSeparated (AffineSpace ι Foundations.Scheme.ProjectiveSpace.complexBase ↘ Foundations.Scheme.ProjectiveSpace.complexBase))
  let : QuasiCompact (complexFiniteAffineSpaceOver ι).hom := inferInstanceAs (QuasiCompact (AffineSpace ι Foundations.Scheme.ProjectiveSpace.complexBase ↘ Foundations.Scheme.ProjectiveSpace.complexBase))
  exact CycleClass.Thom.SeparatedSchemeTopology.Constructions.schemePoints_metrizable (complexFiniteAffineSpaceOver ι)

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

instance finiteAffineSpaceOver_integral [IsIntegral X.left] [IsLocallyNoetherian X.left] :
    IsIntegral (finiteAffineSpaceOver ι X).left := inferInstanceAs (IsIntegral (AffineSpace ι X.left))

instance finiteAffineSpaceOver_smooth [Smooth X.hom] : Smooth (finiteAffineSpaceOver ι X).hom := by
  rw [finiteAffineSpaceOver_structure]
  exact smooth_comp (AffineSpace ι X.left ↘ X.left) X.hom

instance finiteAffineSpaceOver_noetherian [AlgebraicGeometry.IsNoetherian X.left] :
    AlgebraicGeometry.IsNoetherian (finiteAffineSpaceOver ι X).left :=
  inferInstanceAs (AlgebraicGeometry.IsNoetherian (AffineSpace ι X.left))

instance finiteAffineSpaceOver_metrizable [LocallyOfFiniteType X.hom] [IsSeparated X.hom] [QuasiCompact X.hom] :
    MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (finiteAffineSpaceOver ι X)) := by
  let : IsSeparated (finiteAffineSpaceOver ι X).hom := by
    rw [finiteAffineSpaceOver_structure]
    exact IsSeparated.stableUnderComposition.comp_mem (AffineSpace ι X.left ↘ X.left) X.hom
      inferInstance inferInstance
  let : QuasiCompact (finiteAffineSpaceOver ι X).hom := by
    rw [finiteAffineSpaceOver_structure]
    exact quasiCompact_comp (AffineSpace ι X.left ↘ X.left) X.hom
  let : LocallyOfFiniteType (finiteAffineSpaceOver ι X).hom := by
    rw [finiteAffineSpaceOver_structure]
    exact locallyOfFiniteType_comp (AffineSpace ι X.left ↘ X.left) X.hom
  exact CycleClass.Thom.SeparatedSchemeTopology.Constructions.schemePoints_metrizable (finiteAffineSpaceOver ι X)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceOver.BundleCycles
