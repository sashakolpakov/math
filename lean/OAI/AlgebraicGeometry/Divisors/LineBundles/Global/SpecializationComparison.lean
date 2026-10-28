import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecializationCartier
import OAI.AlgebraicGeometry.Divisors.LineBundles.SpecializationCycleForgetting

/-! # Specialization Comparison -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecializationComparison.BundleCycles

noncomputable section

/-! # LineBundleCycles: the constructed global Chow specialization recovers the original complete cycle formula -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

def puncturedSpecializationCycleInput (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ]
      (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint
        (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ (Deformation.BundleCycles.globalDeformationProjection I ≫ f)) (d + 1) →₀ ℚ) :=
  (DimensionChow.BundleCycles.dimensionCycleTransport (ChowSpecialization.BundleCycles.puncturedStructureMap_eq I f) (d + 1)).comp (Punctured.SupportExtension.BundleCycles.puncturedGradedCycleExtension I f d)

theorem deformationOpenClosure_forget (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (Deformation.BundleCycles.globalDeformationProjection I ≫ f) (d + 1)
      (Open.CycleRestriction.BundleCycles.openDimensionCycleExtension (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) (Deformation.BundleCycles.globalDeformationProjection I ≫ f)
        (d + 1) (puncturedSpecializationCycleInput I f d z)) =
      SpecializationCartier.BundleCycles.deformationClosureCycleExtension I (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) := by
  exact (SpecializationCycleForgetting.BundleCycles.openDimensionCycleExtension_forget (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I)
    (Deformation.BundleCycles.globalDeformationProjection I ≫ f) (d + 1) _).trans
      (congrArg (Finsupp.mapDomain (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I))
        ((DimensionChow.BundleCycles.dimensionCycleTransport_forget (ChowSpecialization.BundleCycles.puncturedStructureMap_eq I f) (d + 1) _).trans
          (Punctured.SupportExtension.BundleCycles.puncturedGradedCycleExtension_forget I f d z)))

theorem deformationFiberSpecialization_forget_push (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Finsupp.mapDomain (SpecialFiber.BundleCycles.globalSpecialFiberMap I)
      (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (SpecialFiber.BundleCycles.globalSpecialFiberMap I ≫ (Deformation.BundleCycles.globalDeformationProjection I ≫ f)) d
        (Deformation.FiberSpecialization.BundleCycles.deformationFiberCycleSpecialization I f d (puncturedSpecializationCycleInput I f d z))) =
      Finsupp.mapDomain (SpecialFiber.BundleCycles.globalSpecialFiberMap I) (CycleSpecialization.BundleCycles.globalCycleSpecialization I (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z)) := by
  exact (SpecializationCycleForgetting.BundleCycles.principalCartierFiberCycleMap_forget_push (SpecialFiber.BundleCycles.globalSpecialFiberMap I)
    (Specialization.BundleCycles.globalDeformationParameterSection I) (Specialization.BundleCycles.globalSpecialFiberMap_range I) (Deformation.BundleCycles.globalDeformationProjection I ≫ f) d
    (Open.CycleRestriction.BundleCycles.openDimensionCycleExtension (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I) (Deformation.BundleCycles.globalDeformationProjection I ≫ f)
      (d + 1) (puncturedSpecializationCycleInput I f d z))).trans
        ((congrArg (Principal.CartierFiber.BundleCycles.principalCartierPointMap (Specialization.BundleCycles.globalDeformationParameterSection I))
          (deformationOpenClosure_forget I f d z)).trans
            (SpecializationCartier.BundleCycles.globalCycleSpecialization_push_cartier I (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z)).symm)

theorem globalGradedCycleSpecialization_eq_deformation (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    DimensionChow.BundleCycles.dimensionCycleTransport (ChowSpecialization.BundleCycles.specialFiberStructureMap_eq I f) d
      (Deformation.FiberSpecialization.BundleCycles.deformationFiberCycleSpecialization I f d (puncturedSpecializationCycleInput I f d z)) =
        Graded.GlobalSpecialization.BundleCycles.globalGradedCycleSpecialization I f d z := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d
  rw [DimensionChow.BundleCycles.dimensionCycleTransport_forget]
  apply Finsupp.mapDomain_injective (SpecialFiber.BundleCycles.globalSpecialFiberMap I).isClosedEmbedding.injective
  have hg := LinearMap.congr_fun (Graded.GlobalSpecialization.BundleCycles.globalGradedCycleSpecialization_push I f d) z
  exact (deformationFiberSpecialization_forget_push I f d z).trans
    (congrArg (Finsupp.mapDomain (SpecialFiber.BundleCycles.globalSpecialFiberMap I)) hg.symm)

theorem globalChowSpecialization_grading (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    ChowSpecialization.BundleCycles.globalChowSpecialization I f d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ (SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d (Graded.GlobalSpecialization.BundleCycles.globalGradedCycleSpecialization I f d z) := by
  rw [ChowSpecialization.BundleCycles.globalChowSpecialization_cycle]
  change DimensionChow.BundleCycles.dimensionChowTransport (ChowSpecialization.BundleCycles.specialFiberStructureMap_eq I f) d
    (DimensionChow.BundleCycles.dimensionCycleToChowQ (SpecialFiber.BundleCycles.globalSpecialFiberMap I ≫ (Deformation.BundleCycles.globalDeformationProjection I ≫ f)) d
      (Deformation.FiberSpecialization.BundleCycles.deformationFiberCycleSpecialization I f d (puncturedSpecializationCycleInput I f d z))) = _
  rw [DimensionChow.BundleCycles.dimensionChowTransport_cycle, globalGradedCycleSpecialization_eq_deformation]

theorem globalGradedCycleSpecialization_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d).comap
        (Graded.GlobalSpecialization.BundleCycles.globalGradedCycleSpecialization I f d) := by
  intro z hz
  apply (DimensionChow.BundleCycles.dimensionCycleToChowQ_eq_zero_iff (SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d _).mp
  rw [← globalChowSpecialization_grading,
    (DimensionChow.BundleCycles.dimensionCycleToChowQ_eq_zero_iff f d z).mpr hz, map_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecializationComparison.BundleCycles
