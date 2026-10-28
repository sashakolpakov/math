import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.SupportExtension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ChowSpecialization
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow

/-! # Chow Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.ChowSpecialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual global Chow specialization from the original scheme to its normal cone

Pull cycles to the punctured deformation, close and intersect with the
actual parameter, and take the closed-fiber class. Each step descends
through the genuine rational-equivalence quotient by a proved theorem.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

omit [AlgebraicGeometry.IsNoetherian X] [LocallyOfFiniteType f] in
theorem puncturedStructureMap_eq :
    Punctured.DeformationCharts.BundleCycles.puncturedDeformationProjection I ≫ f =
      Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I ≫ (Deformation.BundleCycles.globalDeformationProjection I ≫ f) :=
  Category.assoc _ _ _

omit [AlgebraicGeometry.IsNoetherian X] [LocallyOfFiniteType f] in
theorem specialFiberStructureMap_eq :
    SpecialFiber.BundleCycles.globalSpecialFiberMap I ≫ (Deformation.BundleCycles.globalDeformationProjection I ≫ f) =
      SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f :=
  (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ f) (SpecialFiber.BundleCycles.globalSpecialFiberMap_toBase I))

def globalChowSpecialization (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d :=
  (DimensionChow.BundleCycles.dimensionChowTransport (specialFiberStructureMap_eq I f) d).comp
    ((Deformation.ChowSpecialization.BundleCycles.deformationChowSpecialization I f d).comp
      ((DimensionChow.BundleCycles.dimensionChowTransport (puncturedStructureMap_eq I f) (d + 1)).comp
        (Punctured.SupportExtension.BundleCycles.puncturedChowExtension I f d)))

theorem globalChowSpecialization_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    globalChowSpecialization I f d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionChowTransport (specialFiberStructureMap_eq I f) d
        (Deformation.FiberSpecialization.BundleCycles.deformationFiberClassSpecialization I f d
          (DimensionChow.BundleCycles.dimensionCycleTransport (puncturedStructureMap_eq I f) (d + 1)
            (Punctured.SupportExtension.BundleCycles.puncturedGradedCycleExtension I f d z))) := by
  change DimensionChow.BundleCycles.dimensionChowTransport (specialFiberStructureMap_eq I f) d (Deformation.ChowSpecialization.BundleCycles.deformationChowSpecialization I f d
    (DimensionChow.BundleCycles.dimensionChowTransport (puncturedStructureMap_eq I f) (d + 1)
      (Punctured.SupportExtension.BundleCycles.puncturedChowExtension I f d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z)))) = _
  rw [Punctured.SupportExtension.BundleCycles.puncturedChowExtension_cycle, DimensionChow.BundleCycles.dimensionChowTransport_cycle, Deformation.ChowSpecialization.BundleCycles.deformationChowSpecialization_cycle]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.ChowSpecialization.BundleCycles
