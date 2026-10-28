import OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationComponentSupportClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Chow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport

/-! # Presentation Graded Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationGradedCycle.BundleCycles

noncomputable section

/-! The finite codimension cycles of an integral presentation occupy the exact complementary dimension grade, with all original point coefficients preserved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier] (p d : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap)

def presentationDimensionPoint (Z : X.DimensionCycleSupport p) : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.structureMap d :=
  ⟨irreducibleSetEquivPoints Z.val, by
    rw [OrderIso.symm_apply_apply]
    have h := PresentationComponentSupportClass.BundleCycles.integralPresentationSupport_dimension X p Z
    omega⟩

def presentationGradedCycle : X.RationalDimensionCycle p →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.structureMap d →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (presentationDimensionPoint X p d hd)

theorem presentationGradedCycle_single (Z : X.DimensionCycleSupport p) (r : ℚ) :
    presentationGradedCycle X p d hd (Finsupp.single Z r) =
      Finsupp.single (presentationDimensionPoint X p d hd Z) r := Finsupp.mapDomain_single

theorem presentationGradedCycle_forget (z : X.RationalDimensionCycle p) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion X.structureMap d (presentationGradedCycle X p d hd z) = Chow.BundleCycles.pointCycle X p z := by
  change Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding X.structureMap d)
    (Finsupp.mapDomain (presentationDimensionPoint X p d hd) z) = _
  rw [← Finsupp.mapDomain_comp]
  exact (Finsupp.embDomain_eq_mapDomain (Chow.BundleCycles.cyclePointEmbedding X p) z).symm

theorem presentationGradedCycle_chow (z : X.RationalDimensionCycle p) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ X.structureMap d (Chow.BundleCycles.pointCycle X p z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ X.structureMap d (presentationGradedCycle X p d hd z) := by
  rw [← presentationGradedCycle_forget X p d hd]
  exact Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion X.structureMap d _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationGradedCycle.BundleCycles
