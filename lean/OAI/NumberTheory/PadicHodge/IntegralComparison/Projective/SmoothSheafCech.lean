import OAI.NumberTheory.PadicHodge.IntegralComparison.HolomorphicSmoothCech
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafFactorization
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.AdditiveImage

/-! # Smooth Sheaf Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SmoothSheafCech

noncomputable section

/-! The original algebraic-to-smooth sheaf map is a quasi-isomorphism
on a projective coordinate Čech cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  {ι : Type} (U : ι → X.left.Opens)

def map := AlgebraicGeometry.Comparison.Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X) U
  (AlgebraicGeometry.Comparison.Betti.Godement.AdditiveImage.additiveDirectImageComplexMap (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X)
    (AlgebraicGeometry.Comparison.Betti.Smooth.SheafMap.algebraicToSmoothSheafMap X))

theorem factorization : SmoothSheafCech.map X U =
    AlgebraicGeometry.Comparison.Betti.ReferenceFormCechTotal.originalHolomorphicCechTotalMap X U ≫
      HolomorphicSmoothCech.inclusionMap X U := by
  unfold SmoothSheafCech.map
  rw [← AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafFactorization.algebraicToHolomorphicSheafMap_factorization X]
  change AlgebraicGeometry.Comparison.Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X) U
    (AlgebraicGeometry.Comparison.Betti.Godement.AdditiveImage.additiveDirectImageComplexMap (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X)
      (AlgebraicGeometry.Comparison.Betti.Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X ≫
        ((AlgebraicGeometry.Comparison.Betti.TopologicalSheafPullback.sheafDirectImage (AlgebraicGeometry.Comparison.Betti.Analytification.Base.analytificationMap X)).mapHomologicalComplex
          (.up ℕ)).map (AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafComplex.inclusionSheafMap
            (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))) = _
  erw [AlgebraicGeometry.Comparison.Betti.Godement.AdditiveImage.additiveDirectImageComplexMap_postcompose,
    AlgebraicGeometry.Comparison.Betti.Cech.Column.sheafCechPullbackTotalMap_postcompose]
  rfl

theorem embedded_map_quasiIso [IsProper X.hom]
    (n : ℕ) (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1))) [IsClosedImmersion f.left] :
    QuasiIso (SmoothSheafCech.map X (fun i => f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i)) := by
  rw [factorization]
  exact quasiIso_comp _ _
    (hφ := AlgebraicGeometry.Comparison.Betti.EmbeddedReferenceForm.embeddedOriginalHolomorphicCechTotalMap_quasiIso n X f)
    (hφ' := HolomorphicSmoothCech.embedded_inclusionMap_quasiIso X (n + 1) f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SmoothSheafCech
