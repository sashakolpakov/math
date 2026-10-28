import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.SheafCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.CechQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedHolomorphicAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.CechCover

/-! # Holomorphic Smooth Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.HolomorphicSmoothCech

noncomputable section

/-! The actual holomorphic-to-smooth inclusion is a quasi-isomorphism
on the Čech total of an induced projective coordinate cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def inclusionMap {ι : Type} (U : ι → X.left.Opens) :=
  Acyclic.CechQuasiIso.cechMap (X := TopCat.of (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (fun i => AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (U i))
    (AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafComplex.inclusionSheafMap (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

theorem embedded_inclusionMap_quasiIso [IsProper X.hom]
    (n : ℕ) (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsClosedImmersion f.left] :
    QuasiIso (inclusionMap X (fun i => f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) := by
  have : T2Space (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := AlgebraicGeometry.Comparison.Betti.SeparatedPointTopology.separated_complexPoints_t2Space X
  have : LocallyCompactSpace (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_locallyCompact X
  have : SecondCountableTopology (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_secondCountable X
  apply Acyclic.CechQuasiIso.cechMap_quasiIso
  · exact AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafQuasiIso.inclusionSheafMap_quasiIso
      (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  · intro r
    exact AlgebraicGeometry.Comparison.Betti.EmbeddedHolomorphicAcyclicity.embeddedHolomorphicFormsCechAcyclic n X f r
  · intro r
    exact IntegralComparison.Smooth.SheafCohomology.cech_acyclic (E := AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel X)
      (fun i => AlgebraicGeometry.Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)) r

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.HolomorphicSmoothCech
