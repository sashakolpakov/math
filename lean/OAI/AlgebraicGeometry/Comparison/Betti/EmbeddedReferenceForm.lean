import OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedCoherentCech
import OAI.AlgebraicGeometry.Comparison.Betti.ReferenceFormCechTotal

/-! # Embedded Reference Form -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedReferenceForm

noncomputable section

/-! The original algebraic-to-holomorphic form comparison is a quasi-isomorphism on Čech columns and total complexes of smooth integral projective closed subvarieties. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Comparison.Betti.ReferenceFormCechTotal.Dolbeault

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

variable (n : ℕ) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1))) [IsClosedImmersion f.left]

theorem embeddedOriginalFormCechMap_quasiIso (r : ℕ) :
    QuasiIso (ReferenceFormCech.algebraicHolomorphicFormCechMap X
      (fun i => f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i) r) := by
  let M := Exterior.ModuleSheaf.exteriorFormsModuleSheaf X r
  let : M.IsQuasicoherent := Betti.Smooth.ExteriorFrames.smooth_exteriorFormsModuleSheaf_quasicoherent X r
  let : M.IsFiniteType := Betti.Smooth.ExteriorFrames.smooth_exteriorFormsModuleSheaf_finiteType X r
  exact Projective.ReferenceForm.algebraicHolomorphicFormCechMap_quasiIso_of_module X
    (fun i => f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i) r
    (EmbeddedCoherentCech.embeddedCoherentCechMap_quasiIso n X f M)

theorem embeddedOriginalHolomorphicCechTotalMap_quasiIso :
    QuasiIso (ReferenceFormCechTotal.originalHolomorphicCechTotalMap X
      (fun i => f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i)) :=
  ReferenceFormCechTotal.originalHolomorphicCechTotalMap_quasiIso_of_columns X
    (fun i => f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i)
    (embeddedOriginalFormCechMap_quasiIso n X f)

end

end OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedReferenceForm
