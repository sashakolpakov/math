import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularHypercohomologyNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSheafComparison

/-! # Singular Constant Cohomology Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularConstantCohomologyNaturality

noncomputable section

/-! # The original singular/constant comparison respects genuine inverse image -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular

variable (R : Type) [Field R]

/-- The unchanged original comparison, expressed in its original constant hypercohomology. -/
theorem canonicalSingularToConstantSheafLinearEquiv_hypercohomology
    (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]
    (n : ℕ) (α : AlgebraicTopology.Singular.CohomologyTo.Cohomology R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n) :
    (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology R X n).symm
        (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv R X n α) =
      (Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv R X n).symm
        (CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv R X n
          (CanonicalSheafComparison.rawGlobalToSheafGlobalAddEquiv R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n
            ((Coefficient.SheafComparison.rawSingularHomologyIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n).inv α))) := by
  change (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology R X n).symm
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology R X n) _) = _
  exact (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology R X n).symm_apply_apply _

variable {X Y : Over (Spec (.of ℂ))}
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [Foundations.ProjectiveSpaceIs.IsProjective Y.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual singular pullback becomes actual original constant inverse image under comparison. -/
theorem originalSingularToConstantHypercohomology_naturality (f : X ⟶ Y) (n : ℕ)
    (α : AlgebraicTopology.Singular.CohomologyTo.Cohomology R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) n) :
    SingularConstantNaturality.originalCoefficientConstantHypercohomologyPullback R f (n : ℤ)
        ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology R Y n).symm
          (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv R Y n α)) =
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology R X n).symm
        (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv R X n
          (AlgebraicTopology.Singular.CohomologyTo.cohomologyMap R n (DeRhamPresheafPullback.originalAnalyticSchemeMap f) α)) := by
  let rX := (Coefficient.SheafComparison.rawSingularHomologyIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n).addCommGroupIsoToAddEquiv
  let rY := (Coefficient.SheafComparison.rawSingularHomologyIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) n).addCommGroupIsoToAddEquiv
  let tX := CanonicalSheafComparison.rawGlobalToSheafGlobalAddEquiv R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n
  let tY := CanonicalSheafComparison.rawGlobalToSheafGlobalAddEquiv R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) n
  let gX := CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv R X n
  let gY := CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv R Y n
  let sX := Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv R X n
  let sY := Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv R Y n
  have hr : rX.symm (AlgebraicTopology.Singular.CohomologyTo.cohomologyMap R n (DeRhamPresheafPullback.originalAnalyticSchemeMap f) α) =
      HomologicalComplex.homologyMap (SingularGlobalNaturality.originalRawSingularGlobalPullback R f) n (rY.symm α) := by
    apply rX.injective
    rw [rX.apply_symm_apply]
    have h := ConcreteCategory.congr_hom
      (SingularNaturality.originalRawSingularGlobalPullback_homologyIso R f n) (rY.symm α)
    exact (h.trans (congrArg (AlgebraicTopology.Singular.CohomologyTo.cohomologyMap R n (DeRhamPresheafPullback.originalAnalyticSchemeMap f))
      (rY.apply_symm_apply α))).symm
  have ht : tX (HomologicalComplex.homologyMap
      (SingularGlobalNaturality.originalRawSingularGlobalPullback R f) n (rY.symm α)) =
      HomologicalComplex.homologyMap (SingularGlobalNaturality.originalSingularGlobalPullback R f) n (tY (rY.symm α)) := by
    have h := congrArg (fun p ↦ HomologicalComplex.homologyMap p n)
      (SingularGlobalNaturality.originalRawSingularGlobalPullback_sheafification R f)
    simp only [HomologicalComplex.homologyMap_comp] at h
    exact (ConcreteCategory.congr_hom h (rY.symm α)).symm
  have hg : gX (tX (rX.symm (AlgebraicTopology.Singular.CohomologyTo.cohomologyMap R n (DeRhamPresheafPullback.originalAnalyticSchemeMap f) α))) =
      SingularConstantNaturality.originalSingularHypercohomologyPullback R f (n : ℤ) (gY (tY (rY.symm α))) :=
    (congrArg (fun z ↦ gX (tX z)) hr).trans
      ((congrArg gX ht).trans (SingularHypercohomologyNaturality.originalSingularGlobalToHypercohomology_naturality R f n _))
  rw [canonicalSingularToConstantSheafLinearEquiv_hypercohomology,
    canonicalSingularToConstantSheafLinearEquiv_hypercohomology]
  apply sX.injective
  change sX (SingularConstantNaturality.originalCoefficientConstantHypercohomologyPullback R f (n : ℤ)
      (sY.symm (gY (tY (rY.symm α))))) =
    sX (sX.symm (gX (tX (rX.symm (AlgebraicTopology.Singular.CohomologyTo.cohomologyMap R n (DeRhamPresheafPullback.originalAnalyticSchemeMap f) α)))))
  rw [sX.apply_symm_apply]
  have hs : sX (SingularConstantNaturality.originalCoefficientConstantHypercohomologyPullback R f (n : ℤ)
      (sY.symm (gY (tY (rY.symm α))))) =
      SingularConstantNaturality.originalSingularHypercohomologyPullback R f (n : ℤ) (gY (tY (rY.symm α))) :=
    (SingularConstantNaturality.originalSingularHypercohomologyPullback_constantComparison R f (n : ℤ)
      (sY.symm (gY (tY (rY.symm α))))).symm.trans
        (congrArg (SingularConstantNaturality.originalSingularHypercohomologyPullback R f (n : ℤ))
          (sY.apply_symm_apply (gY (tY (rY.symm α)))))
  exact hs.trans hg.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SingularConstantCohomologyNaturality
