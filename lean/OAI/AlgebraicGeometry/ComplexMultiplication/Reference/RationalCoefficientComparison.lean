import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalCoefficientHypercohomology
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.BettiBridge

/-! # Rational Coefficient Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalCoefficientComparison

noncomputable section

/-! # The original constant-sheaf comparison retains actual rational-to-complex coefficients -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

set_option backward.isDefEq.respectTransparency false in
/-- The original raw-to-sheaf equivalence commutes with actual coefficient inclusion. -/
theorem rawGlobalToSheafGlobalAddEquiv_rational_coefficient (Y : TopCat.{0})
    [ParacompactSpace Y] [T2Space Y] (n : ℕ)
    (z : (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex ℚ Y).homology n) :
    CanonicalSheafComparison.rawGlobalToSheafGlobalAddEquiv ℂ Y n
        (HomologicalComplex.homologyMap (RationalCoefficientGlobalUnits.originalRationalToComplexRawGlobalMap Y) n z) =
      HomologicalComplex.homologyMap
        (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (RationalCoefficient.originalRationalToComplexSingularSheafMap Y)) n
        (CanonicalSheafComparison.rawGlobalToSheafGlobalAddEquiv ℚ Y n z) := by
  change HomologicalComplex.homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℂ Y) n
      (HomologicalComplex.homologyMap (RationalCoefficientGlobalUnits.originalRationalToComplexRawGlobalMap Y) n z) =
    HomologicalComplex.homologyMap
      (((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (RationalCoefficient.originalRationalToComplexSingularSheafMap Y)) n
      (HomologicalComplex.homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex ℚ Y) n z)
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (RationalCoefficientGlobalUnits.originalRationalToComplexRawGlobalMap_unit Y)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h z

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation exposes the actual original raw, global and hypercohomology comparisons. -/
theorem canonicalSingularToConstantSheafLinearEquiv_apply (R : Type) [Field R] (n : ℕ)
    (z : AlgebraicTopology.Singular.CohomologyTo.Cohomology R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n) :
    CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv R X n z =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology R X n
        ((Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv R X n).symm
          (CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv R X n
            (CanonicalSheafComparison.rawGlobalToSheafGlobalAddEquiv R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n
              ((Coefficient.SheafComparison.rawSingularHomologyIso R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n).inv z)))) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the original scheme comparison on an actual Betti class. -/
theorem schemeConstantCohomologyBridgeEquiv_apply (R : Type) [Field R] (n : ℕ)
    (z : Betti.Scheme.schemeBetti (ModuleCat.of R R) X n) :
    BettiBridge.schemeConstantCohomologyBridgeEquiv R X n z =
      CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv R X n
        (SingularCochainBridge.singularCohomologyBridgeEquiv R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n
          (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R)
            (PointBettiBridge.complexPointSpaceIso X).inv n z)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Exact coefficient naturality of the original singular-to-constant-sheaf comparison. -/
theorem canonicalSingularToConstantSheafLinearEquiv_rational_coefficient (n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology
      (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n) :
    CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv ℂ X n
        (SingularCochainBridge.singularCohomologyBridgeEquiv ℂ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n
          (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n z)) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n
        (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X) n
          ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm
            (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv ℚ X n
              (SingularCochainBridge.singularCohomologyBridgeEquiv ℚ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n z)))) := by
  let Y : TopCat.{0} := TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)
  let rQ := (Coefficient.SheafComparison.rawSingularHomologyIso ℚ Y n).symm.addCommGroupIsoToAddEquiv
  let rC := (Coefficient.SheafComparison.rawSingularHomologyIso ℂ Y n).symm.addCommGroupIsoToAddEquiv
  let tQ := CanonicalSheafComparison.rawGlobalToSheafGlobalAddEquiv ℚ Y n
  let tC := CanonicalSheafComparison.rawGlobalToSheafGlobalAddEquiv ℂ Y n
  let gQ := CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv ℚ X n
  let gC := CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv ℂ X n
  let sQ := Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv ℚ X n
  let sC := Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv ℂ X n
  let cQ := ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n
  let cC := ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n
  let f := RationalCoefficient.originalRationalToComplexSingularSheafMap Y
  let fΓ := ((AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
    (ComplexShape.up ℕ)).map f
  have hr : rC (SingularCochainBridge.singularCohomologyBridgeEquiv ℂ Y n
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology Y n z)) =
    HomologicalComplex.homologyMap (RationalCoefficientGlobalUnits.originalRationalToComplexRawGlobalMap Y) n
      (rQ (SingularCochainBridge.singularCohomologyBridgeEquiv ℚ Y n z)) :=
    (RationalCoefficientGlobalUnits.originalRationalToComplexRawGlobalMap_homology Y n z).symm
  have ht (a : (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex ℚ Y).homology n) :
      tC (HomologicalComplex.homologyMap (RationalCoefficientGlobalUnits.originalRationalToComplexRawGlobalMap Y) n a) =
    HomologicalComplex.homologyMap fΓ n (tQ a) :=
    rawGlobalToSheafGlobalAddEquiv_rational_coefficient Y n a
  have hg (a : (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex ℚ Y).homology n) :
      gC (HomologicalComplex.homologyMap fΓ n a) =
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (RationalCoefficient.originalRationalToComplexSingularSheafIntMap X) n (gQ a) :=
    RationalCoefficientHypercohomology.singularGlobalToHypercohomologyAddEquiv_coefficient_naturality ℚ ℂ X f n a
  have hs (a : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℚ) n) :
      sC.symm (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (RationalCoefficient.originalRationalToComplexSingularSheafIntMap X) n a) =
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X) n (sQ.symm a) := by
    apply sC.injective
    exact (sC.apply_symm_apply _).trans
      ((RationalCoefficientHypercohomology.constantHypercohomologySingularAddEquiv_rational_coefficient X n (sQ.symm a)).trans
        (congrArg
          (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (RationalCoefficient.originalRationalToComplexSingularSheafIntMap X) n)
          (sQ.apply_symm_apply a))).symm
  rw [canonicalSingularToConstantSheafLinearEquiv_apply,
    canonicalSingularToConstantSheafLinearEquiv_apply]
  change cC (sC.symm (gC (tC (rC (SingularCochainBridge.singularCohomologyBridgeEquiv ℂ Y n
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology Y n z)))))) =
    cC (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X) n
      (cQ.symm (cQ (sQ.symm (gQ (tQ (rQ (SingularCochainBridge.singularCohomologyBridgeEquiv ℚ Y n z))))))))
  rw [hr, ht, hg, hs, AddEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The original scheme Betti bridge retains the actual ordinary rational-to-complex inclusion. -/
theorem schemeConstantCohomologyBridgeEquiv_rational_coefficient (n : ℕ)
    (z : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X n) :
    BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X n
        (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace X) n z) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n
        (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X) n
          ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm
            (BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X n z))) := by
  have h := AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology_naturality
    (PointBettiBridge.complexPointSpaceIso X).inv n
  have hz := ConcreteCategory.congr_hom h z
  change AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (PointBettiBridge.complexPointSpaceIso X).inv n z) =
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ)
      (PointBettiBridge.complexPointSpaceIso X).inv n
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace X) n z) at hz
  rw [schemeConstantCohomologyBridgeEquiv_apply, schemeConstantCohomologyBridgeEquiv_apply]
  exact (congrArg
    (fun a => CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv ℂ X n
      (SingularCochainBridge.singularCohomologyBridgeEquiv ℂ (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n a)) hz.symm).trans
    (canonicalSingularToConstantSheafLinearEquiv_rational_coefficient X n _)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalCoefficientComparison
