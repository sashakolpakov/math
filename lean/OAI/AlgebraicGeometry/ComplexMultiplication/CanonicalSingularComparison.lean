import OAI.AlgebraicGeometry.ComplexMultiplication.GlobalNaturalityCompute
import OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.SheafComparison
import OAI.Algebra.Homology.Notation

/-! # Canonical Singular Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSingularComparison

noncomputable section

/-! # Canonical comparison through the original singular-cochain resolution -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

variable (R : Type) [Field R] (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- Global cohomology of the actual integer-indexed singular-cochain resolution maps
canonically and bijectively to its hypercohomology. -/
theorem singularGlobalToHypercohomology_bijective (n : ℤ) :
    Function.Bijective (GlobalNaturality.globalSectionsToHypercohomology X
      (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R) n) := by
  let F : ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X :=
    (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(ComplexPoint.Basic.ComplexSchemePoint X)).obj (AddCommGrpCat.of R)
  let e : ComplexPoint.Basic.ComplexSchemePoint.constantCoefficientSheafComplexInt X R ≅
      (CochainComplex.singleFunctor (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).obj F :=
    HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl
  let ι : (CochainComplex.singleFunctor (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).obj F ⟶
      ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R :=
    e.inv ≫ ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R
  let : Mono (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R) :=
    AlgebraicTopology.Singular.SheafCochainResolution.constantsToSingularCochainComplexInt_mono R ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  let : QuasiIso (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R) :=
    ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt_quasiIso X R
  let : IsIso e.inv := inferInstance
  let : Mono e.inv := inferInstance
  let : QuasiIso e.inv := inferInstance
  let : Mono ι := by dsimp only [ι]; infer_instance
  let : QuasiIso ι := by dsimp only [ι]; infer_instance
  exact GlobalNaturalityCompute.globalSectionsToHypercohomology_flasque_bijective X F _ ι
    (Coefficient.SheafComparison.singularCochainComplexInt_isFlasque R X) n

/-- The canonical additive equivalence, with no choice of a scalar action on a resolution. -/
def singularIntegerGlobalToHypercohomologyAddEquiv (n : ℤ) :
    (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt ↧(ComplexPoint.Basic.ComplexSchemePoint X)
      (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R)).homology n ≃+
        ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R) n :=
  AddEquiv.ofBijective (GlobalNaturality.globalSectionsToHypercohomology X
    (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R) n) (singularGlobalToHypercohomology_bijective R X n)

/-- The original natural-number global singular resolution computes the same hypercohomology. -/
def singularGlobalToHypercohomologyAddEquiv (n : ℕ) :
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R ↧(ComplexPoint.Basic.ComplexSchemePoint X)).homology n ≃+
      ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R) (n : ℤ) :=
  (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso R X n).symm.addCommGroupIsoToAddEquiv.trans <|
    singularIntegerGlobalToHypercohomologyAddEquiv R X n

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSingularComparison
