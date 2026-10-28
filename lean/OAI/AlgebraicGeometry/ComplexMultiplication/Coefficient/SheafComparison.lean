import OAI.AlgebraicGeometry.ComplexMultiplication.GlobalSections
import OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Singular
import OAI.AlgebraicTopology.Singular.CohomologyTo
import OAI.AlgebraicTopology.Singular.SheafCochainResolution
import OAI.AlgebraicTopology.Sheaf.FlasqueExtendNat
import OAI.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact
import OAI.Algebra.Homology.Notation

/-! # Sheaf Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.SheafComparison

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # Constant-sheaf and ordinary singular cohomology with field coefficients -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoint _root_.TopologicalSpace

variable (R : Type) [Field R] (X : Over (Spec ↧ℂ))

/-- The global-section complex commutes with extending singular cochains to integer degrees. -/
def singularGlobalIntegerHomologyIso (n : ℕ) :
    (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt ↧(ComplexPoint.Basic.ComplexSchemePoint X)
      (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R)).homology (n : ℤ) ≅
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R
      ↧(ComplexPoint.Basic.ComplexSchemePoint X)).homology n :=
  HomologicalComplex.homologyMapIso
    (OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso
      (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor ↧(ComplexPoint.Basic.ComplexSchemePoint X))
      (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R ↧(ComplexPoint.Basic.ComplexSchemePoint X))
      ComplexShape.embeddingUpNat) (n : ℤ) ≪≫
  (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R
    ↧(ComplexPoint.Basic.ComplexSchemePoint X)).extendHomologyIso ComplexShape.embeddingUpNat rfl

/-- Evaluation of raw singular cochains on the top open computes ordinary singular cohomology. -/
def rawSingularHomologyIso (Y : TopCat.{0}) (n : ℕ) :
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R Y).homology n ≅
      (forget₂ (ModuleCat R) AddCommGrpCat).obj
        (AlgebraicTopology.Singular.CohomologyTo.Cohomology R Y n) :=
  HomologicalComplex.homologyMapIso
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso R Y ≪≫
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
        (AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen R Y).symm) n ≪≫
  ((AlgebraicTopology.Singular.CohomologyTo.SingularCochainComplex R Y).sc n).mapHomologyIso
    (forget₂ (ModuleCat R) AddCommGrpCat)

variable [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- Every term of the singular-cochain resolution on the given projective variety is flasque. -/
theorem singularCochainComplexInt_isFlasque (i : ℤ) :
    ((ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R).X i).IsFlasque := by
  let : ∀ U : Opens (ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace U := ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  apply AlgebraicTopology.Sheaf.FlasqueExtendNat.TopCat.extendNat_term_isFlasque
  intro m
  change (AlgebraicTopology.Singular.SheafCochain.singularCochainSheaf R ↧(ComplexPoint.Basic.ComplexSchemePoint X) m).IsFlasque
  infer_instance

/-- Hypercohomology of the actual singular-cochain resolution is computed by its global sections. -/
def singularHypercohomologyGlobalAddEquiv (n : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R) (n : ℤ) ≃+
      (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R
        ↧(ComplexPoint.Basic.ComplexSchemePoint X)).homology n := by
  let F : ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X :=
    (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor ↧(ComplexPoint.Basic.ComplexSchemePoint X)).obj (AddCommGrpCat.of R)
  let e : ComplexPoint.Basic.ComplexSchemePoint.constantCoefficientSheafComplexInt X R ≅
      (CochainComplex.singleFunctor (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).obj F :=
    HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl
  let ι : (CochainComplex.singleFunctor (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) 0).obj F ⟶
      ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R :=
    e.inv ≫ ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R
  letI : Mono (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R) :=
    AlgebraicTopology.Singular.SheafCochainResolution.constantsToSingularCochainComplexInt_mono R ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  letI : QuasiIso (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R) :=
    ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt_quasiIso X R
  letI : IsIso e.inv := inferInstance
  letI : Mono e.inv := inferInstance
  letI : QuasiIso e.inv := inferInstance
  letI : Mono ι := by dsimp only [ι]; infer_instance
  letI : QuasiIso ι := by dsimp only [ι]; infer_instance
  exact (GlobalSections.flasqueResolutionHypercohomologyGlobalAddEquiv X F _ ι
    (singularCochainComplexInt_isFlasque R X) n).trans
      (singularGlobalIntegerHomologyIso R X n).addCommGroupIsoToAddEquiv

/-- The actual constant-to-singular resolution gives an additive cohomology comparison. -/
def constantHypercohomologySingularAddEquiv (n : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt R X) (n : ℤ) ≃+
      ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R) (n : ℤ) where
  toEquiv := Localization.SmallShiftedHom.postcompEquiv
    (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R)
    (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt_quasiIso X R)
  map_add' := (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R) n).map_add

/-- Constant-sheaf cohomology of the original analytic space agrees additively with ordinary
singular cohomology, for rational or complex coefficients. -/
def constantSheafSingularAddEquiv [Algebra R ℂ] (n : ℕ) :
    H^n(X; R) ≃+ AlgebraicTopology.Singular.CohomologyTo.Cohomology R ↧(ComplexPoint.Basic.ComplexSchemePoint X) n := by
  let Y : TopCat.{0} := ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  letI : ParacompactSpace Y := inferInstance
  letI : QuasiIso (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R Y) :=
    Singular.SingularCoefficients.topOpenToGlobalSingularCochainSheafComplex_quasiIso R
  let e := asIso (HomologicalComplex.homologyMap
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R Y) n)
  exact (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology R X n).symm.trans <|
    (constantHypercohomologySingularAddEquiv R X n).trans <|
    (singularHypercohomologyGlobalAddEquiv R X n).trans <|
    e.symm.addCommGroupIsoToAddEquiv.trans <|
    (rawSingularHomologyIso R Y n).addCommGroupIsoToAddEquiv

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.SheafComparison
