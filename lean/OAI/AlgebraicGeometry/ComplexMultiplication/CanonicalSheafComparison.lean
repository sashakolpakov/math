import OAI.AlgebraicGeometry.ComplexMultiplication.SingularDualMap
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSingularNaturality
import OAI.Algebra.Homology.Notation

/-! # Canonical Sheaf Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSheafComparison

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # The canonical linear singular-to-constant-sheaf comparison -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular

variable (R : Type) [Field R] (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

omit [Foundations.ProjectiveSpaceIs.IsProjective X.hom] in
/-- The original constant resolution comparison respects its actual coefficient scalar maps. -/
lemma constantHypercohomologySingularAddEquiv_scalar (n : ℕ) (q : R)
    (z : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt R X) n) :
    Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv R X n
        (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex R X q) n z) =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (Coefficient.Scalars.singularCochainSheafComplexIntScalar R q X) n
        (Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv R X n z) := by
  change ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R) n
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex R X q) n z) =
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (Coefficient.Scalars.singularCochainSheafComplexIntScalar R q X) n
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R) n z)
  exact (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply X (ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex R X q)
      (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R) n z).symm.trans <|
    (congrArg (fun f => ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X f n z)
      (Coefficient.ScalarCompatibility.fieldScalarComplex_constantsToSingularInt R X q)).trans <|
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply X (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R)
      (Coefficient.Scalars.singularCochainSheafComplexIntScalar R q X) n z

/-- The raw-to-sheafified global comparison induces an actual additive equivalence. -/
def rawGlobalToSheafGlobalAddEquiv (Y : TopCat.{0}) [ParacompactSpace Y] [T2Space Y] (n : ℕ) :
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R Y).homology n ≃+
      (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R Y).homology n := by
  let : QuasiIso (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R Y) :=
    Coefficient.Singular.SingularCoefficients.topOpenToGlobalSingularCochainSheafComplex_quasiIso R
  exact (asIso (HomologicalComplex.homologyMap
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R Y) n)).addCommGroupIsoToAddEquiv

/-- The original raw and sheafified scalar chain maps give commuting maps on global cohomology. -/
lemma rawGlobalToSheafGlobalAddEquiv_scalar (Y : TopCat.{0})
    [ParacompactSpace Y] [T2Space Y] (n : ℕ) (q : R)
    (z : (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R Y).homology n) :
    rawGlobalToSheafGlobalAddEquiv R Y n
        (HomologicalComplex.homologyMap (SingularScalars.rawGlobalSingularScalar R Y q) n z) =
      HomologicalComplex.homologyMap (SingularScalars.sheafGlobalSingularScalar R Y q) n
        (rawGlobalToSheafGlobalAddEquiv R Y n z) := by
  have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
    (SingularScalars.rawGlobalSingularScalar_comparison R Y q)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact congrArg (fun f => f z) h

/-- The canonical comparison uses the original raw cochain map and constant-sheaf resolution. -/
def canonicalSingularToConstantSheafAddEquiv (n : ℕ) :
    AlgebraicTopology.Singular.CohomologyTo.Cohomology R ↧(ComplexPoint.Basic.ComplexSchemePoint X) n ≃+ H^n(X; R) :=
  (Coefficient.SheafComparison.rawSingularHomologyIso R ↧(ComplexPoint.Basic.ComplexSchemePoint X) n).symm.addCommGroupIsoToAddEquiv.trans <|
    (rawGlobalToSheafGlobalAddEquiv R ↧(ComplexPoint.Basic.ComplexSchemePoint X) n).trans <|
    (CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv R X n).trans <|
    (Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv R X n).symm.trans <|
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology R X n

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison preserves the original coefficient scalar actions. -/
lemma canonicalSingularToConstantSheafAddEquiv_smul (n : ℕ) (q : R)
    (z : AlgebraicTopology.Singular.CohomologyTo.Cohomology R ↧(ComplexPoint.Basic.ComplexSchemePoint X) n) :
    canonicalSingularToConstantSheafAddEquiv R X n (q • z) =
      q • canonicalSingularToConstantSheafAddEquiv R X n z := by
  let Y : TopCat.{0} := ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  let r := (Coefficient.SheafComparison.rawSingularHomologyIso R Y n).addCommGroupIsoToAddEquiv
  let t := rawGlobalToSheafGlobalAddEquiv R Y n
  let g := CanonicalSingularComparison.singularGlobalToHypercohomologyAddEquiv R X n
  let s := Coefficient.SheafComparison.constantHypercohomologySingularAddEquiv R X n
  let c := ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology R X n
  have hr : r.symm (q • z) =
      HomologicalComplex.homologyMap (SingularScalars.rawGlobalSingularScalar R Y q) n (r.symm z) := by
    apply r.injective
    rw [AddEquiv.apply_symm_apply]
    exact (congrArg (fun x : AlgebraicTopology.Singular.CohomologyTo.Cohomology R Y n => q • x) (r.apply_symm_apply z)).symm.trans
      (SingularDualMap.rawSingularHomologyIso_scalar R Y q n (r.symm z)).symm
  have hg (a : (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R Y).homology n) :
      g (HomologicalComplex.homologyMap (SingularScalars.sheafGlobalSingularScalar R Y q) n a) =
        ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (Coefficient.Scalars.singularCochainSheafComplexIntScalar R q X) n (g a) :=
    CanonicalSingularNaturality.singularGlobalToHypercohomologyAddEquiv_naturality R X
      (Coefficient.Scalars.singularCochainSheafComplexScalar R Y q) n a
  have hs (a : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R) n) :
      s.symm (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (Coefficient.Scalars.singularCochainSheafComplexIntScalar R q X) n a) =
        ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex R X q) n (s.symm a) := by
    apply s.injective
    rw [AddEquiv.apply_symm_apply, constantHypercohomologySingularAddEquiv_scalar,
      AddEquiv.apply_symm_apply]
  have hc (a : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt R X) n) :
      c (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldScalarComplex R X q) n a) = q • c a := by
    apply c.symm.injective
    rw [AddEquiv.symm_apply_apply, ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology_symm_smul,
      AddEquiv.symm_apply_apply]
  change c (s.symm (g (t (r.symm (q • z))))) = q • c (s.symm (g (t (r.symm z))))
  rw [hr, rawGlobalToSheafGlobalAddEquiv_scalar,
    hg, hs, hc]

/-- The canonical comparison is linear for the actual coefficient field. -/
def canonicalSingularToConstantSheafLinearEquiv (n : ℕ) :
    AlgebraicTopology.Singular.CohomologyTo.Cohomology R ↧(ComplexPoint.Basic.ComplexSchemePoint X) n ≃ₗ[R] H^n(X; R) :=
  { canonicalSingularToConstantSheafAddEquiv R X n with
    map_smul' := canonicalSingularToConstantSheafAddEquiv_smul R X n }

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSheafComparison
