import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousInvariantRepresentative
import OAI.RepresentationTheory.Theta.Geometric.HermitianAntiholomorphicCovectors

/-! # Homogeneous Covector -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousCovector

noncomputable section

section

/-! The invariant form representing a homogeneous native line bundle
has an actual Hermitian translation coordinate. -/

open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

def nativeType01ChartCovector (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : RepresentationTheory.Theta.Geometric.ClosedPureDolbeaultMap.ClosedType01Forms A.variety.analyticModel A.variety.analyticSpace) :
    Analysis.DifferentialForms.Manifold.Basic.FormValue A.variety.analyticModel 1 :=
  AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv 1 (RepresentationTheory.Theta.Geometric.AbelianAntiholomorphicInvariant.abelianType01InvariantRepresentative A a)

theorem nativeType01ChartCovector_pure (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : RepresentationTheory.Theta.Geometric.ClosedPureDolbeaultMap.ClosedType01Forms A.variety.analyticModel A.variety.analyticSpace) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree A.variety.analyticModel 0 1 (nativeType01ChartCovector A a) := by
  have h : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree A.variety.analyticModel A.variety.analyticSpace 0 1
      (RepresentationTheory.Theta.Geometric.AbelianAntiholomorphicInvariant.abelianType01InvariantRepresentative A a).val.val := by
    rw [RepresentationTheory.Theta.Geometric.AbelianAntiholomorphicInvariant.abelianType01InvariantRepresentative_eq A a]
    exact a.val.property
  exact (congrArg (Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree A.variety.analyticModel 0 1)
    (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv_apply 1 (RepresentationTheory.Theta.Geometric.AbelianAntiholomorphicInvariant.abelianType01InvariantRepresentative A a))).mpr
      ((AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantForm_pure_iff (p := 0) (q := 1) (RepresentationTheory.Theta.Geometric.AbelianAntiholomorphicInvariant.abelianType01InvariantRepresentative A a)).mp h)

theorem homogeneousLineBundle_hermitian_representative (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : A.variety.analyticModel →ₗ⋆[ℂ] A.variety.analyticModel →ₗ[ℂ] ℂ)
    (hsym : ∀ a b, H b a = star (H a b)) (hpos : ∀ a, a ≠ 0 → 0 < (H a a).re)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A) (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    ∃ (a : RepresentationTheory.Theta.Geometric.ClosedPureDolbeaultMap.ClosedType01Forms A.variety.analyticModel A.variety.analyticSpace)
      (z : A.variety.analyticModel),
      RepresentationTheory.Theta.Geometric.ClosedFormPicardZero.closedFormPicardMap A.variety a = HolomorphicLineClass.nativeHolomorphicLineClass A.variety L ∧
        ∀ v : Fin 1 → A.variety.analyticModel,
          nativeType01ChartCovector A a v = (Real.pi : ℂ) * H (v 0) z := by
  obtain ⟨a, ha⟩ := HomogeneousInvariantRepresentative.homogeneousLineBundle_closedForm_representative A L hL
  obtain ⟨z, hz⟩ := RepresentationTheory.Theta.Geometric.HermitianAntiholomorphicCovectors.exists_hermitian_antiholomorphic_covector H hsym hpos
    (nativeType01ChartCovector A a) (nativeType01ChartCovector_pure A a)
  exact ⟨a, z, ha, hz⟩

end

section

/-! Actual closed antiholomorphic forms inject complex linearly into
the native tangent space's antiholomorphic dual. -/

open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

def nativeType01ChartCovectorLinear (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    RepresentationTheory.Theta.Geometric.ClosedPureDolbeaultMap.ClosedType01Forms A.variety.analyticModel A.variety.analyticSpace →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Basic.FormValue A.variety.analyticModel 1 :=
  (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (E := A.variety.analyticModel) (G := A.variety.analyticSpace) 1).toLinearMap.comp
    ((AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianInvariantDeRhamEquiv A 1).symm.toLinearMap.comp
      (RepresentationTheory.Theta.Geometric.ClosedAntiholomorphicDeRham.closedType01DeRhamClass A.variety.analyticModel A.variety.analyticSpace))

theorem nativeType01ChartCovectorLinear_apply (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : RepresentationTheory.Theta.Geometric.ClosedPureDolbeaultMap.ClosedType01Forms A.variety.analyticModel A.variety.analyticSpace) :
    nativeType01ChartCovectorLinear A a = nativeType01ChartCovector A a := rfl

theorem nativeType01ChartCovectorLinear_injective (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Function.Injective (nativeType01ChartCovectorLinear A) :=
  (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (E := A.variety.analyticModel) (G := A.variety.analyticSpace) 1).injective.comp
    ((AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianInvariantDeRhamEquiv A 1).symm.injective.comp
      (RepresentationTheory.Theta.Geometric.ClosedAntiholomorphicDeRham.closedType01DeRhamClass_injective A.variety.analyticModel A.variety.analyticSpace))

def nativeType01AntilinearCovector (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    RepresentationTheory.Theta.Geometric.ClosedPureDolbeaultMap.ClosedType01Forms A.variety.analyticModel A.variety.analyticSpace →ₗ[ℂ]
      (A.variety.analyticModel →ₗ⋆[ℂ] ℂ) where
  toFun a := RepresentationTheory.Theta.Geometric.HermitianAntiholomorphicCovectors.antiholomorphicOneCovector (nativeType01ChartCovector A a)
    (nativeType01ChartCovector_pure A a)
  map_add' a b := by
    ext v
    exact congrArg (fun t : Analysis.DifferentialForms.Manifold.Basic.FormValue A.variety.analyticModel 1 => t (fun _ => v))
      (map_add (nativeType01ChartCovectorLinear A) a b)
  map_smul' c a := by
    ext v
    exact congrArg (fun t : Analysis.DifferentialForms.Manifold.Basic.FormValue A.variety.analyticModel 1 => t (fun _ => v))
      (map_smul (nativeType01ChartCovectorLinear A) c a)

theorem nativeType01AntilinearCovector_reconstruct (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : RepresentationTheory.Theta.Geometric.ClosedPureDolbeaultMap.ClosedType01Forms A.variety.analyticModel A.variety.analyticSpace)
    (v : Fin 1 → A.variety.analyticModel) :
    nativeType01AntilinearCovector A a (v 0) = nativeType01ChartCovector A a v :=
  RepresentationTheory.Theta.Geometric.HermitianAntiholomorphicCovectors.antiholomorphicOneCovector_reconstruct (nativeType01ChartCovector A a)
    (nativeType01ChartCovector_pure A a) v

theorem nativeType01AntilinearCovector_injective (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Function.Injective (nativeType01AntilinearCovector A) := by
  intro a b h
  apply nativeType01ChartCovectorLinear_injective A
  ext v
  exact (nativeType01AntilinearCovector_reconstruct A a v).symm.trans
    ((congrArg (fun t : A.variety.analyticModel →ₗ⋆[ℂ] ℂ => t (v 0)) h).trans
      (nativeType01AntilinearCovector_reconstruct A b v))

end

/-! The native Dolbeault vector space injects into the actual tangent
space, using closed antiholomorphic representatives and a positive
Hermitian pairing. -/

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
  (H : A.variety.analyticModel →ₗ⋆[ℂ] A.variety.analyticModel →ₗ[ℂ] ℂ)
  (hsym : ∀ a b, H b a = star (H a b)) (hpos : ∀ a, a ≠ 0 → 0 < (H a a).re)

def nativeDolbeaultHermitianCoordinate :
    RepresentationTheory.Theta.Geometric.DolbeaultQuotient.DolbeaultOneSpace A.variety.analyticModel A.variety.analyticSpace →ₗ[ℂ] A.variety.analyticModel :=
  (RepresentationTheory.Theta.Geometric.HermitianAntiDual.hermitianAntiDualEquiv H hsym hpos).symm.toLinearMap.comp
    ((nativeType01AntilinearCovector A).comp (RepresentationTheory.Theta.Geometric.Projective.DolbeaultEquiv.projectiveDolbeaultEquiv A.variety).symm.toLinearMap)

theorem nativeDolbeaultHermitianCoordinate_injective :
    Function.Injective (nativeDolbeaultHermitianCoordinate A H hsym hpos) :=
  (RepresentationTheory.Theta.Geometric.HermitianAntiDual.hermitianAntiDualEquiv H hsym hpos).symm.injective.comp
    ((nativeType01AntilinearCovector_injective A).comp (RepresentationTheory.Theta.Geometric.Projective.DolbeaultEquiv.projectiveDolbeaultEquiv A.variety).symm.injective)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousCovector
