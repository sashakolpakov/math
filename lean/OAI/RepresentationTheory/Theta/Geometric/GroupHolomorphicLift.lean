import OAI.RepresentationTheory.Theta.Geometric.InvariantFormsRealization
import OAI.RepresentationTheory.Theta.Geometric.Affine.IdentityDimension

/-! # Group Holomorphic Lift -/

namespace OAI.RepresentationTheory.Theta.Geometric.GroupHolomorphicLift

noncomputable section

section

/-! Every actual invariant holomorphic one-form on a smooth integral
separated complex group scheme is the smooth realization of an algebraic
one-form. The inverse is obtained from the constructed cotangent map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

attribute [local instance] InvariantFormsSmooth.nativeGroupRealLie InvariantFormsSmooth.nativeGroupComplexLie

variable {G U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] [G.left.IsSeparated] [IsAffine U.left]
    (i : U ⟶ G) [IsOpenImmersion i.left]
    (e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U) (he : e ≫ i = 1)
    [Algebra Γ(U.left, ⊤) ℂ] [IsScalarTower ℂ Γ(U.left, ⊤) ℂ]
    (hscalar : ∀ a : Γ(U.left, ⊤), algebraMap Γ(U.left, ⊤) ℂ a = AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e a)

theorem identityCotangentInvariantLinear_surjective :
    Function.Surjective (InvariantFormsRealization.identityCotangentInvariantLinear i e he hscalar) := by
  let : Smooth U.hom := by rw [← i.w]; infer_instance
  let : FiniteDimensional ℂ (InvariantAlgebraicForms.identityChartCotangent U) := Affine.IdentityDimension.identityChartCotangent_finiteDimensional U
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (InvariantFormsRealization.identityCotangentInvariantLinear_injective i e he hscalar)
  exact (Affine.IdentityDimension.identityChartCotangent_finrank i e hscalar).trans
    (InvariantHolomorphicDimension.invariantHolomorphic_finrank (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel G) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G)).symm

def identityCotangentInvariantEquiv : InvariantAlgebraicForms.identityChartCotangent U ≃ₗ[ℂ]
    InvariantHolomorphicDimension.invariantHolomorphicSubmodule (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel G) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) :=
  LinearEquiv.ofBijective (InvariantFormsRealization.identityCotangentInvariantLinear i e he hscalar)
    ⟨InvariantFormsRealization.identityCotangentInvariantLinear_injective i e he hscalar,
      identityCotangentInvariantLinear_surjective i e he hscalar⟩

def invariantHolomorphicAlgebraicLift :
    InvariantHolomorphicDimension.invariantHolomorphicSubmodule (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel G) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) →ₗ[ℂ] AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms G :=
  (InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar).comp
    (identityCotangentInvariantEquiv i e he hscalar).symm.toLinearMap

theorem invariantHolomorphicAlgebraicLift_realization
    (form : InvariantHolomorphicDimension.invariantHolomorphicSubmodule (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel G) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G)) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm G (invariantHolomorphicAlgebraicLift i e he hscalar form) =
      form.val.val :=
  congrArg (fun z : InvariantHolomorphicDimension.invariantHolomorphicSubmodule
    (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel G) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) => z.val.val)
    ((identityCotangentInvariantEquiv i e he hscalar).apply_symm_apply form)

end

/-! The original smooth complex group supplies an affine identity chart,
so invariant holomorphic forms have a constructed algebraic lift without
any additional chart or algebraization hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

attribute [local instance] InvariantFormsSmooth.nativeGroupRealLie InvariantFormsSmooth.nativeGroupComplexLie

variable (G : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G] [IsIntegral G.left] [Smooth G.hom] [G.left.IsSeparated]

theorem exists_groupHolomorphicAlgebraicLift :
    ∃ L : InvariantHolomorphicDimension.invariantHolomorphicSubmodule (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel G) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) →ₗ[ℂ] AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms G,
      ∀ form, AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm G (L form) = form.val.val := by
  obtain ⟨U, hU, p, hp⟩ := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift G (1 : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G)
  let A := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra G U
  let W := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A
  let : IsAffine W.left := inferInstanceAs (IsAffine (Spec (.of A)))
  let i : W ⟶ G := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap G U hU
  let : IsOpenImmersion i.left := by change IsOpenImmersion hU.fromSpec; infer_instance
  let e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints W := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A p
  have he : e ≫ i = 1 := hp
  let : Algebra Γ(W.left, ⊤) ℂ := InvariantAlgebraicForms.identityChartPointAlgebra e
  let : IsScalarTower ℂ Γ(W.left, ⊤) ℂ := IsScalarTower.of_algHom (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv W e)
  have hs : ∀ a : Γ(W.left, ⊤), algebraMap Γ(W.left, ⊤) ℂ a = AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv W e a :=
    fun _ => rfl
  exact ⟨invariantHolomorphicAlgebraicLift i e he hs,
    invariantHolomorphicAlgebraicLift_realization i e he hs⟩

def groupHolomorphicAlgebraicLift :
    InvariantHolomorphicDimension.invariantHolomorphicSubmodule (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel G) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) →ₗ[ℂ] AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms G :=
  (exists_groupHolomorphicAlgebraicLift G).choose

theorem groupHolomorphicAlgebraicLift_realization
    (form : InvariantHolomorphicDimension.invariantHolomorphicSubmodule (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel G) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G)) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm G (groupHolomorphicAlgebraicLift G form) = form.val.val :=
  (exists_groupHolomorphicAlgebraicLift G).choose_spec form

end

end OAI.RepresentationTheory.Theta.Geometric.GroupHolomorphicLift
