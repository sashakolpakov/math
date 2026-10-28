import OAI.RepresentationTheory.Theta.Geometric.InvariantFormsSmooth
import OAI.RepresentationTheory.Theta.Geometric.InvariantFormsFaithfulness
import OAI.RepresentationTheory.Theta.Geometric.InvariantHolomorphicDimension
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GlobalFormFaithfulness
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OpenPurity

/-! # Invariant Forms Realization -/

namespace OAI.RepresentationTheory.Theta.Geometric.InvariantFormsRealization

noncomputable section

/-! The algebraic cotangent construction embeds into the actual invariant
holomorphic forms through the canonical smooth realization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GlobalFormFaithfulness
attribute [local instance] InvariantFormsSmooth.nativeGroupRealLie InvariantFormsSmooth.nativeGroupComplexLie

variable {G U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] [G.left.IsSeparated] [IsAffine U.left]
    (i : U ⟶ G) [IsOpenImmersion i.left]
    (e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U) (he : e ≫ i = 1)
    [Algebra Γ(U.left, ⊤) ℂ] [IsScalarTower ℂ Γ(U.left, ⊤) ℂ]
    (hscalar : ∀ a : Γ(U.left, ⊤), algebraMap Γ(U.left, ⊤) ℂ a = AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e a)

def identityCotangentInvariantLinear : InvariantAlgebraicForms.identityChartCotangent U →ₗ[ℂ]
    InvariantHolomorphicDimension.invariantHolomorphicSubmodule (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel G) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) where
  toFun a := ⟨⟨AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm G (InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar a),
    InvariantFormsSmooth.identityCotangentOneForm_smooth_invariant i e he hscalar a⟩,
    AlgebraicGeometry.HodgeConjecture.CMExtraction.OpenPurity.Kaehler.globalSmoothForm_pure G (InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar a)⟩
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm G).comp (InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar)).map_add a b
  map_smul' c a := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm G).comp (InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar)).map_smul c a

theorem identityCotangentInvariantLinear_injective :
    Function.Injective (identityCotangentInvariantLinear i e he hscalar) := by
  intro a b h
  apply InvariantFormsFaithfulness.identityCotangentOneForm_injective i e he hscalar
  apply AlgebraicGeometry.AbelianScheme.TateComparison.GlobalFormFaithfulness.globalSmoothForm_injective G
  exact congrArg (fun z : InvariantHolomorphicDimension.invariantHolomorphicSubmodule
    (AlgebraicGeometry.Comparison.Betti.RegularSmoothness.NativeModel G) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) => z.val.val) h

end

end OAI.RepresentationTheory.Theta.Geometric.InvariantFormsRealization
