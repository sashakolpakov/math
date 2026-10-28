import OAI.RepresentationTheory.Theta.Geometric.CotangentIdentityEvaluation
import OAI.RepresentationTheory.Theta.Geometric.PointCotangentPairing

/-! # Invariant Forms Faithfulness -/

namespace OAI.RepresentationTheory.Theta.Geometric.InvariantFormsFaithfulness

noncomputable section

/-! Evaluation at the identity detects the full cotangent vector, so
the actual construction of algebraic invariant forms is injective. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.CategoryTheory.MonObj

variable {G U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj G] [IsAffine U.left]
    (i : U ⟶ G) [IsOpenImmersion i.left]
    (e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U) (he : e ≫ i = 1)
    [Algebra Γ(U.left, ⊤) ℂ] [IsScalarTower ℂ Γ(U.left, ⊤) ℂ]
    (hscalar : ∀ a : Γ(U.left, ⊤), algebraMap Γ(U.left, ⊤) ℂ a = AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e a)

def identityCotangentEvaluation (δ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e)) :
    InvariantAlgebraicForms.identityChartCotangent U →ₗ[ℂ] ℂ :=
  (AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e) δ).comp
    (InvariantAlgebraicForms.identityCotangentTestValue i e he hscalar (CommAlgCat.of ℂ Γ(U.left, ⊤)) (CotangentIdentityEvaluation.affineIdentityTest U ≫ i))

theorem identityCotangentEvaluation_pairing (δ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e)) :
    identityCotangentEvaluation i e he hscalar δ =
      PointCotangentPairing.pointCotangentPairingEquiv (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e) hscalar δ := by
  apply CotangentValueExt.pointCotangent_complexLinearMap_ext
  intro a
  rw [PointCotangentPairing.pointCotangentPairingEquiv_D]
  exact CotangentIdentityEvaluation.identityCotangentOneForm_atIdentity_D
    (R := CommAlgCat.of ℂ Γ(U.left, ⊤)) (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e) δ i e he hscalar
    (AlgHom.id ℂ Γ(U.left, ⊤)) (AlgHom.comp_id _) a

theorem identityCotangentOneForm_injective :
    Function.Injective (InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  apply PointCotangentPairing.pointCotangentPairing_separates (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e) hscalar v
  intro δ
  rw [← identityCotangentEvaluation_pairing i e he hscalar δ]
  change AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e) δ
    ((InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar v).val (CommAlgCat.of ℂ Γ(U.left, ⊤))
      (CotangentIdentityEvaluation.affineIdentityTest U ≫ i)) = 0
  rw [hv]
  exact map_zero _

end

end OAI.RepresentationTheory.Theta.Geometric.InvariantFormsFaithfulness
