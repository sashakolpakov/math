import OAI.RepresentationTheory.Theta.Geometric.IsoGlobalGauge
import OAI.RepresentationTheory.Theta.Geometric.QuotientPullback
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation

/-! # Iso Gauge -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoGauge

noncomputable section

/-! A genuine isomorphism from a translated algebraic theta quotient
produces the global holomorphic gauge used in the kernel criterion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem exists_holomorphic_translationGauge_of_native_iso
    {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hdeg : G.degree = F.degree + 1) (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (he : ∀ u v, e (u + v) = e u * e v)
    (f : A.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (g : A.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (hf : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
      (F.projectiveMap t))
    (hg : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (e t) = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension
      (G.projectiveMap t))
    (a : Φ.space)
    (u : ((AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback
      (AlgebraicTranslation.abelianTranslation A (e (QuotientAddGroup.mk a))).left).sheaf ≅
        (AlgebraicQuotient.algebraicThetaQuotient f.left g.left).sheaf) :
    ∃ c : Φ.space → ℂ, Differentiable ℂ c ∧ (∀ z, c z ≠ 0) ∧
      ∀ (l : Φ.periodIntegerLattice) (z : Φ.space),
        c (z + l.val) * J.value l (z + a) = J.value l z * c z := by
  let τ := AlgebraicTranslation.abelianTranslation A (e (QuotientAddGroup.mk a))
  let p := fun z : Φ.space => e (QuotientAddGroup.mk z)
  apply IsoGlobalGauge.exists_holomorphic_translationGauge_of_theta_iso F G hdeg (τ ≫ f) f (τ ≫ g) g
    ((QuotientPullback.thetaQuotientPullbackIso τ.left f.left g.left).symm ≪≫ u) a p
    ((e.contMDiff.comp Φ.periodProjection_contMDiff).mdifferentiable (by simp))
  · intro l z
    apply congrArg e
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have hz : z + l.val - z = l.val := by abel
    rw [hz]
    exact l.property
  · intro z
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map τ (e (QuotientAddGroup.mk z))) = _
    rw [AlgebraicTranslation.abelianTranslation_period A e he, ← QuotientAddGroup.mk_add, hf]
  · intro z
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map τ (e (QuotientAddGroup.mk z))) = _
    rw [AlgebraicTranslation.abelianTranslation_period A e he, ← QuotientAddGroup.mk_add, hg]
  · exact fun z => hf (QuotientAddGroup.mk z)
  · exact fun z => hg (QuotientAddGroup.mk z)

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoGauge
