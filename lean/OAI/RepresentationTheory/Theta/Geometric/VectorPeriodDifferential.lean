import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation
import OAI.RepresentationTheory.Theta.Geometric.Torus.Derivative
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

/-! # Vector Period Differential -/

namespace OAI.RepresentationTheory.Theta.Geometric.VectorPeriodDifferential

noncomputable section

section

/-! The native vector-period uniformization has bijective differential
at every point, with its literal quotient projection retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem vectorPeriod_mfderiv_eq {Φ : Torus.Data.CM.ProjectivePeriodData} (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (z : Φ.space) :
    mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, AlgebraicAction.AbelianModel A)) (fun w => e (QuotientAddGroup.mk w)) z =
      mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, AlgebraicAction.AbelianModel A)) e (QuotientAddGroup.mk z) := by
  have H := mfderiv_comp z
    (e.contMDiff.mdifferentiableAt (x := QuotientAddGroup.mk z) (by simp))
    (Φ.periodProjection_contMDiff.mdifferentiableAt (x := z) (by simp))
  rw [Φ.periodProjection_mfderiv] at H
  exact H

theorem vectorPeriod_mfderiv_bijective {Φ : Torus.Data.CM.ProjectivePeriodData} (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (z : Φ.space) :
    Function.Bijective (mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, AlgebraicAction.AbelianModel A))
      (fun w => e (QuotientAddGroup.mk w)) z) := by
  rw [vectorPeriod_mfderiv_eq]
  exact (e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_bijective (by trivial)

end

/-! Differentiating the actual algebraic translation agrees with
translating the original vector-period parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

set_option backward.isDefEq.respectTransparency false in
theorem vectorPeriodTranslation_mfderiv {Φ : Torus.Data.CM.ProjectivePeriodData} (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (he : ∀ u v, e (u + v) = e u * e v) (z b a : Φ.space) :
    mfderiv (𝓘(ℂ, AlgebraicAction.AbelianModel A)) (𝓘(ℂ, AlgebraicAction.AbelianModel A))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AlgebraicTranslation.abelianTranslation A (e (QuotientAddGroup.mk b))))
      (e (QuotientAddGroup.mk z))
      (mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, AlgebraicAction.AbelianModel A))
        (fun w => e (QuotientAddGroup.mk w)) z a) =
      mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, AlgebraicAction.AbelianModel A))
        (fun w => e (QuotientAddGroup.mk w)) (z + b) a := by
  let p := fun w : Φ.space => e (QuotientAddGroup.mk w)
  let τ := AlgebraicTranslation.abelianTranslation A (e (QuotientAddGroup.mk b))
  have hp : MDifferentiable (𝓘(ℂ, Φ.space)) (𝓘(ℂ, AlgebraicAction.AbelianModel A)) p :=
    (e.contMDiff.comp Φ.periodProjection_contMDiff).mdifferentiable (by simp)
  have hadd := ((hasFDerivAt_id (𝕜 := ℂ) z).add_const b).hasMFDerivAt
  have hc := mfderiv_comp_apply z
    ((AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map τ 1).mdifferentiableAt one_ne_zero) (hp z) a
  have hd := mfderiv_comp_apply z (hp (z + b)) hadd.mdifferentiableAt a
  rw [hadd.mfderiv] at hd
  have heq : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map τ ∘ p = p ∘ (fun w => w + b) := by
    funext w
    exact (AlgebraicTranslation.abelianTranslation_period A e he (QuotientAddGroup.mk b) (QuotientAddGroup.mk w)).trans
      (congrArg e (QuotientAddGroup.mk_add _ w b).symm)
  change mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, AlgebraicAction.AbelianModel A))
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map τ ∘ p) z a = _ at hc
  rw [heq] at hc
  exact hc.symm.trans hd

end

end OAI.RepresentationTheory.Theta.Geometric.VectorPeriodDifferential
