import OAI.RepresentationTheory.Theta.Geometric.VectorPeriodDifferential
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualNaturality

/-! # Vector Period Dual Points -/

namespace OAI.RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints

noncomputable section

/-! The actual dual-number point of a vector-period first jet commutes
with actual algebraic translation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

def vectorPeriodDualPoint {Φ : Torus.Data.CM.ProjectivePeriodData} (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (z a : Φ.space) : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ A.toOver :=
  (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv A.toOver (e (QuotientAddGroup.mk z))
    (mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, AlgebraicAction.AbelianModel A))
      (fun w => e (QuotientAddGroup.mk w)) z a)).val

theorem exists_vectorPeriodDualPoint {Φ : Torus.Data.CM.ProjectivePeriodData} (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (z : Φ.space) (r : AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints A.toOver (e (QuotientAddGroup.mk z))) :
    ∃ a : Φ.space, vectorPeriodDualPoint A e z a = r.val := by
  let t := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv A.toOver (e (QuotientAddGroup.mk z))
  obtain ⟨a, ha⟩ := (VectorPeriodDifferential.vectorPeriod_mfderiv_bijective A e z).surjective (t.symm r)
  exact ⟨a, congrArg Subtype.val ((congrArg t ha).trans (t.apply_symm_apply r))⟩

set_option backward.isDefEq.respectTransparency false in
theorem vectorPeriodDualPoint_translates {Φ : Torus.Data.CM.ProjectivePeriodData} (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (he : ∀ u v, e (u + v) = e u * e v) (z b a : Φ.space) :
    vectorPeriodDualPoint A e (z + b) a =
      vectorPeriodDualPoint A e z a ≫ AlgebraicTranslation.abelianTranslation A (e (QuotientAddGroup.mk b)) := by
  have hn := AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualNaturality.nativeSchemeTangentDual_natural
    (AlgebraicTranslation.abelianTranslation A (e (QuotientAddGroup.mk b))) (e (QuotientAddGroup.mk z))
    (mfderiv (𝓘(ℂ, Φ.space)) (𝓘(ℂ, AlgebraicAction.AbelianModel A))
      (fun w => e (QuotientAddGroup.mk w)) z a)
  have hp : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AlgebraicTranslation.abelianTranslation A (e (QuotientAddGroup.mk b)))
      (e (QuotientAddGroup.mk z)) = e (QuotientAddGroup.mk (z + b)) :=
    (AlgebraicTranslation.abelianTranslation_period A e he _ _).trans (congrArg e (QuotientAddGroup.mk_add _ z b).symm)
  rw [VectorPeriodDifferential.vectorPeriodTranslation_mfderiv A e he z b a, hp] at hn
  exact hn

theorem abelianTranslation_dualPoint (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) (r : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ A.toOver) :
    r ≫ AlgebraicTranslation.abelianTranslation A p = r * (toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ p) := by
  change r ≫ ((𝟙 A.toOver) * (Over.mkIdTerminal.from A.toOver ≫ p)) = _
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc]
  congr 1
  apply congrArg (fun f => f ≫ p)
  exact Over.mkIdTerminal.hom_ext _ _

end

end OAI.RepresentationTheory.Theta.Geometric.VectorPeriodDualPoints
