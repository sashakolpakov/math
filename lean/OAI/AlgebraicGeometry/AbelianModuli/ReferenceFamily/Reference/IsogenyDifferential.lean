import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel
import OAI.RepresentationTheory.Theta.Geometric.VectorPeriodDifferential
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

/-! # Isogeny Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The reference lattice isogeny has bijective native differential,
as follows from its exact comparison with both period projections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.VectorPeriodDifferential

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : IsogenyKernel.ReferenceLatticeIsogeny M D)

local instance IsogenyKernel.ReferenceLatticeIsogeny.isogenyDerivative_integral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance IsogenyKernel.ReferenceLatticeIsogeny.isogenyDerivative_smooth (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

def IsogenyKernel.ReferenceLatticeIsogeny.nativeMap : M.abelian.toOver ⟶ D.abelian.toOver := p.isogeny.hom

instance IsogenyKernel.ReferenceLatticeIsogeny.nativeMap_isMonHom : IsMonHom p.nativeMap := p.isogeny.preservesGroup

theorem IsogenyKernel.ReferenceLatticeIsogeny.mfderiv_bijective (a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    Function.Bijective (mfderiv (𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)) (𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel D.abelian))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap) a) := by
  obtain ⟨t, rfl⟩ := M.period.surjective a
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
  let m := fun v : F.periodData.space => M.period (QuotientAddGroup.mk v)
  let n := fun v : F.periodData.space => D.period (QuotientAddGroup.mk v)
  have hcomp : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap ∘ m = n :=
    funext (fun v => p.period_eq (QuotientAddGroup.mk v))
  have hm := RepresentationTheory.Theta.Geometric.VectorPeriodDifferential.vectorPeriod_mfderiv_bijective M.abelian M.period w
  have hn := RepresentationTheory.Theta.Geometric.VectorPeriodDifferential.vectorPeriod_mfderiv_bijective D.abelian D.period w
  have hc := mfderiv_comp w
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map p.nativeMap 1).mdifferentiableAt one_ne_zero)
    ((M.period.contMDiff.comp F.periodData.periodProjection_contMDiff).mdifferentiableAt (by simp))
  apply (Function.Bijective.of_comp_iff
    (mfderiv (𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)) (𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel D.abelian))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap) (m w)) hm).mp
  change Function.Bijective ((mfderiv (𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)) (𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel D.abelian))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap) (m w)).comp
    (mfderiv (𝓘(ℂ, F.periodData.space)) (𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)) m w))
  change mfderiv (𝓘(ℂ, F.periodData.space)) (𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel D.abelian))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap ∘ m) w =
      (mfderiv (𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)) (𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel D.abelian))
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap) (m w)).comp
      (mfderiv (𝓘(ℂ, F.periodData.space)) (𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)) m w) at hc
  rw [hcomp] at hc
  exact hc ▸ hn

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
