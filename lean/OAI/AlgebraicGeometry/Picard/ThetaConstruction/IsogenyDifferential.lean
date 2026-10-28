import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualIsogenyKernel
import OAI.RepresentationTheory.Theta.Geometric.VectorPeriodDifferential
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps

/-! # Isogeny Differential -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The integral-dual lattice isogeny has bijective native differential,
as follows from its exact comparison with both period projections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.VectorPeriodDifferential

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel F} {D : IntegralDualModel.Geometric.IntegralDualAlgebraicModel F}
    (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M D)

local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.isogenyDerivative_integral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.isogenyDerivative_smooth (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

def IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.nativeMap : M.abelian.toOver ⟶ D.abelian.toOver := p.isogeny.hom

instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.nativeMap_isMonHom : IsMonHom p.nativeMap := p.isogeny.preservesGroup

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.mfderiv_bijective (a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    Function.Bijective (mfderiv (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel D.abelian))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap) a) := by
  obtain ⟨t, rfl⟩ := M.period.surjective a
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective t
  let m := fun v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space => M.period (QuotientAddGroup.mk v)
  let n := fun v : (ProjectivePeriodData.Geometric.projectivePeriodData F).space => D.period (QuotientAddGroup.mk v)
  have hcomp : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap ∘ m = n :=
    funext (fun v => p.comparison (QuotientAddGroup.mk v))
  have hm := RepresentationTheory.Theta.Geometric.VectorPeriodDifferential.vectorPeriod_mfderiv_bijective M.abelian M.period w
  have hn := RepresentationTheory.Theta.Geometric.VectorPeriodDifferential.vectorPeriod_mfderiv_bijective D.abelian D.period w
  have hc := mfderiv_comp w
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map p.nativeMap 1).mdifferentiableAt one_ne_zero)
    ((M.period.contMDiff.comp (ProjectivePeriodData.Geometric.projectivePeriodData F).periodProjection_contMDiff).mdifferentiableAt (by simp))
  apply (Function.Bijective.of_comp_iff
    (mfderiv (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel D.abelian))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap) (m w)) hm).mp
  change Function.Bijective ((mfderiv (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel D.abelian))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap) (m w)).comp
    (mfderiv (𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space)) (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) m w))
  change mfderiv (𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space)) (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel D.abelian))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap ∘ m) w =
      (mfderiv (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel D.abelian))
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap) (m w)).comp
      (mfderiv (𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData F).space)) (𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)) m w) at hc
  rw [hcomp] at hc
  exact hc ▸ hn

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
