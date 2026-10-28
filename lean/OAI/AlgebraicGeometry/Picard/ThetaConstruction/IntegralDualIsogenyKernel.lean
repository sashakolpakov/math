import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualModel
import OAI.RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation

/-! # Integral Dual Isogeny Kernel -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The actual lattice isogeny retains its exact period comparison.
Every complex kernel point lifts to the original integral dual lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}

local instance IntegralDualIsogenyKernel.Geometric.dualKernelIntegral (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance IntegralDualIsogenyKernel.Geometric.dualKernelSmooth (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

section
variable (N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T)

def IntegralDualModel.Geometric.IntegralDualAlgebraicModel.periodAddEquiv : T.integralDualPeriodData.periodTorus ≃+
    Additive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N.abelian.toOver) where
  toFun t := Additive.ofMul (N.period t)
  invFun a := N.period.symm a.toMul
  left_inv := N.period.symm_apply_apply
  right_inv := N.period.apply_symm_apply
  map_add' := N.period_add

theorem IntegralDualModel.Geometric.IntegralDualAlgebraicModel.period_zero : N.period 0 = 1 := congrArg Additive.toMul N.periodAddEquiv.map_zero

end

structure IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny (M : PeriodModel.Geometric.AlgebraicPeriodModel T) (N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T) where
  isogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny M.abelianScheme N.abelianScheme
  etale : Etale isogeny.hom.left
  comparison : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map isogeny.hom (M.period t) = N.period (IntegralDualModel.Geometric.integralDualTorusMap T t)

attribute [instance] IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.etale

theorem IntegralDualIsogenyKernel.Geometric.exists_integralDualLatticeIsogeny (M : PeriodModel.Geometric.AlgebraicPeriodModel T) :
    ∃ N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T, Nonempty (IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N) := by
  obtain ⟨N, p, hp, hc⟩ := IntegralDualModel.Geometric.exists_integral_dual_algebraic_isogeny M
  exact ⟨N, ⟨⟨p, hp, hc⟩⟩⟩

namespace IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny
variable {M : PeriodModel.Geometric.AlgebraicPeriodModel T} {N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T}
    (p : IntegralDualLatticeIsogeny M N)

theorem kernel_lattice_lift (a : p.isogeny.kernelAt (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) :
    ∃ v : T.integralDualLattice, M.period (QuotientAddGroup.mk v.val) = a.val := by
  obtain ⟨t, ht⟩ := M.period.surjective a.val
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
  have ha : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.isogeny.hom (M.period (QuotientAddGroup.mk v)) = 1 := by
    have he : M.period (QuotientAddGroup.mk v) = a.val := ht
    exact (congrArg (fun z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver =>
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.isogeny.hom z) he).trans a.property
  rw [p.comparison] at ha
  have hz := N.period.injective (ha.trans N.period_zero.symm)
  change (QuotientAddGroup.mk v : T.integralDualPeriodData.periodTorus) = 0 at hz
  have hz' : (QuotientAddGroup.mk (show DefinitionsIntegral.Tangent g from v) :
      DefinitionsIntegral.Tangent g ⧸ T.integralDualLattice.toAddSubgroup) = 0 := hz
  exact ⟨⟨v, (QuotientAddGroup.eq_zero_iff (show DefinitionsIntegral.Tangent g from v)).mp hz'⟩, ht⟩

theorem kernel_translation_preserves (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hL : ∀ v : T.integralDualLattice,
      Nonempty ((L.pullback (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian
        (M.period (QuotientAddGroup.mk v.val))).left).sheaf ≅ L.sheaf))
    (a : p.isogeny.kernelAt (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) :
    Nonempty ((L.pullback (RepresentationTheory.Theta.Geometric.AlgebraicTranslation.abelianTranslation M.abelian a.val).left).sheaf ≅ L.sheaf) := by
  obtain ⟨v, hv⟩ := p.kernel_lattice_lift a
  rw [← hv]
  exact hL v

end IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
