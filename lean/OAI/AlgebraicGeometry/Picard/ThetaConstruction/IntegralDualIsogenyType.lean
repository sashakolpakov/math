import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualTorusKernel
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualIsogenyKernel
import OAI.RepresentationTheory.Theta.Geometric.IsogenyKernelDegree

/-! # Integral Dual Isogeny Type -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The actual algebraic lattice isogeny has the fixed elementary
divisors and finite-flat degree over every geometric field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel T} {N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T}
    (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N)

local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.kernelSource_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.kernelSource_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.kernelTarget_integral : IsIntegral N.abelian.toOver.left := N.abelian.variety.property
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.kernelTarget_smooth : Smooth N.abelian.toOver.hom := N.abelian.variety.presentation.smooth

def IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.complexKernelEquiv : Multiplicative (IntegralDualModel.Geometric.integralDualTorusMap T).ker ≃*
    p.isogeny.kernelAt (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase) where
  toFun t := ⟨M.period t.toAdd.val, by
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.isogeny.hom (M.period t.toAdd.val) = 1
    rw [p.comparison, show IntegralDualModel.Geometric.integralDualTorusMap T t.toAdd.val = 0 from t.toAdd.property]
    exact N.period_zero⟩
  invFun a := Multiplicative.ofAdd ⟨M.period.symm a.val, by
    apply N.period.injective
    exact (p.comparison _).symm.trans
      ((congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.isogeny.hom) (M.period.apply_symm_apply a.val)).trans
        (a.property.trans N.period_zero.symm))⟩
  left_inv t := by
    apply congrArg Multiplicative.ofAdd
    exact Subtype.ext (M.period.symm_apply_apply t.toAdd.val)
  right_inv a := Subtype.ext (M.period.apply_symm_apply a.val)
  map_mul' t u := Subtype.ext (M.period_add t.toAdd.val u.toAdd.val)

def IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.typeKernelLabels (D : PolarizationTypeData.Geometric.IntegralPolarizationType E) :
    Multiplicative ((∀ i : Fin g, ZMod (D.elementaryDivisors i)) ×
      (∀ i : Fin g, ZMod (D.elementaryDivisors i))) ≃*
        p.isogeny.kernelAt (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase) :=
  (AddEquiv.toMultiplicative (T.latticeKernelTypeEquiv D).symm).trans p.complexKernelEquiv

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.geometricKernel (D : PolarizationTypeData.Geometric.IntegralPolarizationType E)
    (K : Type) [Field K] (z : Spec (.of K) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    Nonempty (p.isogeny.kernelAt (Over.mk z) ≃*
      Multiplicative ((∀ i : Fin g, ZMod (D.elementaryDivisors i)) ×
        (∀ i : Fin g, ZMod (D.elementaryDivisors i)))) :=
  ⟨(RepresentationTheory.Theta.Geometric.IsogenyKernelLabels.isogenyKernel_geometric_labels p.isogeny _ (p.typeKernelLabels D) K z).some.symm⟩

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.hasPolarizationType (D : PolarizationTypeData.Geometric.IntegralPolarizationType E) :
    p.isogeny.HasPolarizationType D.elementaryDivisors := by
  let : IsIntegral N.abelianScheme.scheme.left := N.abelian.variety.property
  let (i : Fin g) : NeZero (D.elementaryDivisors i) := ⟨ne_of_gt (D.positive i)⟩
  constructor
  · intro b
    rw [RepresentationTheory.Theta.Geometric.IsogenyKernelDegree.isogeny_finrank_of_complex_labels p.isogeny _ (p.typeKernelLabels D) b]
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_prod,
      Fintype.card_pi, ZMod.card, pow_two]
  · intro K _ _ z
    exact p.geometricKernel D K z

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
