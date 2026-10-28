import OAI.AlgebraicGeometry.Picard.ThetaConstruction.MarkedDiscriminant
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualModel

/-! # Integral Dual Torus Kernel -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The actual kernel of the integral-dual torus map is the
discriminant of the original marked integer form. -/

section
open OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualModel.Geometric

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} (T : DefinitionsIntegral.MarkedPolarizedTorus g E)

local instance DefinitionsIntegral.MarkedPolarizedTorus.integralDualPeriodNormal :
    T.integralDualPeriodData.periodIntegerLattice.toAddSubgroup.Normal :=
  inferInstanceAs (T.integralDualLattice.toAddSubgroup.Normal)

def DefinitionsIntegral.MarkedPolarizedTorus.latticeKernelLift : T.integralDualLattice →+ (IntegralDualModel.Geometric.integralDualTorusMap T).ker where
  toFun v := ⟨QuotientAddGroup.mk v.val, by
    change (QuotientAddGroup.mk v.val : DefinitionsIntegral.Tangent g ⧸ T.integralDualLattice.toAddSubgroup) = 0
    exact (QuotientAddGroup.eq_zero_iff v.val).mpr v.property⟩
  map_zero' := Subtype.ext (@QuotientAddGroup.mk_zero (DefinitionsIntegral.Tangent g) inferInstance T.lattice inferInstance)
  map_add' u v := Subtype.ext (@QuotientAddGroup.mk_add (DefinitionsIntegral.Tangent g)
    inferInstance T.lattice inferInstance u.val v.val)

theorem DefinitionsIntegral.MarkedPolarizedTorus.latticeKernelLift_surjective : Function.Surjective T.latticeKernelLift := by
  intro t
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk_surjective t.val
  have hzero := t.property
  change IntegralDualModel.Geometric.integralDualTorusMap T t.val = 0 at hzero
  rw [← hv] at hzero
  change (QuotientAddGroup.mk v : DefinitionsIntegral.Tangent g ⧸ T.integralDualLattice.toAddSubgroup) = 0 at hzero
  have hvL : v ∈ T.integralDualLattice := (@QuotientAddGroup.eq_zero_iff (DefinitionsIntegral.Tangent g) inferInstance
    T.integralDualLattice.toAddSubgroup inferInstance v).mp hzero
  exact ⟨⟨v, hvL⟩, Subtype.ext hv⟩

theorem DefinitionsIntegral.MarkedPolarizedTorus.latticeKernelLift_ker : T.latticeKernelLift.toIntLinearMap.ker = T.integralDualInclusion.range := by
  ext v
  change T.latticeKernelLift v = 0 ↔ ∃ u, T.integralDualInclusion u = v
  constructor
  · intro h
    have hz := congrArg Subtype.val h
    have hv : v.val ∈ T.lattice := (QuotientAddGroup.eq_zero_iff v.val).mp hz
    exact ⟨⟨v.val, hv⟩, Subtype.ext rfl⟩
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    exact (QuotientAddGroup.eq_zero_iff u.val).mpr u.property

def DefinitionsIntegral.MarkedPolarizedTorus.discriminantKernelEquiv :
    (T.integralDualLattice ⧸ T.integralDualInclusion.range) ≃+ (IntegralDualModel.Geometric.integralDualTorusMap T).ker :=
  ((Submodule.quotEquivOfEq _ _ T.latticeKernelLift_ker.symm).trans
    (LinearMap.quotKerEquivOfSurjective T.latticeKernelLift.toIntLinearMap
      T.latticeKernelLift_surjective)).toAddEquiv

def DefinitionsIntegral.MarkedPolarizedTorus.latticeKernelTypeEquiv (D : PolarizationTypeData.Geometric.IntegralPolarizationType E) :
    (IntegralDualModel.Geometric.integralDualTorusMap T).ker ≃+
      ((∀ i : Fin g, ZMod (D.elementaryDivisors i)) ×
        (∀ i : Fin g, ZMod (D.elementaryDivisors i))) :=
  T.discriminantKernelEquiv.symm.trans (T.discriminantTypeEquiv D)

end

namespace IntegralDualTorusKernel.Geometric.MarkedPolarizedTorus

end IntegralDualTorusKernel.Geometric.MarkedPolarizedTorus

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
