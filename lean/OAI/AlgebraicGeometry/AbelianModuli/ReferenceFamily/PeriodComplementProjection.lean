import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure

/-! # Period Complement Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodComplementProjection.IntrinsicRationalPeriods

noncomputable section

/-! The conjugate period kernel maps isomorphically to the actual
native tangent space under the genuine period projection. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

def conjugatePeriodProjection : IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel A →ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A :=
  (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).domRestrict (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel A)

theorem conjugatePeriodProjection_bijective : Function.Bijective (conjugatePeriodProjection A) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    apply Subtype.ext
    exact IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.complexPeriodProjection_conjugate_joint_zero A u.val hu u.property
  · intro v
    obtain ⟨u, hu⟩ := Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection_surjective A v
    have hm : u ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A).ker ⊔ IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel A := by
      rw [(IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodKernels_complementary A).sup_eq_top]
      trivial
    obtain ⟨p, hp, q, hq, he⟩ := Submodule.mem_sup.mp hm
    refine ⟨⟨q, hq⟩, ?_⟩
    change Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A q = v
    have h := (congrArg (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A) he).trans hu
    simpa only [map_add, LinearMap.mem_ker.mp hp, zero_add] using h

def conjugatePeriodProjectionEquiv : IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel A ≃ₗ[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A :=
  LinearEquiv.ofBijective (conjugatePeriodProjection A) (conjugatePeriodProjection_bijective A)

theorem conjugatePeriodProjectionEquiv_apply (u : IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel A) :
    conjugatePeriodProjectionEquiv A u = Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection A u.val := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PeriodComplementProjection.IntrinsicRationalPeriods
