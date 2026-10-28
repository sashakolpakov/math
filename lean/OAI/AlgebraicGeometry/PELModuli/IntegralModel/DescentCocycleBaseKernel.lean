import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleChange

/-! # Descent Cocycle Base Kernel -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleBaseKernel.DescentCocycle

noncomputable section

/-! The family overlap is the actual base change of a specified
kernel-pair presentation of its base cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
    {B T X R : C} (u : T ⟶ B) (a : X ⟶ T) (s t : R ⟶ T) (hk : IsKernelPair u s t)

def baseKernelProjection : DescentCocycleChange.DescentCocycle.overlap u a ⟶ R :=
  hk.lift (DescentCocycleChange.DescentCocycle.source u a ≫ a) (DescentCocycleChange.DescentCocycle.base u a) ((Category.assoc _ _ _).trans (DescentCocycleChange.DescentCocycle.source_condition u a))

theorem baseKernelProjection_source : baseKernelProjection u a s t hk ≫ s = DescentCocycleChange.DescentCocycle.source u a ≫ a :=
  hk.lift_fst _ _ _

theorem baseKernelProjection_target : baseKernelProjection u a s t hk ≫ t = DescentCocycleChange.DescentCocycle.base u a :=
  hk.lift_snd _ _ _

theorem baseKernelProjection_square :
    IsPullback (DescentCocycleChange.DescentCocycle.source u a) (baseKernelProjection u a s t hk) a s := by
  have h : IsPullback (DescentCocycleChange.DescentCocycle.source u a) (baseKernelProjection u a s t hk ≫ t) (a ≫ u) u := by
    rw [baseKernelProjection_target]
    exact IsPullback.of_hasPullback _ _
  exact h.of_bot (baseKernelProjection_source u a s t hk).symm hk

variable (z : T ⟶ X) (hz : z ≫ a = 𝟙 T)

def baseKernelSection : R ⟶ DescentCocycleChange.DescentCocycle.overlap u a :=
  pullback.lift (s ≫ z) t (by
    rw [Category.assoc, ← Category.assoc z, hz, Category.id_comp]
    exact hk.w)

theorem baseKernelSection_projection :
    baseKernelSection u a s t hk z hz ≫ baseKernelProjection u a s t hk = 𝟙 R := by
  apply hk.hom_ext
  · rw [Category.assoc, baseKernelProjection_source, ← Category.assoc]
    rw [show baseKernelSection u a s t hk z hz ≫ DescentCocycleChange.DescentCocycle.source u a = s ≫ z from pullback.lift_fst _ _ _,
      Category.assoc, hz, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, baseKernelProjection_target]
    exact (pullback.lift_snd _ _ _).trans (Category.id_comp t).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleBaseKernel.DescentCocycle
