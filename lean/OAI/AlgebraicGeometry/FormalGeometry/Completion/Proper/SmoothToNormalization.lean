import OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothToNormalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizationComponentCover

/-! # Smooth To Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.SmoothToNormalization.Construction

noncomputable section

/-! # Completion: smoothness of the entire actual map to normalization -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- The actual connected components cover a Noetherian scheme by open subschemes. -/
def noetherianComponentCover (X : Scheme.{u}) [IsNoetherian X] : X.OpenCover where
  I₀ := X
  X x := (FiberComponents.Construction.noetherianComponentOpen X x).toScheme
  f x := (FiberComponents.Construction.noetherianComponentOpen X x).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x => ⟨x, ⟨x, mem_connectedComponent⟩, rfl⟩, inferInstance⟩

/-- Smoothness of the actual first normalization factor does not require a connected total space. -/
theorem proper_smooth_family_toNormalization_smooth (K : Type u) [Field K]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (CommRingCat.of K)) [IsProper pX] [Smooth pX]
    (f : X ⟶ Y) [IsProper f] [Smooth f] : Smooth f.toNormalization := by
  have : IsNoetherian X := FiberComponents.Construction.properField_isNoetherian K pX
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) (noetherianComponentCover X)]
  intro x
  let U := FiberComponents.Construction.noetherianComponentOpen X x
  let f' := NormalizationComponentCover.Construction.properComponentFamily f x
  have : Smooth f' := by unfold f' NormalizationComponentCover.Construction.properComponentFamily; infer_instance
  have : Smooth f'.toNormalization :=
    SmoothToNormalization.Construction.proper_smooth_toNormalization_smooth K (U.ι ≫ pX) f'
  have : Smooth (f'.toNormalization ≫ NormalizationComponentCover.Construction.properComponentNormalizationMap f x) := inferInstance
  change Smooth (U.ι ≫ f.toNormalization)
  rw [← ClopenNormalization.Construction.clopenNormalizationMap_toNormalization f U isClosed_connectedComponent]
  exact this

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.SmoothToNormalization.Construction
