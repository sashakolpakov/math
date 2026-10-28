import OAI.RepresentationTheory.Theta.Geometric.NestedMultilinearRestriction

/-! # Power Open Frame Restriction -/

namespace OAI.RepresentationTheory.Theta.Geometric.PowerOpenFrameRestriction

noncomputable section

/-! Power frames of the actual algebraic module sheaf commute with native
restriction to smaller opens. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem tensorPowerOpenFrame_restrict {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) (n : ℕ) :
    AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h (AlgebraicPowerFrames.tensorPowerOpenFrame M U e n) =
      AlgebraicPowerFrames.tensorPowerOpenFrame M V (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h e) n := by
  rw [← AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition.nativeOpenFrame_eq_over, ← AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition.nativeOpenFrame_eq_over]
  apply Iso.ext
  apply AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrict_hom_ext V.ι M n
  change ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear M n).restrict V.ι).postcomp
      ((AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition.nestedRestrictionIso h (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule M n)).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE h)).map (PowerFrameMultilinear.tensorPowerRestrictedFrame U.ι M e n).hom ≫
        (Scheme.Modules.restrictUnitIso (X.homOfLE h)).hom) =
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear M n).restrict V.ι).postcomp
      (PowerFrameMultilinear.tensorPowerRestrictedFrame V.ι M (AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition.nativeOpenFrame h e) n).hom
  rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp, ← NestedMultilinearRestriction.multilinear_nestedRestriction,
    ← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_postcomp, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.postcomp_comp,
    ← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.restrict_postcomp, PowerFrameMultilinear.tensorPowerRestrictedFrame_spec,
    GlobalPowerFrameRestriction.framedMultilinear_restrict, PowerFrameMultilinear.tensorPowerRestrictedFrame_spec]
  unfold PowerFrameMultilinear.framedMultilinear
  rw [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.precomp_comp]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric.PowerOpenFrameRestriction
